{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, RecordWildCards, OverloadedStrings, TemplateHaskell #-}
module Lamdu.GUI.ExpressionEdit.HoleEdit.ResultGroups
    ( makeAll, HaveHiddenResults(..)
    , Result(..)
    , ResultsList(..), rlExtraResultsPrefixId, rlMain, rlExtra
    , prefixId
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (filterM)
import           Control.Monad.ListT (ListT)
import           Control.MonadA (MonadA)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Char as Char
import           Data.Function (on)
import           Data.List (isInfixOf, isPrefixOf)
import qualified Data.List.Class as ListClass
import           Data.List.Utils (sortOn)
import           Data.Monoid ((<>))
import           Data.Store.Transaction (Transaction)
import qualified Data.Store.Transaction as Transaction
import qualified Graphics.UI.Bottle.WidgetId as WidgetId
import qualified Lamdu.Config as Config
import qualified Lamdu.Data.Anchors as Anchors
import qualified Lamdu.Expr.IRef as ExprIRef
import qualified Lamdu.Expr.Lens as ExprLens
import qualified Lamdu.Expr.Val as V
import           Lamdu.Formatting (Format(..))
import           Lamdu.GUI.ExpressionEdit.HoleEdit.Info (HoleInfo(..), hiSearchTerm)
import qualified Lamdu.GUI.ExpressionEdit.HoleEdit.ValTerms as ValTerms
import qualified Lamdu.GUI.ExpressionEdit.HoleEdit.WidgetIds as HoleWidgetIds
import           Lamdu.GUI.ExpressionGui.Monad (ExprGuiM)
import qualified Lamdu.GUI.ExpressionGui.Monad as ExprGuiM
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import           Lamdu.Sugar.Names.Types (Name(..))
import qualified Lamdu.Sugar.Types as Sugar

import           Prelude.Compat

type T = Transaction

data Group m = Group
    { _groupSearchTerms :: [String]
    , _groupId :: WidgetId.Id
    , _groupResults ::
        ListT (T m) (Sugar.HoleResultScore, T m (Sugar.HoleResult (Name m) m))
    }

Lens.makeLenses ''Group

data ResultType = GoodResult | BadResult
    deriving (Eq, Ord)

data Result m = Result
    { rType :: ResultType
    , -- Warning: This transaction should be ran at most once!
        -- Running it more than once will cause inconsistencies.
        rHoleResult :: T m (Sugar.HoleResult (Name m) m)
    , rId :: WidgetId.Id
    }

data IsPreferred = Preferred | NotPreferred
    deriving (Eq, Ord)

data ResultsList m = ResultsList
    { _rlPreferred :: IsPreferred -- Move to top of result list
    , _rlExtraResultsPrefixId :: WidgetId.Id
    , _rlMain :: Result m
    , _rlExtra :: [Result m]
    }
Lens.makeLenses ''ResultsList

prefixId :: HoleInfo m -> WidgetId.Id
prefixId = HoleWidgetIds.hidResultsPrefix . hiIds

mResultsListOf ::
    HoleInfo m -> WidgetId.Id ->
    [(ResultType, T m (Sugar.HoleResult (Name m) m))] ->
    Maybe (ResultsList m)
mResultsListOf _ _ [] = Nothing
mResultsListOf holeInfo baseId (x:xs) = Just
    ResultsList
    { _rlPreferred = NotPreferred
    , _rlExtraResultsPrefixId = extraResultsPrefixId
    , _rlMain = mkResult (prefixId holeInfo <> baseId) x
    , _rlExtra = zipWith mkExtra [(0::Int)..] xs
    }
    where
        mkExtra = mkResult . extraResultId
        extraResultId i = WidgetId.joinId extraResultsPrefixId [BS8.pack (show i)]
        extraResultsPrefixId = prefixId holeInfo <> WidgetId.Id ["extra results"] <> baseId
        mkResult resultId (typ, holeResult) =
            Result
            { rType = typ
            , rHoleResult = holeResult
            , rId = resultId
            }

makeResultsList ::
    MonadA m => HoleInfo m -> Group m ->
    T m (Maybe (ResultsList m))
makeResultsList holeInfo group =
    group ^. groupResults
    & ListClass.toList
    <&> sortOn (^. _1)
    <&> Lens.mapped . _1 %~ checkGood
    <&> mResultsListOf holeInfo (group ^. groupId)
    <&> Lens.mapped %~ rlPreferred .~ toPreferred
    where
        checkGood x
            | x < [5] = GoodResult
            | otherwise = BadResult
        toPreferred
            | [searchTerm] == group ^. groupSearchTerms = Preferred
            | otherwise = NotPreferred
        searchTerm = hiSearchTerm holeInfo

data HaveHiddenResults = HaveHiddenResults | NoHiddenResults

collectResults :: MonadA m => Config.Hole -> ListT m (ResultsList f) -> m ([ResultsList f], HaveHiddenResults)
collectResults Config.Hole{..} resultsM =
    do
        (collectedResults, remainingResultsM) <-
            ListClass.splitWhenM (return . (>= holeResultCount) . length . fst) $
            ListClass.scanl step ([], []) resultsM
        remainingResults <- ListClass.toList $ ListClass.take 2 remainingResultsM
        let results =
                last (collectedResults ++ remainingResults)
                & Lens.both %~ reverse
        results
            & _1 %~ sortOn resultsListScore
            & uncurry (++)
            & splitAt holeResultCount
            & _2 %~ haveHiddenResults
            & return
    where
        haveHiddenResults [] = NoHiddenResults
        haveHiddenResults _ = HaveHiddenResults
        resultsListScore x = (x ^. rlPreferred, rType (x ^. rlMain))
        step results x =
            results
            & case resultsListScore x of
                (NotPreferred, BadResult) -> _2
                _ -> _1
                %~ (x :)

makeAll ::
    MonadA m => HoleInfo m ->
    ExprGuiM m ([ResultsList m], HaveHiddenResults)
makeAll holeInfo =
    do
        config <- ExprGuiM.readConfig <&> Config.hole
        makeAllGroups holeInfo
            <&> ListClass.fromList
            <&> ListClass.mapL (makeResultsList holeInfo)
            <&> ListClass.catMaybes
            >>= collectResults config
            & ExprGuiM.transaction

mkGroup :: MonadA m => Sugar.HoleOption (Name m) m -> T m (Group m)
mkGroup option =
    do
        sugaredBaseExpr <- option ^. Sugar.hoSugaredBaseExpr
        names <- option ^. Sugar.hoNames
        pure Group
            { _groupSearchTerms =
              ValTerms.body (sugaredBaseExpr ^. Sugar.rBody) <>
              (names <&> snd <&> ValTerms.ofName)
            , _groupResults = option ^. Sugar.hoResults
            , _groupId = WidgetIds.hash (option ^. Sugar.hoVal)
            }

tryBuildLiteral ::
    (Format a, MonadA m) => (a -> Sugar.Literal) -> HoleInfo m ->
    T m (Maybe (Sugar.HoleOption (Name m) m))
tryBuildLiteral mkLiteral holeInfo =
    hiSearchTerm holeInfo
    & tryParse
    <&> mkLiteral
    & Lens._Just %%~ hiHole holeInfo ^. Sugar.holeActions . Sugar.holeOptionLiteral

literalGroups :: MonadA m => HoleInfo m -> T m [Sugar.HoleOption (Name m) m]
literalGroups holeInfo =
    [ tryBuildLiteral Sugar.LiteralNum holeInfo
    , tryBuildLiteral Sugar.LiteralBytes holeInfo
    , tryBuildLiteral Sugar.LiteralText holeInfo
    ] & sequenceA <&> (^.. Lens.traverse . Lens._Just)

insensitivePrefixOf :: String -> String -> Bool
insensitivePrefixOf = isPrefixOf `on` map Char.toLower

insensitiveInfixOf :: String -> String -> Bool
insensitiveInfixOf = isInfixOf `on` map Char.toLower

globalNameMatches :: Monad m => String -> V.Val () -> T m Bool
globalNameMatches searchTerm (V.Val () body) =
    case body of
    V.BLeaf (V.LGlobal globalId) -> verifyName (ExprIRef.defI globalId)
    V.BToNom (V.Nom nomId h) | isHole h -> verifyName nomId
    V.BFromNom (V.Nom nomId h) | isHole h -> verifyName nomId
    _ -> return True
    where
        isHole = Lens.notNullOf ExprLens.valHole
        verifyName entity =
            Anchors.assocNameRef entity & Transaction.getP
            <&> (searchTerm `insensitiveInfixOf`)

makeAllGroups :: MonadA m => HoleInfo m -> T m [Group m]
makeAllGroups holeInfo =
    (++)
    <$> (literalGroups holeInfo >>= mapM mkGroup)
    <*> (hiHole holeInfo ^. Sugar.holeActions . Sugar.holeOptions
         >>= preFilter
         >>= mapM mkGroup
         <&> holeMatches (hiSearchTerm holeInfo))
    where
        -- This is used to filter globals/nominals prior to sugaring
        -- to avoid type-checking globals/nominals if the name doesn't
        -- match. After sugaring, we also need a filter for the
        -- non-globals.
        preFilter =
            filterM
            (globalNameMatches (hiSearchTerm holeInfo) .
             (^. Sugar.hoVal))

groupOrdering :: String -> Group m -> [Bool]
groupOrdering searchTerm group =
    map not
    [ null (group ^. groupSearchTerms)
    , match (==)
    , match isPrefixOf
    , match insensitivePrefixOf
    , match isInfixOf
    ]
    where
        match f = any (f searchTerm) (group ^. groupSearchTerms)

holeMatches :: String -> [Group m] -> [Group m]
holeMatches searchTerm groups =
    groups
    & filterBySearchTerm
    & sortOn (groupOrdering searchTerm)
    where
        filterBySearchTerm
            | null searchTerm = id
            | otherwise = filter nameMatch
        nameMatch group = any (insensitiveInfixOf searchTerm) (group ^. groupSearchTerms)
