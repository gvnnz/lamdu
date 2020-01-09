-- | Common completions for holes and fragments

{-# LANGUAGE TypeFamilies, TypeOperators, TupleSections #-}
module Lamdu.Sugar.Convert.Completions
    ( suggestForType, querySuggesteds
    , suggestForTypeObvious, suggestForTypeUTermWithoutSplit, suggestCaseWith
    ) where

import qualified Control.Lens as Lens
import           Control.Monad.State
import           Control.Monad.Transaction (MonadTransaction)
import           Hyper
import           Hyper.Infer (InferResult, inferResult)
import           Hyper.Type.AST.FuncType
import           Hyper.Type.AST.Row (RowExtend(..))
import           Hyper.Type.Prune
import           Hyper.Unify
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New (newUnbound, newTerm)
import           Hyper.Unify.Term
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T
import           Lamdu.Sugar.Internal (InternalName, nameWithContext, nameWithoutContext, taggedName)
import qualified Lamdu.Sugar.Types as Sugar

import           Lamdu.Prelude

-- | Term with unifiable type annotations
type TypedTerm m = Ann (InferResult (UVarOf m)) # V.Term

lamRecordParams :: V.Var -> Ann a # HCompose Prune T.Type -> [InternalName]
lamRecordParams param typ =
    typ ^?
    hVal . hcomposed _Unpruned . T._TRecord . _HCompose
    & maybe [] goRow
    where
        goRow row =
            case row ^? hVal . hcomposed _Unpruned of
            Just (T.RExtend (V.RowExtend tag _ rest)) ->
                nameWithContext param tag : goRow (rest ^. _HCompose)
            _ -> []

compositeTagNames ::
    Lens.ATraversal' (V.Term # Ann a) (V.RowExtend T.Tag V.Term V.Term # Ann a) ->
    Ann a # V.Term ->
    [InternalName]
compositeTagNames cons term =
    case term ^? hVal . Lens.cloneTraversal cons of
    Nothing -> []
    Just (RowExtend tag _ rest) -> nameWithoutContext tag : compositeTagNames cons rest

querySuggesteds ::
    MonadTransaction n i =>
    Ann a # V.Term ->
    StateT (Sugar.Queries InternalName i) i Sugar.Priority
querySuggesteds term =
    StateT $
    \queries ->
    let queryConsume l x =
            case queries ^. Lens.cloneLens l of
            Nothing -> pure (Sugar.PriorityAvoid, queries)
            Just q -> q x <&> (, queries & Lens.cloneLens l .~ Nothing)
        queryConsumeAny l mkName =
            case queries ^. Lens.cloneLens l of
            Sugar.QueryNone -> pure (Sugar.PriorityAvoid, queries)
            Sugar.QueryTypeDirected q -> mkName >>= q <&> (, queries)
            Sugar.QueryAny q ->
                do
                    x <- mkName
                    q x <&>
                        (, queries
                            & Lens.cloneLens l . Sugar._QueryAny . Lens.imapped . Lens.index x
                            .~ pure Sugar.PriorityAvoid
                        )
    in
    case term ^. hVal of
    V.BLam (V.TypedLam param typ _) -> queryConsume Sugar.qLam (lamRecordParams param typ)
    V.BLeaf V.LRecEmpty -> queryConsume Sugar.qRecord []
    V.BRecExtend{} -> queryConsume Sugar.qRecord (compositeTagNames V._BRecExtend term)
    V.BLeaf V.LAbsurd -> queryConsume Sugar.qCase []
    V.BCase{} -> queryConsume Sugar.qCase (compositeTagNames V._BCase term)
    V.BGetField (V.GetField _ tag) -> queryConsumeAny Sugar.qGetField (pure (nameWithoutContext tag))
    V.BInject (V.Inject tag _) -> queryConsumeAny Sugar.qInject (pure (nameWithoutContext tag))
    V.BToNom (V.ToNom nom _) -> queryConsumeAny Sugar.qNom (taggedName nom)
    V.BApp{} -> error "Suggest shouldn't suggest apply"
    V.BLeaf V.LHole -> error "Suggest shouldn't suggest hole"
    V.BLeaf V.LVar{} -> error "Suggest shouldn't suggest variable"
    V.BLeaf V.LLiteral{} -> error "Suggest shouldn't suggest literal"
    V.BLeaf V.LFromNom{} -> error "Suggest shouldn't suggest from-nom"

lookupBody :: Unify f t => UVarOf f # t -> f (Maybe (t # UVarOf f))
lookupBody x = semiPruneLookup x <&> (^? _2 . _UTerm . uBody)

-- | Suggest values that fit a type, may "split" once, to suggest many
-- injects for a sum type. These are offerred in holes (not fragments).
suggestForType ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Type -> m [TypedTerm m]
suggestForType t =
    -- TODO: DSL for matching/deref'ing UVar structure
    lookupBody t
    >>= \case
    Just (T.TVariant r) -> forVariant r
    typ -> suggestForTypeUTermWithoutSplit typ <&> (^.. Lens._Just)
    <&> Lens.mapped %~ Ann (inferResult # t)

forVariant ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Row -> m [V.Term # Ann (InferResult (UVarOf m))]
forVariant r =
    lookupBody r >>=
    \case
    Just (T.RExtend (RowExtend tag typ rest)) ->
        (:)
        <$> (suggestForTypeObvious typ <&> V.Inject tag <&> V.BInject)
        <*> forVariant rest
    _ -> pure []

suggestForTypeObvious ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Type -> m (TypedTerm m)
suggestForTypeObvious t =
    lookupBody t
    >>= suggestForTypeUTermObvious
    <&> fromMaybe (V.BLeaf V.LHole)
    <&> Ann (inferResult # t)

suggestForTypeUTermWithoutSplit ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    Maybe (T.Type # UVarOf m) -> m (Maybe (V.Term # Ann (InferResult (UVarOf m))))
suggestForTypeUTermWithoutSplit (Just (T.TRecord r)) = forRecord r
suggestForTypeUTermWithoutSplit t = suggestForTypeUTermObvious t

suggestForTypeUTermObvious ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    Maybe (T.Type # UVarOf m) -> m (Maybe (V.Term # Ann (InferResult (UVarOf m))))
suggestForTypeUTermObvious (Just (T.TFun (FuncType param result))) =
    lookupBody param >>=
    \case
    Just (T.TVariant row) -> suggestCaseWith row result
    _ -> suggestLam result
    <&> Just
suggestForTypeUTermObvious _ = pure Nothing

suggestLam ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Type ->
    m (V.Term # Ann (InferResult (UVarOf m)))
suggestLam result =
    V.TypedLam "var"
    <$> (newUnbound <&> (inferResult #) <&> (`Ann` (_HCompose # Pruned)))
    <*> suggestForTypeObvious result
    <&> V.BLam

forRecord ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Row -> m (Maybe (V.Term # Ann (InferResult (UVarOf m))))
forRecord r =
    lookupBody r >>=
    \case
    Just T.REmpty -> V.BLeaf V.LRecEmpty & Just & pure
    Just (T.RExtend (RowExtend tag typ rest)) ->
        RowExtend tag
        <$> suggestForTypeObvious typ
        <*> ( Ann
                <$> (newTerm (T.TRecord rest) <&> (inferResult #))
                <*> (forRecord rest <&> fromMaybe (V.BLeaf V.LHole))
            )
        <&> V.BRecExtend
        <&> Just
    _ -> pure Nothing

suggestCaseWith ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Row -> UVarOf m # T.Type ->
    m (V.Term # Ann (InferResult (UVarOf m)))
suggestCaseWith variantType resultType =
    lookupBody variantType >>=
    \case
    Just T.REmpty -> V.BLeaf V.LAbsurd & pure
    Just (T.RExtend (RowExtend tag fieldType rest)) ->
        RowExtend tag
        <$> (Ann
                <$> (mkCaseType fieldType <&> (inferResult #))
                <*> (V.TypedLam "var"
                    <$> (newUnbound <&> (inferResult #) <&> (`Ann` (_HCompose # Pruned)))
                    <*> suggestForTypeObvious resultType
                    <&> V.BLam
                    )
            )
        <*> (Ann
                <$> (T.TVariant rest & newTerm >>= mkCaseType <&> (inferResult #))
                <*> suggestCaseWith rest resultType)
        <&> V.BCase
        where
            mkCaseType which = FuncType which resultType & T.TFun & newTerm
    _ -> suggestLam resultType
