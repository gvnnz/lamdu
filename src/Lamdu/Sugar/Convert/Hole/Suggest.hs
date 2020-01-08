{-# LANGUAGE TypeFamilies, TypeApplications, TypeOperators, RankNTypes #-}
module Lamdu.Sugar.Convert.Hole.Suggest
    ( forType
    , termTransforms
    , termTransformsWithModify
    ) where

import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Monad.State (StateT)
import qualified Control.Monad.State as State
import           Hyper
import           Hyper.Infer (InferResult, inferResult, inferBody)
import           Hyper.Type.AST.FuncType
import           Hyper.Type.AST.Nominal
import           Hyper.Type.AST.Row (RowExtend(..))
import           Hyper.Type.Prune
import           Hyper.Unify
import           Hyper.Unify.Binding (UVar)
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New (newUnbound, newTerm)
import           Hyper.Unify.Term
import           Lamdu.Calc.Infer (PureInfer, InferState, runPureInfer)
import qualified Lamdu.Calc.Lens as ExprLens
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T

import           Lamdu.Prelude

-- | Term with unifiable type annotations
type TypedTerm m = Ann (InferResult (UVarOf m)) # V.Term

lookupBody :: Unify f t => UVarOf f # t -> f (Maybe (t # UVarOf f))
lookupBody x = semiPruneLookup x <&> (^? _2 . _UTerm . uBody)

-- | These are offered in fragments (not holes). They transform a term
-- by wrapping it in a larger term where it appears once.
termTransforms ::
    V.Scope # UVar ->
    (forall n. InferResult UVar # n -> a # n) ->
    (a # V.Term -> InferResult UVar # V.Term) ->
    Ann a # V.Term ->
    StateT InferState [] (Ann a # V.Term)
termTransforms srcScope mkPl getInferred src =
    getInferred (src ^. hAnn) ^. inferResult & lookupBody & liftInfer ()
    <&> (^? Lens._Just . T._TRecord)
    >>=
    \case
    Just row | Lens.nullOf (hVal . V._BRecExtend) src ->
        transformGetFields mkPl src row
    _ -> termTransformsWithoutSplit srcScope mkPl getInferred src

transformGetFields ::
    (InferResult UVar # V.Term -> a # V.Term) ->
    Ann a # V.Term -> UVar # T.Row ->
    StateT InferState [] (Ann a # V.Term)
transformGetFields mkPl src row =
    lookupBody row & liftInfer ()
    <&> (^? Lens._Just . T._RExtend)
    >>=
    \case
    Nothing -> empty
    Just (RowExtend tag typ rest) ->
        pure (Ann (mkPl (inferResult # typ)) (V.BGetField (V.GetField src tag)))
        <|> transformGetFields mkPl src rest

liftInfer :: env -> PureInfer env a -> StateT InferState [] a
liftInfer e act =
    do
        s <- State.get
        case runPureInfer e s act of
            Left{} -> empty
            Right (r, newState) -> r <$ State.put newState

termTransformsWithoutSplit ::
    V.Scope # UVar ->
    (forall n. InferResult UVar # n -> a # n) ->
    (a # V.Term -> InferResult UVar # V.Term) ->
    Ann a # V.Term ->
    StateT InferState [] (Ann a # V.Term)
termTransformsWithoutSplit srcScope mkPl getInferred src =
    do
        -- Don't modify a redex from the outside.
        -- Such transform are more suitable in it!
        Lens.nullOf (hVal . V._BApp . V.appFunc . hVal . V._BLam) src & guard

        (s1, typ) <-
            getInferred (src ^. hAnn) ^. inferResult & semiPruneLookup & liftInfer ()
        case typ ^? _UTerm . uBody of
            Just (T.TInst (NominalInst name _params))
                | Lens.nullOf (hVal . V._BToNom) src ->
                    do
                        fromNomRes <- V.LFromNom name & V.BLeaf & inferBody
                        let fromNomTyp = fromNomRes ^. Lens._2 . _ANode
                        resultType <- newUnbound
                        _ <- FuncType s1 resultType & T.TFun & newTerm >>= unify fromNomTyp
                        V.App (mkResult fromNomTyp (V.BLeaf (V.LFromNom name))) src
                            & V.BApp & mkResult resultType & pure
                    & liftInfer srcScope
                    >>= termOptionalTransformsWithoutSplit srcScope mkPl getInferred
            Just (T.TVariant row) | Lens.nullOf (hVal . V._BInject) src ->
                do
                    dstType <- newUnbound
                    caseType <- FuncType s1 dstType & T.TFun & newTerm
                    suggestCaseWith row dstType
                        <&> Ann (inferResult # caseType)
                        <&> hflipped %~ hmap (const mkPl)
                        <&> (`V.App` src) <&> V.BApp <&> mkResult dstType
                & liftInfer (V.emptyScope @UVar)
            _ | Lens.nullOf (hVal . V._BLam) src ->
                -- Apply if compatible with a function
                do
                    argType <- liftInfer (V.emptyScope @UVar) newUnbound
                    resType <- liftInfer (V.emptyScope @UVar) newUnbound
                    _ <-
                        FuncType argType resType & T.TFun & newTerm
                        >>= unify s1
                        & liftInfer (V.emptyScope @UVar)
                    arg <-
                        forTypeWithoutSplit argType & liftInfer (V.emptyScope @UVar)
                        <&> hflipped %~ hmap (const mkPl)
                    let applied = V.App src arg & V.BApp & mkResult resType
                    pure applied
                        <|>
                        do
                            -- If the suggested argument has holes in it
                            -- then stop suggesting there to avoid "overwhelming"..
                            Lens.nullOf (ExprLens.valLeafs . V._LHole) arg & guard
                            termTransformsWithoutSplit srcScope mkPl getInferred applied
            _ -> empty
    where
        mkResult t = Ann (mkPl (inferResult # t))

termOptionalTransformsWithoutSplit ::
    V.Scope # UVar ->
    (forall n. InferResult UVar # n -> a # n) ->
    (a # V.Term -> InferResult UVar # V.Term) ->
    Ann a # V.Term ->
    StateT InferState [] (Ann a # V.Term)
termOptionalTransformsWithoutSplit srcScope mkPl getInferred src =
    pure src <|>
    termTransformsWithoutSplit srcScope mkPl getInferred src

-- | Suggest values that fit a type, may "split" once, to suggest many
-- injects for a sum type. These are offerred in holes (not fragments).
forType ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Type -> m [TypedTerm m]
forType t =
    -- TODO: DSL for matching/deref'ing UVar structure
    lookupBody t
    >>= \case
    Just (T.TVariant r) -> forVariant r [V.BLeaf V.LHole] <&> Lens.mapped %~ Ann (inferResult # t)
    typ -> forTypeUTermWithoutSplit typ <&> Ann (inferResult # t) <&> (:[])

forVariant ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Row ->
    [V.Term # Ann (InferResult (UVarOf m))] ->
    m [V.Term # Ann (InferResult (UVarOf m))]
forVariant r def =
    lookupBody r >>=
    \case
    Just (T.RExtend extend) -> forVariantExtend extend
    _ -> pure def

forVariantExtend ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    RowExtend T.Tag T.Type T.Row # UVarOf m ->
    m [V.Term # Ann (InferResult (UVarOf m))]
forVariantExtend (RowExtend tag typ rest) =
    (:)
    <$> (forTypeWithoutSplit typ <&> V.Inject tag <&> V.BInject)
    <*> forVariant rest []

forTypeWithoutSplit ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Type -> m (TypedTerm m)
forTypeWithoutSplit t =
    lookupBody t >>= forTypeUTermWithoutSplit <&> Ann (inferResult # t)

forTypeUTermWithoutSplit ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    Maybe (T.Type # UVarOf m) -> m (V.Term # Ann (InferResult (UVarOf m)))
forTypeUTermWithoutSplit t =
    case t of
    Just (T.TRecord row) -> suggestRecord row
    Just (T.TFun (FuncType param result)) ->
        lookupBody param >>=
        \case
        Just (T.TVariant row) -> suggestCaseWith row result
        _ ->
            V.TypedLam "var"
            <$> (newUnbound <&> (inferResult #) <&> (`Ann` (_HCompose # Pruned)))
            <*> forTypeWithoutSplit result
            <&> V.BLam
    _ -> V.BLeaf V.LHole & pure

suggestRecord ::
    (UnifyGen m T.Type, UnifyGen m T.Row) =>
    UVarOf m # T.Row ->
    m (V.Term # Ann (InferResult (UVarOf m)))
suggestRecord r =
    lookupBody r >>=
    \case
    Just T.REmpty -> V.BLeaf V.LRecEmpty & pure
    Just (T.RExtend (RowExtend tag typ rest)) ->
        RowExtend tag
        <$> autoLambdas typ
        <*> (Ann <$> (newTerm (T.TRecord rest) <&> (inferResult #)) <*> suggestRecord rest)
        <&> V.BRecExtend
    _ -> V.BLeaf V.LHole & pure

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
                    <*> autoLambdas resultType
                    <&> V.BLam
                    )
            )
        <*> (Ann
                <$> (T.TVariant rest & newTerm >>= mkCaseType <&> (inferResult #))
                <*> suggestCaseWith rest resultType)
        <&> V.BCase
        where
            mkCaseType which = FuncType which resultType & T.TFun & newTerm
    _ ->
        -- TODO: Maybe this should be a lambda, like a TFun from non-variant
        V.BLeaf V.LHole & pure

autoLambdas :: Unify m T.Type => UVarOf m # T.Type -> m (TypedTerm m)
autoLambdas typ =
    lookupBody typ >>=
    \case
    Just (T.TFun result) ->
        autoLambdas (result ^. funcOut)
        <&> V.TypedLam "var" (Ann (inferResult # (result ^. funcIn)) (_HCompose # Pruned))
        <&> V.BLam
    _ -> V.BLeaf V.LHole & pure
    <&> Ann (inferResult # typ)

fillHoles ::
    (forall n. InferResult UVar # n -> a # n) ->
    (a # V.Term -> InferResult UVar # V.Term) ->
    Ann a # V.Term ->
    PureInfer (V.Scope # UVar) (Ann a # V.Term)
fillHoles mkPl getInferred (Ann pl (V.BLeaf V.LHole)) =
    forTypeWithoutSplit (getInferred pl ^. inferResult)
    <&> hflipped %~ hmap (const mkPl)
fillHoles mkPl getInferred (Ann pl (V.BApp (V.App func arg))) =
    -- Dont fill in holes inside apply funcs. This may create redexes..
    fillHoles mkPl getInferred arg <&> V.App func <&> V.BApp <&> Ann pl
fillHoles _ _ v@(Ann _ (V.BGetField (V.GetField (Ann _ (V.BLeaf V.LHole)) _))) =
    -- Dont fill in holes inside get-field.
    pure v
fillHoles mkPl getInferred x =
    hVal
    ( htraverse $
        \case
        HWitness V.W_Term_Term -> fillHoles mkPl getInferred
        _ -> pure
    ) x

-- | Transform by wrapping OR modifying a term. Used by both holes and
-- fragments to expand "seed" terms. Holes include these as results
-- whereas fragments emplace their content inside holes of these
-- results.
termTransformsWithModify ::
    V.Scope # UVar ->
    (forall n. InferResult UVar # n -> a # n) ->
    (a # V.Term -> InferResult UVar # V.Term) ->
    Ann a # V.Term ->
    StateT InferState [] (Ann a # V.Term)
termTransformsWithModify _ _ _ v@(Ann _ V.BLam {}) = pure v -- Avoid creating a surprise redex
termTransformsWithModify _ _ _ v@(Ann pl0 (V.BInject (V.Inject tag (Ann pl1 (V.BLeaf V.LHole))))) =
    -- Variant:<hole> ==> Variant.
    pure (Ann pl0 (V.BInject (V.Inject tag (Ann pl1 (V.BLeaf V.LRecEmpty)))))
    <|> pure v
termTransformsWithModify srcScope mkPl getInferred src =
    getInferred (src ^. hAnn) ^. inferResult & lookupBody & liftInfer ()
    >>=
    \case
    Just T.TRecord{} | Lens.has ExprLens.valVar src ->
        -- A "params record" (or just a let item which is a record..)
        pure src
    _ ->
        do
            t <- fillHoles mkPl getInferred src & liftInfer V.emptyScope
            pure t <|> termTransforms srcScope mkPl getInferred t
