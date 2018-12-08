{-# LANGUAGE DisambiguateRecordFields, KindSignatures, FlexibleInstances, DefaultSignatures #-}
module Lamdu.Sugar.Convert.Binder
    ( convertDefinitionBinder, convertLam
    , convertBinder
    ) where

import           AST (Node, Children(..), overChildren, monoChildren)
import           AST.Functor.Ann (Ann(..), ann, val, annotations)
import qualified Control.Lens.Extended as Lens
import qualified Data.Map as Map
import           Data.Property (MkProperty')
import qualified Data.Property as Property
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Data.Anchors as Anchors
import qualified Lamdu.Data.Ops.Subexprs as SubExprs
import           Lamdu.Expr.IRef (DefI, ValP)
import qualified Lamdu.Expr.IRef as ExprIRef
import qualified Lamdu.Infer as Infer
import           Lamdu.Sugar.Convert.Binder.Float (makeFloatLetToOuterScope)
import           Lamdu.Sugar.Convert.Binder.Inline (inlineLet)
import           Lamdu.Sugar.Convert.Binder.Params (ConventionalParams(..), convertParams, convertLamParams, cpParams, cpAddFirstParam, mkVarInfo)
import           Lamdu.Sugar.Convert.Binder.Redex (Redex(..))
import qualified Lamdu.Sugar.Convert.Binder.Redex as Redex
import           Lamdu.Sugar.Convert.Binder.Types (BinderKind(..))
import           Lamdu.Sugar.Convert.Expression.Actions (addActions, makeActions, subexprPayloads)
import qualified Lamdu.Sugar.Convert.Input as Input
import           Lamdu.Sugar.Convert.Monad (ConvertM, scScopeInfo, siLetItems)
import qualified Lamdu.Sugar.Convert.Monad as ConvertM
import           Lamdu.Sugar.Convert.Tag (convertTaggedEntity)
import           Lamdu.Sugar.Internal
import qualified Lamdu.Sugar.Internal.EntityId as EntityId
import qualified Lamdu.Sugar.Lens as SugarLens
import           Lamdu.Sugar.Types
import           Revision.Deltum.Transaction (Transaction)

import           Lamdu.Prelude

type T = Transaction

lamParamToHole ::
    Monad m =>
    V.Lam V.Var V.Term (Ann (Input.Payload m a)) -> T m ()
lamParamToHole (V.Lam param x) =
    SubExprs.getVarsToHole param (x & annotations %~ (^. Input.stored))

makeInline ::
    Monad m =>
    ValP m -> Redex (Input.Payload m a) -> EntityId -> BinderVarInline (T m)
makeInline stored redex useId
    | Lens.has traverse otherUses = CannotInlineDueToUses (drop 1 after ++ before)
    | otherwise =
        inlineLet stored (redex <&> (^. Input.stored) <&> Property.value)
        & InlineVar
    where
        otherUses = filter (/= useId) uses
        uses = redex ^. Redex.paramRefs
        (before, after) = break (== useId) uses

convertLet ::
    (Monad m, Monoid a) =>
    T m ExtractDestination ->
    Input.Payload m a ->
    Redex (Input.Payload m a) ->
    ConvertM m
    (Ann (ConvertPayload m a)
     (Binder InternalName (T m) (T m) (Ann (ConvertPayload m a))))
convertLet float pl redex =
    do
        tag <- convertTaggedEntity param
        (_pMode, value) <-
            convertAssignment binderKind param (redex ^. Redex.arg)
            <&> _2 . ann . pInput . Input.entityId .~
                EntityId.ofValI (redex ^. Redex.arg . ann . Input.stored . Property.pVal)
        letBody <-
            convertBinder bod
            & ConvertM.local (scScopeInfo . siLetItems <>~
                Map.singleton param (makeInline stored redex))
        protectedSetToVal <- ConvertM.typeProtectedSetToVal
        let fixValueNodeActions nodeActions =
                nodeActions
                & extract .~ float
                & mReplaceParent ?~
                    ( protectedSetToVal stored
                        (redex ^. Redex.arg . ann . Input.stored . Property.pVal)
                        <&> EntityId.ofValI
                    )
        postProcess <- ConvertM.postProcessAssert
        let del =
                do
                    lamParamToHole (redex ^. Redex.lam)
                    redex ^. Redex.lam . V.lamOut . ann . Input.stored
                        & replaceWith stored & void
                <* postProcess
        actions <- makeActions pl
        pure Ann
            { _val =
                BinderLet Let
                { _lVarInfo = redex ^. Redex.arg . ann . Input.inferred . Infer.plType & mkVarInfo
                , _lValue = value & ann . pActions %~ fixValueNodeActions
                , _lDelete = del
                , _lName = tag
                , _lBodyScope = redex ^. Redex.bodyScope
                , _lBody =
                    letBody
                    & ann . pActions . mReplaceParent ?~
                        (letBody ^. ann . pInput . Input.entityId <$ del)
                , _lUsages = redex ^. Redex.paramRefs
                }
            , _ann =
                ConvertPayload
                { _pInput =
                    pl
                    & Input.userData .~ redex ^. Redex.lamPl . Input.userData
                , _pActions = actions
                }
            }
    where
        stored = pl ^. Input.stored
        binderKind =
            redex ^. Redex.lam
            & V.lamOut . annotations %~ (^. Input.stored)
            & BinderKindLet
        V.Lam param bod = redex ^. Redex.lam

convertBinder ::
    (Monad m, Monoid a) =>
    Val (Input.Payload m a) ->
    ConvertM m (Node (Ann (ConvertPayload m a)) (Binder InternalName (T m) (T m)))
convertBinder expr@(Ann pl body) =
    case Redex.check body of
    Nothing ->
        ConvertM.convertSubexpression expr & localNewExtractDestPos pl
        <&> \exprS ->
        exprS
        & val %~ BinderExpr
        & ann . pInput .~ pl -- TODO: <-- why is this necessary?
        & ann . pInput . Input.userData .~
            mconcat
            (subexprPayloads
             (body ^.. monoChildren)
             (exprS ^.. val . SugarLens.childPayloads))
    Just redex ->
        do
            float <-
                makeFloatLetToOuterScope (pl ^. Input.stored . Property.pSet) redex
            convertLet float pl redex & localNewExtractDestPos pl

localNewExtractDestPos :: Input.Payload m a -> ConvertM m b -> ConvertM m b
localNewExtractDestPos x =
    ConvertM.scScopeInfo . ConvertM.siMOuter ?~
    ConvertM.OuterScopeInfo
    { _osiPos = x ^. Input.stored
    , _osiScope = x ^. Input.inferred . Infer.plScope
    }
    & ConvertM.local

makeFunction ::
    (Monad m, Monoid a) =>
    MkProperty' (T m) (Maybe BinderParamScopeId) ->
    ConventionalParams m -> Val (Input.Payload m a) ->
    ConvertM m (Function InternalName (T m) (T m) (Ann (ConvertPayload m a)))
makeFunction chosenScopeProp params funcBody =
    convertBinder funcBody
    <&> mkRes
    & ConvertM.local (ConvertM.scScopeInfo %~ addParams)
    where
        mkRes assignmentBody =
            Function
            { _fParams =
                -- TODO: avoid partiality here
                params ^?! cpParams . Lens._Just
            , _fChosenScopeProp = chosenScopeProp ^. Property.mkProperty
            , _fBody = assignmentBody
            , _fBodyScopes = cpScopes params
            , _fAddFirstParam = params ^. cpAddFirstParam
            }
        addParams ctx =
            ctx
            & ConvertM.siTagParamInfos <>~ _cpParamInfos params
            & ConvertM.siNullParams <>~
            case params ^. cpParams of
            Just NullParam{} -> Set.fromList (cpMLamParam params ^.. Lens._Just . _2)
            _ -> Set.empty

makeAssignment ::
    (Monad m, Monoid a) =>
    MkProperty' (T m) (Maybe BinderParamScopeId) ->
    ConventionalParams m -> Val (Input.Payload m a) -> Input.Payload m a ->
    ConvertM m (Assignment InternalName (T m) (T m) (ConvertPayload m a))
makeAssignment chosenScopeProp params funcBody pl =
    case params ^. cpParams of
    Nothing ->
        convertBinder funcBody
        <&> val %~ BodyPlain . AssignPlain (params ^. cpAddFirstParam)
    Just{} ->
        do
            funcS <- makeFunction chosenScopeProp params funcBody
            nodeActions <- makeActions pl & localNewExtractDestPos pl
            pure Ann
                { _ann =
                    ConvertPayload
                    { _pInput =
                        -- TODO: Why are redundant hidden entity ids
                        -- returned here?
                        pl & Input.userData .~ mempty
                    , _pActions = nodeActions
                    }
                , _val = BodyFunction funcS
                }

convertLam ::
    (Monad m, Monoid a) =>
    V.Lam V.Var V.Term (Ann (Input.Payload m a)) ->
    Input.Payload m a -> ConvertM m (ExpressionU m a)
convertLam lam exprPl =
    do
        convParams <- convertLamParams lam exprPl
        func <-
            makeFunction
            (lam ^. V.lamIn & Anchors.assocScopeRef)
            convParams (lam ^. V.lamOut)
        let paramNames =
                func ^.. fParams . _Params . traverse . fpInfo . piTag . tagInfo . tagName
                & Set.fromList
        let lambda
                | useNormalLambda paramNames func =
                    Lambda NormalBinder UnlimitedFuncApply func
                | otherwise =
                    func
                    & fBody %~ markNodeLightParams paramNames
                    & Lambda LightLambda UnlimitedFuncApply
        BodyLam lambda
            & addActions (lam ^.. V.lamOut) exprPl
            <&> val %~
                overChildren (Proxy :: Proxy Children)
                (ann . pActions . mReplaceParent . Lens._Just %~ (lamParamToHole lam >>))

useNormalLambda :: Set InternalName -> Function InternalName i o (Ann a) -> Bool
useNormalLambda paramNames func
    | Set.size paramNames < 2 = True
    | otherwise =
        any (func &)
        [ Lens.has (fBody . val . _BinderLet)
        , Lens.has (fBody . SugarLens.binderPayloads . Lens.filteredByIndex
            (SugarLens._OfExpr . forbiddenLightLamSubExprs))
        , not . allParamsUsed paramNames
        ]
    where
        forbiddenLightLamSubExprs :: Lens.Traversal' (Body name i o (Ann a)) ()
        forbiddenLightLamSubExprs =
            Lens.failing SugarLens.bodyUnfinished
            (_BodyLam . lamFunc . fParams . _Params . Lens.united)

allParamsUsed :: Set InternalName -> Function InternalName i o (Ann a) -> Bool
allParamsUsed paramNames func =
    Set.null (paramNames `Set.difference` usedParams)
    where
        usedParams =
            func ^.. fBody . SugarLens.binderPayloads . Lens.asIndex .
            SugarLens._OfExpr . _BodyGetVar . _GetParam . pNameRef . nrName
            & Set.fromList

class MarkLightParams (t :: (* -> *) -> *) where
    markLightParams :: Set InternalName -> t (Ann a) -> t (Ann a)

    default markLightParams ::
        (Children t, ChildrenConstraint t MarkLightParams) =>
        Set InternalName -> t (Ann a) -> t (Ann a)
    markLightParams = defaultMarkLightParams

defaultMarkLightParams ::
    (Children t, ChildrenConstraint t MarkLightParams) =>
    Set InternalName -> t (Ann a) -> t (Ann a)
defaultMarkLightParams paramNames =
    overChildren (Proxy :: Proxy MarkLightParams)
    (markNodeLightParams paramNames)

markNodeLightParams ::
    MarkLightParams t =>
    Set InternalName ->
    Node (Ann a) t ->
    Node (Ann a) t
markNodeLightParams paramNames =
    val %~ markLightParams paramNames

instance MarkLightParams (Lens.Const a)
instance MarkLightParams (Else InternalName i o)
instance MarkLightParams (Let InternalName i o)
instance MarkLightParams (Function InternalName i o)

instance MarkLightParams (AssignmentBody InternalName i o) where
    markLightParams ps (BodyPlain x) = x & apBody %~ markLightParams ps & BodyPlain
    markLightParams ps (BodyFunction x) = markLightParams ps x & BodyFunction

instance MarkLightParams (Binder InternalName i o) where
    markLightParams ps (BinderExpr x) = markLightParams ps x & BinderExpr
    markLightParams ps (BinderLet x) = markLightParams ps x & BinderLet

instance MarkLightParams (Body InternalName i o) where
    markLightParams paramNames (BodyGetVar (GetParam n))
        | paramNames ^. Lens.contains (n ^. pNameRef . nrName) =
            n
            & pBinderMode .~ LightLambda
            & GetParam & BodyGetVar
    markLightParams paramNames bod = defaultMarkLightParams paramNames bod

-- Let-item or definition (form of <name> [params] = <body>)
convertAssignment ::
    (Monad m, Monoid a) =>
    BinderKind m -> V.Var -> Val (Input.Payload m a) ->
    ConvertM m
    ( Maybe (MkProperty' (T m) PresentationMode)
    , Assignment InternalName (T m) (T m) (ConvertPayload m a)
    )
convertAssignment binderKind defVar expr =
    do
        (mPresentationModeProp, convParams, funcBody) <-
            convertParams binderKind defVar expr
        makeAssignment (Anchors.assocScopeRef defVar) convParams
            funcBody (expr ^. ann)
            <&> (,) mPresentationModeProp

convertDefinitionBinder ::
    (Monad m, Monoid a) =>
    DefI m -> Val (Input.Payload m a) ->
    ConvertM m
    ( Maybe (MkProperty' (T m) PresentationMode)
    , Assignment InternalName (T m) (T m) (ConvertPayload m a)
    )
convertDefinitionBinder defI =
    convertAssignment (BinderKindDef defI) (ExprIRef.globalId defI)
