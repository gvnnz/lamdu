{-# LANGUAGE RecordWildCards #-}

module Lamdu.Sugar.Eval
    ( addEvaluationResults
    ) where

import qualified Control.Lens as Lens
import           Data.CurAndPrev (CurAndPrev)
import           Hyper
import           Lamdu.Eval.Results (EvalResults, erExprValues)
import qualified Lamdu.Sugar.Convert.Eval as ConvertEval
import           Lamdu.Sugar.Internal (InternalName, EvalPrep)
import           Lamdu.Sugar.Internal.EntityId (EntityId(..))
import qualified Lamdu.Sugar.Internal.EntityId as EntityId
import qualified Lamdu.Sugar.Types as Sugar

import           Lamdu.Prelude

class AddEval e where
    addToBody ::
        Applicative i =>
        CurAndPrev EvalResults ->
        Sugar.Body e EvalPrep name i o a ->
        Sugar.Body e (Sugar.EvaluationScopes InternalName i) name i o a

instance AddEval Sugar.Assignment where
    addToBody r (Sugar.BodyFunction x) = addToBody r x & Sugar.BodyFunction
    addToBody r (Sugar.BodyPlain x) =
        x & Sugar.apBody %~ addToBody r & Sugar.BodyPlain

instance AddEval Sugar.Binder where
    addToBody r (Sugar.BinderLet x) = addToBody r x & Sugar.BinderLet
    addToBody r (Sugar.BinderTerm x) = addToBody r x & Sugar.BinderTerm

instance AddEval Sugar.Function where
    addToBody r x@Sugar.Function{..} =
        x
        { Sugar._fParams = undefined
        , Sugar._fBody = addToNode r _fBody
        }

instance AddEval Sugar.Let where
    addToBody r x@Sugar.Let{..} =
        x
        { Sugar._lValue = addToNode r _lValue
        , Sugar._lBody = addToNode r _lBody
        }

instance AddEval Sugar.Term where
    addToBody = undefined

addToNode ::
    (AddEval e, Applicative i) =>
    CurAndPrev EvalResults ->
    Sugar.Expr e EvalPrep name i o a ->
    Sugar.Expr e (Sugar.EvaluationScopes InternalName i) name i o a
addToNode results (Ann (Const a) b) =
    Ann
    { _hAnn =
        a
        & Sugar.plAnnotation . Sugar._AnnotationVal .~
            ( results
                <&> (^. erExprValues . Lens.at u)
                <&> undefined
                & ConvertEval.results (EntityId.ofEvalOf i)
            )
        & Const
    , _hVal = addToBody results b
    }
    where
        EntityId u = i
        i = a ^. Sugar.plEntityId

addEvaluationResults ::
    Applicative i =>
    CurAndPrev EvalResults ->
    Sugar.WorkArea EvalPrep name i o (Sugar.Payload EvalPrep name i o a) ->
    Sugar.WorkArea (Sugar.EvaluationScopes InternalName i) name i o
        (Sugar.Payload (Sugar.EvaluationScopes InternalName i) name i o a)
addEvaluationResults r (Sugar.WorkArea panes repl listGlobals) =
    Sugar.WorkArea
    ( panes <&>
        Sugar.paneBody . Sugar._PaneDefinition . Sugar.drBody .
        Sugar._DefinitionBodyExpression . Sugar.deContent %~ addToNode r)
    (repl & Sugar.replExpr %~ addToNode r)
    listGlobals
