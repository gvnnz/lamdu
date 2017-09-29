-- | A pass on the sugared AST to decide where to put parenthesis
{-# LANGUAGE NoImplicitPrelude, LambdaCase, DeriveFunctor #-}
module Lamdu.Sugar.Parens.Add
    ( NeedsParens(..)
    , add
    ) where

import qualified Control.Lens as Lens
import qualified Lamdu.Calc.Val as V
import qualified Lamdu.CharClassification as Chars
import           Lamdu.Sugar.Names.Types (Name)
import qualified Lamdu.Sugar.Names.Types as Name
import           Lamdu.Sugar.Types

import           Lamdu.Prelude

data Precedence a = Precedence
    { _before :: a
    , _after  :: a
    } deriving (Show, Functor)
instance Applicative Precedence where
    pure = join Precedence
    Precedence af bf <*> Precedence ax bx = Precedence (af ax) (bf bx)

-- | Do we need parenthesis (OR any other visual disambiguation?)
data NeedsParens = NeedsParens | NoNeedForParens
    deriving (Eq)

data PrecCheck = Never | IfGreater !Int | IfGreaterOrEqual !Int

check :: PrecCheck -> Int -> Bool
check Never = const False
check (IfGreater x) = (> x)
check (IfGreaterOrEqual x) = (>= x)

data Classifier
    = NeverParen
    | ParenIf PrecCheck PrecCheck

unambiguous :: Precedence (Maybe Int)
unambiguous = Precedence (Just 0) (Just 0)

-- First "line" gets specified precedence override.
-- Rest of "lines" get 0/0 (unambiguous) override
binderBodyFirstLine ::
    Precedence (Maybe Int) -> BinderBody name m (Precedence (Maybe Int) -> a) ->
    BinderBody name m a
binderBodyFirstLine override =
    bbContent %~ f
    where
        f (BinderLet let_) =
            BinderLet let_
            { _lValue = _lValue let_ & bBody %~ binderBodyFirstLine override
            , _lBody = _lBody let_ <&> (\expr -> expr unambiguous)
            }
        f (BinderExpr expr) = expr override & BinderExpr

mkUnambiguous ::
    Functor sugar =>
    (sugar a -> b) -> sugar (Precedence (Maybe Int) -> a) -> (Classifier, b)
mkUnambiguous cons x =
    (NeverParen, cons (x ?? unambiguous))

precedenceOfGuard ::
    Guard m (Precedence (Maybe Int) -> a) -> (Classifier, Guard m a)
precedenceOfGuard (Guard if_ then_ elseIfs else_ _del) =
    ( ParenIf Never (IfGreater 1)
    , Guard
        (if_ unambiguous)
        (then_ (Precedence (Just 0) Nothing)) -- then appears in end of first line
        (elseIfs <&> (\expr -> expr ?? unambiguous))
        (else_ unambiguous)
        _del
    )

visibleFuncName :: Lens.Getter (BinderVar (Name n) m) Text
visibleFuncName = bvNameRef . nrName . Name.form . Lens.to Name.visible . Lens._1

precedenceOfLabeledApply ::
    LabeledApply (Name n) m (Precedence (Maybe Int) -> a) ->
    (Classifier, LabeledApply (Name n) m a)
precedenceOfLabeledApply apply@(LabeledApply func specialArgs annotatedArgs relayedArgs) =
    case specialArgs of
    NoSpecialArgs -> (NeverParen, apply ?? unambiguous)
    ObjectArg arg ->
        ( ParenIf (IfGreater 10) (IfGreaterOrEqual 10)
        , LabeledApply func (ObjectArg (arg (Precedence (Just 10) Nothing)))
            newAnnotatedArgs relayedArgs
        )
    InfixArgs l r ->
        ( ParenIf (IfGreaterOrEqual prec) (IfGreater prec)
        , LabeledApply func
            (InfixArgs
             (l (Precedence Nothing (Just prec)))
             (r (Precedence (Just prec) Nothing)))
            newAnnotatedArgs relayedArgs
        )
        where
            prec =
                func ^? visibleFuncName . Lens.ix 0
                & maybe 20 Chars.precedence
    where
        newAnnotatedArgs = annotatedArgs <&> (?? unambiguous)

precedenceOfPrefixApply ::
    Apply (Precedence (Maybe Int) -> expr) -> (Classifier, Body name m expr)
precedenceOfPrefixApply (V.Apply f arg) =
    ( ParenIf (IfGreater 10) (IfGreaterOrEqual 10)
    , V.Apply
        (f (Precedence Nothing (Just 10)))
        (arg (Precedence (Just 10) Nothing))
        & BodySimpleApply
    )

precedenceOf ::
    Body (Name n) m (Precedence (Maybe Int) -> a) -> (Classifier, Body (Name n) m a)
precedenceOf =
    \case
    BodyInjectedExpression -> (NeverParen, BodyInjectedExpression)
    BodyLiteral x          -> (NeverParen, BodyLiteral x)
    BodyGetVar x           -> (NeverParen, BodyGetVar x)
    BodyHole x             -> mkUnambiguous BodyHole x
    BodyRecord x           -> mkUnambiguous BodyRecord x
    BodyCase x             -> mkUnambiguous BodyCase x
    BodyLam x              ->
        ( ParenIf Never (IfGreaterOrEqual 1)
        , x & lamBinder . bBody %~
          binderBodyFirstLine (Precedence (Just 1) Nothing) & BodyLam
        )
    BodyFromNom x          -> rightSymbol 1 BodyFromNom x
    BodyToNom x            ->
        ( ParenIf Never (IfGreaterOrEqual 1)
        , x <&> binderBodyFirstLine (Precedence (Just 1) Nothing) & BodyToNom
        )
    BodyInject x           -> leftSymbol 1 BodyInject x
    BodyGetField x         -> rightSymbol 11 BodyGetField x
    BodySimpleApply x      -> precedenceOfPrefixApply x
    BodyLabeledApply x     -> precedenceOfLabeledApply x & _2 %~ BodyLabeledApply
    BodyGuard x            -> precedenceOfGuard x & _2 %~ BodyGuard
    where
        leftSymbol prec cons x =
            ( ParenIf Never (IfGreaterOrEqual prec)
            , cons (x ?? Precedence (Just 0) Nothing)
            )
        rightSymbol prec cons x =
            ( ParenIf (IfGreaterOrEqual prec) Never
            , cons (x ?? Precedence Nothing (Just 0))
            )

add :: Expression (Name n) m a -> Expression (Name n) m (NeedsParens, a)
add = loop (Precedence 0 0)

loop ::
    Precedence Int -> Expression (Name n) m a ->
    Expression (Name n) m (NeedsParens, a)
loop parentPrec (Expression body pl) =
    Expression finalBody (pl & plData %~ (,) needsParens)
    where
        f expr override newParentPrec =
            loop (fromMaybe <$> newParentPrec <*> override) expr
        Precedence parentBefore parentAfter = parentPrec
        needsParens
            | haveParens = NeedsParens
            | otherwise = NoNeedForParens
        haveParens =
            case classifier of
            NeverParen -> False
            ParenIf lCheck rCheck ->
                check lCheck parentBefore || check rCheck parentAfter
        finalBody =
            newBody
            ?? if haveParens
                 then Precedence 0 0
                 else parentPrec
        (classifier, newBody) =
            precedenceOf (body <&> f)