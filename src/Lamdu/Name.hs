{-# LANGUAGE TemplateHaskell #-}
module Lamdu.Name
    ( Stored
    , Collision(..), _NoCollision, _Collision
    , visible
    , TagText(..), ttText, ttCollision
    , TagName(..), tnDisplayText, tnTagCollision, tnIsAutoGen, tnIsOperator
    , Name(..), _AutoGenerated, _NameTag, _Unnamed
    , isValidText, isOperator
    ) where

import qualified Control.Lens as Lens
import qualified Data.Char as Char
import qualified Data.Text as Text
import qualified Lamdu.CharClassification as Chars
import qualified Lamdu.I18N.Name as Texts
import           Lamdu.Precedence (HasPrecedence(..))

import           Lamdu.Prelude

type Stored = Text

data Collision
    = NoCollision
    | Collision Text
    | UnknownCollision -- we have a collision but unknown suffix (inside hole result)
    deriving (Show, Generic, Eq)

data TagText = TagText
    { _ttText :: Text
    , _ttCollision :: Collision
    } deriving (Show, Generic, Eq)

data TagName = TagName
    { _tnDisplayText :: TagText
    , _tnTagCollision :: Collision
    , _tnIsAutoGen :: Bool
    , _tnIsOperator :: Bool
    } deriving (Generic, Eq)

data Name
    = AutoGenerated Text
    | NameTag TagName
    | Unnamed Int
    deriving (Generic, Eq)

visible ::
    (MonadReader env m, Has (Texts.Name Text) env) =>
    Name -> m (TagText, Collision)
visible (NameTag (TagName disp tagCollision _ _)) = pure (disp, tagCollision)
visible (AutoGenerated name) = pure (TagText name NoCollision, NoCollision)
visible (Unnamed suffix) =
    Lens.view (has . Texts.unnamed) <&>
    \x -> (TagText x NoCollision, Collision (Text.pack (show suffix)))

Lens.makeLenses ''TagName
Lens.makeLenses ''TagText
Lens.makePrisms ''Collision
Lens.makePrisms ''Name

instance Show Name where
    show (AutoGenerated text) = unwords ["(AutoName", show text, ")"]
    show (Unnamed suffix) = unwords ["(Unnamed", show suffix, ")"]
    show (NameTag (TagName disp collision _ _)) =
        unwords ["(TagName", show disp, show collision, ")"]

instance HasPrecedence Name where
    precedence (NameTag (TagName disp _ _ _)) =
        disp ^? ttText . Lens.ix 0 . Lens.to precedence & fromMaybe 12
    precedence _ = 12

-- | A valid *search* text for names. Can use '.' to search for
-- names like func-compose (∘)
isValidText :: Text -> Bool
isValidText x =
    Text.all f x
    || Text.all (`elem` Chars.operator) x
    where
        f c = Char.isAlphaNum c || c == '_'

isOperator :: Name -> Bool
isOperator (NameTag tn) = tn ^. tnIsOperator
isOperator _ = False
