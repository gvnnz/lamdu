-- | Common utilities for status bar widgets
{-# LANGUAGE TemplateHaskell, RankNTypes, TypeFamilies, FlexibleContexts #-}
module Lamdu.GUI.StatusBar.Common
    ( StatusWidget(..), widget, globalEventMap
    , hoist
    , makeSwitchStatusWidget, makeBoundedSwitchStatusWidget
    , makeStatusWidget
    , combine, combineEdges
    ) where

import qualified Control.Lens as Lens
import           Data.Property (Property(..))
import qualified Data.Text as Text
import           GUI.Momentu.Align (WithTextPos(..), TextWidget)
import qualified GUI.Momentu.Align as Align
import           GUI.Momentu.Element (Element(..))
import qualified GUI.Momentu.Element as Element
import           GUI.Momentu.EventMap (EventMap)
import qualified GUI.Momentu.EventMap as E
import           GUI.Momentu.Glue ((/|/))
import qualified GUI.Momentu.Glue as Glue
import qualified GUI.Momentu.Hover as Hover
import           GUI.Momentu.MetaKey (MetaKey)
import           GUI.Momentu.State (Gui)
import qualified GUI.Momentu.State as GuiState
import           GUI.Momentu.View (View)
import           GUI.Momentu.Widget (R)
import qualified GUI.Momentu.Widget as Widget
import qualified GUI.Momentu.Widgets.Choice as Choice
import qualified GUI.Momentu.Widgets.Label as Label
import           GUI.Momentu.Widgets.Spacer (HasStdSpacing)
import qualified GUI.Momentu.Widgets.Spacer as Spacer
import qualified GUI.Momentu.Widgets.TextView as TextView
import           Lamdu.Config (Config, HasConfig)
import qualified Lamdu.Config as Config
import           Lamdu.Config.Theme (HasTheme)
import qualified Lamdu.Config.Theme as Theme
import           Lamdu.I18N.Texts (Language, Texts, HasTexts(..))
import qualified Lamdu.GUI.Styled as Styled
import           Lamdu.GUI.Styled (info, label)

import           Lamdu.Prelude

data StatusWidget f = StatusWidget
    { _widget :: TextWidget f
    , _globalEventMap :: Gui EventMap f
    }
Lens.makeLenses ''StatusWidget

instance Functor f => Element (StatusWidget f) where
    setLayers = widget . setLayers
    hoverLayers = widget %~ hoverLayers
    padImpl x y = widget %~ padImpl x y
    scale x = widget %~ scale x
    empty = StatusWidget Element.empty mempty

hoist :: (f GuiState.Update -> g GuiState.Update) -> StatusWidget f -> StatusWidget g
hoist f (StatusWidget w e) =
    StatusWidget
    { _widget = w <&> fmap f
    , _globalEventMap = e <&> f
    }

makeStatusWidget ::
    ( MonadReader env m, Functor f
    , HasTheme env, Element.HasAnimIdPrefix env, TextView.HasStyle env
    , Element.HasLayoutDir env
    , HasTexts env
    ) =>
    (forall a. Lens.ALens' (Texts a) a) -> TextWidget f -> m (StatusWidget f)
makeStatusWidget headerText w =
    info (label headerText) /|/ pure w
    <&> (`StatusWidget` mempty)

makeChoice ::
    ( MonadReader env m, Applicative f, Eq a
    , Hover.HasStyle env, GuiState.HasCursor env, TextView.HasStyle env
    , Element.HasAnimIdPrefix env, Element.HasLayoutDir env
    , HasTexts env
    ) =>
    (forall z. Lens.ALens' (Texts z) z) -> Property f a -> [(Text, a)] ->
    m (TextWidget f)
makeChoice headerText prop choiceVals =
    do
        choices <- traverse mkChoice choiceVals
        text <- Lens.view texts <&> (^# headerText)
        Choice.make ?? prop ?? choices ?? Choice.defaultConfig text ?? myId
            <&> WithTextPos 0 -- TODO: Choice should maintain the WithTextPos
    where
        myId = Widget.Id ("status" : Styled.textIds ^# headerText)
        mkChoice (text, val) =
            Label.makeFocusable text
            <&> (^. Align.tValue)
            <&> (,) val

makeSwitchWidget ::
    ( MonadReader env m, Applicative f, Eq a
    , TextView.HasStyle env, Element.HasAnimIdPrefix env, HasTheme env
    , GuiState.HasCursor env, Hover.HasStyle env, Element.HasLayoutDir env
    , HasTexts env
    ) =>
    (forall z. Lens.ALens' (Texts z) z) -> Property f a -> [(Text, a)] ->
    m (TextWidget f)
makeSwitchWidget headerText prop choiceVals =
    info (label headerText) /|/ makeChoice headerText prop choiceVals

makeSwitchEventMap ::
    ( MonadReader env m, HasConfig env, HasTexts env
    , Eq a, Functor f
    ) =>
    Lens.ALens' Language Text ->
    Lens' Config [MetaKey] ->
    Property f a -> [a] ->
    m (Gui EventMap f)
makeSwitchEventMap headerText keysGetter (Property curVal setVal) choiceVals =
    do
        keys <- Lens.view (Config.config . keysGetter)
        text <- Lens.view (texts . Lens.cloneLens headerText)
        setVal newVal
            & E.keysEventMap keys (E.Doc ["Status bar", "Switch " <> text])
            & pure
    where
        newVal = dropWhile (/= curVal) choiceVals ++ choiceVals & tail & head

makeSwitchStatusWidget ::
    ( MonadReader env m, Applicative f, Eq a
    , HasConfig env, HasTheme env, HasTexts env
    , TextView.HasStyle env, Element.HasAnimIdPrefix env, GuiState.HasCursor env
    , Hover.HasStyle env, Element.HasLayoutDir env
    ) =>
    (forall z. Lens.ALens' (Texts z) z) ->
    Lens' Config [MetaKey] ->
    Property f a -> [(Text, a)] ->
    m (StatusWidget f)
makeSwitchStatusWidget headerText keysGetter prop choiceVals =
    do
        w <- makeSwitchWidget headerText prop choiceVals
        e <- makeSwitchEventMap headerText keysGetter prop (map snd choiceVals)
        pure StatusWidget
            { _widget = w
            , _globalEventMap = e
            }

makeBoundedSwitchStatusWidget ::
    ( MonadReader env m, Applicative f, Eq a, Enum a, Bounded a, Show a
    , HasConfig env, HasTheme env, HasTexts env
    , TextView.HasStyle env, Element.HasAnimIdPrefix env, GuiState.HasCursor env
    , Hover.HasStyle env, Element.HasLayoutDir env
    ) =>
    (forall z. Lens.ALens' (Texts z) z) ->
    Lens' Config [MetaKey] ->
    Property f a ->
    m (StatusWidget f)
makeBoundedSwitchStatusWidget headerText keysGetter prop =
    makeSwitchStatusWidget headerText keysGetter prop choiceVals
    where
        choiceVals = [minBound..maxBound] <&> \val -> (Text.pack (show val), val)

hspacer ::
    (MonadReader env m, Spacer.HasStdSpacing env, Theme.HasTheme env) => m View
hspacer = do
    hSpaceCount <- Lens.view (Theme.theme . Theme.statusBar . Theme.statusBarHSpaces)
    Spacer.getSpaceSize <&> (^. _1) <&> (* hSpaceCount) <&> Spacer.makeHorizontal

combine ::
    ( MonadReader env m, Applicative f
    , Element.HasLayoutDir env, HasStdSpacing env, HasTheme env
    ) => m ([StatusWidget f] -> StatusWidget f)
combine =
    (,,) <$> (Glue.mkPoly ?? Glue.Horizontal) <*> Glue.hbox <*> hspacer
    <&> \(Glue.Poly (|||), hbox, space) statusWidgets ->
    StatusWidget
    { _widget =
        case statusWidgets of
        [] -> Element.empty
        (x:xs) ->
            xs
            <&> (^. widget)
            <&> (space |||)
            & hbox
            & ((x ^. widget) |||)
    , _globalEventMap = statusWidgets ^. Lens.folded . globalEventMap
    }

combineEdges ::
    ( MonadReader env m, Applicative f, Element.HasLayoutDir env
    ) =>
    m (R -> StatusWidget f -> StatusWidget f -> StatusWidget f)
combineEdges =
    Glue.mkPoly ?? Glue.Horizontal
    <&> \(Glue.Poly (|||)) width (StatusWidget xw xe) (StatusWidget yw ye) ->
    let padding = max 0 (width - combinedWidths)
        combinedWidths = xw ^. Element.width + yw ^. Element.width
    in  StatusWidget
        { _widget = xw ||| Spacer.makeHorizontal padding ||| yw
        , _globalEventMap = xe <> ye
        }
