module Lamdu.GUI.TagPane
    ( make
    ) where

import qualified Control.Lens as Lens
import qualified Control.Monad.Reader as Reader
import           Data.Binary.Extended (encodeS)
import qualified Data.Char as Char
import           Data.List (sortOn)
import           Data.Property (Property(..))
import           GUI.Momentu.Align (TextWidget, Aligned(..), WithTextPos(..))
import qualified GUI.Momentu.Align as Align
import qualified GUI.Momentu.Direction as Dir
import qualified GUI.Momentu.Element as Element
import qualified GUI.Momentu.EventMap as E
import qualified GUI.Momentu.Glue as Glue
import qualified GUI.Momentu.I18N as MomentuTexts
import           GUI.Momentu.MetaKey (MetaKey(..), noMods)
import qualified GUI.Momentu.MetaKey as MetaKey
import qualified GUI.Momentu.State as GuiState
import           GUI.Momentu.Widget (Widget)
import qualified GUI.Momentu.Widget as Widget
import qualified GUI.Momentu.Widgets.FocusDelegator as FocusDelegator
import qualified GUI.Momentu.Widgets.Grid as Grid
import qualified GUI.Momentu.Widgets.Spacer as Spacer
import qualified GUI.Momentu.Widgets.TextEdit as TextEdit
import qualified GUI.Momentu.Widgets.TextEdit.Property as TextEdits
import qualified GUI.Momentu.Widgets.TextView as TextView
import qualified Lamdu.Config as Config
import           Lamdu.Config.Theme (Theme)
import           Lamdu.Data.Tag (TextsInLang(..))
import qualified Lamdu.Data.Tag as Tag
import qualified Lamdu.GUI.Styled as Styled
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import qualified Lamdu.I18N.CodeUI as Texts
import           Lamdu.I18N.LangId (LangId(..), _LangId)
import           Lamdu.Name (Name(..))
import qualified Lamdu.Sugar.Types as Sugar

import           Lamdu.Prelude

tagRenameId :: Widget.Id -> Widget.Id
tagRenameId = (`Widget.joinId` ["rename"])

disallowedNameChars :: String
disallowedNameChars = ",[]\\`()"

makeTagNameEdit ::
    ( MonadReader env m, Applicative f
    , TextEdit.Deps env, GuiState.HasCursor env
    ) =>
    Property f Text -> Widget.Id ->
    m (TextWidget f)
makeTagNameEdit prop myId =
    TextEdits.makeWordEdit
    ?? pure "  "
    ?? prop
    ?? tagRenameId myId
    <&> Align.tValue . Widget.eventMapMaker . Lens.mapped %~ E.filterChars (`notElem` disallowedNameChars)

makeFocusableTagNameEdit ::
    ( MonadReader env m
    , Applicative o
    , Has (Texts.CodeUI Text) env
    , TextEdit.Deps env
    , GuiState.HasCursor env
    , Has Config.Config env
    ) =>
    Property o Text -> Widget.Id -> m (TextWidget o)
makeFocusableTagNameEdit prop myId =
    do
        env <- Lens.view id
        let fdConfig =
                FocusDelegator.Config
                { FocusDelegator.focusChildKeys = env ^. has . Config.jumpToDefinitionKeys
                , FocusDelegator.focusChildDoc =
                    E.toDoc env
                    [ has . MomentuTexts.edit
                    , has . Texts.tag
                    , has . Texts.renameTag
                    ]
                , FocusDelegator.focusParentKeys =
                    [ MetaKey noMods MetaKey.Key'Escape
                    , MetaKey noMods MetaKey.Key'Enter
                    ]
                , FocusDelegator.focusParentDoc =
                    E.toDoc env
                    [ has . MomentuTexts.edit
                    , has . Texts.tag
                    , has . Texts.stopEditing
                    ]
                }
        (FocusDelegator.make ?? fdConfig ?? FocusDelegator.FocusEntryParent ?? myId
            <&> (Align.tValue %~))
            <*> makeTagNameEdit prop myId

makeLanguageTitle ::
    ( MonadReader env m
    , Has TextView.Style env, Has Dir.Layout env
    , Has (Map LangId Text) env
    ) =>
    Widget.Id -> LangId -> m (Align.WithTextPos (Widget o))
makeLanguageTitle myId lang =
    TextView.make
    <*> (Lens.view has <&> getLang)
    <*> pure (Widget.toAnimId myId <> ["lang-title"])
    <&> Align.tValue %~ Widget.fromView
    where
        getLang :: Map LangId Text -> Text
        getLang x =
            x ^. Lens.at lang
            & fromMaybe (lang ^. _LangId & Lens.ix 0 %~ Char.toUpper)

data Row a = Row
    { _language :: a
    , _space0 :: a
    , _name :: a
    , _space1 :: a
    , _abbreviation :: a
    , _space2 :: a
    , _disambig :: a
    } deriving (Functor, Foldable, Traversable)

langWidgetId :: Widget.Id -> LangId -> Widget.Id
langWidgetId parentId lang =
    parentId `Widget.joinId` [encodeS lang]

nameId :: Widget.Id -> Widget.Id
nameId = (`Widget.joinId` ["name"])

makeLangRow ::
    ( Applicative o
    , MonadReader env m
    , Has (Map LangId Text) env, Has (Texts.CodeUI Text) env
    , TextEdit.Deps env, GuiState.HasCursor env, Has Config.Config env
    ) =>
    Widget.Id -> (LangId -> TextsInLang -> o ()) -> LangId -> TextsInLang ->
    m (Row (Aligned (Widget o)))
makeLangRow parentId setName lang langNames =
    Row
    <$> makeLanguageTitle langId lang
    <*> pure Element.empty
    <*> makeFocusableTagNameEdit nameProp (nameId langId)
    <*> pure Element.empty
    <*> makeFocusableTagNameEdit (mkProp Tag.abbreviation) (langId `Widget.joinId` ["abbr"])
    <*> pure Element.empty
    <*> makeFocusableTagNameEdit (mkProp Tag.disambiguationText) (langId `Widget.joinId` ["disamb"])
    <&> Lens.mapped %~ Align.fromWithTextPos 0
    where
        langId = langWidgetId parentId lang
        nameProp =
            setName lang . (\x -> langNames & Tag.name .~ x)
            & Property (langNames ^. Tag.name)
        mkProp l =
            setName lang .
            (\x -> langNames & Lens.cloneLens l .~ if x == "" then Nothing else Just x)
            & Property (langNames ^. Lens.cloneLens l . Lens._Just)

makeMissingLangRow ::
    ( Applicative o
    , MonadReader env m
    , Has (Map LangId Text) env, Has (Texts.CodeUI Text) env
    , TextEdit.Deps env, GuiState.HasCursor env, Has Config.Config env
    ) =>
    Widget.Id -> (LangId -> TextsInLang -> o ()) -> LangId ->
    m (Row (Aligned (Widget o)))
makeMissingLangRow parentId setName lang =
    Row
    <$> makeLanguageTitle langId lang
    <*> pure Element.empty
    <*> makeFocusableTagNameEdit nameProp (nameId langId)
    <*> pure Element.empty
    <*> pure Element.empty
    <*> pure Element.empty
    <*> pure Element.empty
    <&> Lens.mapped %~ Align.fromWithTextPos 0
    where
        langId = langWidgetId parentId lang
        nameProp =
            setName lang . (\x -> TextsInLang x Nothing Nothing)
            & Property ""

make ::
    ( MonadReader env m
    , Applicative o
    , Has (Texts.CodeUI Text) env, Has (Grid.Texts Text) env
    , TextEdit.Deps env, Glue.HasTexts env
    , GuiState.HasCursor env, Has Theme env
    , Element.HasAnimIdPrefix env, Has Config.Config env
    , Spacer.HasStdSpacing env
    , Has LangId env, Has (Map LangId Text) env
    ) =>
    Sugar.TagPane Name o -> m (Widget o)
make tagPane =
    Styled.addValFrame <*>
    do
        lang <- Lens.view has
        let newForCurrentLang =
                [ makeMissingLangRow myId (tagPane ^. Sugar.tpSetName) lang
                | Lens.nullOf (Sugar.tpLocalizedNames . Lens.ix lang) tagPane
                ]
        let editExistingLangs =
                tagPane ^@.. Sugar.tpLocalizedNames . Lens.itraversed
                & sortOn ((/= lang) . fst)
                <&> uncurry (makeLangRow myId (tagPane ^. Sugar.tpSetName))
        Grid.make <*>
            sequence
            (heading : newForCurrentLang <> editExistingLangs)
            <&> snd
            & GuiState.assignCursor myId (nameId (langWidgetId myId lang))
        & Reader.local (Element.animIdPrefix .~ Widget.toAnimId myId)
    where
        heading =
            row
            (Styled.label MomentuTexts.language)
            (Styled.label Texts.name)
            (Styled.label Texts.abbreviation)
            (Styled.label Texts.disambiguationText)
        hspace = Spacer.stdHSpace <&> WithTextPos 0
        row lang name abbrev disambig =
            Row lang hspace name hspace abbrev hspace disambig
            & sequenceA
            <&> Lens.mapped . Align.tValue %~ Widget.fromView
            <&> Lens.mapped %~ Align.fromWithTextPos 0
        myId = tagPane ^. Sugar.tpTag . Sugar.tagInstance & WidgetIds.fromEntityId
