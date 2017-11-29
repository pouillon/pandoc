{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RelaxedPolyRec       #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- RelaxedPolyRec needed for inlinesBetween on GHC < 7
{-
  Copyright (C) 2017 Yann Pouillon <devops@materialsevolution.es>

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
-}

{- |
   Module      : Text.Pandoc.Readers.DokuWiki
   Copyright   : Copyright (C) 2017 Yann Pouillon
   License     : GNU GPL, version 2 or above

   Maintainer  : Yann Pouillon <devops@materialsevolution.es>
   Stability   : alpha
   Portability : portable

Conversion of dokuwiki text to 'Pandoc' document.
-}
{-
TODO:
_ correctly handle tables within tables
_ parse templates?
-}
module Text.Pandoc.Readers.DokuWiki ( readDokuWiki ) where

import Control.Monad
import Control.Monad.Except (throwError)
import Data.Char (isDigit, isSpace)
import qualified Data.Foldable as F
import Data.List (intercalate, intersperse, isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, maybeToList)
import Data.Monoid ((<>))
import Data.Sequence (ViewL (..), viewl, (<|))
import qualified Data.Set as Set
import Data.Text (Text, unpack)
import Text.HTML.TagSoup
import Text.Pandoc.Builder (Blocks, Inlines, trimInlines)
import qualified Text.Pandoc.Builder as B
import Text.Pandoc.Class (PandocMonad (..))
import Text.Pandoc.Definition
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Parsing hiding (nested)
import Text.Pandoc.Readers.HTML (htmlTag, isBlockTag, isCommentTag)
import Text.Pandoc.Shared (crFilter, safeRead, stringify, stripTrailingNewlines,
                           trim)
import Text.Pandoc.Walk (walk)
import Text.Pandoc.XML (fromEntities)

-- | Read dokuwiki from an input string and return a Pandoc document.
readDokuWiki :: PandocMonad m
              => ReaderOptions -- ^ Reader options
              -> Text          -- ^ String to parse (assuming @'\n'@ line endings)
              -> m Pandoc
readDokuWiki opts s = do
  parsed <- readWithM parseDokuWiki DWState{ dwOptions = opts
                                            , dwMaxNestingLevel = 4
                                            , dwNextLinkNumber  = 1
                                            , dwCategoryLinks = []
                                            , dwHeaderMap = M.empty
                                            , dwIdentifierList = Set.empty
                                            , dwLogMessages = []
                                            , dwInTT = False
                                            }
            (unpack (crFilter s) ++ "\n")
  case parsed of
    Right result -> return result
    Left e       -> throwError e

data DWState = DWState { dwOptions         :: ReaderOptions
                       , dwMaxNestingLevel :: Int
                       , dwNextLinkNumber  :: Int
                       , dwCategoryLinks   :: [Inlines]
                       , dwHeaderMap       :: M.Map Inlines String
                       , dwIdentifierList  :: Set.Set String
                       , dwLogMessages     :: [LogMessage]
                       , dwInTT            :: Bool
                       }

type DWParser m = ParserT [Char] DWState m

instance HasReaderOptions DWState where
  extractReaderOptions = dwOptions

instance HasHeaderMap DWState where
  extractHeaderMap     = dwHeaderMap
  updateHeaderMap f st = st{ dwHeaderMap = f $ dwHeaderMap st }

instance HasIdentifierList DWState where
  extractIdentifierList     = dwIdentifierList
  updateIdentifierList f st = st{ dwIdentifierList = f $ dwIdentifierList st }

instance HasLogMessages DWState where
  addLogMessage m s = s{ dwLogMessages = m : dwLogMessages s }
  getLogMessages = reverse . dwLogMessages

--
-- auxiliary functions
--

-- This is used to prevent exponential blowups for things like:
-- ''a'''a''a'''a''a'''a''a'''a
nested :: PandocMonad m => DWParser m a -> DWParser m a
nested p = do
  nestlevel <- dwMaxNestingLevel `fmap` getState
  guard $ nestlevel > 0
  updateState $ \st -> st{ dwMaxNestingLevel = dwMaxNestingLevel st - 1 }
  res <- p
  updateState $ \st -> st{ dwMaxNestingLevel = nestlevel }
  return res

specialChars :: [Char]
specialChars = "'[]<=&*{}|\":\\"

spaceChars :: [Char]
spaceChars = " \n\t"

sym :: PandocMonad m => String -> DWParser m ()
sym s = () <$ try (string s)

newBlockTags :: [String]
newBlockTags = ["haskell","syntaxhighlight","source","gallery","references"]

isBlockTag' :: Tag String -> Bool
isBlockTag' tag@(TagOpen t _) = (isBlockTag tag || t `elem` newBlockTags) &&
  t `notElem` eitherBlockOrInline
isBlockTag' tag@(TagClose t) = (isBlockTag tag || t `elem` newBlockTags) &&
  t `notElem` eitherBlockOrInline
isBlockTag' tag = isBlockTag tag

isInlineTag' :: Tag String -> Bool
isInlineTag' (TagComment _) = True
isInlineTag' t              = not (isBlockTag' t)

eitherBlockOrInline :: [String]
eitherBlockOrInline = ["applet", "button", "del", "iframe", "ins",
                               "map", "area", "object"]

htmlComment :: PandocMonad m => DWParser m ()
htmlComment = () <$ htmlTag isCommentTag

inlinesInTags :: PandocMonad m => String -> DWParser m Inlines
inlinesInTags tag = try $ do
  (_,raw) <- htmlTag (~== TagOpen tag [])
  if '/' `elem` raw   -- self-closing tag
     then return mempty
     else trimInlines . mconcat <$>
            manyTill inline (htmlTag (~== TagClose tag))

blocksInTags :: PandocMonad m => String -> DWParser m Blocks
blocksInTags tag = try $ do
  (_,raw) <- htmlTag (~== TagOpen tag [])
  let closer = if tag == "li"
                  then htmlTag (~== TagClose "li")
                     <|> lookAhead (
                              htmlTag (~== TagOpen "li" [])
                          <|> htmlTag (~== TagClose "ol")
                          <|> htmlTag (~== TagClose "ul"))
                  else htmlTag (~== TagClose tag)
  if '/' `elem` raw   -- self-closing tag
     then return mempty
     else mconcat <$> manyTill block closer

charsInTags :: PandocMonad m => String -> DWParser m [Char]
charsInTags tag = try $ do
  (_,raw) <- htmlTag (~== TagOpen tag [])
  if '/' `elem` raw   -- self-closing tag
     then return ""
     else manyTill anyChar (htmlTag (~== TagClose tag))

--
-- main parser
--

parseDokuWiki :: PandocMonad m => DWParser m Pandoc
parseDokuWiki = do
  bs <- mconcat <$> many block
  spaces
  eof
  categoryLinks <- reverse . dwCategoryLinks <$> getState
  let categories = if null categoryLinks
                      then mempty
                      else B.para $ mconcat $ intersperse B.space categoryLinks
  reportLogMessages
  return $ B.doc $ bs <> categories

--
-- block parsers
--

block :: PandocMonad m => DWParser m Blocks
block = do
  res <- mempty <$ skipMany1 blankline
     <|> table
     <|> header
     <|> hrule
     <|> orderedList
     <|> bulletList
     <|> definitionList
     <|> mempty <$ try (spaces *> htmlComment)
     <|> preformatted
     <|> blockTag
     <|> (B.rawBlock "dokuwiki" <$> template)
     <|> para
  trace (take 60 $ show $ B.toList res)
  return res

para :: PandocMonad m => DWParser m Blocks
para = do
  contents <- trimInlines . mconcat <$> many1 inline
  if F.all (==Space) contents
     then return mempty
     else return $ B.para contents

table :: PandocMonad m => DWParser m Blocks
table = do
  tableStart
  styles <- option [] parseAttrs
  skipMany spaceChar
  optional blanklines
  let tableWidth = case lookup "width" styles of
                         Just w  -> fromMaybe 1.0 $ parseWidth w
                         Nothing -> 1.0
  caption <- option mempty tableCaption
  optional rowsep
  hasheader <- option False $ True <$ lookAhead (skipSpaces *> char '!')
  (cellspecs',hdr) <- unzip <$> tableRow
  let widths = map ((tableWidth *) . snd) cellspecs'
  let restwidth = tableWidth - sum widths
  let zerocols = length $ filter (==0.0) widths
  let defaultwidth = if zerocols == 0 || zerocols == length widths
                        then 0.0
                        else restwidth / fromIntegral zerocols
  let widths' = map (\w -> if w == 0 then defaultwidth else w) widths
  let cellspecs = zip (map fst cellspecs') widths'
  rows' <- many $ try $ rowsep *> (map snd <$> tableRow)
  optional blanklines
  tableEnd
  let cols = length hdr
  let (headers,rows) = if hasheader
                          then (hdr, rows')
                          else (replicate cols mempty, hdr:rows')
  return $ B.table caption cellspecs headers rows

parseAttrs :: PandocMonad m => DWParser m [(String,String)]
parseAttrs = many1 parseAttr

parseAttr :: PandocMonad m => DWParser m (String, String)
parseAttr = try $ do
  skipMany spaceChar
  k <- many1 letter
  char '='
  v <- (char '"' >> many1Till (satisfy (/='\n')) (char '"'))
       <|> many1 (satisfy $ \c -> not (isSpace c) && c /= '|')
  return (k,v)

tableStart :: PandocMonad m => DWParser m ()
tableStart = try $ guardColumnOne *> skipSpaces *> sym "{|"

tableEnd :: PandocMonad m => DWParser m ()
tableEnd = try $ guardColumnOne *> skipSpaces *> sym "|}"

rowsep :: PandocMonad m => DWParser m ()
rowsep = try $ guardColumnOne *> skipSpaces *> sym "|-" <*
               many (char '-') <* optional parseAttr <* blanklines

cellsep :: PandocMonad m => DWParser m ()
cellsep = try $ do
  skipSpaces
  (char '|' *> notFollowedBy (oneOf "-}+") *> optional (char '|'))
    <|> (char '!' *> optional (char '!'))

tableCaption :: PandocMonad m => DWParser m Inlines
tableCaption = try $ do
  guardColumnOne
  skipSpaces
  sym "|+"
  optional (try $ parseAttr *> skipSpaces *> char '|' *> skipSpaces)
  (trimInlines . mconcat) <$> many (notFollowedBy (cellsep <|> rowsep) *> inline)

tableRow :: PandocMonad m => DWParser m [((Alignment, Double), Blocks)]
tableRow = try $ skipMany htmlComment *> many tableCell

tableCell :: PandocMonad m => DWParser m ((Alignment, Double), Blocks)
tableCell = try $ do
  cellsep
  skipMany spaceChar
  attrs <- option [] $ try $ parseAttrs <* skipSpaces <* char '|' <*
                                 notFollowedBy (char '|')
  skipMany spaceChar
  pos' <- getPosition
  ls <- concat <$> many (notFollowedBy (cellsep <|> rowsep <|> tableEnd) *>
                     ((snd <$> withRaw table) <|> count 1 anyChar))
  bs <- parseFromString (do setPosition pos'
                            mconcat <$> many block) ls
  let align = case lookup "align" attrs of
                    Just "left"   -> AlignLeft
                    Just "right"  -> AlignRight
                    Just "center" -> AlignCenter
                    _             -> AlignDefault
  let width = case lookup "width" attrs of
                    Just xs -> fromMaybe 0.0 $ parseWidth xs
                    Nothing -> 0.0
  return ((align, width), bs)

parseWidth :: String -> Maybe Double
parseWidth s =
  case reverse s of
       ('%':ds) | all isDigit ds -> safeRead ('0':'.':reverse ds)
       _        -> Nothing

template :: PandocMonad m => DWParser m String
template = try $ do
  string "{{"
  notFollowedBy (char '{')
  lookAhead $ letter <|> digit <|> char ':'
  let chunk = template <|> variable <|> many1 (noneOf "{}") <|> count 1 anyChar
  contents <- manyTill chunk (try $ string "}}")
  return $ "{{" ++ concat contents ++ "}}"

blockTag :: PandocMonad m => DWParser m Blocks
blockTag = do
  (tag, _) <- lookAhead $ htmlTag isBlockTag'
  case tag of
      TagOpen "blockquote" _ -> B.blockQuote <$> blocksInTags "blockquote"
      TagOpen "pre" _ -> B.codeBlock . trimCode <$> charsInTags "pre"
      TagOpen "syntaxhighlight" attrs -> syntaxhighlight "syntaxhighlight" attrs
      TagOpen "source" attrs -> syntaxhighlight "source" attrs
      TagOpen "haskell" _ -> B.codeBlockWith ("",["haskell"],[]) . trimCode <$>
                                charsInTags "haskell"
      TagOpen "gallery" _ -> blocksInTags "gallery"
      TagOpen "p" _ -> mempty <$ htmlTag (~== tag)
      TagClose "p"  -> mempty <$ htmlTag (~== tag)
      _ -> B.rawBlock "html" . snd <$> htmlTag (~== tag)

trimCode :: String -> String
trimCode ('\n':xs) = stripTrailingNewlines xs
trimCode xs        = stripTrailingNewlines xs

syntaxhighlight :: PandocMonad m => String -> [Attribute String] -> DWParser m Blocks
syntaxhighlight tag attrs = try $ do
  let mblang = lookup "lang" attrs
  let mbstart = lookup "start" attrs
  let mbline = lookup "line" attrs
  let classes = maybeToList mblang ++ maybe [] (const ["numberLines"]) mbline
  let kvs = maybe [] (\x -> [("startFrom",x)]) mbstart
  contents <- charsInTags tag
  return $ B.codeBlockWith ("",classes,kvs) $ trimCode contents

hrule :: PandocMonad m => DWParser m Blocks
hrule = B.horizontalRule <$ try (string "----" *> many (char '-') *> newline)

guardColumnOne :: PandocMonad m => DWParser m ()
guardColumnOne = getPosition >>= \pos -> guard (sourceColumn pos == 1)

preformatted :: PandocMonad m => DWParser m Blocks
preformatted = try $ do
  guardColumnOne
  char ' '
  let endline' = B.linebreak <$ try (newline <* char ' ')
  let whitespace' = B.str <$> many1 ('\160' <$ spaceChar)
  let spToNbsp ' ' = '\160'
      spToNbsp x   = x
  let nowiki' = mconcat . intersperse B.linebreak . map B.str .
                lines . fromEntities . map spToNbsp <$> try
                  (htmlTag (~== TagOpen "nowiki" []) *>
                   manyTill anyChar (htmlTag (~== TagClose "nowiki")))
  let inline' = whitespace' <|> endline' <|> nowiki'
                  <|> try (notFollowedBy newline *> inline)
  contents <- mconcat <$> many1 inline'
  let spacesStr (Str xs) = all isSpace xs
      spacesStr _        = False
  if F.all spacesStr contents
     then return mempty
     else return $ B.para $ encode contents

encode :: Inlines -> Inlines
encode = B.fromList . normalizeCode . B.toList . walk strToCode
  where strToCode (Str s) = Code ("",[],[]) s
        strToCode Space   = Code ("",[],[]) " "
        strToCode  x      = x
        normalizeCode []  = []
        normalizeCode (Code a1 x : Code a2 y : zs) | a1 == a2 =
          normalizeCode $ Code a1 (x ++ y) : zs
        normalizeCode (x:xs) = x : normalizeCode xs

header :: PandocMonad m => DWParser m Blocks
header = try $ do
  guardColumnOne
  eqs <- many1 (char '=')
  let lev = length eqs
  guard $ lev <= 6
  contents <- trimInlines . mconcat <$> manyTill inline (count lev $ char '=')
  attr <- registerHeader nullAttr contents
  return $ B.headerWith attr lev contents

bulletList :: PandocMonad m => DWParser m Blocks
bulletList = B.bulletList <$>
   (   many1 (listItem '*')
   <|> (htmlTag (~== TagOpen "ul" []) *> spaces *> many (listItem '*' <|> li) <*
        optional (htmlTag (~== TagClose "ul"))) )

orderedList :: PandocMonad m => DWParser m Blocks
orderedList =
       (B.orderedList <$> many1 (listItem '#'))
   <|> try
       (do (tag,_) <- htmlTag (~== TagOpen "ol" [])
           spaces
           items <- many (listItem '#' <|> li)
           optional (htmlTag (~== TagClose "ol"))
           let start = fromMaybe 1 $ safeRead $ fromAttrib "start" tag
           return $ B.orderedListWith (start, DefaultStyle, DefaultDelim) items)

definitionList :: PandocMonad m => DWParser m Blocks
definitionList = B.definitionList <$> many1 defListItem

defListItem :: PandocMonad m => DWParser m (Inlines, [Blocks])
defListItem = try $ do
  terms <- mconcat . intersperse B.linebreak <$> many defListTerm
  -- we allow dd with no dt, or dt with no dd
  defs  <- if B.isNull terms
              then notFollowedBy
                    (try $ skipMany1 (char ':') >> string "<math>") *>
                       many1 (listItem ':')
              else many (listItem ':')
  return (terms, defs)

defListTerm  :: PandocMonad m => DWParser m Inlines
defListTerm = do
  guardColumnOne
  char ';'
  skipMany spaceChar
  pos' <- getPosition
  anyLine >>= parseFromString (do setPosition pos'
                                  trimInlines . mconcat <$> many inline)

listStart :: PandocMonad m => Char -> DWParser m ()
listStart c = char c *> notFollowedBy listStartChar

listStartChar :: PandocMonad m => DWParser m Char
listStartChar = oneOf "*#;:"

anyListStart :: PandocMonad m => DWParser m Char
anyListStart = guardColumnOne >> oneOf "*#:;"

li :: PandocMonad m => DWParser m Blocks
li = lookAhead (htmlTag (~== TagOpen "li" [])) *>
     (firstParaToPlain <$> blocksInTags "li") <* spaces

listItem :: PandocMonad m => Char -> DWParser m Blocks
listItem c = try $ do
  guardColumnOne
  extras <- many (try $ char c <* lookAhead listStartChar)
  if null extras
     then listItem' c
     else do
       skipMany spaceChar
       pos' <- getPosition
       first <- concat <$> manyTill listChunk newline
       rest <- many
                (try $ string extras *> lookAhead listStartChar *>
                       (concat <$> manyTill listChunk newline))
       contents <- parseFromString (do setPosition pos'
                                       many1 $ listItem' c)
                          (unlines (first : rest))
       case c of
           '*' -> return $ B.bulletList contents
           '#' -> return $ B.orderedList contents
           ':' -> return $ B.definitionList [(mempty, contents)]
           _   -> mzero

-- The point of this is to handle stuff like
-- * {{cite book
-- | blah
-- | blah
-- }}
-- * next list item
-- which seems to be valid dokuwiki.
listChunk :: PandocMonad m => DWParser m String
listChunk = template <|> count 1 anyChar

listItem' :: PandocMonad m => Char -> DWParser m Blocks
listItem' c = try $ do
  listStart c
  skipMany spaceChar
  pos' <- getPosition
  first <- concat <$> manyTill listChunk newline
  rest <- many (try $ char c *> lookAhead listStartChar *>
                   (concat <$> manyTill listChunk newline))
  parseFromString (do setPosition pos'
                      firstParaToPlain . mconcat <$> many1 block)
      $ unlines $ first : rest

firstParaToPlain :: Blocks -> Blocks
firstParaToPlain contents =
  case viewl (B.unMany contents) of
       Para xs :< ys -> B.Many $ Plain xs <| ys
       _             -> contents

--
-- inline parsers
--

inline :: PandocMonad m => DWParser m Inlines
inline =  whitespace
      <|> url
      <|> str
      <|> doubleQuotes
      <|> strong
      <|> emph
      <|> image
      <|> internalLink
      <|> externalLink
      <|> math
      <|> inlineTag
      <|> B.singleton <$> charRef
      <|> inlineHtml
      <|> (B.rawInline "dokuwiki" <$> variable)
      <|> (B.rawInline "dokuwiki" <$> template)
      <|> special

str :: PandocMonad m => DWParser m Inlines
str = B.str <$> many1 (noneOf $ specialChars ++ spaceChars)

math :: PandocMonad m => DWParser m Inlines
math = (B.displayMath . trim <$> try (many1 (char ':') >> charsInTags "math"))
   <|> (B.math . trim <$> charsInTags "math")
   <|> (B.displayMath . trim <$> try (dmStart *> manyTill anyChar dmEnd))
   <|> (B.math . trim <$> try (mStart *> manyTill (satisfy (/='\n')) mEnd))
 where dmStart = string "\\["
       dmEnd   = try (string "\\]")
       mStart  = string "\\("
       mEnd    = try (string "\\)")

variable :: PandocMonad m => DWParser m String
variable = try $ do
  string "{{{"
  contents <- manyTill anyChar (try $ string "}}}")
  return $ "{{{" ++ contents ++ "}}}"

inlineTag :: PandocMonad m => DWParser m Inlines
inlineTag = do
  (tag, _) <- lookAhead $ htmlTag isInlineTag'
  case tag of
       TagOpen "ref" _ -> B.note . B.plain <$> inlinesInTags "ref"
       TagOpen "nowiki" _ -> try $ do
          (_,raw) <- htmlTag (~== tag)
          if '/' `elem` raw
             then return mempty
             else B.text . fromEntities <$>
                       manyTill anyChar (htmlTag (~== TagClose "nowiki"))
       TagOpen "br" _ -> B.linebreak <$ (htmlTag (~== TagOpen "br" []) -- will get /> too
                            *> optional blankline)
       TagOpen "strike" _ -> B.strikeout <$> inlinesInTags "strike"
       TagOpen "del" _ -> B.strikeout <$> inlinesInTags "del"
       TagOpen "sub" _ -> B.subscript <$> inlinesInTags "sub"
       TagOpen "sup" _ -> B.superscript <$> inlinesInTags "sup"
       TagOpen "code" _ -> encode <$> inlinesInTags "code"
       TagOpen "tt" _ -> do
         inTT <- dwInTT <$> getState
         updateState $ \st -> st{ dwInTT = True }
         result <- encode <$> inlinesInTags "tt"
         updateState $ \st -> st{ dwInTT = inTT }
         return result
       TagOpen "hask" _ -> B.codeWith ("",["haskell"],[]) <$> charsInTags "hask"
       _ -> B.rawInline "html" . snd <$> htmlTag (~== tag)

special :: PandocMonad m => DWParser m Inlines
special = B.str <$> count 1 (notFollowedBy' (htmlTag isBlockTag') *>
                             oneOf specialChars)

inlineHtml :: PandocMonad m => DWParser m Inlines
inlineHtml = B.rawInline "html" . snd <$> htmlTag isInlineTag'

whitespace :: PandocMonad m => DWParser m Inlines
whitespace = B.space <$ (skipMany1 spaceChar <|> htmlComment)
         <|> B.softbreak <$ endline

endline :: PandocMonad m => DWParser m ()
endline = () <$ try (newline <*
                     notFollowedBy spaceChar <*
                     notFollowedBy newline <*
                     notFollowedBy' hrule <*
                     notFollowedBy tableStart <*
                     notFollowedBy' header <*
                     notFollowedBy anyListStart)

imageIdentifiers :: PandocMonad m => [DWParser m ()]
imageIdentifiers = [sym (identifier ++ ":") | identifier <- identifiers]
    where identifiers = ["File", "Image", "Archivo", "Datei", "Fichier",
                         "Bild"]

image :: PandocMonad m => DWParser m Inlines
image = try $ do
  sym "[["
  choice imageIdentifiers
  fname <- addUnderscores <$> many1 (noneOf "|]")
  _ <- many imageOption
  dims <- try (char '|' *> sepBy (many digit) (char 'x') <* string "px")
          <|> return []
  _ <- many imageOption
  let kvs = case dims of
              [w]    -> [("width", w)]
              [w, h] -> [("width", w), ("height", h)]
              _      -> []
  let attr = ("", [], kvs)
  caption <-   (B.str fname <$ sym "]]")
           <|> try (char '|' *> (mconcat <$> manyTill inline (sym "]]")))
  return $ B.imageWith attr fname ("fig:" ++ stringify caption) caption

imageOption :: PandocMonad m => DWParser m String
imageOption = try $ char '|' *> opt
  where
    opt = try (oneOfStrings [ "border", "thumbnail", "frameless"
                            , "thumb", "upright", "left", "right"
                            , "center", "none", "baseline", "sub"
                            , "super", "top", "text-top", "middle"
                            , "bottom", "text-bottom" ])
      <|> try (string "frame")
      <|> try (oneOfStrings ["link=","alt=","page=","class="] <* many (noneOf "|]"))

collapseUnderscores :: String -> String
collapseUnderscores []           = []
collapseUnderscores ('_':'_':xs) = collapseUnderscores ('_':xs)
collapseUnderscores (x:xs)       = x : collapseUnderscores xs

addUnderscores :: String -> String
addUnderscores = collapseUnderscores . intercalate "_" . words

internalLink :: PandocMonad m => DWParser m Inlines
internalLink = try $ do
  sym "[["
  pagename <- unwords . words <$> many (noneOf "|]")
  label <- option (B.text pagename) $ char '|' *>
             (  (mconcat <$> many1 (notFollowedBy (char ']') *> inline))
             -- the "pipe trick"
             -- [[Help:Contents|] -> "Contents"
             <|> return (B.text $ drop 1 $ dropWhile (/=':') pagename) )
  sym "]]"
  linktrail <- B.text <$> many letter
  let link = B.link (addUnderscores pagename) "wikilink" (label <> linktrail)
  if "Category:" `isPrefixOf` pagename
     then do
       updateState $ \st -> st{ dwCategoryLinks = link : dwCategoryLinks st }
       return mempty
     else return link

externalLink :: PandocMonad m => DWParser m Inlines
externalLink = try $ do
  char '['
  (_, src) <- uri
  lab <- try (trimInlines . mconcat <$>
              (skipMany1 spaceChar *> manyTill inline (char ']')))
       <|> do char ']'
              num <- dwNextLinkNumber <$> getState
              updateState $ \st -> st{ dwNextLinkNumber = num + 1 }
              return $ B.str $ show num
  return $ B.link src "" lab

url :: PandocMonad m => DWParser m Inlines
url = do
  (orig, src) <- uri
  return $ B.link src "" (B.str orig)

-- | Parses a list of inlines between start and end delimiters.
inlinesBetween :: (PandocMonad m, Show b) => DWParser m a -> DWParser m b -> DWParser m Inlines
inlinesBetween start end =
  (trimInlines . mconcat) <$> try (start >> many1Till inner end)
    where inner      = innerSpace <|> (notFollowedBy' (() <$ whitespace) >> inline)
          innerSpace = try $ whitespace <* notFollowedBy' end

emph :: PandocMonad m => DWParser m Inlines
emph = B.emph <$> nested (inlinesBetween start end)
    where start = sym "''" >> lookAhead nonspaceChar
          end   = try $ notFollowedBy' (() <$ strong) >> sym "''"

strong :: PandocMonad m => DWParser m Inlines
strong = B.strong <$> nested (inlinesBetween start end)
    where start = sym "'''" >> lookAhead nonspaceChar
          end   = try $ sym "'''"

doubleQuotes :: PandocMonad m => DWParser m Inlines
doubleQuotes = do
  guardEnabled Ext_smart
  inTT <- dwInTT <$> getState
  guard (not inTT)
  B.doubleQuoted <$> nested (inlinesBetween openDoubleQuote closeDoubleQuote)
    where openDoubleQuote = sym "\"" >> lookAhead nonspaceChar
          closeDoubleQuote = try $ sym "\""
