module Parser where

import Text.XML.HXT.Core
import Data.Tree.NTree.TypeDefs
import Text.HandsomeSoup
import Data.Text (Text)
import qualified Data.Text as T
import Control.Arrow

data HaskellAttr = HAttr Text Text deriving Show
data Token = TStart Text [HaskellAttr] | TEnd Text | TText Text deriving Show

-- Recursive traversal of XmlTree to produce tokens
treeToTokens :: XmlTree -> [Token]
treeToTokens (NTree (XTag name attrs) children) =
    let tagName = T.pack (localPart name)
        parsedAttrs = concatMap attrToAgda attrs
    in TStart tagName parsedAttrs : concatMap treeToTokens children ++ [TEnd tagName]
  where
    attrToAgda (NTree (XAttr attrName) children) =
        let val = T.pack $ concatMap extractText children
        in [HAttr (T.pack (localPart attrName)) val]
    attrToAgda _ = []
    
    extractText (NTree (XText s) _) = s
    extractText _ = ""

treeToTokens (NTree (XText s) _) = [TText (T.pack s)]
treeToTokens _ = []

-- Main entry point using HXT/HandsomeSoup
tokenizeHTML :: Text -> IO [Token]
tokenizeHTML input = do
    let htmlStr = T.unpack input
    -- readString returns an arrow that produces XmlTrees
    trees <- runX (readString [withParseHTML yes, withWarnings no] htmlStr)
    return $ concatMap treeToTokens trees
