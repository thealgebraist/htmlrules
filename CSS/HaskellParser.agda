module CSS.HaskellParser where

open import CSS.Rendering
open import Data.String using (String; _==_)
open import Data.List hiding (span)
open import Data.Product
open import Data.Bool
open import Function
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

record HaskellAttr : Set where
  constructor hAttr
  field
    key : String
    val : String

data Token : Set where
  tstart : String → List HaskellAttr → Token
  tend   : String → Token
  ttext  : String → Token

postulate
  tokenizeHTML : String → IO (List Token)
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# FOREIGN GHC import qualified Parser as P #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

{-# COMPILE GHC HaskellAttr = data P.HaskellAttr (P.HAttr) #-}
{-# COMPILE GHC Token = data P.Token (P.TStart | P.TEnd | P.TText) #-}
{-# COMPILE GHC tokenizeHTML = P.tokenizeHTML #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

_>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

-- Helpers
mapTag : String → Tag
mapTag "div" = div
mapTag "span" = span
mapTag "p" = p
mapTag "h1" = h1
mapTag "h2" = h2
mapTag "img" = img
mapTag _ = div

mapAttr : List HaskellAttr → List Attr
mapAttr [] = []
mapAttr (hAttr k v ∷ as) = attr k v ∷ mapAttr as

-- Tree construction in Agda (Simplified version of previous attempt)
mutual
  {-# TERMINATING #-}
  parseTokens : List Token → List Node × List Token
  parseTokens [] = ([] , [])
  parseTokens (ttext s ∷ ts) = 
    let (ns , rest) = parseTokens ts
    in (text s ∷ ns , rest)
  parseTokens (tstart t attrs ∷ ts) = 
    -- Logic for building tree from tokens
    -- Consume children until tend t
    let (kids , restAfterKids) = parseChildren t ts
        (siblings , finalRest) = parseTokens restAfterKids
    in (elem (mapTag t) (mapAttr attrs) kids ∷ siblings , finalRest)
  parseTokens (tend t ∷ ts) = ([] , tend t ∷ ts)

  {-# TERMINATING #-}
  parseChildren : String → List Token → List Node × List Token
  parseChildren parentTag [] = ([] , [])
  parseChildren parentTag (tok ∷ ts) = 
    let (nodes , rest) = parseTokens (tok ∷ ts)
    in case rest of λ where
         (tend t ∷ final) → 
            case t == parentTag of λ where
              true  → (nodes , final)
              false → (nodes , rest)
         _ → (nodes , rest)

parseHTML : String → IO Node
parseHTML s = do
  toks ← tokenizeHTML s
  let (res , _) = parseTokens toks
  return (elem div [] res)
