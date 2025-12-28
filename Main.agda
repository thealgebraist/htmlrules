{-# OPTIONS --guardedness #-}
module Main where

open import CSS.Rendering
open import CSS.HaskellParser
open import CSS.Svg
open import Data.List hiding (_++_)
open import Data.Product
open import Data.Nat
open import Data.String hiding (show)
open import Function
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.Environment as Env #-}

postulate
  putStrLn : String → IO ⊤
  readFile : String → IO String
  getArgs  : IO (List String)

{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC readFile = Text.readFile . T.unpack #-}
{-# COMPILE GHC getArgs = (map T.pack) <$> Env.getArgs #-}

main = do
  args ← getArgs
  case args of λ where
    [] → putStrLn "Usage: ./Main <input.html>"
    (file ∷ _) → do
      html ← readFile file
      node ← parseHTML html
      let (layout , dl) = render (vp (px 800) (px 600)) node []
          svgContent = dlToSvg dl
          finalSvg = wrapSvg (px 800) (px 600) svgContent
      putStrLn finalSvg
