module CSS.Svg where

open import CSS.Rendering
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.String hiding (show)
open import Data.List hiding (_++_)
open import Function

-- Helper for converting Px to string
showPxVal : Px → String
showPxVal (px n) = showNat n

-- Generate SVG Rect
svgRect : Rect → String → String
svgRect (mkRect x y w h) col = 
  "<rect x=\"" ++ showPxVal x ++ 
  "\" y=\"" ++ showPxVal y ++ 
  "\" width=\"" ++ showPxVal w ++ 
  "\" height=\"" ++ showPxVal h ++ 
  "\" style=\"fill:none;stroke:" ++ col ++ ";stroke-width:1;stroke-opacity:0.5\" />"

-- Generate SVG Text
svgText : Rect → String → String
svgText (mkRect x y w h) content = 
  "<text x=\"" ++ showPxVal (px (Px.n x + 5)) ++ 
  "\" y=\"" ++ showPxVal (px (Px.n y + 15)) ++ 
  "\" font-family=\"monospace\" font-size=\"12\" fill=\"white\">" ++ content ++ "</text>"

-- Convert DrawCmd to SVG string
cmdToSvg : DrawCmd → String
cmdToSvg (DrawBox r col) = svgRect r "white" 
cmdToSvg (DrawImage r imgSrc) = svgRect r "cyan" 
cmdToSvg (DrawText r txt) = svgText r txt
cmdToSvg (DrawCircle r) = "" -- Not implemented

-- Convert DisplayList to SVG content
dlToSvg : DisplayList → String
dlToSvg [] = ""
dlToSvg (c ∷ cs) = cmdToSvg c ++ "\n" ++ dlToSvg cs

-- Wrap in SVG tag
wrapSvg : Px → Px → String → String
wrapSvg (px w) (px h) content = 
  "<svg width=\"" ++ showNat w ++ "\" height=\"" ++ showNat h ++ "\" xmlns=\"http://www.w3.org/2000/svg\">
" ++ 
  "<rect width=\"100%\" height=\"100%\" fill=\"black\" />\n" ++ 
  content ++ 
  "</svg>"