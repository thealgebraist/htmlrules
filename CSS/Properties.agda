module CSS.Properties where

open import CSS.Rendering
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.String hiding (_++_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat.Show using (show)

-- ------------------------------------------------------------------------
-- THEOREM 1: UNIQUENESS
-- Given Viewport, Node, and CSS, the layout coordinates are uniquely defined.
-- ------------------------------------------------------------------------

-- Helper to extract all coordinates (Rects) from a Layout
mutual
  getCoords : Box → List Rect
  getCoords (box _ r _ kids) = r ∷ getCoordsList kids

  getCoordsList : List Box → List Rect
  getCoordsList [] = []
  getCoordsList (b ∷ bs) = getCoords b ++ getCoordsList bs

getAllCoords : Layout → List Rect
getAllCoords bs = getCoordsList bs

-- Proof: Since 'render' is a deterministic function, its output is unique.
-- Therefore, the list of coordinates derived from it is also unique.
coords-unique : ∀ v n css → 
                let (l1 , _) = render v n css 
                    (l2 , _) = render v n css 
                in getAllCoords l1 ≡ getAllCoords l2
coords-unique v n css = refl

-- ------------------------------------------------------------------------
-- THEOREM 2: DEPENDENCY (NON-UNIQUENESS without CSS)
-- The positions of HTML elements given ONLY screen dimensions are NOT uniquely defined.
-- We prove this by counterexample: finding two different CSS inputs that produce
-- different coordinates for the same HTML and Viewport.
-- ------------------------------------------------------------------------

-- Setup: A Viewport and a simple HTML tree (div with two children)
testView : Viewport
testView = vp (px 100) (px 100)

testNode : Node
testNode = elem div [] (elem div [] [] ∷ elem div [] [] ∷ [])

-- CSS 1: All divs have height 10px
css1 : CSS
css1 = rule (sel div) (decl height "10" ∷ []) ∷ []

-- CSS 2: All divs have height 20px
css2 : CSS
css2 = rule (sel div) (decl height "20" ∷ []) ∷ []

-- Helper to extract the Y coordinate of the second child
-- Structure: Root -> [Child1, Child2]
getSecondChildY : Layout → Maybe ℕ
getSecondChildY (root ∷ []) with Box.kids root
... | (c1 ∷ c2 ∷ []) = just (Px.n (Rect.y (Box.rect c2)))
... | _              = nothing
getSecondChildY _    = nothing

-- Calculate the Y positions for both CSS inputs
y1 : Maybe ℕ
y1 = getSecondChildY (proj₁ (render testView testNode css1))

y2 : Maybe ℕ
y2 = getSecondChildY (proj₁ (render testView testNode css2))

-- PROOF: y1 is NOT equal to y2
-- y1 evaluates to 'just 10'
-- y2 evaluates to 'just 20'

y1-is-10 : y1 ≡ just 10
y1-is-10 = refl

y2-is-20 : y2 ≡ just 20
y2-is-20 = refl

-- The core proof: The positions are different
positions-differ : y1 ≢ y2
positions-differ eq with trans (sym y1-is-10) (trans eq y2-is-20)
... | () -- 10 is not 20

-- Conclusion:
-- The layout coordinates depend on the CSS.
-- Therefore, given only Viewport and HTML, the coordinates are not uniquely determined.
