module CSS.Rendering where

open import Data.Nat
open import Data.Nat.Show using (readMaybe; show)
open import Data.List hiding (span)
open import Data.Char using (Char)
open import Data.Product
open import Data.String renaming (_++_ to _^_)
open import Data.Maybe
open import Data.Bool
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- BASIC GEOMETRY
------------------------------------------------------------------------

record Px : Set where
  constructor px
  field n : ℕ

open Px

record Rect : Set where
  constructor mkRect
  field
    x y w h : Px

------------------------------------------------------------------------
-- VIEWPORT
------------------------------------------------------------------------

record Viewport : Set where
  constructor vp
  field width height : Px

------------------------------------------------------------------------
-- HTML DOM (simplified)
------------------------------------------------------------------------

data Tag : Set where
  div span img p h1 h2 : Tag

record Attr : Set where
  constructor attr
  field name value : String

data Node : Set where
  text : String → Node
  elem : Tag → List Attr → List Node → Node

------------------------------------------------------------------------
-- CSS AST (simplified)
------------------------------------------------------------------------

record Selector : Set where
  constructor sel
  field tagName : Tag

open Selector

data Property : Set where
  width height margin padding : Property
  display color background src fontSize : Property

record Decl : Set where
  constructor decl
  field prop : Property
        val  : String

record Rule : Set where
  constructor rule
  field
    selector : Selector
    decls    : List Decl

open Rule

CSS : Set
CSS = List Rule

------------------------------------------------------------------------
-- BOX TREE
------------------------------------------------------------------------

data DisplayType : Set where
  block inline none : DisplayType

record Box : Set where
  inductive
  constructor box
  field
    node  : Node
    rect  : Rect
    dtype : DisplayType
    kids  : List Box

Layout : Set
Layout = List Box

------------------------------------------------------------------------
-- DRAW COMMANDS
------------------------------------------------------------------------

data DrawCmd : Set where
  DrawBox    : Rect → String → DrawCmd -- color
  DrawImage  : Rect → String → DrawCmd -- src
  DrawText   : Rect → String → DrawCmd -- text
  DrawCircle : Rect → DrawCmd

DisplayList : Set
DisplayList = List DrawCmd

------------------------------------------------------------------------
-- HELPER FUNCTIONS
------------------------------------------------------------------------

-- Simple naive string to nat parser for "100", "20" etc.
-- Does not handle "px" suffix automatically, assumes number is pure.
-- But CSS usually has "px".
-- Let's strip "px" if present.

charToNat : Char → Maybe ℕ
charToNat '0' = just 0
charToNat '1' = just 1
charToNat '2' = just 2
charToNat '3' = just 3
charToNat '4' = just 4
charToNat '5' = just 5
charToNat '6' = just 6
charToNat '7' = just 7
charToNat '8' = just 8
charToNat '9' = just 9
charToNat _   = nothing

parseNat' : List Char → ℕ → ℕ
parseNat' [] acc = acc
parseNat' (c ∷ cs) acc with charToNat c
... | just n  = parseNat' cs (acc * 10 + n)
... | nothing = acc -- Stop parsing on non-digit

parseNat : String → ℕ
parseNat s = parseNat' (toList s) 0

-- Remove "px" from end if exists
stripPx : String → String
stripPx s = 
  let l = toList s in
  -- simplistic: just parse the number part
  s 
  -- real implementation would check suffix

-- Equality for Property
eqProp : Property → Property → Bool
eqProp width width = true
eqProp height height = true
eqProp margin margin = true
eqProp padding padding = true
eqProp display display = true
eqProp color color = true
eqProp background background = true
eqProp src src = true
eqProp fontSize fontSize = true
eqProp _ _ = false

findDecl : Property → List Decl → Maybe String
findDecl pr [] = nothing
findDecl pr (d ∷ ds) = if eqProp pr (Decl.prop d) then just (Decl.val d) else findDecl pr ds

-- Matching selectors
tagEq : Tag → Tag → Bool
tagEq div div = true
tagEq span span = true
tagEq img img = true
tagEq p p = true
tagEq h1 h1 = true
tagEq h2 h2 = true
tagEq _ _ = false

matches : Node → Selector → Bool
matches (text _) _ = false
matches (elem t _ _) (sel t') = tagEq t t'

collectDecls : Node → CSS → List Decl
collectDecls n [] = []
collectDecls n (r ∷ rs) = 
  if matches n (Rule.selector r) 
  then Rule.decls r ++ collectDecls n rs 
  else collectDecls n rs

------------------------------------------------------------------------
-- COMPUTED STYLE
------------------------------------------------------------------------

record Style : Set where
  constructor style
  field
    disp         : DisplayType
    computedW    : Px
    computedH    : Px
    bgColor      : String
    fgColor      : String
    imageSource  : Maybe String
    fontSizePx   : Px

parseDisplay : String → DisplayType
parseDisplay "block" = block
parseDisplay "inline" = inline
parseDisplay "none"   = none
parseDisplay _        = block -- default

-- computeStyle implementation
computeStyle : Node → CSS → Style
computeStyle n css =
  let ds = collectDecls n css 
      
      d = case findDecl display ds of λ where
            (just v) → parseDisplay v
            nothing  → case n of λ where -- Defaults based on tag
              (text _) → inline
              (elem div _ _) → block
              (elem p _ _) → block
              (elem h1 _ _) → block
              (elem h2 _ _) → block
              _ → inline
      
      w = case findDecl width ds of λ where
            (just v) → px (parseNat v)
            nothing  → px 0 -- 0 means auto/unspecified here for now
            
      h = case findDecl height ds of λ where
            (just v) → px (parseNat v)
            nothing  → px 0

      bg = case findDecl background ds of λ where
             (just v) → v
             nothing  → "transparent"
             
      fg = case findDecl color ds of λ where
             (just v) → v
             nothing  → "black"

      srcVal = findDecl src ds
      
      fs = case findDecl fontSize ds of λ where
             (just v) → px (parseNat v)
             nothing  → px 16

  in style d w h bg fg srcVal fs

------------------------------------------------------------------------
-- LAYOUT SEMANTICS
------------------------------------------------------------------------

-- We need a layout state or just simple recursion.
-- We'll pass the cursor (x, y) and available width.

layoutKids : Px → Px → Px → List Node → CSS → List Box × Px
layoutKids x y availW [] css = ([] , y)
layoutKids x y availW (n ∷ ns) css = 
  let -- Layout current node
      -- First, compute style to know if it's block or inline (simplified: treat all as block for vertical stacking for now, or text as inline)
      -- But we need to call layoutNode recursively.
      -- To avoid mutual recursion issues if simple, we can define a worker.
      -- But layoutNode calls layoutKids.
      -- We'll use a `layout` function that handles both.
      dummy = [] , y
  in dummy -- Placeholder, see mutual definition below

-- Helper for subtraction
minus : ℕ → ℕ → ℕ
minus a b = a ∸ b

isPositive : ℕ → Bool
isPositive 0 = false
isPositive _ = true

-- Mutual recursion for layout
mutual
  layoutNode' : Px → Px → Px → Node → CSS → Box
  layoutNode' x y availW n css = 
    let s = computeStyle n css
        styW = Style.computedW s
        styH = Style.computedH s
        disp = Style.disp s
        
        -- Determine actual width
        actualW : Px
        actualW = if isPositive (Px.n styW) then styW else availW
        
        -- Layout children
        -- If text node, no children.
        kidsRes : List Box × Px
        kidsRes = case n of λ where
          (text _) → ([] , y) -- Text doesn't have box children in this simplified model, it IS the content.
                              -- But wait, `Box` contains `Node`. If `Node` is text, it's a leaf.
          (elem _ _ children) → layoutChildren x y actualW children css -- x is absolute? No, x is passed in.
                                                                           -- Children x starts at parent x (plus padding/margin if we had them)
        
        childBoxes = proj₁ kidsRes
        maxY       = proj₂ kidsRes
        
        -- Determine height
        actualH : Px
        actualH = if isPositive (Px.n styH) 
                  then styH 
                  else (px (minus (Px.n maxY) (Px.n y))) -- Height based on content
        
        -- Adjust height for text nodes (approximate)
        finalH = case n of λ where
          (text str) → px 20 -- Fixed line height for text
          _          → if isPositive (Px.n actualH) then actualH else (px 20) -- Minimal height
          
    in box n (mkRect x y actualW finalH) disp childBoxes

  layoutChildren : Px → Px → Px → List Node → CSS → List Box × Px
  layoutChildren x y w [] css = ([] , y)
  layoutChildren x y w (n ∷ ns) css =
    let b = layoutNode' x y w n css
        -- Update cursor for next sibling
        -- If block, move down. If inline, move right? 
        -- Simplified: Everything stacks vertically for now.
        -- Or check display type of b.
        h = Rect.h (Box.rect b)
        newY = px ((Px.n y) + (Px.n h))
        
        resRest = layoutChildren x newY w ns css
    in (b ∷ (proj₁ resRest) , (proj₂ resRest))

-- Top level layout
layoutNode : Viewport → Node → CSS → Box
layoutNode v n css = layoutNode' (px 0) (px 0) (Viewport.width v) n css

layoutTree : Viewport → List Node → CSS → List Box
layoutTree v ns css = proj₁ (layoutChildren (px 0) (px 0) (Viewport.width v) ns css)

------------------------------------------------------------------------
-- PAINTING / DRAW ORDER
------------------------------------------------------------------------

mutual
  paintBox : Box → List DrawCmd
  paintBox (box n r d kids) with d
  ... | none = []
  ... | _    = 
    let -- Draw background if not transparent (simplified check)
        
        -- For now, let's just emit DrawBox with a placeholder color or "border".
        contentCmds = case n of λ where
          (text s) → (DrawText r s ∷ [])
          (elem img attrs _) → (DrawImage r "placeholder.png" ∷ []) -- Should parse src from attrs/style
          _ → []
        
        kidCmds = paint kids
    in (DrawBox r "border" ∷ contentCmds ++ kidCmds)

  paint : Layout → DisplayList
  paint [] = []
  paint (b ∷ bs) = paintBox b ++ paint bs

------------------------------------------------------------------------
-- END-TO-END RENDERING
------------------------------------------------------------------------

render : Viewport → Node → CSS → Layout × DisplayList
render v n css =
  let root = layoutNode v n css in
  ( root ∷ [] , paint (root ∷ []) )

------------------------------------------------------------------------
-- UNIQUENESS PROOF
------------------------------------------------------------------------

render-unique :
  ∀ v n css →
    ∀ out1 out2 →
      render v n css ≡ out1 →
      render v n css ≡ out2 →
      out1 ≡ out2
render-unique v n css out1 out2 eq1 eq2 rewrite eq1 | eq2 = refl

------------------------------------------------------------------------
-- CONCRETE EXAMPLES (TESTING)
------------------------------------------------------------------------

-- Helpers for examples
t : String → Node
t s = text s

e : Tag → List Node → Node
e tag kids = elem tag [] kids

e' : Tag → List Decl → List Node → Node
e' tag decls kids = elem tag [] kids -- Decls are in CSS, not inline style for this model?
-- Wait, HTML usually has style attr. The model has `Attr`.
-- `computeStyle` only looks at CSS rules matching tag.
-- So we need to define CSS rules.

-- Sample CSS creation
rule' : Tag → List Decl → Rule
rule' t ds = rule (sel t) ds

d_w : ℕ → Decl
d_w n = decl width (Data.Nat.Show.show n)

d_h : ℕ → Decl
d_h n = decl height (Data.Nat.Show.show n)

d_bg : String → Decl
d_bg c = decl background c

d_c : String → Decl
d_c c = decl color c

-- 16 Examples

-- Example 1: Simple Div
ex1 : Layout × DisplayList
ex1 = render (vp (px 800) (px 600)) 
             (e div (t "Hello" ∷ [])) 
             (rule' div (d_bg "red" ∷ []) ∷ [])

-- Example 2: Nested Divs
ex2 = render (vp (px 500) (px 500))
             (e div (e div (t "Inner" ∷ []) ∷ []))
             []

-- Example 3: Fixed Width
ex3 = render (vp (px 800) (px 600))
             (e div (t "Fixed" ∷ []))
             (rule' div (d_w 100 ∷ []) ∷ [])

-- Example 4: Multiple rules
ex4 = render (vp (px 800) (px 600))
             (e div (e p (t "Paragraph" ∷ []) ∷ []))
             (rule' div (d_w 200 ∷ []) ∷ rule' p (d_c "blue" ∷ []) ∷ [])

-- Example 5: Image
ex5 = render (vp (px 800) (px 600))
             (e img [])
             (rule' img (d_w 50 ∷ d_h 50 ∷ []) ∷ [])

-- Example 6: Span (inline)
ex6 = render (vp (px 800) (px 600))
             (e span (t "Inline text" ∷ []))
             []

-- Example 7: H1 Header
ex7 = render (vp (px 800) (px 600))
             (e h1 (t "Title" ∷ []))
             (rule' h1 (decl fontSize "32" ∷ []) ∷ [])

-- Example 8: Two siblings
ex8 = render (vp (px 400) (px 400))
             (e div (e p (t "One" ∷ []) ∷ e p (t "Two" ∷ []) ∷ []))
             []

-- Example 9: Deep nesting
ex9 = render (vp (px 1000) (px 1000))
             (e div (e div (e div (t "Deep" ∷ []) ∷ []) ∷ []))
             (rule' div (d_w 100 ∷ d_h 100 ∷ []) ∷ [])

-- Example 10: Empty div
ex10 = render (vp (px 800) (px 600))
              (e div [])
              (rule' div (d_h 50 ∷ d_bg "green" ∷ []) ∷ [])

-- Example 11: Text only root
ex11 = render (vp (px 800) (px 600))
              (t "Just text")
              []

-- Example 12: Zero width
ex12 = render (vp (px 800) (px 600))
              (e div (t "Hidden?" ∷ []))
              (rule' div (d_w 0 ∷ []) ∷ [])

-- Example 13: Large content
ex13 = render (vp (px 200) (px 200))
              (e div (t "Very long text..." ∷ []))
              []

-- Example 14: Background color check
ex14 = render (vp (px 800) (px 600))
              (e div (t "Blue" ∷ []))
              (rule' div (d_bg "blue" ∷ []) ∷ [])

-- Example 15: Overriding rules
ex15 = render (vp (px 800) (px 600))
              (e div (t "Color?" ∷ []))
              (rule' div (d_c "red" ∷ []) ∷ rule' div (d_c "blue" ∷ []) ∷ [])

-- Example 16: Unknown tags (fallback)
ex16 = render (vp (px 800) (px 600))
              (e h2 (t "Subtitle" ∷ []))
              []

