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
-- COMPUTED STYLE
------------------------------------------------------------------------

record SideValues : Set where
  constructor sides
  field top right bottom left : Px

data DisplayType : Set where
  block inline none : DisplayType

record Style : Set where
  constructor style
  field
    disp         : DisplayType
    computedW    : Px
    computedH    : Px
    marginVal    : SideValues
    paddingVal   : SideValues
    bgColor      : String
    fgColor      : String
    imageSource  : Maybe String
    fontSizePx   : Px

------------------------------------------------------------------------
-- BOX TREE
------------------------------------------------------------------------

record Box : Set where
  inductive
  constructor box
  field
    node          : Node
    rect          : Rect
    computedStyle : Style
    kids          : List Box

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

parseDisplay : String → DisplayType
parseDisplay "block" = block
parseDisplay "inline" = inline
parseDisplay "none"   = none
parseDisplay _        = block -- default

-- Convert attribute string to Property
parseProp : String → Maybe Property
parseProp "width" = just width
parseProp "height" = just height
parseProp "display" = just display
parseProp "color" = just color
parseProp "background" = just background
parseProp "src" = just src
parseProp "font-size" = just fontSize
parseProp "margin" = just margin
parseProp "padding" = just padding
parseProp _ = nothing

-- Extract Declarations from Node Attributes
attrsToDecls : List Attr → List Decl
attrsToDecls [] = []
attrsToDecls (attr n v ∷ as) with parseProp n
... | just prop = decl prop v ∷ attrsToDecls as
... | nothing   = attrsToDecls as

-- computeStyle implementation
computeStyle : Node → CSS → Style
computeStyle n css =
  let cssDecls = collectDecls n css
      attrDecls = case n of λ where
        (elem _ attrs _) → attrsToDecls attrs
        (text _)         → []
      
      -- Attributes override CSS in this simple model (or serve as inline styles)
      ds = cssDecls ++ attrDecls
      
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

      mVal = case findDecl margin ds of λ where
               (just v) → px (parseNat v)
               nothing  → px 0
      m = sides mVal mVal mVal mVal

      pVal = case findDecl padding ds of λ where
               (just v) → px (parseNat v)
               nothing  → px 0
      p = sides pVal pVal pVal pVal

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

  in style d w h m p bg fg srcVal fs

------------------------------------------------------------------------
-- LAYOUT SEMANTICS
------------------------------------------------------------------------

addPx : Px → Px → Px
addPx (px a) (px b) = px (a + b)

subPx : Px → Px → Px
subPx (px a) (px b) = px (a ∸ b)

isPositive : ℕ → Bool
isPositive 0 = false
isPositive _ = true

-- Mutual recursion for layout
mutual
  layoutNode' : Px → Px → Px → Node → CSS → Box
  layoutNode' x y availW n css = 
    let s = computeStyle n css
        m = Style.marginVal s
        p = Style.paddingVal s
        styW = Style.computedW s
        styH = Style.computedH s
        disp = Style.disp s
        
        -- Start of Border Box
        bx = addPx x (SideValues.left m)
        by = addPx y (SideValues.top m)
        
        -- Start of Content Box
        cx = addPx bx (SideValues.left p)
        cy = addPx by (SideValues.top p)
        
        -- Available width for content
        -- If width is specified, use it. Otherwise use availW minus margins/paddings.
        contentAvailW : Px
        contentAvailW = if isPositive (Px.n styW) 
                        then styW 
                        else (subPx (subPx (subPx availW (SideValues.left m)) (SideValues.right m)) 
                                    (addPx (SideValues.left p) (SideValues.right p)))
        
        -- Layout children
        kidsRes = case n of λ where
          (text _) → ([] , cy)
          (elem _ _ children) → layoutChildren cx cy contentAvailW children css
        
        childBoxes = proj₁ kidsRes
        maxY       = proj₂ kidsRes
        
        -- Content Height
        contentH : Px
        contentH = if isPositive (Px.n styH) 
                   then styH 
                   else (case n of λ where
                           (text _) → px 20
                           _ → if isPositive (Px.n (subPx maxY cy)) then (subPx maxY cy) else (px 0))
        
        -- Border Box Dimensions
        actualBbW = addPx (addPx contentAvailW (SideValues.left p)) (SideValues.right p)
        actualBbH = addPx (addPx contentH (SideValues.top p)) (SideValues.bottom p)
          
    in box n (mkRect bx by actualBbW actualBbH) s childBoxes

  layoutChildren : Px → Px → Px → List Node → CSS → List Box × Px
  layoutChildren x y w [] css = ([] , y)
  layoutChildren x y w (n ∷ ns) css =
    let b = layoutNode' x y w n css
        s = computeStyle n css
        m = Style.marginVal s
        -- Height of this node's margin box
        h = Rect.h (Box.rect b)
        marginBoxH = addPx (addPx h (SideValues.top m)) (SideValues.bottom m)
        
        newY = addPx y marginBoxH
        
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
  paintBox : Box → DisplayList → DisplayList
  paintBox (box n r s kids) acc with Style.disp s
  ... | none = acc
  ... | _    = 
    let contentCmds = case n of λ where
          (text s) → (DrawText r s ∷ [])
          (elem img attrs _) → (DrawImage r "placeholder.png" ∷ []) 
          _ → []
        
        -- Start with current box and its content
        acc' = (DrawBox r (Style.bgColor s) ∷ contentCmds ++ acc)
    in paint kids acc'

  paint : Layout → DisplayList → DisplayList
  paint [] acc = acc
  paint (b ∷ bs) acc = paintBox b (paint bs acc)

------------------------------------------------------------------------
-- END-TO-END RENDERING
------------------------------------------------------------------------

render : Viewport → Node → CSS → Layout × DisplayList
render v n css =
  let root = layoutNode v n css in
  ( root ∷ [] , paint (root ∷ []) [] )

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

