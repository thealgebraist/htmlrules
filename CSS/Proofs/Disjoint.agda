module CSS.Proofs.Disjoint where

open import CSS.Rendering
open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤)

-- Definition: R1 is "above" R2 if R1 ends before or exactly where R2 starts.
StrictlyAbove : Rect → Rect → Set
StrictlyAbove (mkRect _ y1 _ h1) (mkRect _ y2 _ _) =
  (Px.n y1) + (Px.n h1) ≤ (Px.n y2)

-- Siblings in a list of boxes are pairwise disjoint
data SiblingsDisjoint : List Box → Set where
  empty : SiblingsDisjoint []
  single : ∀ b → SiblingsDisjoint (b ∷ [])
  cons : ∀ b1 b2 bs → 
         StrictlyAbove (Box.rect b1) (Box.rect b2) →
         SiblingsDisjoint (b2 ∷ bs) →
         SiblingsDisjoint (b1 ∷ b2 ∷ bs)

-- Lemma: The first box produced by layoutChildren starts at the given y
layout-starts-at-y : ∀ x y w n ns css →
  let boxes = proj₁ (layoutChildren x y w (n ∷ ns) css)
  in case boxes of λ {
       [] → ⊤ ; -- Impossible by definition
       (b ∷ _) → Rect.y (Box.rect b) ≡ y
     }
layout-starts-at-y x y w n ns css = refl

-- Main Proof: layoutChildren produces disjoint siblings
layout-produces-disjoint : 
  ∀ x y w ns css →
  SiblingsDisjoint (proj₁ (layoutChildren x y w ns css))
layout-produces-disjoint x y w [] css = empty
layout-produces-disjoint x y w (n ∷ []) css = single _
layout-produces-disjoint x y w (n1 ∷ n2 ∷ ns) css = 
  let -- Result of recursive call
      b1 = layoutNode' x y w n1 css
      h1 = Rect.h (Box.rect b1)
      y2 = px ((Px.n y) + (Px.n h1))
      
      -- Recursive call
      restResult = layoutChildren x y2 w (n2 ∷ ns) css
      restBoxes = proj₁ restResult
      
      -- We know restBoxes is not empty because (n2 :: ns) is not empty
      -- And layoutChildren on non-empty list produces non-empty list (by inspection of definition)
      -- But Agda doesn't know this automatically without help or matching.
      
      -- Let's inspect the head of restBoxes to form the 'cons' proof
      -- We know head of restBoxes has y = y2
      
      -- Induction Hypothesis
      ih = layout-produces-disjoint x y2 w (n2 ∷ ns) css

  in helper b1 restBoxes y h1 y2 ih
  where
    helper : ∀ b1 bs y h1 y2 → 
             SiblingsDisjoint bs → 
             SiblingsDisjoint (b1 ∷ bs)
    helper b1 [] y h1 y2 ih = single b1
    helper b1 (b2 ∷ bs') y h1 y2 ih = 
       cons b1 b2 bs' 
            (subst (λ v → (Px.n y) + (Px.n h1) ≤ v) 
                   (sym (cong Px.n (layout-starts-at-y x y2 w n2 ns css))) 
                   ≤-refl) 
            ih
