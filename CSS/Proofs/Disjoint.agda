module CSS.Proofs.Disjoint where

open import CSS.Rendering
open import Data.Nat
open import Data.Nat.Properties using (≤-refl; +-mono-≤; m≤m+n; +-assoc; +-comm)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤)

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- Definition: R1 is "above" R2 if R1 ends before or exactly where R2 starts.
StrictlyAbove : Rect → Rect → Set
StrictlyAbove r1 r2 = Px.n (Rect.y r1) + Px.n (Rect.h r1) ≤ Px.n (Rect.y r2)

-- Siblings in a list of boxes are pairwise disjoint
data SiblingsDisjoint : List Box → Set where
  empty : SiblingsDisjoint []
  single : ∀ b → SiblingsDisjoint (b ∷ [])
  cons : ∀ b1 b2 bs → 
         StrictlyAbove (Box.rect b1) (Box.rect b2) →
         SiblingsDisjoint (b2 ∷ bs) →
         SiblingsDisjoint (b1 ∷ b2 ∷ bs)

-- Lemma: The first box produced by layoutChildren starts at y + margin-top
layout-starts-at-y : ∀ x y w n ns css →
  let s = computeStyle n css
      m = Style.marginVal s
  in case (proj₁ (layoutChildren x y w (n ∷ ns) css)) of λ {
       [] → ⊤ ; 
       (b ∷ _) → Px.n (Rect.y (Box.rect b)) ≡ (Px.n y) + (Px.n (SideValues.top m))
     }
layout-starts-at-y x y w n ns css = refl

-- Main Proof: layoutChildren produces disjoint siblings
layout-produces-disjoint : 
  ∀ x y w ns css →
  SiblingsDisjoint (proj₁ (layoutChildren x y w ns css))
layout-produces-disjoint x y w [] css = empty
layout-produces-disjoint x y w (n ∷ []) css = single _
layout-produces-disjoint x y w (n1 ∷ n2 ∷ ns) css = 
  let b1 = layoutNode' x y w n1 css
      s1 = computeStyle n1 css
      m1 = Style.marginVal s1
      h1 = Rect.h (Box.rect b1)
      y2 = addPx y (addPx (addPx h1 (SideValues.top m1)) (SideValues.bottom m1))
      
      boxes2 = proj₁ (layoutChildren x y2 w (n2 ∷ ns) css)
      ih = layout-produces-disjoint x y2 w (n2 ∷ ns) css
  in helper b1 boxes2 y h1 m1 n2 ns ih
  where
    helper : (b1 : Box) (bs : List Box) (y : Px) (h1 : Px) (m1 : SideValues) (n2 : Node) (ns : List Node) → 
             SiblingsDisjoint bs → SiblingsDisjoint (b1 ∷ bs)
    helper b1 [] y h1 m1 n2 ns ih = single b1
    helper b1 (b2 ∷ bs') y h1 m1 n2 ns ih = 
      let s2 = computeStyle n2 css
          m2 = Style.marginVal s2
          
          y2 = addPx y (addPx (addPx h1 (SideValues.top m1)) (SideValues.bottom m1))
          
          p2 : Px.n (Rect.y (Box.rect b2)) ≡ Px.n y2 + Px.n (SideValues.top m2)
          p2 = cong Px.n (layout-starts-at-y x y2 w n2 ns css)
          
          y1n = Px.n (Rect.y (Box.rect b1))
          h1n = Px.n (Rect.h (Box.rect b1))
          y2n = Px.n (Rect.y (Box.rect b2))
          
          sa-proof : y1n + h1n ≤ y2n
          sa-proof = 
            subst (λ v → y1n + h1n ≤ v) (sym p2) 
              (subst (λ v → v ≤ Px.n y2 + Px.n (SideValues.top m2)) 
                (trans (+-assoc (Px.n y) (Px.n (SideValues.top m1)) (Px.n h1))
                  (cong (λ v → Px.n y + v) (+-comm (Px.n (SideValues.top m1)) (Px.n h1))))
                (m≤m+n (Px.n y + (Px.n h1 + Px.n (SideValues.top m1))) (Px.n (SideValues.bottom m1) + Px.n (SideValues.top m2))))

      in cons b1 b2 bs' sa-proof ih
