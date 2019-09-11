-- This file is ported from a part of Martin Escardó's HoTT lecture notes
-- (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html).

{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Section where

open import Util.HoTT.HLevel.Core
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁺ ; subst-subst-sym )


private
  variable
    α β γ : Level
    A B C : Set α


infix 4 _◁_


record HasSection {A : Set α} {B : Set β} (f : A → B) : Set (α ⊔ℓ β) where
  field
    section : B → A
    isSection : ∀ x → f (section x) ≡ x

open HasSection public


record _◁_ (A : Set α) (B : Set β) : Set (α ⊔ℓ β) where
  field
    retraction : B → A
    hasSection : HasSection retraction

  open HasSection hasSection public renaming (isSection to retraction∘section)

open _◁_ public


◁-refl : A ◁ A
◁-refl = record
  { retraction = id
  ; hasSection = record
    { section = id
    ; isSection = λ _ → refl
    }
  }


◁-trans : A ◁ B → B ◁ C → A ◁ C
◁-trans A◁B B◁C = record
  { retraction = A◁B .retraction ∘ B◁C .retraction
  ; hasSection = record
    { section = B◁C .section ∘ A◁B .section
    ; isSection = λ x
        → trans (cong (A◁B .retraction) (B◁C .retraction∘section _))
            (A◁B .retraction∘section _)
    }
  }


Σ-◁ : {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (∀ a → B a ◁ C a)
  → Σ A B ◁ Σ A C
Σ-◁ B◁C = record
  { retraction = λ { (a , c) → a , B◁C a .retraction c }
  ; hasSection = record
    { section = λ { (a , b) → a , B◁C a .section b }
    ; isSection = λ { (a , b) → cong (a ,_) (B◁C a .retraction∘section b) }
    }
  }


◁-pres-IsContr : A ◁ B → IsContr B → IsContr A
◁-pres-IsContr A◁B (b , canon)
  = A◁B .retraction b
  , λ a
      → trans (cong (A◁B .retraction) (canon (A◁B .section a)))
          (A◁B .retraction∘section a)


Σ-◁-reindexing : {A : Set α} {B : Set β} {P : A → Set γ}
  → (r : A ◁ B)
  → Σ A P ◁ Σ B (P ∘ r .retraction)
Σ-◁-reindexing {P = P} r = record
  { retraction = λ { (b , x) → r .retraction b , x }
  ; hasSection = record
    { section = λ where
        (a , x) → r .section a , subst P (sym (r .retraction∘section a)) x
    ; isSection = λ where
        (a , x) → Σ-≡⁺
          ( r .retraction∘section a
          , subst-subst-sym (r .retraction∘section a)
          )
    }
  }
