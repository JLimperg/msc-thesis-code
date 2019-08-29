{-# OPTIONS --without-K --safe #-}
module Util.Relation.Binary.LogicalEquivalence where

open import Relation.Binary using (IsEquivalence ; Setoid)

open import Util.Prelude


private
  variable
    α β γ : Level
    A B C : Set α


infix 4 _↔_


record _↔_ (A : Set α) (B : Set β) : Set (α ⊔ℓ β) where
  field
    forth : A → B
    back : B → A

open _↔_ public


↔-refl : A ↔ A
↔-refl .forth = id
↔-refl .back = id


↔-reflexive : A ≡ B → A ↔ B
↔-reflexive refl = ↔-refl


↔-sym : A ↔ B → B ↔ A
↔-sym A↔B .forth = A↔B .back
↔-sym A↔B .back = A↔B .forth


↔-trans : A ↔ B → B ↔ C → A ↔ C
↔-trans A↔B B↔C .forth = B↔C .forth ∘ A↔B .forth
↔-trans A↔B B↔C .back = A↔B .back ∘ B↔C .back


↔-isEquivalence : IsEquivalence (_↔_ {α})
↔-isEquivalence = record
  { refl = ↔-refl
  ; sym = ↔-sym
  ; trans = ↔-trans
  }


↔-setoid : ∀ α → Setoid (lsuc α) α
↔-setoid α .Setoid.Carrier = Set α
↔-setoid α .Setoid._≈_ = _↔_
↔-setoid α .Setoid.isEquivalence = ↔-isEquivalence
