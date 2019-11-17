{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Equiv.Core where

open import Util.Prelude
open import Util.HoTT.HLevel.Core


infix 4 _≅_ _≃_


private
  variable
    α β γ : Level
    A B C : Set α


Injective : (f : A → B) → Set _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y


record IsIso {A : Set α} {B : Set β} (forth : A → B) : Set (α ⊔ℓ β)
  where
  field
    back : B → A
    back∘forth : ∀ x → back (forth x) ≡ x
    forth∘back : ∀ x → forth (back x) ≡ x


record _≅_ (A : Set α) (B : Set β) : Set (α ⊔ℓ β) where
  field
    forth : A → B
    isIso : IsIso forth

  open IsIso isIso public

open _≅_ public


IsEquiv : {A : Set α} {B : Set β} (forth : A → B)
  → Set (α ⊔ℓ β)
IsEquiv {A = A} {B} forth
  = ∀ b → IsContr (Σ[ a ∈ A ] forth a ≡ b)


record _≃_ (A : Set α) (B : Set β) : Set (α ⊔ℓ β) where
  field
    forth : A → B
    isEquiv : IsEquiv forth

open _≃_ public
