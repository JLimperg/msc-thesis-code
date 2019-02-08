{-# OPTIONS --without-K #-}

module Util.Relation.Binary.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

open import Function using (id)


cast : ∀ {α} {A B : Set α} → A ≡ B → A → B
cast = subst id


subst-trans : ∀ {α} {A : Set α} {ρ} {P : A → Set ρ} {x y z : A} {p : P x}
  → (x≡y : x ≡ y) (y≡z : y ≡ z)
  → subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
subst-trans refl refl = refl


subst-cong : ∀ {α} {A : Set α} {ρ} {P : A → Set ρ} (f : ∀ a → P a) {x y : A}
  → (x≡y : x ≡ y)
  → subst P x≡y (f x) ≡ f y
subst-cong _ refl = refl


sym-cancel-r : ∀ {α} {A : Set α} {x y : A} (x≡y : x ≡ y)
  → trans x≡y (sym x≡y) ≡ refl
sym-cancel-r refl = refl


sym-cancel-l : ∀ {α} {A : Set α} {x y : A} (x≡y : x ≡ y)
  → trans (sym x≡y) x≡y ≡ refl
sym-cancel-l refl = refl
