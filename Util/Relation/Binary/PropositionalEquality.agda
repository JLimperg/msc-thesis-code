module Util.Relation.Binary.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

open import Data.Product using (Σ ; proj₁ ; proj₂)
open import Function using (id)


cast : ∀ {α} {A B : Set α} → A ≡ B → A → B
cast refl x = x


cast-refl : ∀ {α} {A B : Set α} {x : A} → cast refl x ≡ x
cast-refl = refl


cast-trans : ∀ {α} {A B C : Set α}
  → (B≡C : B ≡ C) (A≡B : A ≡ B) {x : A}
  → cast B≡C (cast A≡B x) ≡ cast (trans A≡B B≡C) x
cast-trans refl refl = refl


cast-K : ∀ {α} {A : Set α} (A≡A : A ≡ A) {x : A} → cast A≡A x ≡ x
cast-K refl = refl


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


Σ-≡⁺ : ∀ {α β} {A : Set α} {B : A → Set β} {x y : Σ A B}
  → (eq₁ : proj₁ x ≡ proj₁ y)
  → cast (cong _ eq₁) (proj₂ x) ≡ proj₂ y
  → x ≡ y
Σ-≡⁺ refl refl = refl
