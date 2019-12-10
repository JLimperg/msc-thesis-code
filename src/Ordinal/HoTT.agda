-- Ordinals as defined in the HoTT book.

{-# OPTIONS --without-K --safe #-}
module Ordinal.HoTT where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc ; acc ; WellFounded)
open import Level using (Level ; _⊔_ ; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary using (Rel ; IsEquivalence ; Transitive)


private
  variable
    α β γ ρ ε : Level
    A B C : Set α


record _↔_ (A : Set α) (B : Set β) : Set (α ⊔ β) where
  field
    forth : A → B
    back : B → A

open _↔_ public


IsExtensional : ∀ {α} {A : Set α} (_≈_ : Rel A ε) (_<_ : Rel A ρ) → Set (α ⊔ ε ⊔ ρ)
IsExtensional _≈_ _<_ = ∀ {a b} → (∀ c → (c < a) ↔ (c < b)) → a ≈ b


record IsOrdinal (A : Set α) ε ρ : Set (α ⊔ lsuc (ε ⊔ ρ)) where
  field
    _≈_ : Rel A ε
    ≈-equiv : IsEquivalence _≈_
    _<_ : Rel A ρ
    <-wf : WellFounded _<_
    <-ext : IsExtensional _≈_ _<_
    <-trans : Transitive _<_

  open IsEquivalence ≈-equiv public using () renaming
    ( refl to ≈-refl
    ; sym to ≈-sym
    ; trans to ≈-trans)

open IsOrdinal public


record Ordinal α ε ρ : Set (lsuc (α ⊔ ε ⊔ ρ)) where
  field
    _↓ : Set α
    isOrdinal : IsOrdinal _↓ ε ρ

open Ordinal public


zero : Ordinal 0ℓ 0ℓ 0ℓ
zero = record
  { _↓ = ⊤
  ; isOrdinal = record
    { _≈_ = λ _ _ → ⊤
    ; ≈-equiv = _
    ; _<_ = λ _ _ → ⊥
    ; <-wf = λ _ → acc λ y ()
    ; <-ext = _
    ; <-trans = λ()
    }
  }
