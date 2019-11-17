{-# OPTIONS --without-K #-}
module Util.HoTT.Univalence.Beta where

open import Util.HoTT.Equiv
open import Util.HoTT.Equiv.Induction
open import Util.HoTT.Univalence.Axiom
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁻ ; cast )


private
  variable
    α β γ : Level
    A B C : Set α


≃→≡-β : ≃→≡ (≃-refl {A = A}) ≡ refl
≃→≡-β = ≃→≡∘≡→≃ refl


cast-≃→≡ : ∀ (A≃B : A ≃ B) {x}
  → cast (≃→≡ A≃B) x ≡ A≃B .forth x
cast-≃→≡ A≃B {x}
  = J-≃ (λ A B A≃B → ∀ x → cast (≃→≡ A≃B) x ≡ A≃B .forth x)
      (λ A x → subst (λ p → cast p x ≡ x) (sym ≃→≡-β) refl) A≃B x


cast-≅→≡ : ∀ (A≅B : A ≅ B) {x}
  → cast (≅→≡ A≅B) x ≡ A≅B .forth x
cast-≅→≡ = cast-≃→≡ ∘ ≅→≃
