{-# OPTIONS --without-K #-}
module Util.HoTT.Univalence.Axiom where

open import Util.HoTT.Equiv
open import Util.HoTT.Univalence.Statement
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁻)


private
  variable
    α β γ : Level
    A B C : Set α


postulate
  univalence : ∀ {α} → Univalence α


≃→≡ : A ≃ B → A ≡ B
≃→≡ A≃B = univalence A≃B .proj₁ .proj₁


≡→≃∘≃→≡ : (p : A ≃ B) → ≡→≃ (≃→≡ p) ≡ p
≡→≃∘≃→≡ p = univalence p .proj₁ .proj₂


≃→≡∘≡→≃ : (p : A ≡ B) → ≃→≡ (≡→≃ p) ≡ p
≃→≡∘≡→≃ p = Σ-≡⁻ (univalence (≡→≃ p) .proj₂ (p , refl)) .proj₁


≃→≡-≡→≃-coh : (p : A ≡ B)
  → subst (λ q → ≡→≃ q ≡ ≡→≃ p) (≃→≡∘≡→≃ p) (≡→≃∘≃→≡ (≡→≃ p)) ≡ refl
≃→≡-≡→≃-coh p = Σ-≡⁻ (univalence (≡→≃ p) .proj₂ (p , refl)) .proj₂


≅→≡ : A ≅ B → A ≡ B
≅→≡ = ≃→≡ ∘ ≅→≃
