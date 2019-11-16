{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Util.HoTT.Univalence where

open import Util.HoTT.Equiv
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁻ ; cast )


private
  variable
    α β γ : Level
    A B C : Set α


postulate
  univalence : ∀ {α} {A B : Set α} → IsEquiv (≡→≃ {A = A} {B = B})


≃→≡ : A ≃ B → A ≡ B
≃→≡ A≃B = univalence A≃B .proj₁ .proj₁


≡→≃∘≃→≡ : (p : A ≃ B) → ≡→≃ (≃→≡ p) ≡ p
≡→≃∘≃→≡ p = univalence p .proj₁ .proj₂


≃→≡∘≡→≃ : (p : A ≡ B) → ≃→≡ (≡→≃ p) ≡ p
≃→≡∘≡→≃ p = Σ-≡⁻ (univalence (≡→≃ p) .proj₂ (p , refl)) .proj₁


≃→≡-≡→≃-coh : (p : A ≡ B)
  → subst (λ q → ≡→≃ q ≡ ≡→≃ p) (≃→≡∘≡→≃ p) (≡→≃∘≃→≡ (≡→≃ p)) ≡ refl
≃→≡-≡→≃-coh p = Σ-≡⁻ (univalence (≡→≃ p) .proj₂ (p , refl)) .proj₂


≃→≡-β : ∀ (p : A ≃ B) {x}
  → cast (≃→≡ p) x ≡ p .forth x
≃→≡-β p = {!!}


≅→≡ : A ≅ B → A ≡ B
≅→≡ = ≃→≡ ∘ ≅→≃


≅→≡-β : ∀ (p : A ≅ B) {x}
  → cast (≅→≡ p) x ≡ p .forth x
≅→≡-β p = ≃→≡-β (≅→≃ p)
