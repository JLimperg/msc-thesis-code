{-# OPTIONS --without-K #-}
-- TODO this module can be --safe when Equiv is.
open import Util.HoTT.Equiv

module Util.HoTT.Univalence.Consequences
  (univalence : ∀ {α} {A B : Set α} → IsEquiv (≡→≃ {A = A} {B = B}))
  where

open import Axiom.Extensionality.Propositional using
  (ExtensionalityImplicit ; implicit-extensionality)

open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁻ ; happly)


private
  variable
    α β γ : Level
    A B C : Set α


≃→≡ : A ≃ B → A ≡ B
≃→≡ A≃B = univalence A≃B .proj₁ .proj₁


≡→≃∘≃→≡ : (p : A ≃ B) → ≡→≃ (≃→≡ p) ≡ p
≡→≃∘≃→≡ p = univalence p .proj₁ .proj₂


-- what does this actually mean?
≃→≡∘≡→≃ : {A B : Set α} (p : A ≃ B)
  → (q : A ≡ B) (r : ≡→≃ q ≡ p)
  → Σ[ s ∈ ≃→≡ p ≡ q ] (subst (λ a → ≡→≃ a ≡ p) s (≡→≃∘≃→≡ p) ≡ r)
≃→≡∘≡→≃ p q r = Σ-≡⁻ (univalence p .proj₂ (q , r))


≅→≡ : A ≅ B → A ≡ B
≅→≡ = ≃→≡ ∘ ≅→≃


module _ {A : Set α} {B : A → Set β} where

  -- TODO
  postulate
    happly-IsEquiv : (f g : ∀ a → B a)
      → IsEquiv (happly {f = f} {g})


  funext : {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
  funext {f = f} {g} eq = happly-IsEquiv f g eq .proj₁ .proj₁


  happly∘funext : ∀ {f g} eq
    → happly (funext eq) ≡ eq
  happly∘funext {f} {g} eq = happly-IsEquiv f g eq .proj₁ .proj₂


  funext-unique′ : ∀ {f g} eq
    → (y : Σ-syntax (f ≡ g) (λ p → happly p ≡ eq))
    → (funext eq , happly∘funext eq) ≡ y
  funext-unique′ {f} {g} eq = happly-IsEquiv f g eq .proj₂


  funext-unique : ∀ {f g} eq (p : f ≡ g)
    → happly p ≡ eq
    → funext eq ≡ p
  funext-unique eq p q = proj₁ (Σ-≡⁻ (funext-unique′ eq (p , q)))


  funext∘happly : ∀ {f g} (eq : f ≡ g)
    → funext (happly eq) ≡ eq
  funext∘happly eq = funext-unique (happly eq) eq refl


funext∙ : ExtensionalityImplicit α β
funext∙ = implicit-extensionality funext


