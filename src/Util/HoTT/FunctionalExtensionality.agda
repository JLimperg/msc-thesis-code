{-# OPTIONS --without-K #-}
module Util.HoTT.FunctionalExtensionality where

open import Axiom.Extensionality.Propositional using
  (ExtensionalityImplicit ; implicit-extensionality)

open import Util.Prelude
open import Util.HoTT.Equiv
open import Util.HoTT.Homotopy
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁻ )


private
  variable
    α β γ : Level


module _ {A : Set α} {B : A → Set β} where

  -- TODO
  postulate
    ≡→~-IsEquiv : (f g : ∀ a → B a)
      → IsEquiv (≡→~ {f = f} {g})


  funext : {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g
  funext {f = f} {g} eq = ≡→~-IsEquiv f g eq .proj₁ .proj₁


  ≡→~∘funext : ∀ {f g} (eq : ∀ a → f a ≡ g a)
    → ≡→~ (funext eq) ≡ eq
  ≡→~∘funext {f} {g} eq = ≡→~-IsEquiv f g eq .proj₁ .proj₂


  funext-unique′ : ∀ {f g} eq
    → (y : Σ-syntax (f ≡ g) (λ p → ≡→~ p ≡ eq))
    → (funext eq , ≡→~∘funext eq) ≡ y
  funext-unique′ {f} {g} eq = ≡→~-IsEquiv f g eq .proj₂


  funext-unique : ∀ {f g} eq (p : f ≡ g)
    → ≡→~ p ≡ eq
    → funext eq ≡ p
  funext-unique eq p q = proj₁ (Σ-≡⁻ (funext-unique′ eq (p , q)))


  funext∘≡→~ : ∀ {f g} (eq : f ≡ g)
    → funext (≡→~ eq) ≡ eq
  funext∘≡→~ eq = funext-unique (≡→~ eq) eq refl


funext∙ : ExtensionalityImplicit α β
funext∙ = implicit-extensionality funext


abstract
  subst-funext : ∀ {α β γ} {A : Set α} {B : A → Set β} {f g : ∀ a → B a}
    → (P : ∀ a → B a → Set γ)
    → (f≡g : ∀ x → f x ≡ g x)
    → ∀ {a} (Pf : P a (f a))
    → subst (λ f → P a (f a)) (funext f≡g) Pf ≡ subst (P a) (f≡g a) Pf
  subst-funext P f≡g {a} Pf = sym
    (trans
      (cong (λ p → subst (P a) (p a) Pf) (sym (≡→~∘funext f≡g)))
      go)
    where
      go : subst (P a) (≡→~ (funext f≡g) a) Pf
          ≡ subst (λ f → P a (f a)) (funext f≡g) Pf
      go with funext f≡g
      ... | refl = refl
