module Util.Container.Finite where

open import Size using (Size ; ↑_)

open import Util.Prelude
open import Util.Vec using (All₂ ; tabulate)


record Container : Set₁ where
  constructor _▷_
  field
    Shape : Set
    Pos : Shape → ℕ

open Container public


⟦_⟧ : Container → Set → Set
⟦ S ▷ P ⟧ X = ∃[ s ] (Fin (P s) → X)
-- Fin (P s) → X is isomorphic to Vec X (P s). However, the latter leads to
-- termination trouble -- we'd need sized vectors, which defeats the point of
-- the exercise (or, I suppose, wfrec).


map : ∀ {ℂ A B} → (A → B) → ⟦ ℂ ⟧ A → ⟦ ℂ ⟧ B
map {S ▷ P} f (s , p) = s , f ∘ p


map-id : ∀ {ℂ A x} → map {ℂ} {A} id x ≡ x
map-id = refl


map-∘ : ∀ {ℂ A B C} (f : B → C) (g : A → B) {x : ⟦ ℂ ⟧ A}
  → map (f ∘ g) x ≡ map f (map g x)
map-∘ f g = refl


liftEq : ∀ {ℂ A} → (A → A → Set) → ⟦ ℂ ⟧ A → ⟦ ℂ ⟧ A → Set
liftEq {S ▷ P} R (sh , pos) (sh′ , pos′)
  = Σ[ eqS ∈ sh ≡ sh′ ] (∀ i → R (pos i) (pos′ (subst (Fin ∘ P) eqS i)))
-- Hardcoding propositional equality on shapes for now. May have to generalise
-- to an arbitrary relation.


data μ (ℂ : Container) : Size → Set where
  sup : ∀ {s} → ⟦ ℂ ⟧ (μ ℂ s) → μ ℂ (↑ s)
