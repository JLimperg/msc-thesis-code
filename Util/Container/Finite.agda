module Util.Container.Finite where

open import Relation.Binary using (Rel)
open import Size using (Size ; ↑_)

open import Util.Prelude


record Container : Set₁ where
  constructor _▷_
  field
    Shape : Set
    Pos : Shape → ℕ

open Container public


⟦_⟧ : Container → ∀ {ℓ} → Set ℓ → Set ℓ
⟦ S ▷ P ⟧ X = ∃[ s ] (Fin (P s) → X)
-- Fin (P s) → X is isomorphic to Vec X (P s). However, the latter leads to
-- termination trouble -- we'd need sized vectors, which defeats the point of
-- the exercise (or, I suppose, wfrec).


map : ∀ {ℂ ℓ} {A B : Set ℓ} → (A → B) → ⟦ ℂ ⟧ A → ⟦ ℂ ⟧ B
map {S ▷ P} f (s , p) = s , f ∘ p


map-id : ∀ {ℂ ℓ} {A : Set ℓ} {x} → map {ℂ} {A = A} id x ≡ x
map-id = refl


map-∘ : ∀ {ℂ ℓ} {A B C : Set ℓ} (f : B → C) (g : A → B) {x : ⟦ ℂ ⟧ A}
  → map (f ∘ g) x ≡ map f (map g x)
map-∘ f g = refl


-- Hardcoding propositional equality on shapes for now.
data Eqℂ {ℂ ℓ ρ} {A : Set ℓ} (R : Rel A ρ) : Rel (⟦ ℂ ⟧ A) ρ where
  Eqℂ-intro : ∀ {sh : Shape ℂ} {pos pos′ : Fin (Pos ℂ sh) → A}
    → (∀ i → R (pos i) (pos′ i))
    → Eqℂ R (sh , pos) (sh , pos′)


data μ (ℂ : Container) : Size → Set where
  sup : ∀ {s} → ⟦ ℂ ⟧ (μ ℂ s) → μ ℂ (↑ s)
