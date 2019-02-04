module Util.Container.Finite where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; ∃-syntax ; _,_)
open import Function using (id ; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Size using (Size ; ↑_)

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
  = sh ≡ sh′ × All₂ R (tabulate pos) (tabulate pos′)
-- Hardcoding propositional equality on shapes for now. May have to generalise
-- to an arbitrary relation.


data μ (ℂ : Container) : Size → Set where
  sup : ∀ {s} → ⟦ ℂ ⟧ (μ ℂ s) → μ ℂ (↑ s)
