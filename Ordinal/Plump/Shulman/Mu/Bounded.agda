module Ordinal.Plump.Shulman.Mu.Bounded where

open import Ordinal.Plump.Shulman
open import Util.Container.Finite
open import Util.Prelude


data W (ℂ : Container) : Set where
  sup : ⟦ ℂ ⟧ (W ℂ) → W ℂ


W-height : ∀ {ℂ} → W ℂ → Ord lzero
W-height {S ▷ P} (sup (sh , pos)) = limSuc (Fin (P sh)) (W-height ∘ pos)


Mu : Container → Ord lzero → Set
Mu ℂ α = Σ[ w ∈ W ℂ ] W-height w ≤ α


_≈_ : ∀ {ℂ α β} → Mu ℂ α → Mu ℂ β → Set
x ≈ y = proj₁ x ≡ proj₁ y


≈-refl : ∀ {ℂ α} {x : Mu ℂ α} → x ≈ x
≈-refl = refl


≈-sym : ∀ {ℂ α β} {x : Mu ℂ α} {y : Mu ℂ β} → x ≈ y → y ≈ x
≈-sym = sym


≈-trans : ∀ {ℂ α β γ} {x : Mu ℂ α} {y : Mu ℂ β} {z : Mu ℂ γ}
  → x ≈ y → y ≈ z → x ≈ z
≈-trans = trans
