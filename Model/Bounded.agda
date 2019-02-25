module Model.Bounded where

open import Axioms using (funext)
open import Ordinal.Plump.Shulman
open import Ordinal.Plump.Shulman.Mu.Bounded
open import Util.Container.Finite
open import Util.Prelude


μ→W : ∀ {ℂ s} → μ ℂ s → W ℂ
μ→W (sup (sh , pos)) = sup (sh , μ→W ∘ pos)


-- Can we generalise the size?
W→μ : ∀ {ℂ} → W ℂ → μ ℂ ∞
W→μ (sup (sh , pos)) = sup (sh , W→μ ∘ pos)


μ→W→μ : ∀ {ℂ} {x : μ ℂ ∞} → W→μ (μ→W x) ≡ x
μ→W→μ {x = sup (sh , pos)} = cong (sup ∘ (sh ,_)) (funext λ _ → μ→W→μ)


W→μ→W : ∀ {ℂ} {x : W ℂ} → μ→W (W→μ x) ≡ x
W→μ→W {x = sup (sh , pos)} = cong (sup ∘ (sh ,_)) (funext λ _ → W→μ→W)


μ-height : ∀ {ℂ s} → μ ℂ s → Ord lzero
μ-height = W-height ∘ μ→W


μ→Mu : ∀ {ℂ s} (x : μ ℂ s) → Mu ℂ (μ-height x)
μ→Mu x = μ→W x , ≤-refl


Mu→μ : ∀ {ℂ α} → Mu ℂ α → μ ℂ ∞
Mu→μ x = W→μ (proj₁ x)


μ→Mu→μ : ∀ {ℂ} {x : μ ℂ ∞} → Mu→μ (μ→Mu x) ≡ x
μ→Mu→μ = μ→W→μ


Mu→μ→Mu : ∀ {ℂ α} {x : Mu ℂ α} → μ→Mu (Mu→μ x) ≈ x
Mu→μ→Mu = W→μ→W
