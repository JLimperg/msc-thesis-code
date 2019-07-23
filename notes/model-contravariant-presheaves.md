# Model

Like the 'covariant presheaf' model, but with contravariant presheaves.


## Prerequisites

### Sizes

The set of sizes is

  𝕆 ≔ ℕ ⊎ {∞, ⋆}.
  
We define < on 𝕆 by

- n < m ∈ 𝕆 iff n < m ∈ ℕ
- n < ∞ < ⋆   ∀ n ∈ ℕ.

(𝕆, <) is a preorder category. We write 𝕆<n for the subcategory of 𝕆 containing
all sizes m < n.


## ⊢ Δ

⟦⊢ Δ⟧ : Cats

⟦⊢ ()⟧ ≔ ⊤  [the terminal category]

⟦⊢ Δ, n⟧ ≔
  - objects: pairs (δ ∈ ⟦Δ⟧, m ∈ 𝕆<(⟦Δ ⊢ n⟧ δ))
  - morphisms: f : (δ, m) → (δ′, m′) is a pair (f₀ : δ ≤ δ′ ∈ ⟦Δ⟧, f₁ : m ≤ m′ ∈ 𝕆)
  [rest trivial]
  
π₁ : ⟦Δ, n⟧ → ⟦Δ⟧
π₁ (δ, m) ≔ δ
π₁ (δ ≤ δ′, m ≤ m′) ≔ δ ≤ δ′

π₂ : ⟦Δ, n⟧ → 𝕆
π₂ (δ, m) ≔ m
π₂ (δ ≤ δ′, m ≤ m′) ≔ m ≤ m′


## Δ ⊢ n

⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆

⟦Δ, n ⊢ v0⟧ : Σ ⟦Δ⟧ Fₙ → 𝕆
⟦Δ, n ⊢ v0⟧ ≔ 𝕆<→𝕆 ∘ π₂

⟦Δ, n ⊢ vsuc x⟧ : Σ ⟦Δ⟧ Fₙ → 𝕆
⟦Δ, n ⊢ vsuc x⟧ ≔ ⟦Δ ⊢ x⟧ ∘ π₁
  given
    ⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆
    ⟦Δ ⊢ x⟧ : ⟦Δ⟧ → 𝕆

⟦Δ ⊢ 0⟧ : ⟦Δ⟧ → 𝕆
⟦Δ ⊢ 0⟧ ≔ Const 0

[similar for ∞ and ⋆]

⟦Δ ⊢ ↑ n⟧ : ⟦Δ⟧ → 𝕆
⟦Δ ⊢ ↑ n⟧ ≔ (+ 1) ∘ ⟦Δ ⊢ n⟧
  given
    ⟦Δ ⊢ n < ∞⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ n⟧ δ < ∞
    
    
## Δ ⊢ n < m

⟦Δ ⊢ n < m⟧ : ∀ δ ∈ ⟦Δ⟧. ⟦Δ ⊢ n⟧ δ < ⟦Δ ⊢ n⟧ δ

[trivial]


## Δ ⊢ T

⟦Δ ⊢ T⟧ : ⟦Δ⟧ᵒᵖ → Sets

⟦Δ ⊢ ℕ n⟧ δ ≔ ℕ≤(⟦n⟧ δ)
⟦Δ ⊢ ℕ n⟧ (δ ≥ δ′) : ℕ≤(⟦n⟧ δ) → ℕ≤(⟦n⟧ δ′)
⟦Δ ⊢ ℕ n⟧ (δ ≥ δ′) (m ≤ ⟦n⟧ δ) ≔ m | ⟦n⟧ δ′
  where
    m | n ≔ min m n
⟦Δ ⊢ ℕ n⟧ (id : δ ≥ δ) (m ≤ ⟦n⟧ δ) = m | ⟦n⟧ δ = m
⟦Δ ⊢ ℕ n⟧ (δ′ ≥ δ″ ∘ δ ≥ δ′) (m ≤ ⟦n⟧ δ)
  = m | ⟦n⟧ δ″ 
  = (m | ⟦n⟧ δ′) | ⟦n⟧ δ″  [since ⟦n⟧ δ′ ≥ ⟦n⟧ δ″]

⟦Δ ⊢ 𝕊 n⟧ ≔ 𝕊≥ ∘ ⟦n⟧ᵒᵖ
  where
    𝕊≥ : 𝕆ᵒᵖ → Sets
    𝕊≥ n ≔ (k ≤ n) → ℕ
    𝕊≥ (n ≥ m) (s : 𝕊≥n) (k ≤ m) ≔ s k  [k ≤ m ≤ n]
    
⟦Δ ⊢ T ⇒ U⟧ δ ≔ ∀ (σ ≤ δ) → ⟦T⟧ σ → ⟦U⟧ σ
⟦Δ ⊢ T ⇒ U⟧ (δ ≥ δ′) (f : ∀ (σ ≤ δ) → ⟦T⟧ σ → ⟦U⟧ σ) (σ ≤ δ′) (t : ⟦T⟧ σ)
  ≔ f σ t   [σ ≤ δ′ ≤ δ]
  
  [This is just the exponential of presheaves.]
  
⟦Δ ⊢ ∀ n. T⟧ δ ≔ { f : ∀ (m < ⟦n⟧ δ) → ⟦T⟧ (δ, m)
                 | f is downward-consistent }
  where
    f is downward-consistent ≔ ∀ (m m′ < ⟦n⟧ δ) → m ≤ m′ → f m = ⟦T⟧ (δ ≥ δ, m′≥m) (f m′)
⟦Δ ⊢ ∀ n. T⟧ (δ ≥ δ′) : ⟦∀ n. T⟧ δ → ⟦∀ n. T⟧ δ′
⟦Δ ⊢ ∀ n. T⟧ (δ ≥ δ′) (f : ∀ (m < ⟦n⟧ δ) → ⟦T⟧ (δ, m)) (m < ⟦n⟧ δ′) ≔ g
  where
     g ≔ λ (m < ⟦n⟧ δ′) → π₁ᵒᵖ (δ ≥ δ′) (f m)
     m < ⟦n⟧ δ′ ≤ ⟦n⟧ δ by functoriality of ⟦n⟧
     
     For downward-consistency of g, assume m, m′ < ⟦n⟧ δ′ with m ≤ m′. Then
     ⟦T⟧ (δ ≥ δ, m′≥m) (g m′)
     = ⟦T⟧ (δ ≥ δ, m′≥m) (π₁ᵒᵖ (δ ≥ δ′) (f m′))
     = π₁ᵒᵖ (δ ≥ δ′) (⟦T⟧ (δ ≥ δ, m′≥m) (f m′))   [?]
     = π₁ᵒᵖ (δ ≥ δ′) (f m)
     = g m
     
     
## Δ ⊢ Γ

⟦Δ ⊢ Γ⟧ : ⟦Δ⟧ᵒᵖ → Sets

⟦Δ ⊢ ()⟧ ≔ Const ⊤

⟦Δ ⊢ Γ, T⟧ ≔ ⟦Δ ⊢ Γ⟧ × ⟦Δ ⊢ T⟧


## Δ; Γ ⊢ t : T

⟦Δ; Γ ⊢ t : T⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ T⟧ ∈ Fun(⟦Δ⟧ᵒᵖ, Sets)

⟦Δ; Γ, T ⊢ v0 : T⟧ : ⟦Δ ⊢ Γ, T⟧ → ⟦Δ ⊢ T⟧
⟦v0⟧ ≔ π₂

⟦Δ; Γ, U ⊢ vsuc x : T⟧ : ⟦Δ ⊢ Γ, U⟧ → ⟦Δ ⊢ T⟧
⟦vsuc x⟧ ≔ ⟦Δ; Γ ⊢ x : T⟧ ∘ π₁

⟦Δ; Γ ⊢ λ T. t : T ⇒ U⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ T ⇒ U⟧
⟦λ T. t⟧ : ∀ δ → ⟦Δ ⊢ Γ⟧ δ → ⟦Δ ⊢ T ⇒ U⟧ δ
         = ∀ δ → ⟦Γ⟧ δ     → ∀ (σ ≤ δ) → ⟦T⟧ σ → ⟦U⟧ σ
⟦λ T. t⟧ δ γ σ t ≔ TODO
  
⟦Δ; Γ ⊢ zero : ∀ ⋆. ℕ v0⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ ∀ ⋆. ℕ v0⟧
⟦zero⟧ : ∀ δ → ⟦Γ⟧ δ → ⟦∀ ⋆. ℕ v0⟧ δ
       = ∀ δ → ⟦Γ⟧ δ → ∀ (m < ⋆) → ⟦ℕ v0⟧ (δ, m)
       = ∀ δ → ⟦Γ⟧ δ → ∀ (m < ⋆) → ℕ≤m
⟦zero⟧ δ γ m ≔ 0

⟦Δ; Γ ⊢ suc : ∀ ⋆. ∀ v0. ℕ v0 ⇒ ℕ v1⟧
  : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ ∀ ⋆. ∀ v0. ℕ v0 ⇒ ℕ v1⟧
⟦suc⟧ : ∀ δ → ⟦Γ⟧ δ → ⟦∀ ⋆. ∀ v0. ℕ v0 ⇒ ℕ v1⟧ δ
      = ∀ δ → ⟦Γ⟧ δ
        → ∀ (m₁ < ⋆)
        → ⟦∀ v0. ℕ v0 ⇒ ℕ v1⟧ (δ, m₁)
      = ∀ δ → ⟦Γ⟧ δ
        → ∀ (m₁ < ⋆)
        → ∀ (m₂ < m₁)
        → ⟦ℕ v0 ⇒ ℕ v1⟧ (δ, m₁, m₂)
      = ∀ δ → ⟦Γ⟧ δ
        → ∀ (m₁ < ⋆)
        → ∀ (m₂ < m₁)
        → ∀ ((σ₁, m₃, m₄) ≤ (δ, m₁, m₂))
        → ⟦ℕ v0⟧ (σ₁, m₃, m₄)
        → ⟦ℕ v1⟧ (σ₁, m₃, m₄)
      = ∀ δ → ⟦Γ⟧ δ
        → ∀ (m₁ < ⋆)
        → ∀ (m₂ < m₁)
        → ∀ ((σ₁, m₃, m₄) ≤ (δ, m₁, m₂))
        → ℕ≤m₄
        → ℕ≤m₃
⟦suc⟧ δ γ m₁ m₂ (σ₁, m₃, m₄) n ≔ n + 1
  where
    n ≤ m₄ < m₃, so n + 1 ≤ m₃

⟦fix⟧ δ : ⟦Γ⟧ δ → ⟦(∀ α<⋆. (∀ β<α. T β) → T α) → ∀ α<⋆. T α⟧ δ
        = ⟦Γ⟧ δ → ∀ (σ₁ ≤ δ)
                → ⟦∀ α<⋆. (∀ β<α. T β) → T α⟧ σ₁
                → ⟦∀ α<⋆. T α⟧ σ₁
        = ⟦Γ⟧ δ → ∀ (σ₁ ≤ δ)
                → (∀ (m < ⟦⋆⟧ σ₁)
                   → ⟦(∀ β<α. T β) → T α⟧ (σ₁, m))
                → ∀ (m < ⟦⋆⟧ σ₁)
                → ⟦T⟧ (σ₁, m)
        = ⟦Γ⟧ δ → ∀ (σ₁ ≤ δ)
                → (∀ (m < ⋆)
                   → ∀ ((σ₂, m₁) ≤ (σ₁, m))
                   → ⟦∀ β<α. T β⟧ (σ₂, m₁)
                   → ⟦T⟧ (σ₂, m₁))
                → ∀ (m < ⋆)
                → ⟦T⟧ (σ₁, m)
        = ⟦Γ⟧ δ → ∀ (σ₁ ≤ δ)
                → (∀ (m < ⋆)
                   → ∀ ((σ₂, m₁) ≤ (σ₁, m))
                   → (∀ (m₂ < m₁)
                      → ⟦T β⟧ (σ₂, m₁, m₂))
                   → ⟦T⟧ (σ₂, m₁))
                → ∀ (m < ⋆)
                → ⟦T⟧ (σ₁, m)
        = ⟦Γ⟧ δ → ∀ (σ₁ ≤ δ)
                → (∀ (m < ⋆)
                   → ∀ ((σ₂, m₁) ≤ (σ₁, m))
                   → (∀ (m₂ < m₁)
                      → ⟦T⟧ (σ₂, m₂))
                   → ⟦T⟧ (σ₂, m₁))
                → ∀ (m < ⋆)
                → ⟦T⟧ (σ₁, m)
⟦fix⟧ δ (γ : ⟦Γ⟧ δ) (σ₁ ≤ δ) (rec : ∀ m ((σ₂, m₁) ≤ (σ₁, m)) → (∀ m₂ < m₁ → ⟦T⟧ (σ₂, m₂)) → ⟦T⟧ (σ₂, m₁)) m
  ≔ rec m (σ₁, m) f
  where
    f : ∀ m₂ < m → ⟦T⟧ (σ₁, m₂)
    f m₂ ≔ ⟦fix⟧ δ γ σ₁ rec m₂
