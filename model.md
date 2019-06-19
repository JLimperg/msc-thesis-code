# Model

## Preliminaries

### Grothendieck

#### Definition

Let ℂ a category; F : ℂ → Cats. The Grothendieck category Σ ℂ F has

- objects: pairs (x₀, x₁) with x₀ ∈ ℂ; x₁ ∈ F x₁
- morphisms between (x₀, x₁) and (y₀,y₁): pairs (f₀,f₁) with
  * f₀ : x₀ → y₀
  * f₁ : F f₀ x₁ → y₁   [F f₀ : F x₀ → F y₀ ∈ Cats]
- identity: (id : x₀ → x₀, id : F id x₁ → x₁) : (x₀, x₁) → (x₀, x₁)
- composition: Let
  * (f₀, f₁) : (y₀, y₁) → (z₀, z₁)
  * (g₀, g₁) : (x₀, x₁) → (y₀, y₁)
  We have
  * g₀ : x₀ → y₀        ∈ ℂ
  * g₁ : F g₀ x₁ → y₁   ∈ F y₀
  * f₀ : y₀ → z₀        ∈ ℂ
  * f₁ : F f₀ y₁ → z₁   ∈ F z₀
  The composition is (h₀, h₁) with
  * h₀ : x₀ → z₀        ∈ ℂ
    h₀ ≔ f₀ ∘ g₀
  * h₁ : F h₀ x₁ → z₁   ∈ F z₀
       = F (f₀ ∘ g₀) x₁ → z₁
       = F f₀ (F g₀ x₁) → z₁
  * h₁ ≔ f₁              ∘ F f₀ g₁
         : F f₀ y₁ → z₁    : F f₀ (F g₀ x₁) → F f₀ y₁
- left identity: Let (f₀, f₁) : (x₀, x₁) → (y₀, y₁).
  (id, id) ∘ (f₀, f₁)
  = (id ∘ f₀, id ∘ F id f₁)
  = (f₀, f₁)
- right identity: similar.
- associativity:
  Let (f₀, f₁), (g₀, g₁), (h₀, h₁) compatible.
  * ((f₀, f₁) ∘ (g₀, g₁)) ∘ (h₀, h₁)
    = (f₀ ∘ g₀, f₁ ∘ F f₀ g₁) ∘ (h₀, h₁)
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ g₁ ∘ F (f₀ ∘ g₀) g₁)
  * (f₀, f₁) ∘ ((g₀, g₁) ∘ (h₀, h₁))
    = (f₀, f₁) ∘ (g₀ ∘ h₀, g₁ ∘ F g₀ h₁)
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ (g₁ ∘ F g₀ h₁))
    = (f₀ ∘ g₀ ∘ h₀, f₁ ∘ F f₀ g₁ ∘ F (f₀ ∘ g₀) h₁)

#### Projections

π₀ : Σ C F → C   ∈ Cats
π₀ (x₀, x₁) ≔ x₀
π₀ (f₀, f₁) : π₀ (x₀, x₁) → π₀ (y₀, y₁)
π₀ (f₀, f₁) ≔ f₀


π₁ : (x ∈ Σ C F) → F (π₀ x)   ∈ Sets
π₁ (x₀ , x₁) ≔ x₁

[Is there a notion of 'dependent functor'?]

#### Mapping in the first component

Let F : 𝔻 → Cats.

first (G : ℂ → 𝔻) : Σ ℂ (F ∘ G) → Σ 𝔻 F
first G (x₀ ∈ ℂ, x₁ ∈ F (G x₀)) ≔ (G x₀ ∈ 𝔻, x₁ ∈ F (G x₀)
first G (f₀ : x₀ → y₀ ∈ ℂ, f₁ : (F (G f₀)) x₁ → y₁ ∈ F (G y₀))
  : first G (x₀, x₁) → first G (y₀, y₁)
  = (G x₀, x₁) → (G y₀, y₁)
  ≔ (G f₀ : G x₀ → G y₀, f₁ : F (G f₀) x₁ → y₁)


### 𝕆≤

𝕆≤ : 𝕆 → Cats
𝕆≤ k ≔ {l : 𝕆 | l ≤ k}
𝕆≤ (f : n ≤ m) : 𝕆≤ n → 𝕆≤ m
𝕆≤ f k ≔ k                      [k ≤ n ≤ m]


### 𝕆<

similar


### ≲ : Rel 𝕆≤ω

n ≲ m ≔ m < ∞ → n < m


### 𝕆≲

𝕆≲ : 𝕆 → Cats
𝕆≲ k ≔ {l : 𝕆 | l ≲ k}
𝕆≲ (f : n ≤ m) : 𝕆≲ n → 𝕆≲ m
𝕆≲ f k ≔ k                      [k ≲ n ≤ m ; ≲ ⊂ ≤]


## Sizes

### ⟦Δ⟧

⟦Δ⟧ : Category

⟦[]⟧ ≔ ⊤
⟦Δ ∷ n⟧ ≔ Σ ⟦Δ⟧ Fₙ

Fₙ : ⟦Δ⟧ → Cats  ∈ Cats
Fₙ ≔ 𝕆≲ ∘ 𝕆≲ω⊆𝕆 ∘ ⟦Δ ⊢ n⟧

Fₙ δ = 𝕆≲(⟦Δ ⊢ n⟧ δ)
Fₙ (f : δ ≤ δ′) : Fₙ δ → Fₙ δ′
Fₙ f = 𝕆≲ (⟦Δ ⊢ n⟧ f)
Fₙ f n = (𝕆≲ (𝕆≲ω⊆𝕆 (⟦Δ ⊢ n⟧ f))) n = n

[𝕆≲ω⊆𝕆 is the inclusion from 𝕆≲ω to 𝕆.]


π₀ : ⟦Δ ∷ n⟧ → ⟦Δ⟧  ‌∈ Cats
[see above]

π₁ : ⟦Δ ∷ n⟧ → 𝕆≤ω  ∈ Cats
π₁ (δ ∈ ⟦Δ⟧, n ∈ (𝕆≲(⟦Δ ⊢ n⟧ δ))) ≔ n  [⟦Δ ⊢ n⟧ δ ∈ 𝕆≤ω]
π₁ (f₀ : δ ≤ δ′, f₁ : Fₙ f₀ n ≤ n′) : n ≤ n′
- n  ∈ 𝕆≤(⟦Δ ⊢ n⟧ δ)
- n′ ∈ 𝕆≤(⟦Δ ⊢ n⟧ δ′)
- Fₙ f₀ n = n


### ⟦Δ ⊢ i⟧

⟦Δ ⊢ i⟧ : ⟦Δ⟧ → 𝕆≤ω

⟦α⟧ ≔ πα
⟦suc i⟧ ≔ (+ 1) ∘ ⟦i⟧

[πα is the α-th projection (counting from 0 and from the right).]


### ⟦Δ ⊢ n⟧

⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆≤ω

⟦i⟧ ≔ ⟦i⟧                   [inclusion]
⟦∞⟧ ≔ Const ω

[Const is the constant functor.]


## Renamings

### ⟦Δ ⊇ Δ′⟧

⟦Δ ⊇ Δ′⟧ : ⟦Δ⟧ → ⟦Δ′⟧

⟦[] : [] ⊇ []⟧ : ⊤ → ⊤
⟦[]⟧ ≔ id

⟦weak : Δ ⊇ Δ′ → Δ ∷ n ⊇ Δ′⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ n⟧ → ⟦Δ′⟧)
⟦weak⟧ F ≔ F ∘ π₁

⟦lift : (θ : Δ ⊇ Δ′) → Δ ∷ m[θ] ⊇ Δ′ ∷ m⟧ : (⟦Δ⟧ → ⟦Δ′⟧) → (⟦Δ ∷ m[θ]⟧ → ⟦Δ′ ∷ m⟧)
⟦lift⟧ F ≔ first F

wk : Δ ∷ n ⊇ Δ
wk ≔ weak id
⟦wk⟧ = π₁


### ⟦n[θ]⟧

Assume θ : Δ ⊇ Δ′; Δ′ ⊢ n.

⟦Δ ⊢ n[θ]⟧ : ⟦Δ⟧ → 𝕆≤ω
⟦Δ ⊢ n[θ]⟧ ≔ ⟦Δ′ ⊢ n⟧ ∘ ⟦θ⟧


## Substitutions

### ⟦SS Δ Δ′⟧

⟦SS Δ Δ′⟧ : ⟦Δ⟧ → ⟦Δ′⟧

⟦[] : SS Δ []⟧ : ⟦Δ⟧ → ⊤
⟦[]⟧ ≔ !

⟦σ ∷[n] n≲m⟧ : ⟦Δ⟧ → ⟦Δ′ ∷ m⟧
             = ⟦Δ⟧ → Σ ⟦Δ′⟧ Fₘ
⟦σ ∷[n] n≲m⟧ δ ≔ (⟦σ⟧ δ, ⟦n⟧ δ ∈ 𝕆≲(⟦m⟧ (⟦σ⟧ δ)))
  where
    ⟦σ⟧ : ⟦Δ⟧ → ⟦Δ′⟧
    ⟦n⟧ : ⟦Δ⟧ → 𝕆≤ω
    ⟦n≲m : n ≲ m[σ]⟧ : ∀(δ ∈ Δ) → ⟦n⟧ δ ≲ (⟦m⟧ ∘ ⟦σ⟧) δ

⟦idS : SS Δ Δ⟧ : ⟦Δ⟧ → ⟦Δ⟧
⟦idS⟧ = id

⟦0 ≔ n : Δ → Δ ∷ m⟧ : ⟦Δ⟧ → ⟦Δ ∷ m⟧    [n ≲ m]
⟦0 ≔ n⟧ δ = ⟦idS ∷[n] n≲m⟧ δ = (δ, ⟦n⟧ δ)


### ⟦n[σ]⟧

Assume σ : SS Δ Δ′; Δ′ ⊢ n.

⟦Δ ⊢ n[σ]⟧ : ⟦Δ⟧ → 𝕆≤ω
⟦Δ ⊢ n[σ]⟧ ≔ ⟦Δ′ ⊢ n⟧ ∘ ⟦σ⟧


## Relations on Sizes

### ⟦Δ ⊢ Bound α i⟧

⟦Δ ⊢ Bound α i⟧ : ⟦Δ ⊢ α⟧ ≲ ⟦Δ ⊢ i⟧

⟦zero : Δ ∷ i ⊢ Bound 0 i[wk]⟧:
  ⟦Δ ∷ i⟧ = Σ ⟦Δ⟧ ⟦Δ ⊢ i⟧

  ⟦Δ ∷ i ⊢ 0⟧ (x , y)
    = (incl ∘ π₀) (x , y)
    = incl y
    ≲ ⟦Δ ⊢ i⟧ x                [y ∈ 𝕆≲(⟦Δ ⊢ i⟧ x)]
    = (⟦Δ ⊢ i⟧ ∘ π₁) (x , y)
    = ⟦Δ ∷ i ⊢ i[wk]⟧ (x , y)


⟦suc : Bound α i → Bound (α + 1) i[wk]⟧:
  TODO


### ⟦Δ ⊢ n ≲ m⟧

⟦Δ ⊢ n ≲ m⟧ : ⟦Δ ⊢ n⟧ ≲ ⟦Δ ⊢ m⟧

TODO


## Types

### ⟦Δ ⊢ T⟧

⟦Δ ⊢ T⟧ : ⟦Δ⟧ → Sets

⟦Δ ⊢ ℕ n⟧ ≔ ℕ≤ ∘ ⟦Δ ⊢ n⟧

⟦Δ ⊢ T ⇒ U⟧ : ⟦Δ⟧ → Sets
⟦Δ ⊢ T ⇒ U⟧ δ ≔ ∀ (σ ≥ δ) → ⟦Δ ⊢ T⟧ σ → ⟦Δ ⊢ U⟧ σ
⟦Δ ⊢ T ⇒ U⟧ (δ ≤ δ′) : ⟦T ⇒ U⟧ δ → ⟦T ⇒ U⟧ δ′
⟦Δ ⊢ T ⇒ U⟧ (δ ≤ δ′) (f : (σ ≥ δ) → ⟦Δ ⊢ T⟧ σ → ⟦Δ ⊢ U⟧ σ) ≔
  λ (σ ≥ δ′ ≥ δ) (x : ⟦T⟧ σ). f σ x

⟦Δ ⊢ ∀ n. T⟧ : ⟦Δ⟧ → Sets
⟦Δ ⊢ ∀ n. T⟧ δ ≔ ∀ (σ ≥ δ) (m ∈ Fₙ σ) → ⟦Δ ∷ n ⊢ T⟧ (σ, m)
⟦Δ ⊢ ∀ n. T⟧ (δ ≤ δ′) : ⟦Δ ⊢ ∀ n. T⟧ δ → ⟦Δ ⊢ ∀ n. T⟧ δ′
⟦Δ ⊢ ∀ n. T⟧ (δ ≤ δ′) (f : ∀ (σ ≥ δ) (m ∈ Fₙ σ) → ⟦T⟧ (σ, m)) ≔
  λ (σ ≥ δ′ ≥ δ) (m ∈ Fₙ σ). f σ m
  where
    ⟦Δ ⊢ n⟧ : ⟦Δ⟧ → 𝕆≤ω
    ⟦Δ ∷ n ⊢ T⟧ : ⟦Δ ∷ n⟧ → Sets


### ⟦Δ ⊢ T[θ]⟧

Let θ : Δ ⊇ Δ′; Δ′ ⊢ T.

⟦Δ ⊢ T[θ]⟧ : ⟦Δ⟧ → Sets
⟦Δ ⊢ T[θ]⟧ ≔ ⟦Δ′ ⊢ T⟧ ∘ ⟦θ⟧


### ⟦Δ ⊢ Γ⟧

⟦Δ ⊢ Γ⟧ : ⟦Δ⟧ → Sets

⟦Δ ⊢ ()⟧ ≔ ⊤
⟦Δ ⊢ Γ ∷ T⟧ ≔ ⟦Δ ⊢ Γ⟧ × ⟦Δ ⊢ T⟧


### ⟦Δ ⊢ Γ[θ]⟧

Let θ : Δ ⊇ Δ′; Δ′ ⊢ Γ.

⟦Δ ⊢ Γ[θ]⟧ : ⟦Δ⟧ → Sets
⟦Δ ⊢ Γ[θ]⟧ ≔ ⟦Δ′ ⊢ Γ⟧ ∘ ⟦θ⟧


## Terms

### ⟦Δ; Γ ⊢ t : T⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ T⟧


⟦Δ; Γ ∷ T ⊢ 0 : T⟧ : ⟦Δ ⊢ Γ ∷ T⟧ → ⟦Δ ⊢ T⟧
⟦Δ; Γ ∷ T ⊢ 0 : T⟧ ≔ π₁
  where
    ⟦Δ ⊢ Γ ∷ T⟧ = ⟦Δ ⊢ Γ⟧ × ⟦Δ ⊢ T⟧

⟦Δ; Γ ∷ T ⊢ x + 1 : T⟧ : ⟦Δ ⊢ Γ ∷ T⟧ → ⟦Δ ⊢ T⟧
  TODO

⟦Δ; Γ ⊢ λ T. t⟧ : ⟦Γ⟧ → ⟦T ⇒ U⟧
⟦λ T. t⟧ δ : ⟦Γ⟧ δ → ⟦T ⇒ U⟧ δ
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) → ⟦T⟧ σ → ⟦U⟧ σ
⟦λ T. t⟧ δ γ σ x ≔ ⟦t⟧ σ (⟦Γ⟧ (δ ≤ σ) γ, x)
  where
    ⟦t⟧ δ : ⟦Γ ∷ T⟧ δ → ⟦U⟧ δ
          = ⟦Γ⟧ δ × ⟦T⟧ δ → ⟦U⟧ δ

⟦Δ; Γ ⊢ t u : U⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ U⟧
⟦t u⟧ δ : ⟦Γ⟧ δ → U ⟦δ⟧
⟦t u⟧ δ γ ≔ ⟦t⟧ δ γ δ (⟦u⟧ δ γ)
  where
    ⟦t⟧ δ : ⟦Γ⟧ δ → ⟦T ⇒ U⟧ δ
          = ⟦Γ⟧ δ → ∀ (σ ≥ δ) → ⟦T⟧ σ → ⟦U⟧ σ
    ⟦u⟧ δ : ⟦Γ⟧ δ → ⟦T⟧ δ

⟦Δ; Γ ⊢ cast t : U⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ U⟧
  TODO

⟦Δ; Γ ⊢ λ n. t : ∀ n. T⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ ∀ n. T⟧
⟦λ n. t⟧ δ : ⟦Γ⟧ δ → ⟦∀ n. T⟧ δ
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ Fₙ σ) → ⟦T⟧ (σ, m)
⟦λ n. t⟧ δ γ σ m ≔ ⟦t⟧ (σ, m) (⟦Γ⟧ (δ ≤ σ) γ)
  where
    ⟦Δ ∷ n; Γ[wk] ⊢ t : T⟧ : ⟦Δ ∷ n ⊢ Γ[wk]⟧ → ⟦Δ ∷ n ⊢ T⟧
                           = (⟦Δ ⊢ Γ⟧ ∘ ⟦wk⟧) → ⟦Δ ∷ n ⊢ T⟧
    ⟦t⟧ (δ, n) : ⟦Γ⟧ δ → ⟦T⟧ (δ, n)

⟦Δ; Γ ⊢ t m : T[0 ≔ m]⟧ : ⟦Δ ⊢ Γ⟧ → ⟦Δ ⊢ T[0 ≔ m]⟧
⟦t m⟧ δ : ⟦Γ⟧ δ → ⟦T[0 ≔ m]⟧ δ
        = ⟦Γ⟧ δ → ⟦T⟧ (δ, ⟦m⟧ δ)
⟦t m⟧ δ γ ≔ ⟦t⟧ δ γ δ (⟦m⟧ δ)
  where
    ⟦m ≲ n⟧ δ : ⟦m⟧ δ ≲ ⟦n⟧ δ
    ⟦t⟧ δ : ⟦Γ⟧ δ → ⟦∀ n. T⟧ δ
          = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≲(⟦n⟧ σ)) → ⟦T⟧ (σ, m)

⟦Δ; Γ ⊢ 0 : ∀∞. ℕ 0⟧ : ⟦Γ⟧ → ⟦∀ ∞. ℕ 0⟧
⟦0⟧ δ : ⟦Γ⟧ δ → ⟦∀ ∞. ℕ 0⟧ δ
      = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F‌∞ σ) → ⟦ℕ 0⟧ (σ, m)
      = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F‌∞ σ) → ℕ≤(⟦0⟧ (σ, m))
      = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F‌∞ σ) → ℕ≤m
⟦0⟧ δ γ σ m ≔ 0

⟦Δ; Γ ⊢ suc : ∀ ∞. ∀ 0. ℕ 0 ⇒ ℕ 1⟧ : ⟦Γ⟧ → ⟦∀ ∞. ∀ 0. ℕ 0 ⇒ ℕ 1⟧
⟦suc⟧ δ : ⟦Γ⟧ δ → ⟦∀ ∞. ∀ 0. ℕ 0 ⇒ ℕ 1⟧ δ
        = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F∞ σ) → ⟦∀ 0. ℕ 0 ⇒ ℕ 1⟧ (σ, m)
        = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≲ω)
                → ∀ ((σ₁, m₁) ≥ (σ, m)) (m₂ ∈ 𝕆≲m₁)
                → ⟦ℕ 0 ⇒ ℕ 1⟧ (σ₁, m₁, m₂)
        = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≲ω)
                → ∀ ((σ₁, m₁) ≥ (σ, m)) (m₂ ∈ 𝕆≲m₁)
                → ∀ ((σ₂, m₃, m₄) ≥ (σ₁, m₁, m₂))
                → ⟦ℕ 0⟧ (σ₂, m₃, m₄)
                → ⟦ℕ 1⟧ (σ₂, m₃, m₄)
        = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≲ω)
                → ∀ ((σ₁, m₁) ≥ (σ, m)) (m₂ ∈ 𝕆≲m₁)
                → ∀ ((σ₂, m₃, m₄) ≥ (σ₁, m₁, m₂))
                → ℕ≤m₄
                → ℕ≤m₃
⟦suc⟧ δ x σ m (σ₁, m₁) m₂ (σ₂, m₃, m₄) n ≔ n + 1
  where
    m₄ ≲ m₃ since (σ₂, m₃, m₄) ∈ ⟦Δ ∷ ∞ ∷ 0⟧, thus
    - if m₃ = ω: n + 1 ∈ ℕ≤m₃ for any n
    - otherwise: m₄ < m₃, so n + 1 ≤ m₄ + 1 ≤ m₃

⟦Δ; Γ ⊢ caseℕ[T] : ∀∞. T[wk] ⇒ (∀ 0. ℕ 0 ⇒ T[wk ∘ wk]) ⇒ ℕ 0 ⇒ T[wk]⟧
  : ⟦Γ⟧ → ⟦∀∞. T[wk] ⇒ (∀ 0. ℕ 0 ⇒ T[wk ∘ wk]) ⇒ ℕ 0 ⇒ T[wk]⟧
⟦caseℕ[T]⟧ δ : ⟦Γ⟧ δ → ⟦∀∞. T[wk] ⇒ (∀ 0. ℕ 0 ⇒ T[wk ∘ wk]) ⇒ ℕ 0 ⇒ T[wk]⟧ δ
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F∞ σ)
                     → ⟦T[wk] ⇒ (∀ 0. ℕ 0 ⇒ T[wk ∘ wk]) ⇒ ℕ 0 ⇒ T[wk]⟧ (σ, m)
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F∞ σ)
                     → ∀ ((σ₁, m₁) ≥ (σ, m))
                     → ⟦T[wk]⟧ (σ₁, m₁)
                     → ⟦(∀ 0. ℕ 0 ⇒ T[wk ∘ wk]) ⇒ ℕ 0 ⇒ T[wk]⟧ (σ₁, m₁)
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₁, m₁) ≥ (σ, m))
                     → ⟦T⟧ σ₁
                     → ∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                     → ⟦∀ 0. ℕ 0 ⇒ T[wk ∘ wk]⟧ (σ₂, m₂)
                     → ⟦ℕ 0 ⇒ T[wk]⟧ (σ₂, m₂)
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₁, m₁) ≥ (σ, m))
                     → ⟦T⟧ σ₁
                     → ∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                     → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ F₀ (σ₃, m₃))
                       → ⟦ℕ 0 ⇒ T[wk ∘ wk]⟧ (σ₃, m₃, m₄))
                     → ∀ ((σ₃, m₃) ≥ (σ₂, m₂))
                     → ⟦ℕ 0⟧ (σ₃, m₃)
                     → ⟦T[wk]⟧ (σ₃, m₃)
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₁, m₁) ≥ (σ, m))
                     → ⟦T⟧ σ₁
                     → ∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                     → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ F₀ (σ₃, m₃))
                       → ∀ ((σ₄, m₅, m₆) ≥ (σ₃, m₃, m₄))
                       → ⟦ℕ 0⟧ (σ₄, m₅, m₆)
                       → ⟦T[wk ∘ wk]⟧ (σ₄, m₅, m₆))
                     → ∀ ((σ₃, m₃) ≥ (σ₂, m₂))
                     → ℕ≤m₃
                     → T σ₃
             = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₁, m₁) ≥ (σ, m))
                     → ⟦T⟧ σ₁
                     → ∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                     → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ F₀ (σ₃, m₃))
                       → ∀ ((σ₄, m₅, m₆) ≥ (σ₃, m₃, m₄))
                       → ℕ≤m₆
                       → ⟦T⟧ σ₄
                     → ∀ ((σ₃, m₃) ≥ (σ₂, m₂))
                     → ℕ≤m₃
                     → ⟦T⟧ σ₃
⟦caseℕ[T]⟧ δ γ σ m (σ₁, m₁) z (σ₂, m₂) s (σ₃, m₃) n
  ≔ if n = 0
      then ⟦T⟧ (σ₁ ≤ σ₂ ≤ σ₃) z
      else f (σ₃, m₃) (m₃ - 1) (σ₃, m₃, m₃ - 1) (n - 1)

⟦Δ; Γ ⊢ fix[T] : (∀ ∞. (∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ ∀ ∞. T⟧
  : ⟦Γ⟧ → ⟦(∀ ∞. (∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ ∀ ∞. T⟧
⟦fix[T]⟧ δ : ⟦Γ⟧ δ → ⟦(∀ ∞. (∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ ∀ ∞. T⟧ δ
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ)
                   → ⟦∀ ∞. (∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T⟧ σ
                   → ⟦∀ ∞. T⟧ σ
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ)
                   → (∀ (σ₁ ≥ σ) (m ∈ F∞ σ₁)
                     → ⟦(∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T⟧ (σ₁, m))
                   → ∀ (σ₁ ≥ σ) (m ∈ F∞ σ₁)
                   → ⟦T⟧ (σ₁, m)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ)
                   → (∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₂, m₁) ≥ (σ₁, m))
                     → ⟦∀ 0. T[wk ∙ (1 ≔ 0)]⟧ (σ₂, m₁)
                     → ⟦T⟧ (σ₂, m₁))
                   → ∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                   → ⟦T⟧ (σ₁, m)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ)
                   → (∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₂, m₁) ≥ (σ₁, m))
                     → (∀ (σ₃, m₂) ≥ (σ₂, m₁) (m₃ ∈ F₀ (σ₃, m₂))
                       → ⟦T[wk ∙ (1 ≔ 0)]⟧ (ο₃, m₂, m₃))
                     → ⟦T⟧ (σ₂, m₁))
                   → ∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                   → ⟦T⟧ (σ₁, m)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ)
                   → (∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                     → ∀ ((σ₂, m₁) ≥ (σ₁, m))
                     → (∀ ((σ₃, m₂) ≥ (σ₂, m₁)) (m₃ ∈ 𝕆≲m₂)
                       → ⟦T⟧ (ο₃, m₃))
                     → ⟦T⟧ (σ₂, m₁))
                   → ∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
                   → ⟦T⟧ (σ₁, m)
⟦fix[T]⟧ δ γ σ rec σ₁ m ≔ rec σ₁ m (σ₁, m) f
  where
    rec : ∀ (σ₁ ≥ σ) (m ∈ 𝕆≤ω)
        → ∀ ((σ₂, m₁) ≥ (σ₁, m))
        → (∀ ((σ₃, m₂) ≥ (σ₂, m₁)) (m₃ ∈ 𝕆≲m₂)
          → ⟦T⟧ (ο₃, m₃))
        → ⟦T⟧ (σ₂, m₁)
    f : ∀ ((σ₃, m₂) ≥ (σ₁, m)) (m₃ ∈ 𝕆≲m₂) → ⟦T⟧ (σ₃, m₃)
    f (σ₃, m₂) m₃ ≔ fix[T] δ γ σ₃ rec σ₃ m₃ [???]


Alternative type signature for fix[T]:

⟦Δ; Γ ⊢ fix[T] : ∀ ∞. ((∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T[wk]) ⇒ T⟧
  : ⟦Γ⟧ → ⟦∀ ∞. ((∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ T⟧
⟦fix[T]⟧ δ : ⟦Γ⟧ δ → ⟦∀ ∞. ((∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ T⟧ δ
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ F∞ σ)
                   → ⟦((∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T) ⇒ T⟧ (σ, m)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆)
                   → ∀ ((σ₁, m₁) ≥ (σ, m))
                   → ⟦(∀ 0. T[wk ∙ (1 ≔ 0)]) ⇒ T⟧ (σ₁, m₁)
                   → ⟦T⟧ (σ₁, m₁)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆)
                   → ∀ ((σ₁, m₁) ≥ (σ, m))
                   → (∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                      → ⟦∀ 0. T[wk ∙ (1 ≔ 0)]⟧ (σ₂, m₂)
                      → ⟦T⟧ (σ₂, m₂))
                   → ⟦T⟧ (σ₁, m₁)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆)
                   → ∀ ((σ₁, m₁) ≥ (σ, m))
                   → (∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                      → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ F₀ (σ₃, m₃))
                         → ⟦T[wk ∙ (1 ≔ 0)]⟧ (σ₃, m₃, m₄))
                      → ⟦T⟧ (σ₂, m₂))
                   → ⟦T⟧ (σ₁, m₁)
           = ⟦Γ⟧ δ → ∀ (σ ≥ δ) (m ∈ 𝕆)
                   → ∀ ((σ₁, m₁) ≥ (σ, m))
                   → (∀ ((σ₂, m₂) ≥ (σ₁, m₁))
                      → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ 𝕆≲m₃)
                         → ⟦T⟧ (σ₃, m₄))
                      → ⟦T⟧ (σ₂, m₂))
                   → ⟦T⟧ (σ₁, m₁)
⟦fix[T]⟧ δ γ σ m (σ₁, m₁) rec ≔ rec (σ₁, m₁) f
  where
    rec : ∀ ((σ₂, m₂) ≥ (σ₁, m₁))
        → (∀ ((σ₃, m₃) ≥ (σ₂, m₂)) (m₄ ∈ 𝕆≲m₃)
           → ⟦T⟧ (σ₃, m₄))
        → ⟦T⟧ (σ₂, m₂)
    f : ∀ ((σ₃, m₃) ≥ (σ₁, m₁)) (m₄ ∈ 𝕆≲m₃) → ⟦T⟧ (σ₃, m₄)
    f (σ₃, m₃) m₄ ≔ ⟦fix[T]⟧ δ γ σ m (σ₃, m₄) rec  [???]
    
    [We DON'T have m₄ < m₁, so the recursion is not justified!]