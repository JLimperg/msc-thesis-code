# λST

## Syntax

Variable x
  ∷= v0
  |  vsuc x


Size n, m, o
  ∷= x
  |  0
  |  ↑ n
  |  ∞
  |  ⋆
  
  
Size context Δ
  ∷= ()
  |  Δ, n
  

Type T, U, V
  ∷= ℕ n
  |  𝕊 n
  |  T ⇒ U
  |  ∀ n. T
  

Type context Γ
  ∷= ()
  |  Γ, T
  

Term t, u, v
  ∷= x
  |  λ T. t
  |  t u
  |  λ n. t
  |  t n
  |  fix
  |  zero
  |  suc
  |  caseℕ[T]
  |  cons
  |  head
  |  tail
  
  
## Typing

### ⊢ Δ (context formation)

––––
⊢ ()


Δ ⊢ n
––––––
⊢ Δ, n


### Δ ⊢ n (size formation)

Δ ⊢ n
–––––––––
Δ, n ⊢ v0


Δ ⊢ x   Δ ⊢ n
–––––––––––––
Δ, n ⊢ vsuc x


⊢ Δ
–––––
Δ ⊢ 0
Δ ⊢ ∞
Δ ⊢ ⋆


Δ ⊢ n < ∞
–––––––––
Δ ⊢ ↑ n


### Δ ⊢ n < m (strict size comparison)

Δ ⊢ n
–––––––––––––
Δ, n ⊢ v0 < n


Δ ⊢ x < n   Δ ⊢ m
–––––––––––––––––
Δ, m ⊢ vsuc x < n


⊢ Δ
–––––––––
Δ ⊢ 0 < ∞


Δ ⊢ n < ∞
–––––––––––
Δ ⊢ ↑ n < ∞


Δ ⊢ n < ∞
–––––––––––
Δ ⊢ n < ↑ n


Δ ⊢ n < ∞
–––––––––
Δ ⊢ n < ⋆


⊢ Δ
–––––––––
Δ ⊢ ∞ < ⋆


Δ ⊢ n < m   Δ ⊢ m < k
–––––––––––––––––––––   [maybe this is already admissible]
Δ ⊢ n < k


### Δ ⊢ T (type formation)

Δ ⊢ n < ⋆
–––––––––
Δ ⊢ ℕ n


Δ ⊢ n < ⋆
–––––––––
Δ ⊢ 𝕊 n


Δ ⊢ T   Δ ⊢ U
–––––––––––––
Δ ⊢ T ⇒ U


Δ, n ⊢ T
––––––––––
Δ ⊢ ∀ n. T


### Δ ⊢ Γ (context formation)

⊢ Δ
––––––
Δ ⊢ ()


Δ ⊢ Γ   Δ ⊢ T
–––––––––––––
Δ ⊢ Γ, T


### Δ; Γ ⊢ t : T (term typing)

Δ ⊢ Γ   Δ ⊢ T
––––––––––––––––
Δ; Γ, T ⊢ v0 : T


Δ; Γ ⊢ x : T   Δ ⊢ U
––––––––––––––––––––
Δ; Γ, U ⊢ vsuc x : T


Δ; Γ, T ⊢ t : U
–––––––––––––––––––––
Δ; Γ ⊢ λ T. t : T ⇒ U


Δ; Γ ⊢ t : T ⇒ U   Δ; Γ ⊢ u : T
–––––––––––––––––––––––––––––––
Δ; Γ ⊢ t u : U


Δ, n; wk Γ ⊢ t : T
––––––––––––––––––––––
Δ; Γ ⊢ λ n. t : ∀ n. T


Δ; Γ ⊢ t : ∀ m. T   Δ ⊢ n < m
–––––––––––––––––––––––––––––
Δ; Γ ⊢ t n : T[n]


Δ ⊢ Γ
––––––––––––––––––––––––––––––––––––––––––––
Δ; Γ ⊢ zero : ∀ ⋆. ℕ v0
Δ; Γ ⊢ suc : ∀ ⋆. ∀ v0. ℕ v0 ⇒ ℕ v1
Δ; Γ ⊢ cons : ∀ ⋆. ℕ ∞ ⇒ (∀ v0. 𝕊 v0) ⇒ 𝕊 v0
Δ; Γ ⊢ head : ∀ ⋆. 𝕊 v0 ⇒ ℕ ∞
Δ; Γ ⊢ tail : ∀ ⋆. 𝕊 v0 ⇒ ∀ v0. 𝕊 v0


Δ ⊢ Γ   Δ ⊢ T
–––––––––––––––––––––––––––––––––––––––––––––––––––––––
Δ; Γ ⊢ caseℕ[T] : ∀ ⋆. ℕ v0 ⇒ T ⇒ (∀ v0 ⇒ ℕ v0 ⇒ T) ⇒ T


Δ ⊢ Γ   Δ, ⋆ ⊢ T
––––––––––––––––––––––––––––––––––––––––––––––––––––––––
Δ; Γ ⊢ fix[T ∙] : (∀ ⋆. (∀ v0. T v0) ⇒ T v0) ⇒ ∀ ⋆. T v0


## Reduction

### t ⟶β u

(λ T. t) u ⟶ t[u]

(λ n. t) m ⟶ t[m]

caseℕ[T] n (zero n) z s ⟶ z

caseℕ[T] n (suc n m i) z s ⟶ s m i

head n (cons n x xs) ⟶ x

tail n (cons n x xs) ⟶ xs

fix[T ∙] f n ⟶ f n (fix[T ∙] f)

[+ congruence closure]


### t =β u

[the equivalence closure of ⟶β]


## Programming Examples

zeros : ∀ ⋆. 𝕊 v0
zeros ≔ fix[𝕊 ∙] λ (n < ⋆) (rec : ∀ (m < n). 𝕊 m).
        cons n (zero ∞) rec


zeros∞ : 𝕊 ∞
zeros∞ ≔ zeros ∞


map : (ℕ ∞ ⇒ ℕ ∞) ⇒ ∀ ⋆. 𝕊 v0 ⇒ 𝕊 v0
map ≔ λ (f : ℕ ∞ ⇒ ℕ ∞).
      fix[𝕊 ∙ ⇒ 𝕊 ∙] λ (n < ⋆) (rec : ∀ (m < n). 𝕊 m ⇒ 𝕊 m) (xs : 𝕊 n).
      cons n (f (head n xs)) (λ (m < n). rec m (tail n xs m)) 
      
      
upℕ : ∀ ⋆. ∀ v0. ℕ v0 ⇒ ℕ v1
upℕ ≔ λ (n < ⋆) (m < n) (i : ℕ m).
        caseℕ[ℕ n] m i
          zero n
          λ (k < m) (j : ℕ k).
            suc n k j


half : ∀ ⋆. ℕ v0 ⇒ ℕ v0
half ≔ fix[ℕ ∙ ⇒ ℕ ∙] λ (n < ⋆) (rec : ∀ (m < n). ℕ m ⇒ ℕ m) (i : ℕ n).
         caseℕ[ℕ n] n i
           (zero n)
           λ (m < n) (j : ℕ m).
             caseℕ[ℕ n] m j
               (zero n)
               λ (k < m) (l : ℕ k).
                 upℕ n k (rec k l)
