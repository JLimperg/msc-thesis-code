{-# OPTIONS --without-K --safe #-}
module Source.Term where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b ; v0 ; v1 )
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Canonical as SC using () renaming
  ( Sub⊢ to Subₛ⊢ )
open import Source.Size.Substitution.Universe as SU using
  ( ⟨_⟩ ) renaming
  ( Sub⊢ᵤ to Subₛ⊢ᵤ )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; SubTheory-Type
  ; SubTheory-Ctx )
open import Util.Prelude hiding (id ; _∘_)

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type


infix  0 _,_⊢_∶_ _,_⊢ₓ_∶_ Sub⊢
infix  3 _⊇_
infixl 5 sub-syntax-Termₛ sub-syntax-Subₛ sub-syntax-Term sub-syntax-⊇
infixr 6 Λ_,_ Λₛ_,_
infixl 7 _·_ _·ₛ_


Var : Set
Var = ℕ


variable x y : Var


data Term Δ : Set where
  var : (x : Var) → Term Δ
  Λ_,_ : (T : Type Δ) (t : Term Δ) → Term Δ
  _·_ : (t u : Term Δ) → Term Δ
  Λₛ_,_ : (n : Size Δ) (t : Term (Δ ∙ n)) → Term Δ
  _·ₛ_ : (t : Term Δ) (m : Size Δ) → Term Δ
  zero : (n : Size Δ) → Term Δ
  suc : (n m : Size Δ) (i : Term Δ) → Term Δ
  cons : (i : Term Δ) (n : Size Δ) (is : Term Δ) → Term Δ
  head : (n : Size Δ) (is : Term Δ) → Term Δ
  tail : (n : Size Δ) (is : Term Δ) (m : Size Δ) → Term Δ
  caseNat : (T : Type Δ) (n : Size Δ) (i : Term Δ) (z : Term Δ) (s : Term Δ)
    → Term Δ
  fix : (T : Type (Δ ∙ ⋆)) (t : Term Δ) (n : Size Δ) → Term Δ


variable t u v w i is z s t′ u′ v′ w′ i′ is′ z′ s′ : Term Δ


data _,_⊢ₓ_∶_ : ∀ Δ (Γ : Ctx Δ) (x : Var) (T : Type Δ) → Set where
  zero
    : Δ , Γ ∙ T ⊢ₓ zero ∶ T
  suc
    : (⊢x : Δ , Γ ⊢ₓ x ∶ T)
    → Δ , Γ ∙ U ⊢ₓ suc x ∶ T


data _,_⊢_∶_ : ∀ Δ (Γ : Ctx Δ) (t : Term Δ) (T : Type Δ) → Set where
  var
    : (⊢x : Δ , Γ ⊢ₓ x ∶ T)
    → Δ , Γ ⊢ var x ∶ T
  abs
    : (⊢t : Δ , Γ ∙ T ⊢ t ∶ U)
    → Δ , Γ ⊢ Λ T , t ∶ T ⇒ U
  app
    : (⊢t : Δ , Γ ⊢ t ∶ T ⇒ U)
    → (⊢u : Δ , Γ ⊢ u ∶ T)
    → Δ , Γ ⊢ t · u ∶ U
  absₛ
    : (⊢t : Δ ∙ n , Ψ ⊢ t ∶ T)
    → Ψ ≡ Γ [ SC.Wk ]
    → Δ , Γ ⊢ Λₛ n , t ∶ Π n , T
  appₛ
    : (m<n : m < n)
    → (⊢t : Δ , Γ ⊢ t ∶ (Π n , T))
    → U ≡ T [ SC.Fill m ]
    → Δ , Γ ⊢ t ·ₛ m ∶ U
  zero
    : (n<⋆ : n < ⋆)
    → Δ , Γ ⊢ zero n ∶ Nat n
  suc
    : (n<⋆ : n < ⋆)
    → (m<n : m < n)
    → (⊢i : Δ , Γ ⊢ i ∶ Nat m)
    → Δ , Γ ⊢ suc n m i ∶ Nat n
  cons
    : (n<⋆ : n < ⋆)
    → (⊢i : Δ , Γ ⊢ i ∶ Nat ∞)
    → (⊢is : Δ , Γ ⊢ is ∶ Π n , Stream v0)
    → Δ , Γ ⊢ cons i n is ∶ Stream n
  head
    : (n<⋆ : n < ⋆)
    → (⊢is : Δ , Γ ⊢ is ∶ Stream n)
    → Δ , Γ ⊢ head n is ∶ Nat ∞
  tail
    : (n<⋆ : n < ⋆)
    → (m<n : m < n)
    → (⊢is : Δ , Γ ⊢ is ∶ Stream n)
    → Δ , Γ ⊢ tail n is m ∶ Stream m
  caseNat
    : (n<⋆ : n < ⋆)
    → (⊢i : Δ , Γ ⊢ i ∶ Nat n)
    → (⊢z : Δ , Γ ⊢ z ∶ T)
    → (⊢s : Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ U)
    → U ≡ T [ SC.Wk ]
    → Δ , Γ ⊢ caseNat T n i z s ∶ T
  fix
    : (n<⋆ : n < ⋆)
    → (⊢t : Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , U) ⇒ T)
    → U ≡ T [ SC.Skip ]
    → V ≡ T [ SC.Fill n ]
    → Δ , Γ ⊢ fix T t n ∶ V


subₛ : SC.Sub Δ Ω → Term Ω → Term Δ
subₛ σ (var x) = var x
subₛ σ (Λ T , t) = Λ T [ σ ] , subₛ σ t
subₛ σ (t · u) = subₛ σ t · subₛ σ u
subₛ σ (Λₛ n , t) = Λₛ n [ σ ] , subₛ (SC.Keep σ) t
subₛ σ (t ·ₛ m) = subₛ σ t ·ₛ (m [ σ ])
subₛ σ (zero n) = zero (n [ σ ])
subₛ σ (suc n m i) = suc (n [ σ ]) (m [ σ ]) (subₛ σ i)
subₛ σ (cons i n is) = cons (subₛ σ i) (n [ σ ]) (subₛ σ is)
subₛ σ (head n is) = head (n [ σ ]) (subₛ σ is)
subₛ σ (tail n is m) = tail (n [ σ ]) (subₛ σ is) (m [ σ ])
subₛ σ (caseNat T n i z s)
  = caseNat (T [ σ ]) (n [ σ ]) (subₛ σ i) (subₛ σ z) (subₛ σ s)
subₛ σ (fix T t n) = fix (T [ SC.Keep σ ]) (subₛ σ t) (n [ σ ])


sub-syntax-Termₛ = subₛ

syntax sub-syntax-Termₛ σ t = t [ σ ]ₛ


abstract
  subₛ-resp-⊢ₓ : ∀ {σ}
    → σ ∶ Δ ⇒ Ω
    → Ω , Γ ⊢ₓ x ∶ T
    → Δ , Γ [ σ ] ⊢ₓ x ∶ T [ σ ]
  subₛ-resp-⊢ₓ ⊢σ zero = zero
  subₛ-resp-⊢ₓ ⊢σ (suc ⊢x) = suc (subₛ-resp-⊢ₓ ⊢σ ⊢x)


  subₛ-resp-⊢ : ∀ {σ}
    → σ ∶ Δ ⇒ Ω
    → Ω , Γ ⊢ t ∶ T
    → Δ , Γ [ σ ] ⊢ subₛ σ t ∶ T [ σ ]
  subₛ-resp-⊢ ⊢σ (var ⊢x) = var (subₛ-resp-⊢ₓ ⊢σ ⊢x)
  subₛ-resp-⊢ ⊢σ (abs ⊢t) = abs (subₛ-resp-⊢ ⊢σ ⊢t)
  subₛ-resp-⊢ ⊢σ (app ⊢t ⊢u) = app (subₛ-resp-⊢ ⊢σ ⊢t) (subₛ-resp-⊢ ⊢σ ⊢u)
  subₛ-resp-⊢ {Δ} {Γ = Γ} {σ = σ} ⊢σ (absₛ {Ψ = Ψ} ⊢t p)
    = absₛ (subₛ-resp-⊢ (SC.Keep⊢ ⊢σ refl) ⊢t) eq
    where
      eq : Ψ [ SC.Keep σ ] ≡ Γ [ σ ] [ SC.Wk ]
      eq = trans (cong (λ Ψ → Ψ [ SC.Keep σ ]) p)
        ([>>]″ (SC.Keep σ) SC.Wk SC.Wk σ Γ SC.Keep>>Wk)
  subₛ-resp-⊢ {σ = σ} ⊢σ (appₛ {m = m} {T = T} {U = U} m<n ⊢t p)
    = appₛ (SC.sub-resp-< ⊢σ m<n) (subₛ-resp-⊢ ⊢σ ⊢t) eq
    where
      eq : U [ σ ] ≡ T [ SC.Keep σ ] [ SC.Fill (m [ σ ]) ]
      eq = trans (cong (λ U → U [ σ ]) p)
        ([>>]″ _ _ _ _ _ (sym (SC.Fill>>Keep m)))
  subₛ-resp-⊢ ⊢σ (zero n<⋆)
    = zero (SC.sub-resp-< ⊢σ n<⋆)
  subₛ-resp-⊢ ⊢σ (suc n<⋆ m<n ⊢i)
    = suc (SC.sub-resp-< ⊢σ n<⋆) (SC.sub-resp-< ⊢σ m<n) (subₛ-resp-⊢ ⊢σ ⊢i)
  subₛ-resp-⊢ ⊢σ (cons n<⋆ ⊢i ⊢is)
    = cons (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢i) (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ ⊢σ (head n<⋆ ⊢is)
    = head (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ ⊢σ (tail n<⋆ m<n ⊢is)
    = tail (SC.sub-resp-< ⊢σ n<⋆) (SC.sub-resp-< ⊢σ m<n) (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ {σ = σ} ⊢σ (caseNat {T = T} {U = U} n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢i) (subₛ-resp-⊢ ⊢σ ⊢z)
        (subₛ-resp-⊢ ⊢σ ⊢s) eq
    where
      eq : U [ SC.Keep σ ] ≡ T [ σ ] [ SC.Wk ]
      eq = trans (cong (λ U → U [ SC.Keep σ ]) p)
        ([>>]″ _ _ _ _ _ SC.Keep>>Wk)
  subₛ-resp-⊢ {σ = σ} ⊢σ (fix {n = n} {U = U} {T = T} {V = V} n<⋆ ⊢t p q)
    = fix (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢t) eq₀ eq₁
    where
      eq₀ : U [ SC.Keep (SC.Keep σ) ] ≡ T [ SC.Keep σ ] [ SC.Skip ]
      eq₀ = trans (cong (λ U → U [ SC.Keep (SC.Keep σ) ]) p)
        ([>>]″ _ _ _ _ _ SC.KeepKeep>>Skip)

      eq₁ : V [ σ ] ≡ T [ SC.Keep σ ] [ SC.Fill (n [ σ ]) ]
      eq₁ = trans (cong (λ V → V [ σ ]) q)
        ([>>]″ _ _ _ _ _ (sym (SC.Fill>>Keep n)))


  subₛ-Id : (t : Term Δ) → subₛ SC.Id t ≡ t
  subₛ-Id (var x) = refl
  subₛ-Id (Λ T , t) = cong₂ Λ_,_ ([Id] T) (subₛ-Id t)
  subₛ-Id (t · u) = cong₂ _·_ (subₛ-Id t) (subₛ-Id u)
  subₛ-Id (Λₛ n , t)
    rewrite [Id] n | subₛ-Id t
    = refl
  subₛ-Id (t ·ₛ m) = cong₂ _·ₛ_ (subₛ-Id t) ([Id] m)
  subₛ-Id (zero n) = cong zero ([Id] n)
  subₛ-Id (suc n m i)
    rewrite [Id] n | [Id] m | subₛ-Id i
    = refl
  subₛ-Id (cons i n is)
    rewrite subₛ-Id i | [Id] n | subₛ-Id is
    = refl
  subₛ-Id (head n is) = cong₂ head ([Id] n) (subₛ-Id is)
  subₛ-Id (tail n is m)
    rewrite [Id] n | subₛ-Id is | [Id] m
    = refl
  subₛ-Id (caseNat T n i z s)
    rewrite [Id] T | [Id] n | subₛ-Id i | subₛ-Id z | subₛ-Id s
    = refl
  subₛ-Id (fix T t n)
    rewrite [Id] T | subₛ-Id t | [Id] n
    = refl


  subₛ->> : ∀ (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) t
    → subₛ (σ SC.>> τ) t ≡ subₛ σ (subₛ τ t)
  subₛ->> σ τ (var x) = refl
  subₛ->> σ τ (Λ T , t) = cong₂ Λ_,_ ([>>] σ τ T) (subₛ->> σ τ t)
  subₛ->> σ τ (t · u) = cong₂ _·_ (subₛ->> σ τ t) (subₛ->> σ τ u)
  subₛ->> σ τ (Λₛ n , t)
    rewrite [>>] σ τ n
    = cong (λ t → Λₛ SC.sub σ (SC.sub τ n) , t)
        (trans (cong (λ σ → subₛ σ t) (sym (SC.Keep>>Keep {n = n [ τ ]})))
          (subₛ->> (SC.Keep σ) (SC.Keep τ) t))
  subₛ->> σ τ (t ·ₛ m)
    = cong₂ _·ₛ_ (subₛ->> σ τ t) ([>>] σ τ m)
  subₛ->> σ τ (zero n) = cong zero ([>>] σ τ n)
  subₛ->> σ τ (suc n m i)
    rewrite [>>] σ τ n | [>>] σ τ m | subₛ->> σ τ i
    = refl
  subₛ->> σ τ (cons i n is)
    rewrite subₛ->> σ τ i | [>>] σ τ n | subₛ->> σ τ is
    = refl
  subₛ->> σ τ (head n is)
    rewrite [>>] σ τ n | subₛ->> σ τ is
    = refl
  subₛ->> σ τ (tail n is m)
    rewrite [>>] σ τ n | subₛ->> σ τ is | [>>] σ τ m
    = refl
  subₛ->> σ τ (caseNat T n i z s)
    rewrite [>>] σ τ T | [>>] σ τ n | subₛ->> σ τ i | subₛ->> σ τ z
      | subₛ->> σ τ s
    = refl
  subₛ->> σ τ (fix T t n)
    rewrite subₛ->> σ τ t | [>>] σ τ n
    = cong (λ T → fix T (subₛ σ (subₛ τ t)) (n [ τ ] [ σ ]))
        ([>>]′ _ _ _ _ (sym SC.Keep>>Keep))


subₛᵤ : SU.Sub Δ Ω → Term Ω → Term Δ
subₛᵤ σ = subₛ ⟨ σ ⟩


abstract
  subₛᵤ-resp-⊢ : ∀ {σ}
    → σ ∶ Δ ⇒ᵤ Ω
    → Ω , Γ ⊢ t ∶ T
    → Δ , Γ [ σ ]ᵤ ⊢ subₛᵤ σ t ∶ T [ σ ]ᵤ
  subₛᵤ-resp-⊢ ⊢σ ⊢t = subₛ-resp-⊢ (SU.⟨⟩-resp-⊢ ⊢σ) ⊢t


  subₛᵤ-Id : (t : Term Δ) → subₛᵤ SU.Id t ≡ t
  subₛᵤ-Id t = subₛ-Id t


  subₛᵤ->> : ∀ (σ : SU.Sub Δ Δ′) (τ : SU.Sub Δ′ Δ″) t
    → subₛᵤ (σ SU.>> τ) t ≡ subₛᵤ σ (subₛᵤ τ t)
  subₛᵤ->> σ τ t = subₛ->> ⟨ σ ⟩ ⟨ τ ⟩ t


data _⊇_ {Δ} : (Γ Ψ : Ctx Δ) → Set where
  [] : [] ⊇ []
  keep : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ ∙ T
  weak : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ


variable α β γ : Γ ⊇ Ψ


sub⊇ : (σ : SC.Sub Δ Ω) → Γ ⊇ Ψ → Γ [ σ ] ⊇ Ψ [ σ ]
sub⊇ σ [] = []
sub⊇ σ (keep α T) = keep (sub⊇ σ α) (T [ σ ])
sub⊇ σ (weak α T) = weak (sub⊇ σ α) (T [ σ ])


sub-syntax-⊇ = sub⊇

syntax sub-syntax-⊇ σ α = α [ σ ]α


renV : Γ ⊇ Ψ → Var → Var
renV [] x = x -- impossible if x is well-scoped
renV (keep α T) zero = zero
renV (keep α T) (suc x) = suc (renV α x)
renV (weak α T) x = suc (renV α x)


ren : {Γ Ψ : Ctx Δ} → Γ ⊇ Ψ → Term Δ → Term Δ
ren α (var x) = var (renV α x)
ren α (Λ T , t) = Λ T , ren (keep α T) t
ren α (t · u) = ren α t · ren α u
ren α (Λₛ n , t) = Λₛ n , ren (α [ SC.Wk ]α) t
ren α (t ·ₛ m) = ren α t ·ₛ m
ren α (zero n) = zero n
ren α (suc n m i) = suc n m (ren α i)
ren α (cons i n is) = cons (ren α i) n (ren α is)
ren α (head n is) = head n (ren α is)
ren α (tail n is m) = tail n (ren α is) m
ren α (caseNat T n i z s) = caseNat T n (ren α i) (ren α z) (ren α s)
ren α (fix T t n) = fix T (ren α t) n


abstract
  renV-resp-⊢ₓ
    : (α : Γ ⊇ Ψ)
    → Δ , Ψ ⊢ₓ x ∶ T
    → Δ , Γ ⊢ₓ renV α x ∶ T
  renV-resp-⊢ₓ (keep α T) zero = zero
  renV-resp-⊢ₓ (keep α T) (suc ⊢x) = suc (renV-resp-⊢ₓ α ⊢x)
  renV-resp-⊢ₓ (weak α T) ⊢x = suc (renV-resp-⊢ₓ α ⊢x)


  ren-resp-⊢
    : (α : Γ ⊇ Ψ)
    → Δ , Ψ ⊢ t ∶ T
    → Δ , Γ ⊢ ren α t ∶ T
  ren-resp-⊢ α (var ⊢x) = var (renV-resp-⊢ₓ α ⊢x)
  ren-resp-⊢ α (abs ⊢t)
    = abs (ren-resp-⊢ (keep α _) ⊢t)
  ren-resp-⊢ α (app ⊢t ⊢u) = app (ren-resp-⊢ α ⊢t) (ren-resp-⊢ α ⊢u)
  ren-resp-⊢ α (absₛ ⊢t refl)
    = absₛ (ren-resp-⊢ (α [ SC.Wk ]α) ⊢t) refl
  ren-resp-⊢ α (appₛ m<n ⊢t p) = appₛ m<n (ren-resp-⊢ α ⊢t) p
  ren-resp-⊢ α (zero n<⋆) = zero n<⋆
  ren-resp-⊢ α (suc n<⋆ m<n ⊢i) = suc n<⋆ m<n (ren-resp-⊢ α ⊢i)
  ren-resp-⊢ α (cons n<⋆ ⊢i ⊢is)
    = cons n<⋆ (ren-resp-⊢ α ⊢i) (ren-resp-⊢ α ⊢is)
  ren-resp-⊢ α (head n<⋆ ⊢is) = head n<⋆ (ren-resp-⊢ α ⊢is)
  ren-resp-⊢ α (tail n<⋆ m<n ⊢is) = tail n<⋆ m<n (ren-resp-⊢ α ⊢is)
  ren-resp-⊢ α (caseNat n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat n<⋆ (ren-resp-⊢ α ⊢i) (ren-resp-⊢ α ⊢z) (ren-resp-⊢ α ⊢s) p
  ren-resp-⊢ α (fix n<⋆ ⊢t p q) = fix n<⋆ (ren-resp-⊢ α ⊢t) p q


Id⊇ : (Γ : Ctx Δ) → Γ ⊇ Γ
Id⊇ [] = []
Id⊇ (Γ ∙ T) = keep (Id⊇ Γ) T


Wk⊇ : ∀ (Γ : Ctx Δ) T → Γ ∙ T ⊇ Γ
Wk⊇ Γ T = weak (Id⊇ Γ) _


data Sub {Δ} (Γ : Ctx Δ) : (Ψ : Ctx Δ) → Set where
  [] : Sub Γ []
  Snoc : (ν : Sub Γ Ψ) (t : Term Δ) → Sub Γ (Ψ ∙ T)


variable ν φ : Sub Γ Ψ


data Sub⊢ {Δ} (Γ : Ctx Δ) : ∀ Ψ → Sub Γ Ψ → Set where
  [] : Sub⊢ Γ [] []
  Snoc : (⊢ν : Sub⊢ Γ Ψ ν) (⊢t : Δ , Γ ⊢ t ∶ T) → Sub⊢ Γ (Ψ ∙ T) (Snoc ν t)


syntax Sub⊢ Γ Ψ ν = ν ∶ Γ ⇛ Ψ


Weaken : Sub Γ Ψ → Sub (Γ ∙ T) Ψ
Weaken [] = []
Weaken {Γ = Γ} {T = T} (Snoc ν t) = Snoc (Weaken ν) (ren (Wk⊇ Γ T) t)


abstract
  Weaken⊢ : ν ∶ Γ ⇛ Ψ → Weaken ν ∶ Γ ∙ T ⇛ Ψ
  Weaken⊢ [] = []
  Weaken⊢ (Snoc ⊢ν ⊢t)
    = Snoc (Weaken⊢ ⊢ν) (ren-resp-⊢ (Wk⊇ _ _) ⊢t)


Keep : Sub Γ Ψ → ∀ T → Sub (Γ ∙ T) (Ψ ∙ T)
Keep σ T = Snoc (Weaken σ) (var zero)


abstract
  Keep⊢ : ν ∶ Γ ⇛ Ψ → Keep ν T ∶ Γ ∙ T ⇛ Ψ ∙ T
  Keep⊢ ⊢ν = Snoc (Weaken⊢ ⊢ν) (var zero)


Id : Sub Γ Γ
Id {Γ = []} = []
Id {Γ = Γ ∙ T} = Keep Id T


abstract
  Id⊢ : Id ∶ Γ ⇛ Γ
  Id⊢ {Γ = []} = []
  Id⊢ {Γ = Γ ∙ T} = Snoc (Weaken⊢ Id⊢) (var zero)


Wk : Sub (Γ ∙ T) Γ
Wk = Weaken Id


abstract
  Wk⊢ : Wk ∶ Γ ∙ T ⇛ Γ
  Wk⊢ = Weaken⊢ Id⊢


Fill : ∀ (Γ : Ctx Δ) T → Term Δ → Sub Γ (Γ ∙ T)
Fill Γ T t = Snoc Id t


abstract
  Fill⊢ : Δ , Γ ⊢ t ∶ T → Fill Γ T t ∶ Γ ⇛ Γ ∙ T
  Fill⊢ ⊢t = Snoc Id⊢ ⊢t


subν : (σ : SC.Sub Δ Ω) → Sub Γ Ψ → Sub (Γ [ σ ]) (Ψ [ σ ])
subν σ [] = []
subν σ (Snoc ν t) = Snoc (subν σ ν) (t [ σ ]ₛ)


abstract
  subν-resp-⊢ : ∀ {σ} → σ ∶ Δ ⇒ Ω → ν ∶ Γ ⇛ Ψ → subν σ ν ∶ Γ [ σ ] ⇛ Ψ [ σ ]
  subν-resp-⊢ ⊢σ [] = []
  subν-resp-⊢ ⊢σ (Snoc ⊢ν ⊢t) = Snoc (subν-resp-⊢ ⊢σ ⊢ν) (subₛ-resp-⊢ ⊢σ ⊢t)


sub-syntax-Subₛ = subν

syntax sub-syntax-Subₛ σ ν = ν [ σ ]ν


subV : Sub {Δ} Γ Ψ → Var → Term Δ
subV [] x = var x -- impossible if x is well-scoped
subV (Snoc ν t) zero = t
subV (Snoc ν t) (suc x) = subV ν x


sub : Sub {Δ} Γ Ψ → Term Δ → Term Δ
sub ν (var x) = subV ν x
sub ν (Λ T , t) = Λ T , sub (Keep ν T) t
sub ν (t · u) = sub ν t · sub ν u
sub ν (Λₛ n , t) = Λₛ n , sub (ν [ SC.Wk ]ν) t
sub ν (t ·ₛ m) = sub ν t ·ₛ m
sub ν (zero n) = zero n
sub ν (suc n m i) = suc n m (sub ν i)
sub ν (cons i n is) = cons (sub ν i) n (sub ν is)
sub ν (head n is) = head n (sub ν is)
sub ν (tail n is m) = tail n (sub ν is) m
sub ν (caseNat T n i z s) = caseNat T n (sub ν i) (sub ν z) (sub ν s)
sub ν (fix T t n) = fix T (sub ν t) n


sub-syntax-Term = sub

syntax sub-syntax-Term ν t = t [ ν ]t


abstract
  subV-resp-⊢
    : ν ∶ Γ ⇛ Ψ
    → Δ , Ψ ⊢ₓ x ∶ T
    → Δ , Γ ⊢ subV ν x ∶ T
  subV-resp-⊢ (Snoc ⊢ν ⊢t) zero = ⊢t
  subV-resp-⊢ (Snoc ⊢ν ⊢t) (suc ⊢x) = subV-resp-⊢ ⊢ν ⊢x


  sub-resp-⊢
    : ν ∶ Γ ⇛ Ψ
    → Δ , Ψ ⊢ t ∶ T
    → Δ , Γ ⊢ sub ν t ∶ T
  sub-resp-⊢ ⊢ν (var ⊢x)
    = subV-resp-⊢ ⊢ν ⊢x
  sub-resp-⊢ ⊢ν (abs ⊢t)
    = abs (sub-resp-⊢ (Keep⊢ ⊢ν) ⊢t)
  sub-resp-⊢ ⊢ν (app ⊢t ⊢u)
    = app (sub-resp-⊢ ⊢ν ⊢t) (sub-resp-⊢ ⊢ν ⊢u)
  sub-resp-⊢ ⊢ν (absₛ ⊢t refl)
    = absₛ (sub-resp-⊢ (subν-resp-⊢ SC.Wk⊢ ⊢ν) ⊢t) refl
  sub-resp-⊢ ⊢ν (appₛ m<n ⊢t p)
    = appₛ m<n (sub-resp-⊢ ⊢ν ⊢t) p
  sub-resp-⊢ ⊢ν (zero n<⋆)
    = zero n<⋆
  sub-resp-⊢ ⊢ν (suc n<⋆ m<n ⊢i)
    = suc n<⋆ m<n (sub-resp-⊢ ⊢ν ⊢i)
  sub-resp-⊢ ⊢ν (cons n<⋆ ⊢i ⊢is)
    = cons n<⋆ (sub-resp-⊢ ⊢ν ⊢i) (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (head n<⋆ ⊢is)
    = head n<⋆ (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (tail n<⋆ m<n ⊢is)
    = tail n<⋆ m<n (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (caseNat n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat n<⋆ (sub-resp-⊢ ⊢ν ⊢i) (sub-resp-⊢ ⊢ν ⊢z) (sub-resp-⊢ ⊢ν ⊢s) p
  sub-resp-⊢ ⊢ν (fix n<⋆ ⊢t p q)
    = fix n<⋆ (sub-resp-⊢ ⊢ν ⊢t) p q
