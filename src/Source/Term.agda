{-# OPTIONS --without-K --safe #-}
module Source.Term where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b ; v0
  ; v1 ; _⊢_ ; ⊢_ ; Δ⊢n→⊢Δ )
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Canonical as SC using () renaming
  ( Sub⊢ to Subₛ⊢ )
open import Source.Size.Substitution.Universe as SU using
  ( ⟨_⟩ ) renaming
  ( Sub⊢ᵤ to Subₛ⊢ᵤ )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; _⊢_type ; _⊢_ctx
  ; Δ⊢T→⊢Δ ; Δ⊢Γ→⊢Δ ; Δ⊢Γ∙T→Δ⊢Γ ; Δ⊢Γ∙T→Δ⊢T ; SubTheory-Type ; SubTheory-Ctx )
open import Util.Prelude hiding (id ; _∘_)

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type
open _⊢_
open _⊢_type
open _⊢_ctx


infix  0 _,_⊢_∶_ _,_⊢ₓ_∶_ ⊇⊢ Sub⊢
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
    : (⊢Γ : Δ ⊢ Γ ctx)
    → (⊢T : Δ ⊢ T type)
    → Δ , Γ ∙ T ⊢ₓ zero ∶ T
  suc
    : (⊢x : Δ , Γ ⊢ₓ x ∶ T)
    → (⊢U : Δ ⊢ U type)
    → Δ , Γ ∙ U ⊢ₓ suc x ∶ T


abstract
  ⊢ₓ→⊢Γ : Δ , Γ ⊢ₓ x ∶ T → Δ ⊢ Γ ctx
  ⊢ₓ→⊢Γ (zero ⊢Γ ⊢T) = Snoc ⊢Γ ⊢T
  ⊢ₓ→⊢Γ (suc ⊢x ⊢U) = Snoc (⊢ₓ→⊢Γ ⊢x) ⊢U


  ⊢ₓ→⊢T : Δ , Γ ⊢ₓ x ∶ T → Δ ⊢ T type
  ⊢ₓ→⊢T (zero ⊢Γ ⊢T) = ⊢T
  ⊢ₓ→⊢T (suc ⊢x ⊢U) = ⊢ₓ→⊢T ⊢x


  ⊢ₓ→⊢Δ : Δ , Γ ⊢ₓ x ∶ T → ⊢ Δ
  ⊢ₓ→⊢Δ ⊢x = Δ⊢Γ→⊢Δ (⊢ₓ→⊢Γ ⊢x)


data _,_⊢_∶_ : ∀ Δ (Γ : Ctx Δ) (t : Term Δ) (T : Type Δ) → Set where
  var
    : (x : Var)
    → (⊢x : Δ , Γ ⊢ₓ x ∶ T)
    → Δ , Γ ⊢ var x ∶ T
  abs
    : ∀ T t
    → (⊢t : Δ , Γ ∙ T ⊢ t ∶ U)
    → Δ , Γ ⊢ Λ T , t ∶ T ⇒ U
  app
    : ∀ t u
    → (⊢t : Δ , Γ ⊢ t ∶ T ⇒ U)
    → (⊢u : Δ , Γ ⊢ u ∶ T)
    → Δ , Γ ⊢ t · u ∶ U
  absₛ
    : ∀ n {Ψ : Ctx (Δ ∙ n)} T t
    → (⊢n : Δ ⊢ n)
    → (⊢Γ : Δ ⊢ Γ ctx)
    → (⊢t : Δ ∙ n , Ψ ⊢ t ∶ T)
    → Ψ ≡ Γ [ SC.Wk ]
    → Δ , Γ ⊢ Λₛ n , t ∶ Π n , T
  appₛ
    : ∀ t m (m<n : m < n)
    → (⊢m : Δ ⊢ m)
    → (⊢t : Δ , Γ ⊢ t ∶ (Π n , T))
    → U ≡ T [ SC.Fill m ]
    → Δ , Γ ⊢ t ·ₛ m ∶ U
  zero
    : (n<⋆ : n < ⋆)
    → (⊢n : Δ ⊢ n)
    → (⊢Γ : Δ ⊢ Γ ctx)
    → Δ , Γ ⊢ zero n ∶ Nat n
  suc
    : (n<⋆ : n < ⋆)
    → (m<n : m < n)
    → (⊢n : Δ ⊢ n)
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
    → (⊢m : Δ ⊢ m)
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
    → (⊢n : Δ ⊢ n)
    → (⊢t : Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , U) ⇒ T)
    → U ≡ T [ SC.Skip ]
    → V ≡ T [ SC.Fill n ]
    → Δ , Γ ⊢ fix T t n ∶ V


abstract
  ⊢t→⊢Δ : Δ , Γ ⊢ t ∶ T → ⊢ Δ
  ⊢t→⊢Δ (var x ⊢x) = ⊢ₓ→⊢Δ ⊢x
  ⊢t→⊢Δ (abs T t ⊢t) = ⊢t→⊢Δ ⊢t
  ⊢t→⊢Δ (app t u ⊢t ⊢u) = ⊢t→⊢Δ ⊢t
  ⊢t→⊢Δ (absₛ n T t ⊢n ⊢Γ ⊢t x) = Δ⊢n→⊢Δ ⊢n
  ⊢t→⊢Δ (appₛ t m m<n ⊢m ⊢t x) = ⊢t→⊢Δ ⊢t
  ⊢t→⊢Δ (zero n<⋆ ⊢n ⊢Γ) = Δ⊢n→⊢Δ ⊢n
  ⊢t→⊢Δ (suc n<⋆ m<n ⊢n ⊢t) = ⊢t→⊢Δ ⊢t
  ⊢t→⊢Δ (cons n<⋆ ⊢i ⊢is) = ⊢t→⊢Δ ⊢i
  ⊢t→⊢Δ (head n<⋆ ⊢t) = ⊢t→⊢Δ ⊢t
  ⊢t→⊢Δ (tail n<⋆ m<n ⊢m ⊢is) = ⊢t→⊢Δ ⊢is
  ⊢t→⊢Δ (caseNat n<⋆ ⊢i ⊢z ⊢s x) = ⊢t→⊢Δ ⊢i
  ⊢t→⊢Δ (fix n<⋆ ⊢n ⊢t x x₁) = ⊢t→⊢Δ ⊢t


  ⊢t→⊢Γ : Δ , Γ ⊢ t ∶ T → Δ ⊢ Γ ctx
  ⊢t→⊢Γ (var x ⊢x) = ⊢ₓ→⊢Γ ⊢x
  ⊢t→⊢Γ (abs T t ⊢t) = Δ⊢Γ∙T→Δ⊢Γ (⊢t→⊢Γ ⊢t)
  ⊢t→⊢Γ (app t u ⊢t ⊢u) = ⊢t→⊢Γ ⊢u
  ⊢t→⊢Γ (absₛ n T t ⊢n ⊢Γ ⊢t p) = ⊢Γ
  ⊢t→⊢Γ (appₛ t m m<n ⊢m ⊢t p) = ⊢t→⊢Γ ⊢t
  ⊢t→⊢Γ (zero n<⋆ ⊢n ⊢Γ) = ⊢Γ
  ⊢t→⊢Γ (suc n<⋆ m<n ⊢n ⊢i) = ⊢t→⊢Γ ⊢i
  ⊢t→⊢Γ (cons n<⋆ ⊢i ⊢is) = ⊢t→⊢Γ ⊢i
  ⊢t→⊢Γ (head n<⋆ ⊢is) = ⊢t→⊢Γ ⊢is
  ⊢t→⊢Γ (tail n<⋆ m<n ⊢m ⊢is) = ⊢t→⊢Γ ⊢is
  ⊢t→⊢Γ (caseNat n<⋆ ⊢i ⊢z ⊢s p) = ⊢t→⊢Γ ⊢i
  ⊢t→⊢Γ (fix n<⋆ ⊢n ⊢t p q) = ⊢t→⊢Γ ⊢t


  ⊢t→⊢T : Δ , Γ ⊢ t ∶ T → Δ ⊢ T type
  ⊢t→⊢T (var x ⊢x) = ⊢ₓ→⊢T ⊢x
  ⊢t→⊢T (abs {U = U} T t ⊢t) = arr T U (Δ⊢Γ∙T→Δ⊢T (⊢t→⊢Γ ⊢t)) (⊢t→⊢T ⊢t)
  ⊢t→⊢T (app t u ⊢t ⊢u) with ⊢t→⊢T ⊢t
  ... | arr T U ⊢T ⊢U = ⊢U
  ⊢t→⊢T (absₛ n T t ⊢n ⊢Γ ⊢t p) = pi n T ⊢n (⊢t→⊢T ⊢t)
  ⊢t→⊢T (appₛ t m m<n ⊢m ⊢t refl) with ⊢t→⊢T ⊢t
  ... | pi n T ⊢n ⊢T = []-resp-⊢ ⊢T (SC.Fill⊢ ⊢m ⊢n m<n)
  ⊢t→⊢T (zero n<⋆ ⊢n ⊢Γ) = Nat _ ⊢n
  ⊢t→⊢T (suc n<⋆ m<n ⊢n ⊢i) = Nat _ ⊢n
  ⊢t→⊢T (cons n<⋆ ⊢i ⊢is) with ⊢t→⊢T ⊢is
  ... | pi _ _ ⊢n _ = Stream _ ⊢n
  ⊢t→⊢T (head n<⋆ ⊢is) = Nat ∞ (∞ (⊢t→⊢Δ ⊢is))
  ⊢t→⊢T (tail n<⋆ m<n ⊢m ⊢is) = Stream _ ⊢m
  ⊢t→⊢T (caseNat n<⋆ ⊢i ⊢z ⊢s p) = ⊢t→⊢T ⊢z
  ⊢t→⊢T (fix n<⋆ ⊢n ⊢t refl refl) with ⊢t→⊢T ⊢t
  ⊢t→⊢T (fix n<⋆ ⊢n ⊢t refl refl) | pi _ _ ⊢⋆ (arr _ _ _ ⊢U)
    = []-resp-⊢ ⊢U (SC.Fill⊢ ⊢n ⊢⋆ n<⋆)


-- This is a special case of subst.
cast⊢Γ : ∀ {Δ Γ Ψ t T}
  → Γ ≡ Ψ
  → Δ , Γ ⊢ t ∶ T
  → Δ , Ψ ⊢ t ∶ T
cast⊢Γ refl ⊢t = ⊢t


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
  subₛ-resp-⊢ₓ ⊢σ (zero ⊢Γ ⊢T) = zero ([]-resp-⊢ ⊢Γ ⊢σ) ([]-resp-⊢ ⊢T ⊢σ)
  subₛ-resp-⊢ₓ ⊢σ (suc ⊢x ⊢T) = suc (subₛ-resp-⊢ₓ ⊢σ ⊢x) ([]-resp-⊢ ⊢T ⊢σ)


  subₛ-resp-⊢ : ∀ {σ}
    → σ ∶ Δ ⇒ Ω
    → Ω , Γ ⊢ t ∶ T
    → Δ , Γ [ σ ] ⊢ subₛ σ t ∶ T [ σ ]
  subₛ-resp-⊢ ⊢σ (var x ⊢x) = var x (subₛ-resp-⊢ₓ ⊢σ ⊢x)
  subₛ-resp-⊢ ⊢σ (abs T t ⊢t) = abs _ _ (subₛ-resp-⊢ ⊢σ ⊢t)
  subₛ-resp-⊢ ⊢σ (app t u ⊢t ⊢u) = app _ _ (subₛ-resp-⊢ ⊢σ ⊢t) (subₛ-resp-⊢ ⊢σ ⊢u)
  subₛ-resp-⊢ {Δ} {Γ = Γ} {σ = σ} ⊢σ (absₛ n {Ψ = Ψ} T t ⊢n ⊢Γ ⊢t p)
    = absₛ _ _ _ ([]-resp-⊢ ⊢n ⊢σ) ([]-resp-⊢ ⊢Γ ⊢σ)
        (subₛ-resp-⊢ (SC.Keep⊢ ⊢σ ⊢n refl) ⊢t) eq
    where
      eq : Ψ [ SC.Keep σ ] ≡ Γ [ σ ] [ SC.Wk ]
      eq = trans (cong (λ Ψ → Ψ [ SC.Keep σ ]) p)
        ([>>]″ (SC.Keep σ) SC.Wk SC.Wk σ Γ SC.Keep>>Wk)
  subₛ-resp-⊢ {σ = σ} ⊢σ (appₛ {T = T} {U = U} t m m<n ⊢m ⊢t p)
    = appₛ _ _ (SC.sub-resp-< ⊢σ m<n) ([]-resp-⊢ ⊢m ⊢σ) (subₛ-resp-⊢ ⊢σ ⊢t) eq
    where
      eq : U [ σ ] ≡ T [ SC.Keep σ ] [ SC.Fill (m [ σ ]) ]
      eq = trans (cong (λ U → U [ σ ]) p)
        ([>>]″ _ _ _ _ _ (sym (SC.Fill>>Keep m)))
  subₛ-resp-⊢ ⊢σ (zero n<⋆ ⊢n ⊢Γ)
    = zero (SC.sub-resp-< ⊢σ n<⋆) ([]-resp-⊢ ⊢n ⊢σ) ([]-resp-⊢ ⊢Γ ⊢σ)
  subₛ-resp-⊢ ⊢σ (suc n<⋆ m<n ⊢n ⊢i)
    = suc (SC.sub-resp-< ⊢σ n<⋆) (SC.sub-resp-< ⊢σ m<n) ([]-resp-⊢ ⊢n ⊢σ)
        (subₛ-resp-⊢ ⊢σ ⊢i)
  subₛ-resp-⊢ ⊢σ (cons n<⋆ ⊢i ⊢is)
    = cons (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢i) (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ ⊢σ (head n<⋆ ⊢is)
    = head (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ ⊢σ (tail n<⋆ m<n ⊢m ⊢is)
    = tail (SC.sub-resp-< ⊢σ n<⋆) (SC.sub-resp-< ⊢σ m<n) ([]-resp-⊢ ⊢m ⊢σ)
        (subₛ-resp-⊢ ⊢σ ⊢is)
  subₛ-resp-⊢ {σ = σ} ⊢σ (caseNat {T = T} {U = U} n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat (SC.sub-resp-< ⊢σ n<⋆) (subₛ-resp-⊢ ⊢σ ⊢i) (subₛ-resp-⊢ ⊢σ ⊢z)
        (subₛ-resp-⊢ ⊢σ ⊢s) eq
    where
      eq : U [ SC.Keep σ ] ≡ T [ σ ] [ SC.Wk ]
      eq = trans (cong (λ U → U [ SC.Keep σ ]) p)
        ([>>]″ _ _ _ _ _ SC.Keep>>Wk)
  subₛ-resp-⊢ {σ = σ} ⊢σ (fix {n = n} {U = U} {T = T} {V = V} n<⋆ ⊢n ⊢t p q)
    = fix (SC.sub-resp-< ⊢σ n<⋆) ([]-resp-⊢ ⊢n ⊢σ) (subₛ-resp-⊢ ⊢σ ⊢t) eq₀ eq₁
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


data ⊇⊢ {Δ} : (Γ Ψ : Ctx Δ) → Γ ⊇ Ψ → Set where
  [] : (⊢Δ : ⊢ Δ) → ⊇⊢ [] [] []
  keep : ∀ {α T} (⊢α : ⊇⊢ Γ Ψ α) (⊢T : Δ ⊢ T type)
    → ⊇⊢ (Γ ∙ T) (Ψ ∙ T) (keep α T)
  weak : ∀ {α T} (⊢α : ⊇⊢ Γ Ψ α) (⊢T : Δ ⊢ T type)
    → ⊇⊢ (Γ ∙ T) Ψ (weak α T)


syntax ⊇⊢ Γ Ψ α = α ∶ Γ ⊇ Ψ


abstract
  α∶Γ⊇Ψ→⊢Γ : α ∶ Γ ⊇ Ψ → Δ ⊢ Γ ctx
  α∶Γ⊇Ψ→⊢Γ ([] ⊢Δ) = [] ⊢Δ
  α∶Γ⊇Ψ→⊢Γ (keep ⊢α ⊢T) = Snoc (α∶Γ⊇Ψ→⊢Γ ⊢α) ⊢T
  α∶Γ⊇Ψ→⊢Γ (weak ⊢α ⊢T) = Snoc (α∶Γ⊇Ψ→⊢Γ ⊢α) ⊢T


  α∶Γ⊇Ψ→⊢Ψ : α ∶ Γ ⊇ Ψ → Δ ⊢ Ψ ctx
  α∶Γ⊇Ψ→⊢Ψ ([] ⊢Δ) = [] ⊢Δ
  α∶Γ⊇Ψ→⊢Ψ (keep ⊢α ⊢T) = Snoc (α∶Γ⊇Ψ→⊢Ψ ⊢α) ⊢T
  α∶Γ⊇Ψ→⊢Ψ (weak ⊢α ⊢T) = α∶Γ⊇Ψ→⊢Ψ ⊢α


sub⊇ : (σ : SC.Sub Δ Ω) → Γ ⊇ Ψ → Γ [ σ ] ⊇ Ψ [ σ ]
sub⊇ σ [] = []
sub⊇ σ (keep α T) = keep (sub⊇ σ α) (T [ σ ])
sub⊇ σ (weak α T) = weak (sub⊇ σ α) (T [ σ ])


sub-syntax-⊇ = sub⊇

syntax sub-syntax-⊇ σ α = α [ σ ]α


sub⊇-resp-⊢ : ∀ {σ α} → σ ∶ Δ ⇒ Ω → α ∶ Γ ⊇ Ψ → sub⊇ σ α ∶ Γ [ σ ] ⊇ Ψ [ σ ]
sub⊇-resp-⊢ ⊢σ ([] ⊢Δ) = [] (SC.σ∶Δ⇒Ω→⊢Δ ⊢σ)
sub⊇-resp-⊢ ⊢σ (keep ⊢α ⊢T) = keep (sub⊇-resp-⊢ ⊢σ ⊢α) ([]-resp-⊢ ⊢T ⊢σ)
sub⊇-resp-⊢ ⊢σ (weak ⊢α ⊢T) = weak (sub⊇-resp-⊢ ⊢σ ⊢α) ([]-resp-⊢ ⊢T ⊢σ)


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
    : α ∶ Γ ⊇ Ψ
    → Δ , Ψ ⊢ₓ x ∶ T
    → Δ , Γ ⊢ₓ renV α x ∶ T
  renV-resp-⊢ₓ (keep ⊢α ⊢T) (zero ⊢Ψ ⊢T₀) = zero (α∶Γ⊇Ψ→⊢Γ ⊢α) ⊢T
  renV-resp-⊢ₓ (keep ⊢α ⊢T) (suc ⊢x ⊢T₀) = suc (renV-resp-⊢ₓ ⊢α ⊢x) ⊢T
  renV-resp-⊢ₓ (weak ⊢α ⊢T) ⊢x = suc (renV-resp-⊢ₓ ⊢α ⊢x) ⊢T


  ren-resp-⊢
    : α ∶ Γ ⊇ Ψ
    → Δ , Ψ ⊢ t ∶ T
    → Δ , Γ ⊢ ren α t ∶ T
  ren-resp-⊢ ⊢α (var x ⊢x) = var _ (renV-resp-⊢ₓ ⊢α ⊢x)
  ren-resp-⊢ ⊢α (abs T t ⊢t)
    = abs T _ (ren-resp-⊢ (keep ⊢α (Δ⊢Γ∙T→Δ⊢T (⊢t→⊢Γ ⊢t))) ⊢t)
  ren-resp-⊢ ⊢α (app t u ⊢t ⊢u) = app _ _ (ren-resp-⊢ ⊢α ⊢t) (ren-resp-⊢ ⊢α ⊢u)
  ren-resp-⊢ ⊢α (absₛ n T t ⊢n ⊢Γ ⊢t refl)
    = absₛ _ _ _ ⊢n (α∶Γ⊇Ψ→⊢Γ ⊢α) (ren-resp-⊢ (sub⊇-resp-⊢ (SC.Wk⊢ ⊢n) ⊢α) ⊢t)
        refl
  ren-resp-⊢ ⊢α (appₛ t m m<n ⊢m ⊢t p) = appₛ _ _ m<n ⊢m (ren-resp-⊢ ⊢α ⊢t) p
  ren-resp-⊢ ⊢α (zero n<⋆ ⊢n ⊢Ψ) = zero n<⋆ ⊢n (α∶Γ⊇Ψ→⊢Γ ⊢α)
  ren-resp-⊢ ⊢α (suc n<⋆ m<n ⊢n ⊢i) = suc n<⋆ m<n ⊢n (ren-resp-⊢ ⊢α ⊢i)
  ren-resp-⊢ ⊢α (cons n<⋆ ⊢i ⊢is)
    = cons n<⋆ (ren-resp-⊢ ⊢α ⊢i) (ren-resp-⊢ ⊢α ⊢is)
  ren-resp-⊢ ⊢α (head n<⋆ ⊢is) = head n<⋆ (ren-resp-⊢ ⊢α ⊢is)
  ren-resp-⊢ ⊢α (tail n<⋆ m<n ⊢m ⊢is) = tail n<⋆ m<n ⊢m (ren-resp-⊢ ⊢α ⊢is)
  ren-resp-⊢ ⊢α (caseNat n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat n<⋆ (ren-resp-⊢ ⊢α ⊢i) (ren-resp-⊢ ⊢α ⊢z) (ren-resp-⊢ ⊢α ⊢s) p
  ren-resp-⊢ ⊢α (fix n<⋆ ⊢n ⊢t p q) = fix n<⋆ ⊢n (ren-resp-⊢ ⊢α ⊢t) p q


Id⊇ : (Γ : Ctx Δ) → Γ ⊇ Γ
Id⊇ [] = []
Id⊇ (Γ ∙ T) = keep (Id⊇ Γ) T


abstract
  Id⊇⊢ : Δ ⊢ Γ ctx → Id⊇ Γ ∶ Γ ⊇ Γ
  Id⊇⊢ ([] ⊢Δ) = [] ⊢Δ
  Id⊇⊢ (Snoc ⊢Γ ⊢T) = keep (Id⊇⊢ ⊢Γ) ⊢T


Wk⊇ : ∀ (Γ : Ctx Δ) T → Γ ∙ T ⊇ Γ
Wk⊇ Γ T = weak (Id⊇ Γ) _


abstract
  Wk⊇⊢ : Δ ⊢ Γ ctx → Δ ⊢ T type → Wk⊇ Γ T ∶ Γ ∙ T ⊇ Γ
  Wk⊇⊢ ⊢Γ ⊢T = weak (Id⊇⊢ ⊢Γ) ⊢T


data Sub {Δ} (Γ : Ctx Δ) : (Ψ : Ctx Δ) → Set where
  [] : Sub Γ []
  Snoc : (ν : Sub Γ Ψ) (t : Term Δ) → Sub Γ (Ψ ∙ T)


variable ν φ : Sub Γ Ψ


data Sub⊢ {Δ} (Γ : Ctx Δ) : ∀ Ψ → Sub Γ Ψ → Set where
  [] : (⊢Γ : Δ ⊢ Γ ctx) → Sub⊢ Γ [] []
  Snoc : (⊢ν : Sub⊢ Γ Ψ ν) (⊢t : Δ , Γ ⊢ t ∶ T) → Sub⊢ Γ (Ψ ∙ T) (Snoc ν t)


syntax Sub⊢ Γ Ψ ν = ν ∶ Γ ⇛ Ψ


abstract
  ν∶Γ⇛Ψ→⊢Γ : ν ∶ Γ ⇛ Ψ → Δ ⊢ Γ ctx
  ν∶Γ⇛Ψ→⊢Γ ([] ⊢Γ) = ⊢Γ
  ν∶Γ⇛Ψ→⊢Γ (Snoc ⊢ν ⊢t) = ν∶Γ⇛Ψ→⊢Γ ⊢ν


  ν∶Γ⇛Ψ→⊢Ψ : ν ∶ Γ ⇛ Ψ → Δ ⊢ Ψ ctx
  ν∶Γ⇛Ψ→⊢Ψ ([] ⊢Γ) = [] (Δ⊢Γ→⊢Δ ⊢Γ)
  ν∶Γ⇛Ψ→⊢Ψ (Snoc ⊢ν ⊢t) = Snoc (ν∶Γ⇛Ψ→⊢Ψ ⊢ν) (⊢t→⊢T ⊢t)


Weaken : Sub Γ Ψ → Sub (Γ ∙ T) Ψ
Weaken [] = []
Weaken {Γ = Γ} {T = T} (Snoc ν t) = Snoc (Weaken ν) (ren (Wk⊇ Γ T) t)


abstract
  Weaken⊢ : ν ∶ Γ ⇛ Ψ → Δ ⊢ T type → Weaken ν ∶ Γ ∙ T ⇛ Ψ
  Weaken⊢ ([] ⊢Γ) ⊢T = [] (Snoc ⊢Γ ⊢T)
  Weaken⊢ (Snoc ⊢ν ⊢t) ⊢T
    = Snoc (Weaken⊢ ⊢ν ⊢T) (ren-resp-⊢ (Wk⊇⊢ (ν∶Γ⇛Ψ→⊢Γ ⊢ν) ⊢T) ⊢t)


Keep : Sub Γ Ψ → ∀ T → Sub (Γ ∙ T) (Ψ ∙ T)
Keep σ T = Snoc (Weaken σ) (var zero)


abstract
  Keep⊢ : ν ∶ Γ ⇛ Ψ → Δ ⊢ T type → Keep ν T ∶ Γ ∙ T ⇛ Ψ ∙ T
  Keep⊢ ⊢ν ⊢T = Snoc (Weaken⊢ ⊢ν ⊢T) (var zero (zero (ν∶Γ⇛Ψ→⊢Γ ⊢ν) ⊢T))


Id : Sub Γ Γ
Id {Γ = []} = []
Id {Γ = Γ ∙ T} = Keep Id T


abstract
  Id⊢ : Δ ⊢ Γ ctx → Id ∶ Γ ⇛ Γ
  Id⊢ ([] ⊢Δ) = [] ([] ⊢Δ)
  Id⊢ (Snoc ⊢Γ ⊢T) = Keep⊢ (Id⊢ ⊢Γ) ⊢T


Wk : Sub (Γ ∙ T) Γ
Wk = Weaken Id


abstract
  Wk⊢ : Δ ⊢ Γ ctx → Δ ⊢ T type → Wk ∶ Γ ∙ T ⇛ Γ
  Wk⊢ ⊢Γ ⊢T = Weaken⊢ (Id⊢ ⊢Γ) ⊢T


Fill : ∀ (Γ : Ctx Δ) T → Term Δ → Sub Γ (Γ ∙ T)
Fill Γ T t = Snoc Id t


abstract
  Fill⊢ : Δ , Γ ⊢ t ∶ T → Fill Γ T t ∶ Γ ⇛ Γ ∙ T
  Fill⊢ ⊢t = Snoc (Id⊢ (⊢t→⊢Γ ⊢t)) ⊢t


subν : (σ : SC.Sub Δ Ω) → Sub Γ Ψ → Sub (Γ [ σ ]) (Ψ [ σ ])
subν σ [] = []
subν σ (Snoc ν t) = Snoc (subν σ ν) (t [ σ ]ₛ)


abstract
  subν-resp-⊢ : ∀ {σ} → σ ∶ Δ ⇒ Ω → ν ∶ Γ ⇛ Ψ → subν σ ν ∶ Γ [ σ ] ⇛ Ψ [ σ ]
  subν-resp-⊢ ⊢σ ([] ⊢Γ) = [] ([]-resp-⊢ ⊢Γ ⊢σ)
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
  subV-resp-⊢ (Snoc ⊢ν ⊢t) (zero p q) = ⊢t
  subV-resp-⊢ (Snoc ⊢ν ⊢t) (suc ⊢x p) = subV-resp-⊢ ⊢ν ⊢x


  sub-resp-⊢
    : ν ∶ Γ ⇛ Ψ
    → Δ , Ψ ⊢ t ∶ T
    → Δ , Γ ⊢ sub ν t ∶ T
  sub-resp-⊢ ⊢ν (var x ⊢x)
    = subV-resp-⊢ ⊢ν ⊢x
  sub-resp-⊢ ⊢ν (abs T t ⊢t)
    = abs _ _ (sub-resp-⊢ (Keep⊢ ⊢ν (Δ⊢Γ∙T→Δ⊢T (⊢t→⊢Γ ⊢t))) ⊢t)
  sub-resp-⊢ ⊢ν (app t u ⊢t ⊢u)
    = app _ _ (sub-resp-⊢ ⊢ν ⊢t) (sub-resp-⊢ ⊢ν ⊢u)
  sub-resp-⊢ ⊢ν (absₛ n T t ⊢n ⊢Γ ⊢t refl)
    = absₛ _ _ _ ⊢n (ν∶Γ⇛Ψ→⊢Γ ⊢ν)
        (sub-resp-⊢ (subν-resp-⊢ (SC.Wk⊢ ⊢n) ⊢ν) ⊢t) refl
  sub-resp-⊢ ⊢ν (appₛ t m m<n ⊢m ⊢t p)
    = appₛ _ _ m<n ⊢m (sub-resp-⊢ ⊢ν ⊢t) p
  sub-resp-⊢ ⊢ν (zero n<⋆ ⊢n ⊢Γ)
    = zero n<⋆ ⊢n (ν∶Γ⇛Ψ→⊢Γ ⊢ν)
  sub-resp-⊢ ⊢ν (suc n<⋆ m<n ⊢n ⊢i)
    = suc n<⋆ m<n ⊢n (sub-resp-⊢ ⊢ν ⊢i)
  sub-resp-⊢ ⊢ν (cons n<⋆ ⊢i ⊢is)
    = cons n<⋆ (sub-resp-⊢ ⊢ν ⊢i) (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (head n<⋆ ⊢is)
    = head n<⋆ (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (tail n<⋆ m<n ⊢m ⊢is)
    = tail n<⋆ m<n ⊢m (sub-resp-⊢ ⊢ν ⊢is)
  sub-resp-⊢ ⊢ν (caseNat n<⋆ ⊢i ⊢z ⊢s p)
    = caseNat n<⋆ (sub-resp-⊢ ⊢ν ⊢i) (sub-resp-⊢ ⊢ν ⊢z) (sub-resp-⊢ ⊢ν ⊢s) p
  sub-resp-⊢ ⊢ν (fix n<⋆ ⊢n ⊢t p q)
    = fix n<⋆ ⊢n (sub-resp-⊢ ⊢ν ⊢t) p q
