{-# OPTIONS --without-K --safe #-}
module Source.Term where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b ; v0
  ; v1 )
open import Source.Size.Substitution.Universe as SU using
  ( sub-syntax-Size ; ⟨_⟩ )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; sub-syntax-Type
  ; sub-syntax-Ctx )
open import Util.Prelude hiding (id ; _∘_)

import Source.Size.Substitution.Canonical as SC

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type


infix 0 _,_⊢_∶_ _,_⊢ₓ_∶_
infix  3 _⊇_
infixl 5 sub-syntax-Termₛ sub-syntax-⊇ₛ sub-syntax-Term sub-syntax-Subₛ
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
    : Δ , Γ ⊢ₓ x ∶ T
    → Δ , Γ ∙ U ⊢ₓ suc x ∶ T


data _,_⊢_∶_ : ∀ Δ (Γ : Ctx Δ) (t : Term Δ) (T : Type Δ) → Set where
  var
    : (x : Var)
    → Δ , Γ ⊢ₓ x ∶ T
    → Δ , Γ ⊢ var x ∶ T
  abs
    : ∀ T t
    → Δ , Γ ∙ T ⊢ t ∶ U
    → Δ , Γ ⊢ Λ T , t ∶ T ⇒ U
  app
    : ∀ t u
    → Δ , Γ ⊢ t ∶ T ⇒ U
    → Δ , Γ ⊢ u ∶ T
    → Δ , Γ ⊢ t · u ∶ U
  absₛ
    : ∀ n {Ψ : Ctx (Δ ∙ n)} T t
    → Δ ∙ n , Ψ ⊢ t ∶ T
    → Ψ ≡ Γ [ SU.Wk ]Γ
    → Δ , Γ ⊢ Λₛ n , t ∶ Π n , T
  appₛ
    : ∀ t m (m<n : m < n)
    → Δ , Γ ⊢ t ∶ (Π n , T)
    → U ≡ T [ SU.Fill m m<n ]T
    → Δ , Γ ⊢ t ·ₛ m ∶ U
  zero
    : n < ⋆
    → Δ , Γ ⊢ zero n ∶ Nat n
  suc
    : n < ⋆
    → m < n
    → Δ , Γ ⊢ i ∶ Nat m
    → Δ , Γ ⊢ suc n m i ∶ Nat n
  cons
    : n < ⋆
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → Δ , Γ ⊢ cons i n is ∶ Stream n
  head
    : n < ⋆
    → Δ , Γ ⊢ is ∶ Stream n
    → Δ , Γ ⊢ head n is ∶ Nat ∞
  tail
    : n < ⋆
    → m < n
    → Δ , Γ ⊢ is ∶ Stream n
    → Δ , Γ ⊢ tail n is m ∶ Stream m
  caseNat
    : n < ⋆
    → Δ , Γ ⊢ i ∶ Nat n
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ U
    → U ≡ T [ SU.Wk ]T
    → Δ , Γ ⊢ caseNat T n i z s ∶ T
  fix
    : (n<⋆ : n < ⋆)
    → Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , U) ⇒ T
    → U ≡ T [ SU.Skip ]T
    → V ≡ T [ SU.Fill n n<⋆ ]T
    → Δ , Γ ⊢ fix T t n ∶ V


-- This is a special case of subst.
cast⊢Γ : ∀ {Δ Γ Ψ t T}
  → Γ ≡ Ψ
  → Δ , Γ ⊢ t ∶ T
  → Δ , Ψ ⊢ t ∶ T
cast⊢Γ refl ⊢t = ⊢t


subₛ : (σ : SU.Sub Δ Ω) → Term Ω → Term Δ
subₛ σ (var x) = var x
subₛ σ (Λ T , t) = Λ T [ σ ]T , subₛ σ t
subₛ σ (t · u) = subₛ σ t · subₛ σ u
subₛ σ (Λₛ n , t) = Λₛ n [ σ ]n , subₛ (SU.Keep′ σ) t
subₛ σ (t ·ₛ m) = subₛ σ t ·ₛ (m [ σ ]n)
subₛ σ (zero n) = zero (n [ σ ]n)
subₛ σ (suc n m i) = suc (n [ σ ]n) (m [ σ ]n) (subₛ σ i)
subₛ σ (cons i n is) = cons (subₛ σ i) (n [ σ ]n) (subₛ σ is)
subₛ σ (head n is) = head (n [ σ ]n) (subₛ σ is)
subₛ σ (tail n is m) = tail (n [ σ ]n) (subₛ σ is) (m [ σ ]n)
subₛ σ (caseNat T n i z s)
  = caseNat (T [ σ ]T) (n [ σ ]n) (subₛ σ i) (subₛ σ z) (subₛ σ s)
subₛ σ (fix T t n) = fix (T [ SU.Keep′ σ ]T) (subₛ σ t) (n [ σ ]n)


sub-syntax-Termₛ = subₛ


syntax sub-syntax-Termₛ σ t = t [ σ ]tₛ


subₛ-resp-⊢ₓ : (σ : SU.Sub Δ Ω)
  → Ω , Γ ⊢ₓ x ∶ T
  → Δ , Γ [ σ ]Γ ⊢ₓ x ∶ T [ σ ]T
subₛ-resp-⊢ₓ σ zero = zero
subₛ-resp-⊢ₓ σ (suc p) = suc (subₛ-resp-⊢ₓ σ p)


subₛ-resp-⊢ : (σ : SU.Sub Δ Ω)
  → Ω , Γ ⊢ t ∶ T
  → Δ , Γ [ σ ]Γ ⊢ t [ σ ]tₛ ∶ T [ σ ]T
subₛ-resp-⊢ σ (var x ⊢x) = var x (subₛ-resp-⊢ₓ σ ⊢x)
subₛ-resp-⊢ σ (abs T t ⊢t) = abs _ _ (subₛ-resp-⊢ σ ⊢t)
subₛ-resp-⊢ σ (app t u ⊢t ⊢u) = app _ _ (subₛ-resp-⊢ σ ⊢t) (subₛ-resp-⊢ σ ⊢u)
subₛ-resp-⊢ {Δ} {Γ = Γ} σ (absₛ n {Ψ = Ψ} T t ⊢t p)
  = absₛ (n [ σ ]n) (T [ SU.Keep′ σ ]T) _ (subₛ-resp-⊢ (SU.Keep′ σ) ⊢t) eq
  module subₛ-resp-⊢-absₛ where
    abstract
      eq : Ψ [ SU.Keep′ σ ]Γ ≡ Γ [ σ ]Γ [ SU.Wk ]Γ
      eq = trans (cong (λ Ψ → Ψ [ SU.Keep′ σ ]Γ) p)
        (T.subΓ->>′ (SU.≈⁺ SC.Keep>>Wk) Γ)
subₛ-resp-⊢ {Δ} {Γ = Γ} σ (appₛ {T = T} {U = U} t m m<n ⊢t p)
  = appₛ (t [ σ ]tₛ) (m [ σ ]n) (SU.sub-resp-< σ m<n) (subₛ-resp-⊢ σ ⊢t) eq
  module subₛ-resp-⊢-appₛ where
    abstract
      eq : U [ σ ]T ≡ T [ SU.Keep′ σ ]T [ SU.Fill (m [ σ ]n) (SU.sub-resp-< σ m<n) ]T
      eq = trans (cong (λ U → U [ σ ]T) p)
        (T.sub->>′ (SU.≈⁺ (sym (SC.Fill>>Keep′ m<n _))) T)
subₛ-resp-⊢ σ (zero n<⋆) = zero (SU.sub-resp-< σ n<⋆)
subₛ-resp-⊢ σ (suc n<⋆ m<n ⊢t)
  = suc (SU.sub-resp-< σ n<⋆) (SU.sub-resp-< σ m<n) (subₛ-resp-⊢ σ ⊢t)
subₛ-resp-⊢ σ (cons n<⋆ ⊢i ⊢is)
  = cons (SU.sub-resp-< σ n<⋆) (subₛ-resp-⊢ σ ⊢i) (subₛ-resp-⊢ σ ⊢is)
subₛ-resp-⊢ σ (head n<⋆ ⊢is) = head (SU.sub-resp-< σ n<⋆) (subₛ-resp-⊢ σ ⊢is)
subₛ-resp-⊢ σ (tail n<⋆ m<n ⊢is)
  = tail (SU.sub-resp-< σ n<⋆) (SU.sub-resp-< σ m<n) (subₛ-resp-⊢ σ ⊢is)
subₛ-resp-⊢ σ (caseNat {n = n} {T = T} {U = U} n<⋆ ⊢i ⊢z ⊢s p)
  = caseNat (SU.sub-resp-< σ n<⋆) (subₛ-resp-⊢ σ ⊢i) (subₛ-resp-⊢ σ ⊢z)
      (subₛ-resp-⊢ σ ⊢s) eq
  module subₛ-resp-⊢-caseNat where
    abstract
      eq : U [ SU.Keep′ σ ]T ≡ T [ σ ]T [ SU.Wk ]T
      eq = trans (cong (λ U → U [ SU.Keep′ σ ]T) p) (T.sub->>′ (SU.≈⁺ SC.Keep>>Wk) T)
subₛ-resp-⊢ σ (fix {n = n} {U = U} {T = T} {V = V} n<⋆ ⊢t p q)
  = fix (SU.sub-resp-< σ n<⋆) (subₛ-resp-⊢ σ ⊢t) eq₀ eq₁
  module subₛ-resp-⊢-fix where
    abstract
      eq₀ : U [ SU.Keep′ (SU.Keep′ σ) ]T ≡ T [ SU.Keep′ σ ]T [ SU.Skip ]T
      eq₀ = trans (cong (λ U → U [ SU.Keep′ (SU.Keep′ σ) ]T) p)
        (T.sub->>′ (SU.≈⁺ SC.Keep′Keep′>>Skip) T)

      eq₁ : V [ σ ]T ≡ T [ SU.Keep′ σ ]T [ SU.Fill (n [ σ ]n) (SU.sub-resp-< σ n<⋆) ]T
      eq₁ = trans (cong (λ V → V [ σ ]T) q)
        (T.sub->>′ (SU.≈⁺ (sym (SC.Fill>>Keep′ n<⋆ (SU.sub-resp-< σ n<⋆)))) T)


data _⊇_ {Δ} : (Γ Ψ : Ctx Δ) → Set where
  [] : [] ⊇ []
  keep : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ ∙ T
  weak : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ


variable α β γ : Γ ⊇ Ψ


sub⊇ₛ : (σ : SU.Sub Δ Ω) → Γ ⊇ Ψ → Γ [ σ ]Γ ⊇ Ψ [ σ ]Γ
sub⊇ₛ σ [] = []
sub⊇ₛ σ (keep α T) = keep (sub⊇ₛ σ α) (T.sub σ T)
sub⊇ₛ σ (weak α T) = weak (sub⊇ₛ σ α) (T.sub σ T)


sub-syntax-⊇ₛ = sub⊇ₛ


syntax sub-syntax-⊇ₛ σ α = α [ σ ]α


renV : Γ ⊇ Ψ → Var → Var
renV [] x = x -- impossible if x is well-scoped
renV (keep α T) zero = zero
renV (keep α T) (suc x) = suc (renV α x)
renV (weak α T) x = suc (renV α x)


ren : {Γ Ψ : Ctx Δ} → Γ ⊇ Ψ → Term Δ → Term Δ
ren α (var x) = var (renV α x)
ren α (Λ T , t) = Λ T , ren (keep α T) t
ren α (t · u) = ren α t · ren α u
ren α (Λₛ n , t) = Λₛ n , ren (α [ SU.Wk ]α) t
ren α (t ·ₛ m) = ren α t ·ₛ m
ren α (zero n) = zero n
ren α (suc n m i) = suc n m (ren α i)
ren α (cons i n is) = cons (ren α i) n (ren α is)
ren α (head n is) = head n (ren α is)
ren α (tail n is m) = tail n (ren α is) m
ren α (caseNat T n i z s) = caseNat T n (ren α i) (ren α z) (ren α s)
ren α (fix T t n) = fix T (ren α t) n


renV-resp-⊢ₓ
  : (α : Γ ⊇ Ψ)
  → Δ , Ψ ⊢ₓ x ∶ T
  → Δ , Γ ⊢ₓ renV α x ∶ T
renV-resp-⊢ₓ (keep α T) zero = zero
renV-resp-⊢ₓ (keep α T) (suc p) = suc (renV-resp-⊢ₓ α p)
renV-resp-⊢ₓ (weak α T) p = suc (renV-resp-⊢ₓ α p)


ren-resp-⊢
  : (α : Γ ⊇ Ψ)
  → Δ , Ψ ⊢ t ∶ T
  → Δ , Γ ⊢ ren α t ∶ T
ren-resp-⊢ α (var x ⊢x) = var _ (renV-resp-⊢ₓ α ⊢x)
ren-resp-⊢ α (abs T t ⊢t) = abs T _ (ren-resp-⊢ (keep α T) ⊢t)
ren-resp-⊢ α (app t u ⊢t ⊢u) = app _ _ (ren-resp-⊢ α ⊢t) (ren-resp-⊢ α ⊢u)
ren-resp-⊢ α (absₛ n T t ⊢t refl) = absₛ _ _ _ (ren-resp-⊢ (α [ SU.Wk ]α) ⊢t) refl
ren-resp-⊢ α (appₛ t m m<n ⊢t refl) = appₛ _ _ _ (ren-resp-⊢ α ⊢t) refl
ren-resp-⊢ α (zero n<⋆) = zero n<⋆
ren-resp-⊢ α (suc n<⋆ m<n ⊢i) = suc n<⋆ m<n (ren-resp-⊢ α ⊢i)
ren-resp-⊢ α (cons n<⋆ ⊢i ⊢is) = cons n<⋆ (ren-resp-⊢ α ⊢i) (ren-resp-⊢ α ⊢is)
ren-resp-⊢ α (head n<⋆ ⊢is) = head n<⋆ (ren-resp-⊢ α ⊢is)
ren-resp-⊢ α (tail n<⋆ m<n ⊢is) = tail n<⋆ m<n (ren-resp-⊢ α ⊢is)
ren-resp-⊢ α (caseNat n<⋆ ⊢i ⊢z ⊢s p)
  = caseNat n<⋆ (ren-resp-⊢ α ⊢i) (ren-resp-⊢ α ⊢z) (ren-resp-⊢ α ⊢s) p
ren-resp-⊢ α (fix n<⋆ ⊢t p q) = fix n<⋆ (ren-resp-⊢ α ⊢t) p q


Id⊇ : Γ ⊇ Γ
Id⊇ {Γ = []} = []
Id⊇ {Γ = Γ ∙ T} = keep Id⊇ T


Wk⊇ : Γ ∙ T ⊇ Γ
Wk⊇ = weak Id⊇ _


data Sub {Δ} (Γ : Ctx Δ) : (Ψ : Ctx Δ) → Set where
  [] : Sub Γ []
  snoc : (ν : Sub Γ Ψ) (t : Term Δ)
    → Δ , Γ ⊢ t ∶ T
    → Sub Γ (Ψ ∙ T)


variable ν φ : Sub Γ Ψ


Weaken : Sub Γ Ψ → Sub (Γ ∙ T) Ψ
Weaken [] = []
Weaken {Γ = Γ} {Ψ} {T} (snoc ν t ⊢t)
  = snoc (Weaken ν) (ren Wk⊇ t) (ren-resp-⊢ Wk⊇ ⊢t)


Keep : Sub Γ Ψ → ∀ T → Sub (Γ ∙ T) (Ψ ∙ T)
Keep σ T = snoc (Weaken σ) (var zero) (var _ zero)


Id : Sub Γ Γ
Id {Γ = []} = []
Id {Γ = Γ ∙ T} = Keep Id T


Wk : Sub (Γ ∙ T) Γ
Wk = Weaken Id


Fill : (t : Term Δ) → Δ , Γ ⊢ t ∶ T → Sub Γ (Γ ∙ T)
Fill t p = snoc Id t p


subₛS : (σ : SU.Sub Δ Ω) → Sub Γ Ψ → Sub (Γ [ σ ]Γ) (Ψ [ σ ]Γ)
subₛS σ [] = []
subₛS σ (snoc ν t p) = snoc (subₛS σ ν) (subₛ σ t) (subₛ-resp-⊢ σ p)


sub-syntax-Subₛ = subₛS


syntax sub-syntax-Subₛ σ ν = ν [ σ ]νₛ


subV : Sub {Δ} Γ Ψ → Var → Term Δ
subV [] x = var x -- impossible if x is well-scoped
subV (snoc ν t p) zero = t
subV (snoc ν t p) (suc x) = subV ν x


sub : Sub {Δ} Γ Ψ → Term Δ → Term Δ
sub ν (var x) = subV ν x
sub ν (Λ T , t) = Λ T , sub (Keep ν T) t
sub ν (t · u) = sub ν t · sub ν u
sub ν (Λₛ n , t) = Λₛ n , sub (ν [ SU.Wk ]νₛ) t
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


subV-resp-⊢ : (ν : Sub Γ Ψ)
  → Δ , Ψ ⊢ₓ x ∶ T
  → Δ , Γ ⊢ subV ν x ∶ T
subV-resp-⊢ (snoc ν t ⊢t) zero = ⊢t
subV-resp-⊢ (snoc ν t ⊢t) (suc ⊢x) = subV-resp-⊢ ν ⊢x


sub-resp-⊢ : (ν : Sub Γ Ψ)
  → Δ , Ψ ⊢ t ∶ T
  → Δ , Γ ⊢ sub ν t ∶ T
sub-resp-⊢ ν (var x ⊢x) = subV-resp-⊢ ν ⊢x
sub-resp-⊢ ν (abs T t ⊢t) = abs _ _ (sub-resp-⊢ (Keep ν T) ⊢t)
sub-resp-⊢ ν (app t u ⊢t ⊢u) = app _ _ (sub-resp-⊢ ν ⊢t) (sub-resp-⊢ ν ⊢u)
sub-resp-⊢ ν (absₛ n T t ⊢t refl)
  = absₛ _ _ _ (sub-resp-⊢ (ν [ SU.Wk ]νₛ) ⊢t) refl
sub-resp-⊢ ν (appₛ t m m<n ⊢t refl) = appₛ _ _ _ (sub-resp-⊢ ν ⊢t) refl
sub-resp-⊢ ν (zero n<⋆) = zero n<⋆
sub-resp-⊢ ν (suc n<⋆ m<n ⊢i) = suc n<⋆ m<n (sub-resp-⊢ ν ⊢i)
sub-resp-⊢ ν (cons n<⋆ ⊢i ⊢is) = cons n<⋆ (sub-resp-⊢ ν ⊢i) (sub-resp-⊢ ν ⊢is)
sub-resp-⊢ ν (head n<⋆ ⊢is) = head n<⋆ (sub-resp-⊢ ν ⊢is)
sub-resp-⊢ ν (tail n<⋆ m<n ⊢is) = tail n<⋆ m<n (sub-resp-⊢ ν ⊢is)
sub-resp-⊢ ν (caseNat n<⋆ ⊢i ⊢z ⊢s p)
  = caseNat n<⋆ (sub-resp-⊢ ν ⊢i) (sub-resp-⊢ ν ⊢z) (sub-resp-⊢ ν ⊢s) p
sub-resp-⊢ ν (fix n<⋆ ⊢t p q) = fix n<⋆ (sub-resp-⊢ ν ⊢t) p q
