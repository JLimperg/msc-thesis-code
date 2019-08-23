module Source.Term where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b ; v0
  ; v1 ; sub-syntax-Size)
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; sub-syntax-Type
  ; sub-syntax-Ctx )
open import Util.Prelude hiding (id ; _∘_)

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
  zero suc cons head tail : Term Δ
  caseNat : (T : Type Δ) → Term Δ
  fix : (T : Type (Δ ∙ ⋆)) → Term Δ


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
    : ∀ n T t
    → Δ ∙ n , Γ [ S.Wk ]Γ ⊢ t ∶ T
    → Δ , Γ ⊢ Λₛ n , t ∶ Π n , T
  appₛ
    : ∀ t m (m<n : m < n)
    → Δ , Γ ⊢ t ∶ (Π n , T)
    → Δ , Γ ⊢ t ·ₛ m ∶ T [ S.Fill m m<n ]T
  zero
    : Δ , Γ ⊢ zero ∶ Π ⋆ , Nat v0
  suc
    : Δ , Γ ⊢ suc ∶ Π ⋆ , Π v0 , Nat v0 ⇒ Nat v1
  cons
    : Δ , Γ ⊢ cons ∶ Π ⋆ , Nat ∞ ⇒ (Π v0 , Stream v0) ⇒ Stream v0
  head
    : Δ , Γ ⊢ head ∶ Π ⋆ , Stream v0 ⇒ Nat ∞
  tail
    : Δ , Γ ⊢ tail ∶ Π ⋆ , Stream v0 ⇒ (Π v0 , Stream v0)
  caseNat
    : (T : Type Δ)
    → Δ , Γ ⊢ caseNat T
      ∶ Π ⋆ ,
          Nat v0 ⇒
          T [ S.Wk ]T ⇒
          (Π v0 , Nat v0 ⇒ T [ S.Wk S.>> S.Wk ]T) ⇒
          T [ S.Wk ]T
  fix
    : (T : Type (Δ ∙ ⋆))
    → Δ , Γ ⊢ fix T ∶ (Π ⋆ , (Π v0 , T [ S.Skip ]T) ⇒ T) ⇒ (Π ⋆ , T)


subₛ : (σ : S.Sub Δ Ω) → Term Ω → Term Δ
subₛ σ (var x) = var x
subₛ σ (Λ T , t) = Λ T [ σ ]T , subₛ σ t
subₛ σ (t · u) = subₛ σ t · subₛ σ u
subₛ σ (Λₛ n , t) = Λₛ n [ σ ]n , subₛ (S.Keep′ σ) t
subₛ σ (t ·ₛ m) = subₛ σ t ·ₛ (m [ σ ]n)
subₛ σ zero = zero
subₛ σ suc = suc
subₛ σ cons = cons
subₛ σ head = head
subₛ σ tail = tail
subₛ σ (caseNat T) = caseNat (T [ σ ]T)
subₛ σ (fix T) = fix (T [ S.Keep′ σ ]T)


sub-syntax-Termₛ = subₛ


syntax sub-syntax-Termₛ σ t = t [ σ ]tₛ


subₛ-resp-⊢ₓ : (σ : S.Sub Δ Ω)
  → Ω , Γ ⊢ₓ x ∶ T
  → Δ , Γ [ σ ]Γ ⊢ₓ x ∶ T [ σ ]T
subₛ-resp-⊢ₓ σ zero = zero
subₛ-resp-⊢ₓ σ (suc p) = suc (subₛ-resp-⊢ₓ σ p)


subₛ-resp-⊢ : (σ : S.Sub Δ Ω)
  → Ω , Γ ⊢ t ∶ T
  → Δ , Γ [ σ ]Γ ⊢ t [ σ ]tₛ ∶ T [ σ ]T
subₛ-resp-⊢ σ (var x p) = var x (subₛ-resp-⊢ₓ σ p)
subₛ-resp-⊢ σ (abs T t x) = abs _ _ (subₛ-resp-⊢ σ x)
subₛ-resp-⊢ σ (app t u x y) = app _ _ (subₛ-resp-⊢ σ x) (subₛ-resp-⊢ σ y)
subₛ-resp-⊢ {Δ} {Γ = Γ} σ (absₛ n T t x)
  = absₛ (n [ σ ]n) (T [ S.Keep′ σ ]T) _
      (subst (λ Γ → Δ ∙ n [ σ ]n , Γ ⊢ t [ S.Keep σ refl ]tₛ ∶ T [ S.Keep′ σ ]T)
        (T.subΓ->>′ S.Keep>>Wk Γ)
        (subₛ-resp-⊢ (S.Keep′ σ) x))
subₛ-resp-⊢ {Δ} {Γ = Γ}σ (appₛ {T = T} t m m<n x)
  = subst (λ T → Δ , Γ [ σ ]Γ ⊢ (t [ σ ]tₛ) ·ₛ (m [ σ ]n) ∶ T)
      (T.sub->>′ (S.Fill>>Keep′ m<n _) T)
      (appₛ (t [ σ ]tₛ) (m [ σ ]n) (S.sub-resp-< σ m<n) (subₛ-resp-⊢ σ x))
subₛ-resp-⊢ σ zero = zero
subₛ-resp-⊢ σ suc = suc
subₛ-resp-⊢ σ cons = cons
subₛ-resp-⊢ σ head = head
subₛ-resp-⊢ σ tail = tail
subₛ-resp-⊢ {Δ} {Γ = Γ} σ (caseNat T)
  = subst (λ U → Δ , Γ [ σ ]Γ ⊢ caseNat T [ σ ]tₛ ∶ Π ⋆ , Nat v0 ⇒ U)
      (cong₂ _⇒_
        (T.sub->>′ (sym S.Keep>>Wk) T)
        (cong₂ (λ U V → (Π v0 , Nat v0 ⇒ U) ⇒ V)
          (T.sub->>′ go T)
          (T.sub->>′ (sym S.Keep>>Wk) T)))
      (caseNat (T [ σ ]T))
  where
    go : S.Wk S.>> S.Wk S.>> σ
       ≡ S.Keep′ (S.Keep′ σ) S.>> (S.Wk S.>> S.Wk)
    go = let open ≡-Reasoning in sym (
      begin
        S.Keep′ (S.Keep′ σ) S.>> (S.Wk S.>> S.Wk)
      ≡⟨ S.>>-assoc ⟩
        (S.Keep′ (S.Keep′ σ) S.>> S.Wk) S.>> S.Wk
      ≡⟨ cong (S._>> S.Wk) S.Keep>>Wk ⟩
        (S.Wk S.>> S.Keep′ σ) S.>> S.Wk
      ≡⟨ sym S.>>-assoc ⟩
        S.Wk S.>> (S.Keep′ σ S.>> S.Wk)
      ≡⟨ cong (S.Wk S.>>_) S.Keep>>Wk ⟩
        S.Wk S.>> (S.Wk S.>> σ)
      ≡⟨ S.>>-assoc ⟩
        S.Wk S.>> S.Wk S.>> σ
      ∎)
subₛ-resp-⊢ {Δ} {Γ = Γ} σ (fix T)
  = subst
      (λ U → Δ , Γ [ σ ]Γ ⊢ fix (T [ S.Keep′ σ ]T)
        ∶ (Π ⋆ , (Π v0 , U) ⇒ T [ S.Keep′ σ ]T) ⇒ (Π ⋆ , T [ S.Keep′ σ ]T))
      (T.sub->>′ S.Skip>>Keep′ T)
      (fix (T [ S.Keep′ σ ]T))


data _⊇_ {Δ} : (Γ Ψ : Ctx Δ) → Set where
  [] : [] ⊇ []
  keep : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ ∙ T
  weak : (α : Γ ⊇ Ψ) (T : Type Δ) → Γ ∙ T ⊇ Ψ


variable α β γ : Γ ⊇ Ψ


sub⊇ₛ : (σ : S.Sub Δ Ω) → Γ ⊇ Ψ → Γ [ σ ]Γ ⊇ Ψ [ σ ]Γ
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
ren α (Λₛ n , t) = Λₛ n , ren (α [ S.Wk ]α) t
ren α (t ·ₛ m) = ren α t ·ₛ m
ren α zero = zero
ren α suc = suc
ren α cons = cons
ren α head = head
ren α tail = tail
ren α (caseNat T) = caseNat T
ren α (fix T) = fix T


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
ren-resp-⊢ α (absₛ n T t ⊢t) = absₛ _ _ _ (ren-resp-⊢ (α [ S.Wk ]α) ⊢t)
ren-resp-⊢ α (appₛ t m m<n ⊢t) = appₛ _ _ _ (ren-resp-⊢ α ⊢t)
ren-resp-⊢ α zero = zero
ren-resp-⊢ α suc = suc
ren-resp-⊢ α cons = cons
ren-resp-⊢ α head = head
ren-resp-⊢ α tail = tail
ren-resp-⊢ α (caseNat T) = caseNat T
ren-resp-⊢ α (fix T) = fix T


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


subₛS : (σ : S.Sub Δ Ω) → Sub Γ Ψ → Sub (Γ [ σ ]Γ) (Ψ [ σ ]Γ)
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
sub ν (Λₛ n , t) = Λₛ n , sub (ν [ S.Wk ]νₛ) t
sub ν (t ·ₛ m) = sub ν t ·ₛ m
sub ν zero = zero
sub ν suc = suc
sub ν cons = cons
sub ν head = head
sub ν tail = tail
sub ν (caseNat T) = caseNat T
sub ν (fix T) = fix T


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
sub-resp-⊢ ν (absₛ n T t ⊢t) = absₛ _ _ _ (sub-resp-⊢ (ν [ S.Wk ]νₛ) ⊢t)
sub-resp-⊢ ν (appₛ t m m<n ⊢t) = appₛ _ _ _ (sub-resp-⊢ ν ⊢t)
sub-resp-⊢ ν zero = zero
sub-resp-⊢ ν suc = suc
sub-resp-⊢ ν cons = cons
sub-resp-⊢ ν head = head
sub-resp-⊢ ν tail = tail
sub-resp-⊢ ν (caseNat T) = caseNat T
sub-resp-⊢ ν (fix T) = fix T
