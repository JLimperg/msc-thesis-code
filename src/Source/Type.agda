{-# OPTIONS --without-K --safe #-}
module Source.Type where

open import Source.Size as S using
  ( Size ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; p ; b ; ⊢_ ; _⊢_
  ; Δ⊢n→⊢Δ )
open import Source.Size.Substitution.Canonical as SC using
  ( Sub⊢ ; σ∶Δ⇒Ω→⊢Δ )
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Universe as SU using
  ( σ ; τ ; ι ; ⟨_⟩ )
open import Util.Prelude

open S.Ctx


infix  0 _⊢_type _⊢_ctx
infixr 3 Π_,_
infixr 4 _⇒_
infixl 4 _∙_


data Type (Δ : S.Ctx) : Set where
  Nat : (n : Size Δ) → Type Δ
  Stream : (n : Size Δ) → Type Δ
  _⇒_ : (T U : Type Δ) → Type Δ
  Π_,_ : (n : Size Δ) (T : Type (Δ ∙ n)) → Type Δ


variable T U V W T′ U′ V′ W′ : Type Δ


Π-≡⁺ : ∀ {n m} {T : Type (Δ ∙ n)} {U : Type (Δ ∙ m)}
  → (n≡m : n ≡ m)
  → subst (λ n → Type (Δ ∙ n)) n≡m T ≡ U
  → (Π n , T) ≡ (Π m , U)
Π-≡⁺ refl refl = refl


data _⊢_type Δ : Type Δ → Set where
  Nat : ∀ n (⊢n : Δ ⊢ n) → Δ ⊢ Nat n type
  Stream : ∀ n (⊢n : Δ ⊢ n) → Δ ⊢ Stream n type
  arr : ∀ T U (⊢T : Δ ⊢ T type) (⊢U : Δ ⊢ U type) → Δ ⊢ T ⇒ U type
  pi : ∀ n T (⊢n : Δ ⊢ n) (⊢T : Δ ∙ n ⊢ T type) → Δ ⊢ Π n , T type


abstract
  Δ⊢T→⊢Δ : Δ ⊢ T type → ⊢ Δ
  Δ⊢T→⊢Δ (Nat n ⊢n) = Δ⊢n→⊢Δ ⊢n
  Δ⊢T→⊢Δ (Stream n ⊢n) = Δ⊢n→⊢Δ ⊢n
  Δ⊢T→⊢Δ (arr T U ⊢T ⊢U) = Δ⊢T→⊢Δ ⊢T
  Δ⊢T→⊢Δ (pi n T ⊢n ⊢T) = Δ⊢n→⊢Δ ⊢n


data Ctx (Δ : S.Ctx) : Set where
  [] : Ctx Δ
  _∙_ : (Γ : Ctx Δ) (T : Type Δ) → Ctx Δ


variable Γ Γ′ Γ″ Ψ Ψ′ Ψ″ : Ctx Δ


data _⊢_ctx Δ : Ctx Δ → Set where
  [] : (⊢Δ : ⊢ Δ) → Δ ⊢ [] ctx
  Snoc : (⊢Γ : Δ ⊢ Γ ctx) (⊢T : Δ ⊢ T type) → Δ ⊢ Γ ∙ T ctx


abstract
  Δ⊢Γ→⊢Δ : Δ ⊢ Γ ctx → ⊢ Δ
  Δ⊢Γ→⊢Δ ([] ⊢Δ) = ⊢Δ
  Δ⊢Γ→⊢Δ (Snoc ⊢Γ ⊢T) = Δ⊢Γ→⊢Δ ⊢Γ


  Δ⊢Γ∙T→Δ⊢Γ : Δ ⊢ Γ ∙ T ctx → Δ ⊢ Γ ctx
  Δ⊢Γ∙T→Δ⊢Γ (Snoc ⊢Γ ⊢T) = ⊢Γ


  Δ⊢Γ∙T→Δ⊢T : Δ ⊢ Γ ∙ T ctx → Δ ⊢ T type
  Δ⊢Γ∙T→Δ⊢T (Snoc ⊢Γ ⊢T) = ⊢T


sub : SC.Sub Δ Ω → Type Ω → Type Δ
sub σ (Nat n) = Nat (SC.sub σ n)
sub σ (Stream n) = Stream (SC.sub σ n)
sub σ (T ⇒ U) = sub σ T ⇒ sub σ U
sub σ (Π n , T) = Π SC.sub σ n , sub (SC.Keep σ) T


abstract
  sub-resp-⊢ : ∀ {Δ Ω σ T} → σ ∶ Δ ⇒ Ω → Ω ⊢ T type → Δ ⊢ sub σ T type
  sub-resp-⊢ {σ = σ} ⊢σ (Nat n ⊢n) = Nat _ (SC.sub-resp-⊢ ⊢σ ⊢n)
  sub-resp-⊢ {σ = σ} ⊢σ (Stream n ⊢n) = Stream _ (SC.sub-resp-⊢ ⊢σ ⊢n)
  sub-resp-⊢ ⊢σ (arr T U ⊢T ⊢U)
    = arr _ _ (sub-resp-⊢ ⊢σ ⊢T) (sub-resp-⊢ ⊢σ ⊢U)
  sub-resp-⊢ ⊢σ (pi n T ⊢n ⊢T)
    = pi _ _ (SC.sub-resp-⊢ ⊢σ ⊢n) (sub-resp-⊢ (SC.Keep⊢ ⊢σ ⊢n refl) ⊢T)


  sub->> : ∀ {Δ Δ′ Δ″} (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) T
    → sub (σ SC.>> τ) T ≡ sub σ (sub τ T)
  sub->> σ τ (Nat n) = cong Nat (SC.sub->> n refl)
  sub->> σ τ (Stream n) = cong Stream (SC.sub->> n refl)
  sub->> σ τ (T ⇒ U) = cong₂ _⇒_ (sub->> σ τ T) (sub->> σ τ U)
  sub->> σ τ (Π n , T)
    rewrite SC.sub->> {σ = σ} {τ} n refl
    = cong (λ T → Π SC.sub σ (SC.sub τ n) , T)
        (trans (cong (λ σ → sub σ T) (sym SC.Keep>>Keep))
          (sub->> (SC.Keep σ) (SC.Keep τ) T))


  sub-Id : (T : Type Δ) → sub SC.Id T ≡ T
  sub-Id (Nat n) = cong Nat (SC.sub-Id n refl)
  sub-Id (Stream n) = cong Stream (SC.sub-Id n refl)
  sub-Id (T ⇒ U) = cong₂ _⇒_ (sub-Id T) (sub-Id U)
  sub-Id (Π n , T)
    rewrite SC.sub-Id n refl
    = cong (λ T → Π n , T) (sub-Id T)


instance
  SubTheory-Type : SubTheory Type (λ {Δ} n → Δ ⊢ n type)
  SubTheory-Type = record
    { _[_] = λ T σ → sub σ T
    ; []-resp-⊢ = λ ⊢T ⊢σ → sub-resp-⊢ ⊢σ ⊢T
    ; [Id] = sub-Id
    ; [>>] = sub->>
    }


subΓ : SC.Sub Δ Ω → Ctx Ω → Ctx Δ
subΓ σ [] = []
subΓ σ (Γ ∙ T) = subΓ σ Γ ∙ sub σ T


abstract
  subΓ-resp-⊢ : ∀ {Δ Ω σ Γ} → σ ∶ Δ ⇒ Ω → Ω ⊢ Γ ctx → Δ ⊢ subΓ σ Γ ctx
  subΓ-resp-⊢ ⊢σ ([] ⊢Δ) = [] (σ∶Δ⇒Ω→⊢Δ ⊢σ)
  subΓ-resp-⊢ ⊢σ (Snoc ⊢Γ ⊢T)
    = Snoc (subΓ-resp-⊢ ⊢σ ⊢Γ) (sub-resp-⊢ ⊢σ ⊢T)


  subΓ->> : ∀ (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) Γ
    → subΓ (σ SC.>> τ) Γ ≡ subΓ σ (subΓ τ Γ)
  subΓ->> σ τ [] = refl
  subΓ->> σ τ (Γ ∙ T) = cong₂ _∙_ (subΓ->> σ τ Γ) (sub->> σ τ T)


  subΓ-Id : (Γ : Ctx Δ) → subΓ SC.Id Γ ≡ Γ
  subΓ-Id [] = refl
  subΓ-Id (Γ ∙ T) = cong₂ _∙_ (subΓ-Id Γ) (sub-Id T)


instance
  SubTheory-Ctx : SubTheory Ctx (λ {Δ} Γ → Δ ⊢ Γ ctx)
  SubTheory-Ctx = record
    { _[_] = λ Γ σ → subΓ σ Γ
    ; []-resp-⊢ = λ ⊢Γ ⊢σ → subΓ-resp-⊢ ⊢σ ⊢Γ
    ; [Id] = subΓ-Id
    ; [>>] = subΓ->>
    }
