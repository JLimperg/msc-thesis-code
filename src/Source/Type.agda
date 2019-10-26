{-# OPTIONS --without-K --safe #-}
module Source.Type where

open import Source.Size as S using
  ( Size ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; p ; b )
open import Source.Size.Substitution.Canonical as SC using
  ( Sub⊢ )
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Universe as SU using
  ( σ ; τ ; ι ; ⟨_⟩ )
open import Util.Prelude

open S.Ctx


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


data Ctx (Δ : S.Ctx) : Set where
  [] : Ctx Δ
  _∙_ : (Γ : Ctx Δ) (T : Type Δ) → Ctx Δ


variable Γ Γ′ Γ″ Ψ Ψ′ Ψ″ : Ctx Δ


sub : SC.Sub Δ Ω → Type Ω → Type Δ
sub σ (Nat n) = Nat (SC.sub σ n)
sub σ (Stream n) = Stream (SC.sub σ n)
sub σ (T ⇒ U) = sub σ T ⇒ sub σ U
sub σ (Π n , T) = Π SC.sub σ n , sub (SC.Keep σ) T


abstract
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
  SubTheory-Type : SubTheory Type (λ {Δ} n → ⊤)
  SubTheory-Type = record
    { _[_] = λ T σ → sub σ T
    ; [Id] = sub-Id
    ; [>>] = sub->>
    }


subΓ : SC.Sub Δ Ω → Ctx Ω → Ctx Δ
subΓ σ [] = []
subΓ σ (Γ ∙ T) = subΓ σ Γ ∙ sub σ T


abstract
  subΓ->> : ∀ (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) Γ
    → subΓ (σ SC.>> τ) Γ ≡ subΓ σ (subΓ τ Γ)
  subΓ->> σ τ [] = refl
  subΓ->> σ τ (Γ ∙ T) = cong₂ _∙_ (subΓ->> σ τ Γ) (sub->> σ τ T)


  subΓ-Id : (Γ : Ctx Δ) → subΓ SC.Id Γ ≡ Γ
  subΓ-Id [] = refl
  subΓ-Id (Γ ∙ T) = cong₂ _∙_ (subΓ-Id Γ) (sub-Id T)


instance
  SubTheory-Ctx : SubTheory Ctx (λ {Δ} Γ → ⊤)
  SubTheory-Ctx = record
    { _[_] = λ Γ σ → subΓ σ Γ
    ; [Id] = subΓ-Id
    ; [>>] = subΓ->>
    }
