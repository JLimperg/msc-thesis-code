module LamST.Type where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; ∃ ; Σ-syntax ; ∃-syntax ; _×_ ; _,_)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as ≡ using
  (_≡_ ; refl; module ≡-Reasoning ; sym ; trans ; cong ; cong₂ ; subst)

open import LamST.Size


infixr 7 _⇒_
infix  7 Π_,_


-- Types.
data Ty Δ : Set where
  ℕ : (i : Si Δ) → Ty Δ
  _⇒_ : (T U : Ty Δ) → Ty Δ
  Π_,_ : (n : Si∞ Δ) (T : Ty (Δ ∷ n)) → Ty Δ


variable
  T U : Ty Δ


-- Equality introduction for Π n , T.
Π-≡⁺ : {T : Ty (Δ ∷ n)} {U : Ty (Δ ∷ m)}
  → (p : n ≡ m)
  → subst (λ z → Ty (Δ ∷ z)) p T ≡ U
  → Π n , T ≡ Π m , U
Π-≡⁺ refl refl = refl


-- Renaming for types.
renTy : (θ : Δ ⊇ Δ′) (T : Ty Δ′) → Ty Δ
renTy θ (ℕ i) = ℕ (renSi θ i)
renTy θ (T ⇒ U) = renTy θ T ⇒ renTy θ U
renTy θ (Π n , T) = Π renSi∞ θ n , renTy (lift θ refl) T


-- Substitution for types.
subTy : (σ : SS Δ Δ′) (T : Ty Δ′) → Ty Δ
subTy σ (ℕ i) = ℕ (subSi σ i)
subTy σ (T ⇒ U) = subTy σ T ⇒ subTy σ U
subTy σ (Π n , T) = Π subSi∞ σ n , subTy (liftS σ refl) T


-- Substituting with a renaming is the same as renaming.
subTy-⊇→SS : ∀ (θ : Δ ⊇ Δ′) T → subTy (⊇→SS θ) T ≡ renTy θ T
subTy-⊇→SS θ (ℕ i) = cong ℕ (subSi-⊇→SS θ i)
subTy-⊇→SS θ (T ⇒ U) = cong₂ _⇒_ (subTy-⊇→SS θ T) (subTy-⊇→SS θ U)
subTy-⊇→SS {Δ = Δ} θ (Π n , T)
  = Π-≡⁺ (subSi∞-⊇→SS θ n) (go (subSi∞-⊇→SS θ n) refl refl)
  where
    go
      : {m m′ : Si∞ Δ}
      → (p : m ≡ m′) (q : subSi∞ (⊇→SS θ) n ≡ m) (r : renSi∞ θ n ≡ m′)
      → subst (λ z → Ty (Δ ∷ z)) p (subTy (liftS (⊇→SS θ) q) T) ≡
        renTy (lift θ r) T
    go refl q r
      = ≡.trans (≡.cong (λ z → subTy z T) liftS-cong) (subTy-⊇→SS (lift θ r) T)


-- Type contexts.
data TC Δ : Set where
  [] : TC Δ
  _∷_ : (Γ : TC Δ) (T : Ty Δ) → TC Δ


variable
  Γ Γ′ Γ″ : TC Δ


mapTC : (Ty Δ → Ty Δ′) → TC Δ → TC Δ′
mapTC f [] = []
mapTC f (Γ ∷ T) = mapTC f Γ ∷ f T


subTC : (σ : SS Δ Δ′) → TC Δ′ → TC Δ
subTC σ Γ = mapTC (subTy σ) Γ
