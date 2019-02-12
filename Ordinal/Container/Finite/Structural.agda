{-# OPTIONS --allow-unsolved-metas #-}
module Ordinal.Container.Finite.Structural where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat as ℕ using
  (ℕ ; zero ; suc) renaming
  (_≤_ to _≤ℕ_)
open import Data.Product using (∃-syntax ; Σ-syntax ; _,_ ; proj₁ ; proj₂)
open import Function using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; inspect ; [_])

open import Ordinal using
  (sup ; _≤_ ; refl ; lt ; predL; pred-not-≤) renaming
  (Tree to Ordinal ; embℕ to ℕ→Ordinal)
open import Util.Container.Finite
open import Util.Relation.Binary.Closure.SymmetricTransitive using (SymTrans ; `base ; `sym ; `trans)
open import Util.Vec using (All₂-tabulate⁺ ; All₂-tabulate⁻)

infix 4 _≈_


Mu : (α : Ordinal) (ℂ : Container) → Set
Mu (sup I f) ℂ = ∃[ i ] ⟦ ℂ ⟧ (Mu (f i) ℂ)


monMu : ∀{ℂ α β} (α≤β : α ≤ β) → Mu α ℂ → Mu β ℂ
monMu refl = id
monMu {α = sup I f} (lt i α≤β) (_ , x) = i , map (monMu (predL α≤β)) x


monMuℕ : ∀ {ℂ n m}
  → n ℕ.≤ m
  → Mu (ℕ→Ordinal n) ℂ
  → Mu (ℕ→Ordinal m) ℂ
monMuℕ ℕ.z≤n (() , _)
monMuℕ (ℕ.s≤s n≤m) (_ , s) = _ , map (monMuℕ n≤m) s


_≈_ : ∀ {α ℂ} (t t′ : Mu α ℂ) → Set
_≈_ {sup I f} = SymTrans λ where
  (i , t) (j , u) →
    let β = f i
        γ = f j in
    Σ[ β≤γ ∈ β ≤ γ ] liftEq _≈_ (map (monMu β≤γ) t) u


--------------------------------------------------------------------------------
-- Properties of equality

≈-refl : ∀ {α ℂ} {t : Mu α ℂ} → t ≈ t
≈-refl {sup I f} {ℂ} {i , t}
  = `base (refl , (refl , All₂-tabulate⁺ (λ _ → ≈-refl)))


--------------------------------------------------------------------------------
-- Properties of monMuℕ

monMuℕ-mono : ∀ {ℂ n m} {n≤m : n ≤ℕ m} {x y : Mu (ℕ→Ordinal n) ℂ}
  → x ≈ y
  → monMuℕ n≤m x ≈ monMuℕ n≤m y
monMuℕ-mono {ℂ} {.0} {m} {ℕ.z≤n} {() , _} {y} eq
monMuℕ-mono {ℂ} {suc n} {suc m} {ℕ.s≤s n≤m} {_ , sh , pos} {_ , sh′ , pos′} (`base (n≤n , refl , eq))
  = `base (refl , refl , All₂-tabulate⁺ (λ x → monMuℕ-mono {!!}))
monMuℕ-mono {ℂ} {.(suc _)} {.(suc _)} {ℕ.s≤s n≤m} {x} {y} (`sym eq) = {!!}
monMuℕ-mono {ℂ} {.(suc _)} {.(suc _)} {ℕ.s≤s n≤m} {x} {y} (`trans eq eq₁) = {!!}


--------------------------------------------------------------------------------
-- Properties of monMu

monMu-id : ∀ {ℂ α} {α≤α : α ≤ α} {x : Mu α ℂ}
  → monMu α≤α x ≈ x
monMu-id {ℂ} {α} {refl} {x} = ≈-refl
monMu-id {ℂ} {sup I f} {lt i α≤α} {j , sh , pos} = `base ({!!} , {!!})


monMu-mono : ∀ {ℂ α β} {α≤β : α ≤ β} {x y : Mu α ℂ}
  → x ≈ y
  → monMu α≤β x ≈ monMu α≤β y
monMu-mono {ℂ} {sup I f} {sup .I .f} {refl} {i , _ , pos} {j , _ , pos′} eq = eq
monMu-mono {ℂ} {sup I f} {sup J g} {lt i α≤β} {j , _ , pos} {k , _ , pos′} (`base (fj≤fk , refl , eq)) = `base (refl , refl , (All₂-tabulate⁺ (λ x → {!All₂-tabulate⁻ eq x!})))
monMu-mono {ℂ} {sup I f} {β} {α≤β} {x} {y} (`sym eq) = {!!}
monMu-mono {ℂ} {sup I f} {β} {α≤β} {x} {y} (`trans eq eq₁) = {!!}


monMu-irr : ∀ {ℂ α β} {α≤β₁ α≤β₂ : α ≤ β} {x y : Mu α ℂ}
  → monMu α≤β₁ x ≈ monMu α≤β₂ x
monMu-irr {ℂ} {α} {.α} {refl} {refl} {x} {y} = ≈-refl
monMu-irr {ℂ} {.(sup _ _)} {.(sup _ _)} {refl} {lt i α≤β₂} {j , sh , pos} {j' , sh' , pos'} = ⊥-elim (pred-not-≤ α≤β₂)
monMu-irr {ℂ} {sup .J .g} {sup J g} {lt i α≤β₁} {refl} {j , sh , pos} {k , sh′ , pos′} = `base ({!!} , refl , {!!})
monMu-irr {ℂ} {sup I f} {sup J g} {lt i α≤β₁} {lt i₁ α≤β₂} {j , sh , pos} {k , sh′ , pos′} = `base ({!!} , {!!} , {!!})
