{-# OPTIONS --allow-unsolved-metas #-}
module Ordinal.Tree.Container.Finite.Wellfounded where

open import Data.Nat as ℕ using () renaming (_≤_ to _≤ℕ_)
open import Relation.Binary using (Rel)

open import Ordinal.Tree as Ord using
  (sup ; _≤_ ; refl ; lt ; predL; pred-not-≤) renaming
  (Tree to Ordinal ; embℕ to ℕ→Ordinal)
open import Util.Container.Finite
open import Util.Prelude
open import Util.Relation.Binary.Closure.SymmetricTransitive using
  (SymTrans ; `base ; `sym ; `trans)
open import Util.Vec using (All₂-tabulate⁺ ; All₂-tabulate⁻)

infix 4 _≈_


Mu : (α : Ordinal) (ℂ : Container) → Set
Mu α ℂ = Ord.Mu^ ⟦ ℂ ⟧ α


monMu : ∀ {ℂ α β} (α≤β : α ≤ β) → Mu α ℂ → Mu β ℂ
monMu {ℂ} = Ord.monMu^ ⟦ ℂ ⟧


_≈_ : ∀ {α ℂ} (t t′ : Mu α ℂ) → Set
_≈_ {α} {ℂ} = Ord.EqMu^ ⟦ ℂ ⟧ map liftEq


--------------------------------------------------------------------------------
-- Properties of equality

≈-refl : ∀ {α ℂ} {t : Mu α ℂ} → t ≈ t
≈-refl {α} {ℂ} {t} = Ord.fix go α t
  where
    go : Ord.Rec (λ α → (t : Mu α ℂ) → t ≈ t)
    go rec t
      = `base (refl , refl , ?)


--------------------------------------------------------------------------------
-- Properties of monMu

monMu-id : ∀ {ℂ α} {α≤α : α ≤ α} {x : Mu α ℂ}
  → monMu α≤α x ≡ x
monMu-id {ℂ} = Ord.monMu^-id ⟦ ℂ ⟧


monMu-mono : ∀ {ℂ α β} {α≤β : α ≤ β} {x y : Mu α ℂ}
  → x ≈ y
  → monMu α≤β x ≈ monMu α≤β y
monMu-mono = {!!}


monMu-irr : ∀ {ℂ α β} {α≤β₁ α≤β₂ : α ≤ β} {x y : Mu α ℂ}
  → monMu α≤β₁ x ≈ monMu α≤β₂ x
monMu-irr = {!!}
