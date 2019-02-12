{-# OPTIONS --allow-unsolved-metas #-}
module Examples where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Ordinal using
  (sup ; _<_ ; _≤_ ; refl ; lt) renaming
  (Tree to Ordinal ; tomega to ω ; embℕ to ℕ→Ordinal)

import Util.Container.Finite as ContainerFin
import Ordinal.Container.Finite.Structural as OrdinalFin

module Nat where

  open ContainerFin
  open OrdinalFin


  Natℂ : Container
  Natℂ = S ▷ P
    module Natℂ where
      data S : Set where
        zero suc : S

      P : S → ℕ
      P zero = 0
      P suc = 1


  Nat : Set
  Nat = Mu ω Natℂ


  fwd : (n : ℕ) → Mu (ℕ→Ordinal (suc n)) Natℂ
  fwd zero = _ , Natℂ.zero , λ()
  fwd (suc x) = _ , Natℂ.suc , λ _ → fwd x


  fwd′ : ℕ → Nat
  fwd′ n = monMu (lt (suc n) refl) (fwd n)


  bwd : ∀ {α} → Mu α Natℂ → ℕ
  bwd {sup I f} (i , Natℂ.zero , pos) = zero
  bwd {sup I f} (i , Natℂ.suc , pos) = suc (bwd (pos zero))


  bwd∘fwd : ∀ {n} → bwd (fwd n) ≡ n
  bwd∘fwd {zero} = refl
  bwd∘fwd {suc n} rewrite bwd∘fwd {n} = refl


  -- Not true due to 'intensional' ≤.
  bwd-≤ : ∀ {α} {x : Mu α Natℂ} → ℕ→Ordinal (suc (bwd x)) ≤ α
  bwd-≤ {sup I f} {i , Natℂ.zero , pos} = {!!}
  bwd-≤ {sup I f} {i , Natℂ.suc , pos} = {!bwd-≤ {x = pos zero}!}


  fwd∘bwd : ∀ {α} {x : Mu α Natℂ} → monMu bwd-≤ (fwd (bwd x)) ≈ x
  fwd∘bwd {sup I f} {i , Natℂ.zero , pos} = {!!}
  fwd∘bwd {sup I f} {i , Natℂ.suc , pos} = {!!}
