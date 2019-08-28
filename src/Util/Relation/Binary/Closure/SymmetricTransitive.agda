{-# OPTIONS --without-K --safe #-}
module Util.Relation.Binary.Closure.SymmetricTransitive where

open import Relation.Binary using (Rel)

open import Util.Prelude


data SymTrans {α ρ} {A : Set α} (R : Rel A ρ) : Rel A (α ⊔ℓ ρ) where
  `base : ∀ {x y} → R x y → SymTrans R x y
  `sym : ∀ {x y} → SymTrans R y x → SymTrans R x y
  `trans : ∀ {x y z} → SymTrans R x y → SymTrans R y z → SymTrans R x z
