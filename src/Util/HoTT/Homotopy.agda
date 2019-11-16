{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Homotopy where

open import Relation.Binary using (IsEquivalence)

open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (cong-app)


module _ {α β} {A : Set α} {B : A → Set β} where

  _~_ : (f g : ∀ a → B a) → Set (α ⊔ℓ β)
  f ~ g = ∀ a → f a ≡ g a


  ~-refl : ∀ {f} → f ~ f
  ~-refl a = refl


  ~-sym : ∀ {f g} → f ~ g → g ~ f
  ~-sym f~g a = sym (f~g a)


  ~-trans : ∀ {f g h} → f ~ g → g ~ h → f ~ h
  ~-trans f~g g~h a = trans (f~g a) (g~h a)


  ~-IsEquivalence : IsEquivalence _~_
  ~-IsEquivalence = record { refl = ~-refl ; sym = ~-sym ; trans = ~-trans }


  ≡→~ : ∀ {f g} → f ≡ g → f ~ g
  ≡→~ = cong-app
