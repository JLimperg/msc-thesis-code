{-# OPTIONS --without-K #-}
module Util.HoTT.Univalence.Statement where

open import Util.HoTT.Equiv
open import Util.Prelude


Univalence : ∀ α → Set (lsuc α)
Univalence α = {A B : Set α} → IsEquiv (≡→≃ {A = A} {B = B})
