{-# OPTIONS --without-K #-}
module Util.HoTT.Univalence where

open import Util.HoTT.Equiv

import Util.HoTT.Univalence.Consequences as Consequences


postulate
  univalence : ∀ {α} {A B : Set α} → IsEquiv (≡→≃ {A = A} {B = B})


open Consequences univalence public
