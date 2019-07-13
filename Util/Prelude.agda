{-# OPTIONS --without-K #-}
module Util.Prelude where

open import Data.Bool public using
  (Bool ; true ; false)
open import Data.Empty public using
  (⊥ ; ⊥-elim)
open import Data.Fin public using
  (Fin ; zero ; suc)
open import Data.List public using
  (List ; [] ; _∷_)
open import Data.Maybe public using
  (Maybe ; just ; nothing)
open import Data.Nat public using
  (ℕ ; zero ; suc)
open import Data.Product public using
  (Σ ; ∃ ; Σ-syntax ; ∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum public using
  (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit public using
  (⊤)
open import Data.Vec public using
  (Vec ; [] ; _∷_)
open import Function public using
  (id ; _∘_ ; _∘′_ ; _$_)
open import Level public using
  (Level ; 0ℓ; Lift ; lift ; lower) renaming
  (zero to lzero ; suc to lsuc ; _⊔_ to _⊔ℓ_)
open import Relation.Binary.PropositionalEquality public using
  (_≡_ ; refl ; sym ; trans ; cong ; subst ; module ≡-Reasoning)
