{-# OPTIONS --without-K --safe #-}
module Util.Data.Product where

open import Data.Product public hiding (map₂)


map₂ : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (∀ a → B a → C a)
  → Σ A B → Σ A C
map₂ f (a , b) = a , f a b
