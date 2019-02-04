module Axioms where

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B}
    → (∀ x → f x ≡ g x)
    → f ≡ g
