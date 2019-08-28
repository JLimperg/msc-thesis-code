{-# OPTIONS --without-K --safe #-}
module Util.Vec where

open import Data.Vec public
open import Data.Vec.All as All public using (All ; [] ; _∷_)
open import Data.Vec.Any as Any public using (Any ; here ; there)
open import Data.Vec.Membership.Propositional public using (_∈_)

open import Data.Nat as ℕ using (_≤_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)

open import Util.Prelude

import Data.Nat.Properties as ℕ


max : ∀ {n} → Vec ℕ n → ℕ
max = foldr _ ℕ._⊔_ 0


max-weaken : ∀ {n} x (xs : Vec ℕ n) → max xs ≤ max (x ∷ xs)
max-weaken _ _ = ℕ.n≤m⊔n _ _


max-maximal : ∀ {n} (xs : Vec ℕ n) → All (_≤ max xs) xs
max-maximal [] = []
max-maximal (x ∷ xs)
  = ℕ.m≤m⊔n _ _
  ∷ All.map (λ x≤max → ℕ.≤-trans x≤max (max-weaken x xs)) (max-maximal xs)


All→∈→P : ∀ {α β} {A : Set α} {P : A → Set β} {n} {xs : Vec A n}
  → All P xs
  → ∀ {x}
  → x ∈ xs
  → P x
All→∈→P (px ∷ allP) (here refl) = px
All→∈→P (px ∷ allP) (there x∈xs) = All→∈→P allP x∈xs


max-maximal-∈ : ∀ {n x} {xs : Vec ℕ n} → x ∈ xs → x ≤ max xs
max-maximal-∈ = All→∈→P (max-maximal _)


data All₂ {α} {A : Set α} {ρ} (R : Rel A ρ)
  : ∀ {n} → Vec A n → Vec A n → Set (α ⊔ ρ) where
  [] : All₂ R [] []
  _∷_ : ∀ {n x y} {xs ys : Vec A n}
    → R x y
    → All₂ R xs ys
    → All₂ R (x ∷ xs) (y ∷ ys)


All₂-tabulate⁺ : ∀ {α} {A : Set α} {ρ} {R : Rel A ρ} {n} {f g : Fin n → A}
  → (∀ x → R (f x) (g x))
  → All₂ R (tabulate f) (tabulate g)
All₂-tabulate⁺ {n = zero} p = []
All₂-tabulate⁺ {n = suc n} p = p zero ∷ All₂-tabulate⁺ (λ x → p (suc x))


All₂-tabulate⁻ : ∀ {α} {A : Set α} {ρ} {R : Rel A ρ} {n} {f g : Fin n → A}
  → All₂ R (tabulate f) (tabulate g)
  → ∀ x → R (f x) (g x)
All₂-tabulate⁻ [] ()
All₂-tabulate⁻ (fzRgz ∷ all) zero = fzRgz
All₂-tabulate⁻ (fzRgz ∷ all) (suc x) = All₂-tabulate⁻ all x
