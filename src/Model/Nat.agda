{-# OPTIONS --without-K #-}
module Model.Nat where

open import Model.Size as MS using
  ( Size ; _≤_ ; _<_ ; ≤-prop ) renaming
  ( SizesRG to Sizes )
open import Model.Type.Core
open import Util.HoTT.HLevel
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁺)

import Data.Nat.Properties as ℕ

open Size


ℕ≤ : Size → Set
ℕ≤ n = ∃[ m ] (nat m ≤ n)


ℕ≤-IsSet : ∀ {n} → IsSet (ℕ≤ n)
ℕ≤-IsSet = Σ-IsSet ℕ.≡-irrelevant (λ m → IsOfHLevel-suc 1 ≤-prop)


abstract
  ℕ≤-≡⁺ : ∀ {n} {m m′} (m≤n : nat m ≤ n) (m′≤n : nat m′ ≤ n)
    → m ≡ m′
    → (m , m≤n) ≡ (m′ , m′≤n)
  ℕ≤-≡⁺ _ _ m≡m′ = Σ-≡⁺ (m≡m′ , ≤-prop _ _)


Nat : ⟦Type⟧ Sizes
Nat = record
  { ObjHSet = λ n → HLevel⁺ (ℕ≤ n) ℕ≤-IsSet
  ; eqHProp = λ { _ (n , _) (m , _) → HLevel⁺ (n ≡ m) ℕ.≡-irrelevant }
  ; eq-refl = λ _ → refl
  }


castℕ≤ : ∀ {n m} → n ≤ m → ℕ≤ n → ℕ≤ m
castℕ≤ n≤m (k , k≤n) = k , go
  where abstract go = MS.≤-trans k≤n n≤m


zero≤ : ∀ n → ℕ≤ n
zero≤ n = 0 , MS.0≤n


suc≤ : ∀ n m → m < n → ℕ≤ m → ℕ≤ n
suc≤ n m m<n (x , x≤m) = suc x , MS.n<m→Sn≤m (MS.≤→<→< x≤m m<n)


caseℕ≤ : ∀ {α} {A : Set α} {n}
  → ℕ≤ n
  → A
  → (∀ m → m < n → ℕ≤ m → A)
  → A
caseℕ≤ (zero , _) z s = z
caseℕ≤ (suc x , Sx≤n) z s = s (nat x) (MS.Sn≤m→n<m Sx≤n) (x , MS.≤-refl)
