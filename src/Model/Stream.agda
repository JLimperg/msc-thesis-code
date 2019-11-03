{-# OPTIONS --without-K #-}
module Model.Stream where

open import Model.Size as MS using
  ( Size ; Sizes ; _≤_ ; _<_ ; ≤-IsProp ; ≤-trans )
open import Model.Type.Core
open import Util.HoTT.HLevel
open import Util.HoTT.Univalence
open import Util.Prelude

import Data.Nat.Properties as ℕ

open Size


Colist : Size → Set
Colist n = ∀ m → nat m ≤ n → ℕ


abstract
  Colist-≡⁺ : ∀ {n} {xs ys : Colist n}
    → (∀ m m≤n → xs m m≤n ≡ ys m m≤n)
    → xs ≡ ys
  Colist-≡⁺ eq = funext λ m → funext λ m≤n → eq m m≤n


  Colist-≡⁻ : ∀ {n} {xs ys : Colist n}
    → xs ≡ ys
    → ∀ m m≤n₀ m≤n₁ → xs m m≤n₀ ≡ ys m m≤n₁
  Colist-≡⁻ {xs = xs} refl m m≤n₀ m≤n₁ = cong (xs m) (≤-IsProp _ _)


  Colist-IsSet : ∀ {n} → IsSet (Colist n)
  Colist-IsSet = ∀-IsSet λ m → ∀-IsSet λ m≤n → ℕ.≡-irrelevant


castColist : ∀ {n m} → n ≤ m → Colist m → Colist n
castColist n≤m xs k k≤n = xs k go
  where abstract go = ≤-trans k≤n n≤m


Stream : ⟦Type⟧ Sizes
Stream = record
  { ObjHSet = λ n → HLevel⁺ (Colist n) Colist-IsSet
  ; eqHProp = λ {n} {n′} _ xs ys
      → ∀-HProp ℕ λ m → ∀-HProp (nat m ≤ n) λ m≤n → ∀-HProp (nat m ≤ n′) λ m≤n′
      → HLevel⁺ (xs m m≤n ≡ ys m m≤n′) ℕ.≡-irrelevant
  ; eq-refl = λ x m m≤n m≤n′ → cong (x m) (≤-IsProp _ _)
  }


cons : ∀ {n} → ℕ → (∀ m → m < n → Colist m) → Colist n
cons x xs zero _ = x
cons x xs (suc k) Sk≤n = xs (nat k) go k MS.≤-refl
  where abstract go = MS.Sn≤m→n<m Sk≤n


head : ∀ {n} → Colist n → ℕ
head xs = xs 0 MS.0≤n


tail : ∀ {n} → Colist n → ∀ m → m < n → Colist m
tail xs m m<n k k≤m = xs (suc k) go
  where abstract go = MS.n<m→Sn≤m (MS.≤→<→< k≤m m<n)


abstract
  cons-≡⁺ : ∀ {n n′ i i′ is is′}
    → i ≡ i′
    → (∀ m (m<n : m < n) (m<n′ : m < n′) k k≤m
        → is m m<n k k≤m ≡ is′ m m<n′ k k≤m)
    → ∀ m m<n m<n′
    → cons i is m m<n ≡ cons i′ is′ m m<n′
  cons-≡⁺ i≡i′ is≡is′ zero m<n₀ m<n₁ = i≡i′
  cons-≡⁺ {is′ = is′} i≡i′ is≡is′ (suc m) m<n m<n′
    = trans (is≡is′ (nat m) (MS.Sn≤m→n<m m<n) (MS.Sn≤m→n<m m<n′) m MS.≤-refl)
        (cong (λ p → is′ _ p _ _) (MS.<-IsProp _ _))


  head-≡⁺ : ∀ {n n′ is is′}
    → (∀ m (m≤n : nat m ≤ n) (m≤n′ : nat m ≤ n′) → is m m≤n ≡ is′ m m≤n′)
    → head is ≡ head is′
  head-≡⁺ is≡is′ = is≡is′ 0 MS.0≤n MS.0≤n


  tail-≡⁺ : ∀ {n n′ is is′}
    → (∀ m (m≤n : nat m ≤ n) (m≤n′ : nat m ≤ n′)
        → is m m≤n ≡ is′ m m≤n′)
    → ∀ m m′ m<n m′<n′ k k≤m k≤m′
    → tail is m m<n k k≤m ≡ tail is′ m′ m′<n′ k k≤m′
  tail-≡⁺ {is′ = is′} is≡is′ m m′ m<n m′<n′ k k≤m k≤m′
    = trans (is≡is′ (suc k) _ (MS.n<m→Sn≤m (MS.≤→<→< k≤m′ m′<n′)))
        (cong (is′ (suc k)) (≤-IsProp _ _))
