module Model.Colist where

open import Data.Maybe using (Is-just ; Is-nothing)

import Data.Nat as ℕ
import Data.Nat.Properties as ℕ

open import Axioms using (funext)
open import Model.Size
open import Util.Prelude hiding (Size ; Size<_ ; ∞ ; ↑_)


private
  variable
    A : Set


Colist : Set → Size → Set
Colist A n = (m : ℕ) → nat m ≤ n → A


-- Equality of colists is extensional equality of functions.
_≈_ : ∀ {n} (xs ys : Colist A n) → Set
xs ≈ ys = ∀ m m≤n m≤n₀ → xs m m≤n ≡ ys m m≤n₀


-- Assuming functional extensionality, ≈ implies ≡.
≈→≡ : ∀ {n} {xs ys : Colist A n} → xs ≈ ys → xs ≡ ys
≈→≡ xs≈ys = funext λ m → funext λ m≤n → xs≈ys m m≤n m≤n


≈-refl : ∀ {n} (xs : Colist A n) → xs ≈ xs
≈-refl xs m p p′ = cong (xs m) ≤-prop


Colistₛ : Set → SizedType
Colistₛ A = record
  { Ty = Colist A
  ; down = down
  ; down-id = ≈→≡ ∘ down-id
  ; down-∘ = λ n≤m m≤o xs → ≈→≡ (down-∘ n≤m m≤o xs)
  }
  where
    down : ∀ {n m} → n ≤ m → Colist A m → Colist A n
    down n≤m xs k k≤m = xs k (≤-trans k≤m n≤m)


    down-id : ∀ {n} (xs : Colist A n) → down ≤-refl xs ≈ xs
    down-id xs k _ _ = ≈-refl xs k _ _


    down-∘ : ∀ {n m o} (n≤m : n ≤ m) (m≤o : m ≤ o) (xs : Colist A o)
      → down (≤-trans n≤m m≤o) xs ≈ down n≤m (down m≤o xs)
    down-∘ n≤m m≤o xs k _ _ = ≈-refl xs k _ _


head : ∀ {n} → Colist A n → A
head xs = xs 0 0≤n


tail : ∀ {n} → Colist A n → ⟦∀⟧ n (Colistₛ A)
tail xs = record
  { arr = λ m m<n k k≤m → xs (suc k) (n<m→n+1≤m (≤→<→< k≤m m<n))
  ; consistent = λ m<n m′<n m≤m′ → funext λ k → funext λ k′ → ≈-refl xs _ _ _
  }


cons : ∀ {n} → A → (⟦∀⟧ n (Colistₛ A)) → Colist A n
cons x xs zero m≤n = x
cons x xs (suc m) m+1≤n = ⟦∀⟧.arr xs (nat m) (n+1≤m→n<m m+1≤n) m (nat ℕ.≤-refl)


head-cons : ∀ {n} (x : A) (xs : ⟦∀⟧ n (Colistₛ A))
  → head (cons x xs) ≡ x
head-cons x xs = refl


tail-cons : ∀ {n m} (m<n : m < n) (x : A) (xs : ⟦∀⟧ n (Colistₛ A))
  → ⟦∀⟧.arr (tail (cons x xs)) m m<n ≈ ⟦∀⟧.arr xs m m<n
tail-cons {n = n} {m} m<n x xs k k≤m k≤m₀
  = trans (cong (λ f → f k ≤-refl) (⟦∀⟧.consistent xs _ m<n k≤m))
      (cong (⟦∀⟧.arr xs m m<n k) ≤-prop)
