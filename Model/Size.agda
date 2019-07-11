module Model.Size where

open import Data.Nat as ℕ using (s≤s ; z≤n)

import Data.Nat.Properties as ℕ

open import Axioms using (funext)
open import Util.Prelude hiding (Size ; ∞ ; ↑_)


infixl 7 _⊓_
infix 4 _<_ _≤_ _>_ _≥_


data Size : Set where
  nat : (n : ℕ) → Size
  ∞ : Size


data _<_ : (n m : Size) → Set where
  nat : ∀ {n m} → n ℕ.< m → nat n < nat m
  ∞ : ∀ {n} → nat n < ∞


data _≤_ : (n m : Size) → Set where
  nat : ∀ {n m} → n ℕ.≤ m → nat n ≤ nat m
  ∞ : ∀ {n} → n ≤ ∞


≤-prop : ∀ {n m} {p q : n ≤ m} → p ≡ q
≤-prop {p = nat p} {nat q} = cong nat (ℕ.≤-irrelevant p q)
≤-prop {p = ∞} {∞} = refl


<-prop : ∀ {n m} {p q : n < m} → p ≡ q
<-prop {p = nat p} {nat q} = cong nat (ℕ.<-irrelevant p q)
<-prop {p = ∞} {∞} = refl


≤-refl : ∀ {n} → n ≤ n
≤-refl {nat n} = nat ℕ.≤-refl
≤-refl {∞} = ∞


_>_ : (n m : Size) → Set
n > m = m < n


_≥_ : (n m : Size) → Set
n ≥ m = m ≤ n


0≤n : ∀ {n} → nat 0 ≤ n
0≤n {nat n} = nat z≤n
0≤n {∞} = ∞


<→≤ : ∀ {n m} → n < m → n ≤ m
<→≤ (nat n<m) = nat (ℕ.<⇒≤ n<m)
<→≤ ∞ = ∞


≤-trans : ∀ {n m o} → n ≤ m → m ≤ o → n ≤ o
≤-trans (nat n≤m) (nat m≤o) = nat (ℕ.≤-trans n≤m m≤o)
≤-trans (nat n≤m) ∞ = ∞
≤-trans ∞ ∞ = ∞


≤→<→≤ : ∀ {n m o} → n ≤ m → m < o → n ≤ o
≤→<→≤ n≤m m<o = ≤-trans n≤m (<→≤ m<o)


≤→<→< : ∀ {n m o} → n ≤ m → m < o → n < o
≤→<→< (nat n≤m) (nat m<o) = nat (ℕ.<-transʳ n≤m m<o)
≤→<→< (nat n<o) ∞ = ∞


szero : Size
szero = nat 0


ssuc : ∀ {n} → n < ∞ → Size
ssuc {nat n} ∞ = nat (suc n)


ssuc′ : Size → Size
ssuc′ (nat n) = nat (suc n)
ssuc′ ∞ = ∞


Size→ℕ : ∀ {n} → n < ∞ → ℕ
Size→ℕ {nat n} (∞ {n}) = n


ssuc′-resp-≤ : ∀ {n m} → n ≤ m → ssuc′ n ≤ ssuc′ m
ssuc′-resp-≤ (nat n≤m) = nat (s≤s n≤m)
ssuc′-resp-≤ ∞ = ∞


n+1≤m→n<m : ∀ {n m} → nat (suc n) ≤ m → nat n < m
n+1≤m→n<m (nat n+1≤m) = nat n+1≤m
n+1≤m→n<m ∞ = ∞


n<m→n+1≤m : ∀ {n m} → n < m → ssuc′ n ≤ m
n<m→n+1≤m (nat n<m) = nat n<m
n<m→n+1≤m ∞ = ∞


_⊓_ : (n m : Size) → Size
nat n ⊓ nat m = nat (n ℕ.⊓ m)
nat n ⊓ ∞ = nat n
∞ ⊓ m = m


n⊓∞≡n : ∀ {n} → n ⊓ ∞ ≡ n
n⊓∞≡n {nat n} = refl
n⊓∞≡n {∞} = refl


n<o→n⊓m<o : ∀ {n} m {o} → n < o → n ⊓ m < o
n<o→n⊓m<o (nat m) (nat n<o) = nat (ℕ.m<n⇒m⊓o<n _ n<o)
n<o→n⊓m<o (nat m) ∞ = ∞
n<o→n⊓m<o ∞ (nat n<m) = nat n<m
n<o→n⊓m<o ∞ ∞ = ∞


nat⊓n<∞ : ∀ {i} n → nat i ⊓ n < ∞
nat⊓n<∞ {i} n = n<o→n⊓m<o n ∞


⊓-assoc : ∀ n m o → n ⊓ (m ⊓ o) ≡ n ⊓ m ⊓ o
⊓-assoc (nat n) (nat m) (nat o) = cong nat (sym (ℕ.⊓-assoc n m o))
⊓-assoc (nat n) (nat m) ∞ = refl
⊓-assoc (nat n) ∞ o = refl
⊓-assoc ∞ m o = refl


⊓-comm : ∀ n m → n ⊓ m ≡ m ⊓ n
⊓-comm (nat n) (nat m) = cong nat (ℕ.⊓-comm _ _)
⊓-comm (nat n) (∞) = refl
⊓-comm ∞ (nat n) = refl
⊓-comm ∞ ∞ = refl


n≤m→n⊓m≡n : ∀ {n m} → n ≤ m → n ⊓ m ≡ n
n≤m→n⊓m≡n (nat n≤m) = cong nat (ℕ.m≤n⇒m⊓n≡m n≤m)
n≤m→n⊓m≡n ∞ = n⊓∞≡n


n≤m→m⊓n≡n : ∀ {n m} → n ≤ m → m ⊓ n ≡ n
n≤m→m⊓n≡n {n} {m} n≤m = trans (⊓-comm m n) (n≤m→n⊓m≡n n≤m)


-- A sized type is a contravariant functor over sizes.
record SizedType : Set₁ where
  field
    Ty : Size → Set
    down : ∀ {n m} → n ≤ m → Ty m → Ty n
    down-id : ∀ {n} (x : Ty n) → down ≤-refl x ≡ x
    down-∘ : ∀ {n m o} (n≤m : n ≤ m) (m≤o : m ≤ o) x
      → down (≤-trans n≤m m≤o) x ≡ down n≤m (down m≤o x)


open SizedType


Constₛ : Set → SizedType
Constₛ T = record
  { Ty = λ _ → T
  ; down = λ _ → id
  ; down-id = λ _ → refl
  ; down-∘ = λ _ _ _ → refl
  }


_⇒ₛ_ : (T S : SizedType) → SizedType
T ⇒ₛ S = record
  { Ty = λ n → ∀ N → N ≤ n → Ty T N → Ty S N
  ; down = λ n≤m f N N≤n x → f N (≤-trans N≤n n≤m) x
  ; down-id = λ f → funext λ N → funext λ N≤n → funext λ x
      → cong (λ p → f N p x) ≤-prop
  ; down-∘ = λ n≤m m≤o f → funext λ N → funext λ N≤n → funext λ x
      → cong (λ p → f N p x) ≤-prop
  }


-- Bounded quantification over sized types is modeled by a downward-consistent
-- family.
record ⟦∀⟧ (n : Size) (T : SizedType) : Set where
  field
    arr : ∀ m → m < n → Ty T m
    consistent : ∀ {m m′} (m<n : m < n) (m′<n : m′ < n) (m≤m′ : m ≤ m′)
      → arr m m<n ≡ down T m≤m′ (arr m′ m′<n)
