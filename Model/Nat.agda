module Model.Nat where

import Data.Nat as ℕ
import Data.Nat.Properties as ℕ

open import Axioms using (funext)
open import Model.Size
open import Util.Prelude hiding (Size ; Size<_ ; ∞ ; ↑_)


infix 7 _ₙ⊓_


Nat : Size → Set
Nat n = Σ[ i ∈ ℕ ] nat i ≤ n


Nat-≡-intro : ∀ {n} {i j : Nat n} → proj₁ i ≡ proj₁ j → i ≡ j
Nat-≡-intro {i = i , i≤n} {j , j≤n} refl = cong (i ,_) ≤-prop


_ₙ⊓_ : ℕ → Size → ℕ
i ₙ⊓ nat n = i ℕ.⊓ n
i ₙ⊓ ∞ = i


ₙ⊓≡⊓ : ∀ i n → nat (i ₙ⊓ n) ≡ nat i ⊓ n
ₙ⊓≡⊓ i (nat n) = refl
ₙ⊓≡⊓ i ∞ = refl


iₙ⊓n≤n : ∀ i n → nat (i ₙ⊓ n) ≤ n
iₙ⊓n≤n i (nat n) = nat (ℕ.m⊓n≤n _ _)
iₙ⊓n≤n i ∞ = ∞


i≤n→iₙ⊓n≡i : ∀ {i n} → nat i ≤ n → i ₙ⊓ n ≡ i
i≤n→iₙ⊓n≡i (nat i≤m) = ℕ.m≤n⇒m⊓n≡m i≤m
i≤n→iₙ⊓n≡i ∞ = refl


iₙ⊓nₙ⊓m≡iₙ⊓n⊓m : ∀ i n m → (i ₙ⊓ n) ₙ⊓ m ≡ i ₙ⊓ (n ⊓ m)
iₙ⊓nₙ⊓m≡iₙ⊓n⊓m i (nat n) (nat m) = ℕ.⊓-assoc _ _ _
iₙ⊓nₙ⊓m≡iₙ⊓n⊓m i (nat n) ∞ = refl
iₙ⊓nₙ⊓m≡iₙ⊓n⊓m i ∞ (nat m) = refl
iₙ⊓nₙ⊓m≡iₙ⊓n⊓m i ∞ ∞ = refl


Natₛ : SizedType
Natₛ = record
  { Ty = Nat
  ; down = down
  ; down-id = down-id
  ; down-∘ = down-∘
  }
  where
    down : ∀ {n m} → n ≤ m → Nat m → Nat n
    down {n} {m} n≤m (i , i≤m) = i ₙ⊓ n , iₙ⊓n≤n i n


    down-id : ∀ {n} (i : Nat n) → down ≤-refl i ≡ i
    down-id (i , i≤n) = Nat-≡-intro (i≤n→iₙ⊓n≡i i≤n)


    down-∘ : ∀ {n m o} (n≤m : n ≤ m) (m≤o : m ≤ o) (i : Nat o)
      → down (≤-trans n≤m m≤o) i ≡ down n≤m (down m≤o i)
    down-∘ {n} {m} {o} n≤m m≤o (i , i≤o) = Nat-≡-intro (sym
      let open ≡-Reasoning in
      begin
        (i ₙ⊓ m) ₙ⊓ n
      ≡⟨ iₙ⊓nₙ⊓m≡iₙ⊓n⊓m i m n ⟩
        (i ₙ⊓ (m ⊓ n))
      ≡⟨ cong (i ₙ⊓_) (n≤m→m⊓n≡n n≤m) ⟩
        i ₙ⊓ n
      ∎)


Zero : ∀ {n} → Nat n
Zero = 0 , 0≤n


Suc : ∀ {n} → ⟦∀⟧ n (Natₛ ⇒ₛ Constₛ (Nat n))
Suc = record
  { arr = λ where
      m m<n N N≤m (i , i≤N)
        → suc i
        , ≤-trans (ssuc′-resp-≤ i≤N) (≤-trans (ssuc′-resp-≤ N≤m) (n<m→n+1≤m m<n))
  ; consistent = λ m<n m′<n m≤m′
      → funext λ N → funext λ N≤n → funext λ i → Nat-≡-intro refl
  }


case : ∀ {T : Set} {n} → Nat n → T → (⟦∀⟧ n (Natₛ ⇒ₛ Constₛ T)) → T
case (zero , i≤n) z s = z
case (suc i , i+1≤n) z s
  = ⟦∀⟧.arr s (nat i) (n+1≤m→n<m i+1≤n) (nat i) ≤-refl (i , ≤-refl)


case-Zero : ∀ {T} {n} (z : T) (s : ⟦∀⟧ n (Natₛ ⇒ₛ Constₛ T))
  → case Zero z s ≡ z
case-Zero z s = refl


case-Suc : ∀ {T} {n} (z : T) (s : ⟦∀⟧ n (Natₛ ⇒ₛ Constₛ T))
  → ∀ {m} (m<n : m < n) (i : ℕ) (i≤m : nat i ≤ m)
  → case (⟦∀⟧.arr Suc m m<n (nat i) i≤m (i , ≤-refl)) z s
  ≡ ⟦∀⟧.arr s m m<n (nat i) i≤m (i , ≤-refl)
case-Suc {T} {n} z s {m} m<n i i≤m
  = lem {nat i} {m} _ m<n i≤m (nat i) ≤-refl i≤m (i , ≤-refl)
  where
    lem : ∀ {k k′} (k<n : k < n) (k′<n : k′ < n) (k≤k′ : k ≤ k′)
      → ∀ N (N≤k : N ≤ k) (N≤k′ : N ≤ k′) (i : Nat N)
      → ⟦∀⟧.arr s k k<n N N≤k i
      ≡ ⟦∀⟧.arr s k′ k′<n N N≤k′ i
    lem k<n k′<n k≤k′ N N≤k N≤k′ i
      rewrite ⟦∀⟧.consistent s k<n k′<n k≤k′
      = cong (λ p → ⟦∀⟧.arr s _ k′<n N p i) ≤-prop
