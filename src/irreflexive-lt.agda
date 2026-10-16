{- With Agda's current sized types, we have a size ∞ with ∞ < ∞. That's
   obviously troublesome if we want to interpret sizes as ordinals and < as the
   less-than relation, and indeed we can use this rule to prove false (in
   multiple different ways).

   This file is an experiment to see whether we could still work with a system
   that doesn't have this rule.
-}

{-# OPTIONS --postfix-projections --sized-types #-}
module irreflexive-lt where

open import Size


postulate
  𝟘 : Size


data Size≲ : (j : Size) → Set where
  ≲∞ : (i : Size) → Size≲ ∞
  <→≲ : ∀ {j} (i : Size< j) → Size≲ j


from≲ : ∀ {j} → Size≲ j → Size
from≲ (≲∞ i) = i
from≲ (<→≲ i) = i

∞′ : Size≲ ∞
∞′ = ≲∞ ∞


--------------------------------------------------------------------------------
-- Natural numbers


data ℕ (i : Size) : Set where
  zero : ℕ i
  suc : (j : Size< i) → ℕ j → ℕ i


-- Using the successor at size ∞ becomes nontrivial. The following is NOT
-- allowed since we use (∞ : Size< ∞).
-- suc₀ : ℕ ∞ → ℕ ∞
-- suc₀ n = suc ∞ n


-- Workaround: superfluous pattern matching.
suc₁ : ℕ ∞ → ℕ ∞
suc₁ zero = suc 𝟘 zero
suc₁ (suc j x) = suc (↑ j) (suc j x)


-- Case analysis
caseℕ : {T : Set} → (i : Size) → ℕ i → T → ((j : Size< i) → ℕ j → T) → T
caseℕ i zero z s = z
caseℕ i (suc j n) z s = s j n


-- Dependent elimination (with size-based termination).
indℕ : (P : (i : Size) → ℕ i → Set)
  → ((i : Size) → P i zero)
  → ((i : Size) (j : Size< i) (n : ℕ j) → P j n → P i (suc j n))
  → (i : Size) (n : ℕ i) → P i n
indℕ P Z S i zero = Z i
indℕ P Z S i (suc j n) = S i j n (indℕ P Z S j n)


--------------------------------------------------------------------------------
-- Streams


record 𝕊 (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : (j : Size< i) → 𝕊 A j

open 𝕊


variable
  A B : Set


-- Again, we CANNOT use tail at ∞ directly since this uses (∞ : Size< ∞).
-- tail₀ : 𝕊 ∞ → 𝕊 ∞
-- tail₀ xs = tail xs ∞


-- Workaround: The equivalent of the 'superfluous pattern matching' workaround
-- for suc.
tail₁ : 𝕊 A ∞ → 𝕊 A ∞
tail₁ xs .head = head {i = 𝟘} (tail xs 𝟘) -- [1]
tail₁ xs .tail j = tail (tail xs (↑ j)) j

-- [1] Without the implicit argument, this doesn't typecheck. Apparently the
-- size argument to head gets eagerly instantiated to ∞ or something.


replicate : (i : Size) → A → 𝕊 A i
replicate i a .head = a
replicate i a .tail j = replicate j a


map𝕊 : (A → B) → (i : Size) → 𝕊 A i → 𝕊 B i
map𝕊 f i xs .head = f (head xs)
map𝕊 f i xs .tail j = map𝕊 f j (tail xs j)



--------------------------------------------------------------------------------
-- Rose trees


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A


mapList : (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs


data Tree (A : Set) (i : Size) : Set where
  leaf : A → Tree A i
  node : (j : Size< i) → List (Tree A j) → Tree A i


mapTree : (A → B) → (i : Size) → Tree A i → Tree B i
mapTree f i (leaf x) = leaf (f x)
mapTree f i (node j cs) = node j (mapList (mapTree f j) cs)


--------------------------------------------------------------------------------
-- Potentially infinite lists


mutual
  data CoList (A : Set) (i : Size) : Set where
    [] : CoList A i
    _∷_ : A → CoList′ A i → CoList A i


  record CoList′ (A : Set) (i : Size) : Set where
    coinductive
    field
      force : (j : Size< i) → CoList A j

open CoList′


open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl)


postulate
  force-parametric : ∀ {A i} (xs : CoList′ A i) (j j′ : Size< i)
    → xs .force j ≅ xs .force j′

  size-parametric : ∀ {T : Size< ∞ → Set} (f : (i : Size< ∞) → T i)
    → (j j′ : Size< ∞)
    → f j ≅ f j′


mutual
  data _≈_ {A i j} : CoList A i → CoList A j → Set where
    [] : [] ≈ []
    _∷_ : ∀ {x y xs ys}
      → x ≡ y
      → xs ≈′ ys
      → (x ∷ xs) ≈ (y ∷ ys)


  record _≈′_ {A i j} (xs : CoList′ A i) (ys : CoList′ A j) : Set where
    coinductive
    field
      force : (k : Size< i) (l : Size< j) → xs .force k ≈ ys .force l

open _≈′_


force∞ : CoList′ A ∞ → CoList A ∞
force∞ {A} xs with xs .force 𝟘
... | [] = []
... | y ∷ ys = y ∷ ys′
  where
    ys′ : CoList′ A ∞
    ys′ .force i with xs .force (↑ i)
    ... | [] = []
    ... | z ∷ zs = zs .force i


𝕊→CoList : (i : Size) → 𝕊 A i → CoList A i
𝕊→CoList i xs = head xs ∷ λ { .force j → 𝕊→CoList j (tail xs j) }


-- Radical thought: Just kill ∞ altogether and work with (∀ i → CoList A i) and
-- (∃ i → List A i) directly. How much less useful does that make the system?
--
-- Perhaps we can auto-derive the iso (∃ i → List A i) ≅ List A.


-- Radical thought: What if we only provide the Thunk type from the stdlib? Can
-- we recover all other coinductive types from that?
