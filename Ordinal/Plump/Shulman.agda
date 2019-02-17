-- Plump ordinals as presented by Shulman
-- https://homotopytypetheory.org/2014/02/22/surreals-plump-ordinals/
--
-- Aka Aczel sets. Implementation mostly stolen from Andreas Abel.
module Ordinal.Plump.Shulman where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product using
  (Σ ; ∃; ∃-syntax ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Function using (id; _$_)
open import Level using
  (Level; Lift; lower) renaming
  (zero to lzero; suc to lsuc ; _⊔_ to _⊔ℓ_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


-- Definition of ordinals, equality, orders
------------------------------------------------------------------------

-- Ordinals are infinitely branching well-founded trees.
-- The branching type is given at each node.

data Ord ℓ : Set (lsuc ℓ) where
  sup : (I : Set ℓ) (els : I → Ord ℓ) → Ord ℓ

-- Branching type

Br : ∀{ℓ} (a : Ord ℓ) → Set ℓ
Br (sup I _) = I

-- Elements

els : ∀{ℓ} (a : Ord ℓ) (i : Br a) → Ord ℓ
els (sup _ f) = f

syntax els a i = a ` i

lift-Ord : ∀{a ℓ} → Ord ℓ → Ord (a ⊔ℓ ℓ)
lift-Ord {a} (sup I f) = sup (Lift a I) λ i → lift-Ord {a} (f (lower i))

-- Equality and orders

mutual
  _<_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  a < sup _ f = ∃[ i ] (a ≅ f i)

  _≅_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  a ≅ b = (a ≤ b) × (b ≤ a)

  _≤_  : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  sup _ f ≤ b = ∀ i → f i < b

_≮_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≮ b = ¬ (a < b)

_≇_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≇ b = ¬ (a ≅ b)

-- Reflexivity

mutual
  ≤-refl : ∀{ℓ} (a : Ord ℓ) → a ≤ a
  ≤-refl (sup _ f) i = i , ≅-refl (f i)

  ≅-refl : ∀{ℓ} (a : Ord ℓ) → a ≅ a
  ≅-refl a = ≤-refl a , ≤-refl a

-- Transitivity

mutual
  ≤-trans : ∀{ℓ} {a b c : Ord ℓ} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans {ℓ} {sup _ f} {sup _ g} {sup _ h} p q i = let
      j , d = p i
      k , e = q j
    in k , ≅-trans d e

  ≅-trans : ∀{ℓ} {a b c : Ord ℓ} (d : a ≅ b) (e : b ≅ c) → a ≅ c
  ≅-trans (p , p') (q , q') = ≤-trans p q , ≤-trans q' p'

-- Symmetry

≅-sym : ∀{ℓ} {a b : Ord ℓ} (p : a ≅ b) → b ≅ a
≅-sym (p , p') = p' , p

-- Introduction and elimination for <

<-intro : ∀{ℓ} {a b : Ord ℓ} → ∃[ i ] (a ≅ (b ` i)) → a < b
<-intro {ℓ} {a} {sup _ f} p = p

<-elim : ∀{ℓ} {a b : Ord ℓ} (p : a < b) → ∃[ i ] (a ≅ (b ` i))
<-elim {ℓ} {a} {sup _ f} p = p

-- Introduction and elimination for ≤

≤-intro : ∀{ℓ} {a b : Ord ℓ} → (∀ {c} → c < a → c < b) → a ≤ b
≤-intro {a = sup _ f} cast i = cast (i , ≅-refl _)

≤-elim : ∀{ℓ} {a b c : Ord ℓ} → b ≤ c → a < b → a < c
≤-elim {ℓ} {a} {sup _ f} {sup _ g} q (i , d) = let
    j , e = q i
  in j , ≅-trans d e

-- Compatibility of < with ≤

<-trans-≤ : ∀{ℓ} {a b c : Ord ℓ} → a < b → b ≤ c → a < c
<-trans-≤ a<b b≤c = ≤-elim b≤c a<b

-- Compatibility of < with ≅

<-congʳ : ∀{ℓ} {a b c : Ord ℓ} → a < b → b ≅ c → a < c
<-congʳ p (q , _) = <-trans-≤ p q

<-congˡ : ∀{ℓ} {a b c : Ord ℓ} → a ≅ b → b < c → a < c
<-congˡ {ℓ} {a} {b} {sup _ f} d (i , e) = i , ≅-trans d e

-- < implies ≤; < is transitive

mutual
  <→≤ : ∀{ℓ} {a b : Ord ℓ} → a < b → a ≤ b
  <→≤ {a = sup I f} {sup J g} a<b i = <-trans {a = f i} {b = sup I f} {c = sup J g} (i , ≅-refl _) a<b

  <-trans : ∀{ℓ} {a b c : Ord ℓ} → a < b → b < c → a < c
  <-trans {a = a} {b} {c} a<b b<c = ≤-trans-< {a = a} {b = b} {c = c} (<→≤ {a = a} {b = b} a<b) b<c
  -- <-trans {a = sup I f} {b = sup J g} {c = sup K h} (i , a≅gi) (j , b≅hj)
  --   = j , {!!}

  ≤-trans-< : ∀{ℓ} {a b c : Ord ℓ} → a ≤ b → b < c → a < c
  ≤-trans-< {a = sup A fa} {sup B fb} {sup C fc} a≤b b<c = {!!}

-- Foundation:  If  a ≤ b  then  b ≮ a.

≤-found : ∀{ℓ} {a b : Ord ℓ} → a ≤ b → b ≮ a
≤-found {ℓ} {sup _ f} {b} p (i , q , _) = ≤-found q (p i)

-- Thus, a ≮ a.

<-irr : ∀{ℓ} {a : Ord ℓ} → a ≮ a
<-irr = ≤-found (≤-refl _)

-- Predicates over ordinals (need to respect equality)

IsPred : ∀ {ℓ} (P : Ord ℓ → Set ℓ) → Set (lsuc ℓ)
IsPred {ℓ} P = ∀{a b : Ord ℓ} (e : a ≅ b) (p : P a) → P b

record Pred ℓ : Set (lsuc ℓ) where
  constructor pred
  field
    _!_  : Ord ℓ → Set ℓ
    resp : IsPred _!_


-- <-induction.

<-ind : ∀{ℓ} {P} → IsPred P
      → (f : ∀ (a : Ord ℓ) → (∀ {b} → b < a → P b) → P a)
      → ∀ a → P a
<-ind P-transp f a@(sup _ ela) = f a λ where
  (i , eqv) → P-transp (≅-sym eqv) (<-ind P-transp f (ela i))


-- Get a selection function from ≤

sel-from-≤ : ∀{ℓ} {a b : Ord ℓ} → a ≤ b → Br a → Br b
sel-from-≤ {a = sup _ f} {b = sup _ g} p i = proj₁ (p i)

-- Constructions on sets
------------------------------------------------------------------------

-- Zero

ozero : ∀{ℓ} → Ord ℓ
ozero {ℓ} = sup (Lift ℓ ⊥) λ()

-- Successor?

osuc : ∀{ℓ} → Ord ℓ → Ord ℓ
osuc {ℓ} a = sup (Lift ℓ ⊤) λ _ → a

-- Maximum/Supremum

_⊔_ : ∀{ℓ} (a b : Ord ℓ) → Ord ℓ
a ⊔ b = sup (_ ⊎ _) λ where
  (inj₁ i) → a ` i
  (inj₂ j) → b ` j

⊔-introˡ : ∀{ℓ} {a b c : Ord ℓ} → c < a → c < (a ⊔ b)
⊔-introˡ {a = sup _ f} (i , e) = inj₁ i , e

⊔-introʳ : ∀{ℓ} {a b c : Ord ℓ} → c < b → c < (a ⊔ b)
⊔-introʳ {b = sup _ g} (i , e) = inj₂ i , e

⊔-elim : ∀{ℓ} {a b c : Ord ℓ} → c < (a ⊔ b) → (c < a) ⊎ (c < b)
⊔-elim {a = sup _ f}               (inj₁ i , e) = inj₁ (i , e)
⊔-elim {a = sup _ _} {b = sup _ g} (inj₂ i , e) = inj₂ (i , e)

-- TODO simplify
⊔-case : ∀{ℓ} {a b c : Ord ℓ} → c < (a ⊔ b) → ∀ {q} {Q : Set q} → (c < a → Q) → (c < b → Q) → Q
⊔-case p left right = [ left , right ]′ (⊔-elim p)

⊔-split : ∀{ℓ q} {Q : Set q} {a b c : Ord ℓ} → (c < a → Q) → (c < b → Q) → c < (a ⊔ b) → Q
⊔-split left right p = ⊔-case p left right

⊔-mon : ∀{ℓ} {a a′ b b′ : Ord ℓ} → a ≤ a′ → b ≤ b′ → (a ⊔ b) ≤ (a′ ⊔ b′)
⊔-mon a≤a′ b≤b′ = ≤-intro (⊔-split (λ c<a → ⊔-introˡ (≤-elim a≤a′ c<a))
                                   (λ c<b → ⊔-introʳ (≤-elim b≤b′ c<b)))

⊔-cong : ∀{ℓ} {a a′ b b′ : Ord ℓ} → a ≅ a′ → b ≅ b′ → (a ⊔ b) ≅ (a′ ⊔ b′)
⊔-cong (a≤a′ , a′≤a) (b≤b′ , b′≤b) = ⊔-mon a≤a′ b≤b′ , ⊔-mon a′≤a b′≤b

-- Supremum of a family of ordinals

⨆ᶠ : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) → Ord ℓ
⨆ᶠ {ℓ} {I} f = sup (∃[ i ] Br (f i)) λ p → f (proj₁ p) ` proj₂ p

⨆ᶠ-intro : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} {i : I} → c < f i → c < ⨆ᶠ f
⨆ᶠ-intro f {c} {i} p = let
    j , e = <-elim p
  in (i , j) , e

⨆ᶠ-elim : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} → c < ⨆ᶠ f → ∃[ i ] (c < f i)
⨆ᶠ-elim _ ((i , j) , e) = i , <-intro (j , e)

⨆ᶠ-mon : ∀{ℓ} {I : Set ℓ} {f f′ : I → Ord ℓ} → (∀ i → f i ≤ f′ i) → ⨆ᶠ f ≤ ⨆ᶠ f′
⨆ᶠ-mon {f = f} {f′} p = ≤-intro λ c<⨆ᶠf → let
    i , q = ⨆ᶠ-elim f c<⨆ᶠf
  in ⨆ᶠ-intro f′ (≤-elim (p i) q)

⨆ᶠ-cong : ∀{ℓ} {I : Set ℓ} {f f' : I → Ord ℓ} → (∀ i → f i ≅ f' i) → ⨆ᶠ f ≅ ⨆ᶠ f'
⨆ᶠ-cong p = ⨆ᶠ-mon (λ i → proj₁ (p i))
          , ⨆ᶠ-mon (λ i → proj₂ (p i))

-- Supremum of all ordinals smaller than some given ordinal

⨆ : ∀{ℓ} (a : Ord ℓ) → Ord ℓ
⨆ (sup _ f) = ⨆ᶠ f

⨆-intro : ∀{ℓ} {a b : Ord ℓ} → b < a → b ≤ ⨆ a
⨆-intro {a = sup _ f} (i , b≅fi) = ≤-intro λ c<b → let
    j , d = <-elim (<-congʳ c<b b≅fi)
  in (i , j) , d

⨆-elim : ∀{ℓ} {a c : Ord ℓ} → c < ⨆ a → ∃[ b ] ((b < a) × (c < b))
⨆-elim {a = sup _ f} ((i , j) , e) = f i , (i , ≅-refl _) , <-intro (j , e)
