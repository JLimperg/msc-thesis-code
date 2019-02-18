-- Plump ordinals as presented by Shulman
-- https://homotopytypetheory.org/2014/02/22/surreals-plump-ordinals/
--
-- Implementation based on an implementation of Aczel sets by Andreas Abel.
module Ordinal.Plump.Shulman where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product using
  (Σ ; ∃; ∃-syntax ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Function using (id; _$_)
open import Induction.WellFounded as WfRec using (Acc ; acc ; WellFounded)
open import Level using
  (Level; Lift; lower) renaming
  (zero to lzero; suc to lsuc ; _⊔_ to _⊔ℓ_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)


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
  a < sup _ f = ∃[ i ] (a ≤ f i)

  _≤_  : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  sup _ f ≤ b = ∀ i → f i < b

_≅_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≅ b = (a ≤ b) × (b ≤ a)

_≮_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≮ b = ¬ (a < b)

_≇_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≇ b = ¬ (a ≅ b)

-- Intro/Elim rules for </≤ (for nicer proofs below)

<-intro : ∀ {ℓ} {a b : Ord ℓ} → ∃[ i ] (a ≤ (b ` i)) → a < b
<-intro {b = sup I f} p = p

<-elim : ∀ {ℓ} {a b : Ord ℓ} → a < b → ∃[ i ] (a ≤ (b ` i))
<-elim {b = sup I f} p = p

≤-intro : ∀ {ℓ} {a b : Ord ℓ} → (∀ i → (a ` i) < b) → a ≤ b
≤-intro {a = sup I f} p = p

≤-elim : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → (∀ i → (a ` i) < b)
≤-elim {a = sup I f} p = p

-- Reflexivity

≤-refl : ∀ {ℓ} {a : Ord ℓ} → a ≤ a
≤-refl {a = sup _ f} i = i , ≤-refl

≅-refl : ∀ {ℓ} {a : Ord ℓ} → a ≅ a
≅-refl = ≤-refl , ≤-refl

-- < implies ≤

<→≤ : ∀ {ℓ} {a b : Ord ℓ} → a < b → a ≤ b
<→≤ {ℓ} {sup A fa} {sup B fb} (i , fa<fb) j = i , <→≤ (fa<fb j)

-- Transitivity

mutual
  ≤-trans-< : ∀ {ℓ} {a b c : Ord ℓ} → a ≤ b → b < c → a < c
  ≤-trans-< {ℓ} {a} {b} {sup C fc} a≤b (i , b≤fci) = i , ≤-trans a≤b b≤fci

  ≤-trans : ∀ {ℓ} {a b c : Ord ℓ} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans {ℓ} {sup A fa} {sup B fb} {c} a≤b b≤c i
    = let j , fai≤fbj = a≤b i in
      ≤-trans-< fai≤fbj (b≤c j)

<-trans-≤ : ∀ {ℓ} {a b c : Ord ℓ} → a < b → b ≤ c → a < c
<-trans-≤ {ℓ} {a} {sup B fb} {sup C fc} (i , a≤fbi) b≤c
  = let j , fbi≤fcj = b≤c i in
    j , ≤-trans a≤fbi fbi≤fcj

<-trans : ∀ {ℓ} {a b c : Ord ℓ} → a < b → b < c → a < c
<-trans {ℓ} {a} {b} {sup C fc} a<b (i , b≤fci) = i , <→≤ (<-trans-≤ a<b b≤fci)

≅-trans : ∀ {ℓ} {a b c : Ord ℓ} (d : a ≅ b) (e : b ≅ c) → a ≅ c
≅-trans (p , p') (q , q') = ≤-trans p q , ≤-trans q' p'

-- Symmetry

≅-sym : ∀ {ℓ} {a b : Ord ℓ} (p : a ≅ b) → b ≅ a
≅-sym (p , p') = p' , p

-- Alternative interpretation of ≤ in terms of <

≤-intro′ : ∀ {ℓ} {a b : Ord ℓ} → (∀ {c} → c < a → c < b) → a ≤ b
≤-intro′ {a = sup _ f} cast i = cast (i , ≤-refl)

≤-elim′ : ∀ {ℓ} {b c : Ord ℓ} → b ≤ c → ∀ {a} → a < b → a < c
≤-elim′ b≤c a<b = <-trans-≤ a<b b≤c

-- Compatibility of ≤ with ≅

≤-congˡ : ∀ {ℓ} {a b c : Ord ℓ} → a ≅ b → a ≤ c → b ≤ c
≤-congˡ {ℓ}  (a≤b , b≤a) a≤c = ≤-trans b≤a a≤c

≤-congʳ : ∀ {ℓ} {a b c : Ord ℓ} → b ≅ c → a ≤ b → a ≤ c
≤-congʳ (b≤c , c≤b) a≤b = ≤-trans a≤b b≤c

-- Compatibility of < with ≅

<-congʳ : ∀ {ℓ} {a b c : Ord ℓ} → b ≅ c → a < b → a < c
<-congʳ (b≤c , c≤b) a<b = <-trans-≤ a<b b≤c

<-congˡ : ∀ {ℓ} {a b c : Ord ℓ} → a ≅ b → a < c → b < c
<-congˡ (a≤b , b≤a) a<c = ≤-trans-< b≤a a<c

-- Foundation: a ≤ b implies b ≮ a

≤-found : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → b ≮ a
≤-found {ℓ} {sup A fa} {b} a≤b (i , b≤fai) = ≤-found b≤fai (a≤b i)

-- Thus, a ≮ a.

<-irr : ∀ {ℓ} {a : Ord ℓ} → a ≮ a
<-irr = ≤-found ≤-refl

-- Predicates over ordinals (need to respect equality)

IsPred : ∀ {ℓ} (P : Ord ℓ → Set ℓ) → Set (lsuc ℓ)
IsPred {ℓ} P = {a b : Ord ℓ} → a ≅ b → P a → P b

record Pred ℓ : Set (lsuc ℓ) where
  constructor pred
  field
    _!_  : Ord ℓ → Set ℓ
    resp : IsPred _!_

open Pred

-- <-induction.

<-acc-down : ∀ {ℓ} {a b : Ord ℓ} → a < b → Acc _<_ b → Acc _<_ a
<-acc-down {ℓ} {sup A fa} {b} a<b (acc rs) = rs (sup A fa) a<b

<-acc-down-≤ : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → Acc _<_ b → Acc _<_ a
<-acc-down-≤ {ℓ} {sup A fa} {b} fai<b b-acc = acc λ where
  x (i , x≤fai) → <-acc-down (≤-trans-< x≤fai (fai<b i)) b-acc

<-wf : ∀ {ℓ} → WellFounded (_<_ {ℓ})
<-wf (sup I f) = acc λ { x (i , x≤fi) → <-acc-down-≤ x≤fi (<-wf (f i)) }

<-ind : ∀ {ℓ ℓ′} (P : Ord ℓ → Set ℓ′)
  → (∀ a → (∀ b → b < a → P b) → P a)
  → ∀ a → P a
<-ind = WfRec.All.wfRec <-wf _


-- Constructions on ordinals
------------------------------------------------------------------------

-- Zero

ozero : ∀{ℓ} → Ord ℓ
ozero {ℓ} = sup (Lift ℓ ⊥) λ()

-- Successor?

osuc : ∀ {ℓ} → Ord ℓ → Ord ℓ
osuc {ℓ} a = sup (Lift ℓ ⊤) λ _ → a

-- Lo and behold!
osuc-mon-< : ∀ {ℓ} {a b : Ord ℓ} → a < b → osuc a < osuc b
osuc-mon-< a<b = _ , λ _ → a<b

osuc-mon-≤ : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → osuc a ≤ osuc b
osuc-mon-≤ a≤b _ = _ , a≤b

osuc-cong : ∀ {ℓ} {a b : Ord ℓ} → a ≅ b → osuc a ≅ osuc b
osuc-cong (a≤b , b≤a) = osuc-mon-≤ a≤b , osuc-mon-≤ b≤a

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

⊔-case : ∀{ℓ} {a b c : Ord ℓ} → c < (a ⊔ b) → ∀ {q} {Q : Set q} → (c < a → Q) → (c < b → Q) → Q
⊔-case p left right = [ left , right ]′ (⊔-elim p)

⊔-split : ∀{ℓ q} {Q : Set q} {a b c : Ord ℓ} → (c < a → Q) → (c < b → Q) → c < (a ⊔ b) → Q
⊔-split left right p = ⊔-case p left right

⊔-mon : ∀{ℓ} {a a′ b b′ : Ord ℓ} → a ≤ a′ → b ≤ b′ → (a ⊔ b) ≤ (a′ ⊔ b′)
⊔-mon a≤a′ b≤b′ = ≤-intro′ (⊔-split (λ c<a → ⊔-introˡ (≤-elim′ a≤a′ c<a))
                                   (λ c<b → ⊔-introʳ (≤-elim′ b≤b′ c<b)))

⊔-cong : ∀{ℓ} {a a′ b b′ : Ord ℓ} → a ≅ a′ → b ≅ b′ → (a ⊔ b) ≅ (a′ ⊔ b′)
⊔-cong (a≤a′ , a′≤a) (b≤b′ , b′≤b) = ⊔-mon a≤a′ b≤b′ , ⊔-mon a′≤a b′≤b

-- Supremum of a family of ordinals

⨆ᶠ : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) → Ord ℓ
⨆ᶠ {ℓ} {I} f = sup (∃[ i ] Br (f i)) λ p → f (proj₁ p) ` proj₂ p

⨆ᶠ-intro : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} {i : I} → c < f i → c < ⨆ᶠ f
⨆ᶠ-intro f {c} {i} c<fi
  = let j , c≤ = <-elim c<fi in
    (i , j) , c≤

⨆ᶠ-elim : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} → c < ⨆ᶠ f → ∃[ i ] (c < f i)
⨆ᶠ-elim _ ((i , j) , e) = i , <-intro (j , e)

⨆ᶠ-mon : ∀{ℓ} {I : Set ℓ} {f f′ : I → Ord ℓ} → (∀ i → f i ≤ f′ i) → ⨆ᶠ f ≤ ⨆ᶠ f′
⨆ᶠ-mon {f = f} {f′} p = ≤-intro′ λ c<⨆ᶠf →
  let i , q = ⨆ᶠ-elim f c<⨆ᶠf in
  ⨆ᶠ-intro f′ (≤-elim′ (p i) q)

⨆ᶠ-cong : ∀{ℓ} {I : Set ℓ} {f f' : I → Ord ℓ} → (∀ i → f i ≅ f' i) → ⨆ᶠ f ≅ ⨆ᶠ f'
⨆ᶠ-cong p = ⨆ᶠ-mon (λ i → proj₁ (p i))
          , ⨆ᶠ-mon (λ i → proj₂ (p i))

-- Supremum of all ordinals smaller than some given ordinal

⨆ : ∀{ℓ} (a : Ord ℓ) → Ord ℓ
⨆ (sup _ f) = ⨆ᶠ f

⨆-intro : ∀{ℓ} {a b : Ord ℓ} → b < a → b ≤ ⨆ a
⨆-intro {a = sup A fa} {b = sup B fb} (i , b≤fi) = ≤-intro λ j →
  let k , p = <-elim (b≤fi j) in _ , p

⨆-elim : ∀{ℓ} {a c : Ord ℓ} → c < ⨆ a → ∃[ b ] ((b < a) × (c < b))
⨆-elim {a = sup _ f} ((i , j) , c≤) = f i , (i , ≤-refl) , <-intro (_ , c≤)
