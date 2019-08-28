-- Plump ordinals as presented by Shulman
-- https://homotopytypetheory.org/2014/02/22/surreals-plump-ordinals/
--
-- Implementation based on an implementation of Aczel sets by Andreas Abel.
module Ordinal.Shulman where

open import Data.Sum using ([_,_]′)
open import Induction.WellFounded as WfRec using (Acc ; acc ; WellFounded)
open import Relation.Binary using (IsEquivalence)
open import Relation.Nullary using (¬_)

open import Ordinal.HoTT using (IsOrdinal ; IsExtensional ; _↔_ ; forth ; back)
open import Util.Prelude


-- Definition of ordinals, equality, orders
------------------------------------------------------------------------

-- Ordinals are infinitely branching well-founded trees.
-- The branching type is given at each node.

data Ord ℓ : Set (lsuc ℓ) where
  limSuc : (I : Set ℓ) (els : I → Ord ℓ) → Ord ℓ

-- Branching type

Br : ∀ {ℓ} (a : Ord ℓ) → Set ℓ
Br (limSuc I _) = I

-- Elements

els : ∀ {ℓ} (a : Ord ℓ) (i : Br a) → Ord ℓ
els (limSuc _ f) = f

syntax els a i = a ` i

lift-Ord : ∀ {a ℓ} → Ord ℓ → Ord (a ⊔ℓ ℓ)
lift-Ord {a} (limSuc I f) = limSuc (Lift a I) λ i → lift-Ord {a} (f (lower i))

-- Equality and orders

mutual
  _<_ : ∀ {ℓ} (a b : Ord ℓ) → Set ℓ
  a < limSuc _ f = ∃[ i ] (a ≤ f i)

  _≤_  : ∀ {ℓ} (a b : Ord ℓ) → Set ℓ
  limSuc _ f ≤ b = ∀ i → f i < b

_≅_ : ∀ {ℓ} (a b : Ord ℓ) → Set ℓ
a ≅ b = (a ≤ b) × (b ≤ a)

_≮_ : ∀ {ℓ} (a b : Ord ℓ) → Set ℓ
a ≮ b = ¬ (a < b)

_≇_ : ∀ {ℓ} (a b : Ord ℓ) → Set ℓ
a ≇ b = ¬ (a ≅ b)

-- Intro/Elim rules for </≤ (for nicer proofs below)

<-intro : ∀ {ℓ} {a b : Ord ℓ} → ∃[ i ] (a ≤ (b ` i)) → a < b
<-intro {b = limSuc I f} p = p

<-elim : ∀ {ℓ} {a b : Ord ℓ} → a < b → ∃[ i ] (a ≤ (b ` i))
<-elim {b = limSuc I f} p = p

≤-intro : ∀ {ℓ} {a b : Ord ℓ} → (∀ i → (a ` i) < b) → a ≤ b
≤-intro {a = limSuc I f} p = p

≤-elim : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → (∀ i → (a ` i) < b)
≤-elim {a = limSuc I f} p = p

-- Reflexivity

≤-refl : ∀ {ℓ} {a : Ord ℓ} → a ≤ a
≤-refl {a = limSuc _ f} i = i , ≤-refl

≅-refl : ∀ {ℓ} {a : Ord ℓ} → a ≅ a
≅-refl = ≤-refl , ≤-refl

-- < implies ≤

<→≤ : ∀ {ℓ} {a b : Ord ℓ} → a < b → a ≤ b
<→≤ {ℓ} {limSuc A fa} {limSuc B fb} (i , fa<fb) j = i , <→≤ (fa<fb j)

-- Transitivity

mutual
  <-trans-≤ : ∀ {ℓ} {a b c : Ord ℓ} → a < b → b ≤ c → a < c
  <-trans-≤ {b = limSuc _ f} (i , p) h = ≤-trans-< p (h i)

  ≤-trans-< : ∀ {ℓ} {a b c : Ord ℓ} → a ≤ b → b < c → a < c
  ≤-trans-< {c = limSuc _ f} p (i , q) = i , ≤-trans p q

  ≤-trans : ∀ {ℓ} {a b c : Ord ℓ} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans {a = limSuc _ f} h q i = <-trans-≤ (h i) q

<-trans : ∀ {ℓ} {a b c : Ord ℓ} → a < b → b < c → a < c
<-trans {ℓ} {a} {b} {limSuc C fc} a<b (i , b≤fci) = i , <→≤ (<-trans-≤ a<b b≤fci)

≅-trans : ∀ {ℓ} {a b c : Ord ℓ} (d : a ≅ b) (e : b ≅ c) → a ≅ c
≅-trans (p , p′) (q , q′) = ≤-trans p q , ≤-trans q′ p′

-- Symmetry

≅-sym : ∀ {ℓ} {a b : Ord ℓ} (p : a ≅ b) → b ≅ a
≅-sym (p , p′) = p′ , p


-- ≅ is an equivalence relation.

≅-equiv : ∀ {ℓ} → IsEquivalence (_≅_ {ℓ})
≅-equiv = record
  { refl = ≅-refl
  ; sym = ≅-sym
  ; trans = ≅-trans
  }

-- < is 'extensional'.

<-ext-≤ : ∀ {ℓ} {a b : Ord ℓ} → (∀ c → c < a → c < b) → a ≤ b
<-ext-≤ {a = limSuc I els} p i = p (els i) (i , ≤-refl)

<-ext : ∀ {ℓ} → IsExtensional {ℓ} _≅_ _<_
<-ext p = <-ext-≤ (λ c → forth (p c)) , <-ext-≤ (λ c → back (p c))

-- Alternative interpretation of ≤ in terms of <

≤-intro′ : ∀ {ℓ} {b c : Ord ℓ} → (∀ {a} → a < b → a < c) → b ≤ c
≤-intro′ {b = limSuc _ f} cast i = cast (i , ≤-refl)

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
≤-found {ℓ} {limSuc A fa} {b} a≤b (i , b≤fai) = ≤-found b≤fai (a≤b i)

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

<-acc-≤ : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → Acc _<_ b → Acc _<_ a
<-acc-≤ {ℓ} {limSuc A fa} {b} fai<b (acc rs) = acc λ where
  x (i , x≤fai) → rs x (≤-trans-< x≤fai (fai<b i))

<-wf : ∀ {ℓ} → WellFounded (_<_ {ℓ})
<-wf (limSuc I f) = acc λ { x (i , x≤fi) → <-acc-≤ x≤fi (<-wf (f i)) }

<-ind : ∀ {ℓ ℓ′} (P : Ord ℓ → Set ℓ′)
  → (∀ a → (∀ b → b < a → P b) → P a)
  → ∀ a → P a
<-ind = WfRec.All.wfRec <-wf _

-- Ordinals are ordinals (in the sense of the HoTT book).

isOrdinal : ∀ {ℓ} → IsOrdinal (Ord ℓ) ℓ ℓ
isOrdinal = record
  { _≈_ = _≅_
  ; ≈-equiv = ≅-equiv
  ; _<_ = _<_
  ; <-wf = <-wf
  ; <-ext = <-ext
  ; <-trans = <-trans
  }

-- Constructions on ordinals
------------------------------------------------------------------------

-- Zero

ozero : ∀ {ℓ} → Ord ℓ
ozero {ℓ} = limSuc (Lift ℓ ⊥) λ()

-- Successor?

osuc : ∀ {ℓ} → Ord ℓ → Ord ℓ
osuc {ℓ} a = limSuc (Lift ℓ ⊤) λ _ → a

-- Lo and behold!
osuc-mon-< : ∀ {ℓ} {a b : Ord ℓ} → a < b → osuc a < osuc b
osuc-mon-< a<b = _ , λ _ → a<b

osuc-mon-≤ : ∀ {ℓ} {a b : Ord ℓ} → a ≤ b → osuc a ≤ osuc b
osuc-mon-≤ a≤b _ = _ , a≤b

osuc-cong : ∀ {ℓ} {a b : Ord ℓ} → a ≅ b → osuc a ≅ osuc b
osuc-cong (a≤b , b≤a) = osuc-mon-≤ a≤b , osuc-mon-≤ b≤a

-- Maximum/Supremum

_⊔_ : ∀ {ℓ} (a b : Ord ℓ) → Ord ℓ
a ⊔ b = limSuc (_ ⊎ _) λ where
  (inj₁ i) → a ` i
  (inj₂ j) → b ` j

⊔-introˡ : ∀ {ℓ} a {b c : Ord ℓ} → a < b → a < (b ⊔ c)
⊔-introˡ a {limSuc _ f} (i , e) = inj₁ i , e

⊔-introʳ : ∀ {ℓ} a {b c : Ord ℓ} → a < c → a < (b ⊔ c)
⊔-introʳ a {c = limSuc _ g} (i , e) = inj₂ i , e

⊔-≤-introˡ : ∀ {ℓ} a {b c : Ord ℓ} → a ≤ b → a ≤ (b ⊔ c)
⊔-≤-introˡ a a≤b = ≤-intro λ i → ⊔-introˡ _ (≤-elim a≤b i)

⊔-≤-introˡ′ : ∀ {ℓ} {a : Ord ℓ} b → a ≤ (a ⊔ b)
⊔-≤-introˡ′ b = ⊔-≤-introˡ _ ≤-refl

⊔-≤-introʳ : ∀ {ℓ} a {b c : Ord ℓ} → a ≤ c → a ≤ (b ⊔ c)
⊔-≤-introʳ a a≤c = ≤-intro λ i → ⊔-introʳ _ (≤-elim a≤c i)

⊔-≤-introʳ′ : ∀ {ℓ} a {b : Ord ℓ} → b ≤ (a ⊔ b)
⊔-≤-introʳ′ a = ⊔-≤-introʳ _ ≤-refl

⊔-elim : ∀ {ℓ} {a b c : Ord ℓ} → c < (a ⊔ b) → (c < a) ⊎ (c < b)
⊔-elim {a = limSuc _ f}               (inj₁ i , e) = inj₁ (i , e)
⊔-elim {a = limSuc _ _} {b = limSuc _ g} (inj₂ i , e) = inj₂ (i , e)

⊔-case : ∀ {ℓ} {a b c : Ord ℓ} → c < (a ⊔ b) → ∀ {q} {Q : Set q} → (c < a → Q) → (c < b → Q) → Q
⊔-case p left right = [ left , right ]′ (⊔-elim p)

⊔-split : ∀ {ℓ q} {Q : Set q} {a b c : Ord ℓ} → (c < a → Q) → (c < b → Q) → c < (a ⊔ b) → Q
⊔-split left right p = ⊔-case p left right

⊔-mon : ∀ {ℓ} {a a′ b b′ : Ord ℓ} → a ≤ a′ → b ≤ b′ → (a ⊔ b) ≤ (a′ ⊔ b′)
⊔-mon a≤a′ b≤b′ = ≤-intro′ (⊔-split (λ c<a → ⊔-introˡ _ (≤-elim′ a≤a′ c<a))
                                   (λ c<b → ⊔-introʳ _ (≤-elim′ b≤b′ c<b)))

⊔-cong : ∀ {ℓ} {a a′ b b′ : Ord ℓ} → a ≅ a′ → b ≅ b′ → (a ⊔ b) ≅ (a′ ⊔ b′)
⊔-cong (a≤a′ , a′≤a) (b≤b′ , b′≤b) = ⊔-mon a≤a′ b≤b′ , ⊔-mon a′≤a b′≤b

meh : ({α α′ β : Ord lzero} → α < β → α′ < β → (α ⊔ α′) < β)
  → (A : Set) → A ⊎ ¬ A
meh p A
  = let α<β : α < β
        α<β = true , ≤-refl
        α′<β : α′ < β
        α′<β = false , ≤-refl in
    go (p α<β α′<β)
  where
    oone = osuc ozero
    α = limSuc A λ _ → oone
    α′ = oone
    β = limSuc Bool λ { true → α ; false → α′ }

    go : (α ⊔ α′) < β → A ⊎ ¬ A
    go (true , α⊔α′≤α) = inj₁ (proj₁ (α⊔α′≤α (inj₂ _)))
    go (false , α⊔α′≤α′) = inj₂ λ a → lower (proj₁ (proj₂ (α⊔α′≤α′ (inj₁ a)) _))

-- Supremum of a family of ordinals

⨆ᶠ : ∀ {ℓ} {I : Set ℓ} (f : I → Ord ℓ) → Ord ℓ
⨆ᶠ {ℓ} {I} f = limSuc (∃[ i ] Br (f i)) λ { (i , j) → f i ` j }

⨆ᶠ-intro : ∀ {ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} {i : I} → c < f i → c < ⨆ᶠ f
⨆ᶠ-intro f {c} {i} c<fi
  = let j , c≤ = <-elim c<fi in
    (i , j) , c≤

⨆ᶠ-elim : ∀ {ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} → c < ⨆ᶠ f → ∃[ i ] (c < f i)
⨆ᶠ-elim _ ((i , j) , e) = i , <-intro (j , e)

⨆ᶠ-mon : ∀ {ℓ} {I : Set ℓ} {f f′ : I → Ord ℓ} → (∀ i → f i ≤ f′ i) → ⨆ᶠ f ≤ ⨆ᶠ f′
⨆ᶠ-mon {f = f} {f′} p = ≤-intro′ λ c<⨆ᶠf →
  let i , q = ⨆ᶠ-elim f c<⨆ᶠf in
  ⨆ᶠ-intro f′ (≤-elim′ (p i) q)

⨆ᶠ-cong : ∀ {ℓ} {I : Set ℓ} {f f′ : I → Ord ℓ} → (∀ i → f i ≅ f′ i) → ⨆ᶠ f ≅ ⨆ᶠ f′
⨆ᶠ-cong p = ⨆ᶠ-mon (λ i → proj₁ (p i))
          , ⨆ᶠ-mon (λ i → proj₂ (p i))

-- Supremum of all ordinals smaller than some given ordinal

⨆ : ∀ {ℓ} (a : Ord ℓ) → Ord ℓ
⨆ (limSuc _ f) = ⨆ᶠ f

⨆-intro : ∀ {ℓ} {a b : Ord ℓ} → b < a → b ≤ ⨆ a
⨆-intro {a = limSuc A fa} {b = limSuc B fb} (i , b≤fi) = ≤-intro λ j →
  let k , p = <-elim (b≤fi j) in _ , p

⨆-elim : ∀ {ℓ} {a c : Ord ℓ} → c < ⨆ a → ∃[ b ] ((b < a) × (c < b))
⨆-elim {a = limSuc _ f} ((i , j) , c≤) = f i , (i , ≤-refl) , <-intro (_ , c≤)
