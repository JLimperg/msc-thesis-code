-- Sets in ITT following Aczel, Werner, Barras
module Ordinal.Plump.Shulman where

open import Level using (Level; _⊔_; Lift; lower) renaming (zero to lzero; suc to lsuc)

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function using (id; _$_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


-- Definition of sets, elementhood, and equality
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

lift-Ord : ∀{a ℓ} → Ord ℓ → Ord (a ⊔ ℓ)
lift-Ord {a} (sup I f) = sup (Lift a I) λ i → lift-Ord {a} (f (lower i))

-- Elementhood and extensional equality (recursive)

mutual
  _∈_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  a ∈ sup _ f = ∃ λ i → a ≅ f i

  _≅_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  a ≅ b = (a ⊂ b) × (b ⊂ a)

  _⊂_  : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
  sup _ f ⊂ b = ∀ i → f i ∈ b

_∉_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ∉ b = ¬ (a ∈ b)

_≇_ : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
a ≇ b = ¬ (a ≅ b)

-- Reflexivity

mutual
  ⊂-refl : ∀{ℓ} (a : Ord ℓ) → a ⊂ a
  ⊂-refl (sup _ f) i = i , ≅-refl (f i)

  ≅-refl : ∀{ℓ} (a : Ord ℓ) → a ≅ a
  ≅-refl a = ⊂-refl a , ⊂-refl a

-- Transitivity

mutual
  ⊂-trans : ∀{ℓ} {a b c : Ord ℓ} (p : a ⊂ b) (q : b ⊂ c) → a ⊂ c
  ⊂-trans {ℓ} {sup _ f} {sup _ g} {sup _ h} p q i = let
      j , d = p i
      k , e = q j
    in k , ≅-trans d e

  ≅-trans : ∀{ℓ} {a b c : Ord ℓ} (d : a ≅ b) (e : b ≅ c) → a ≅ c
  ≅-trans (p , p') (q , q') = ⊂-trans p q , ⊂-trans q' p'

-- Symmetry

≅-sym : ∀{ℓ} {a b : Ord ℓ} (p : a ≅ b) → b ≅ a
≅-sym (p , p') = p' , p

-- Introduction and elimination for ∈

∈-intro : ∀{ℓ} {a b : Ord ℓ} (p : ∃ λ i → a ≅ (b ` i)) → a ∈ b
∈-intro {ℓ} {a} {sup _ f} p = p

∈-elim : ∀{ℓ} {a b : Ord ℓ} (p : a ∈ b) → ∃ λ i → a ≅ (b ` i)
∈-elim {ℓ} {a} {sup _ f} p = p

-- Introduction and elimination for ⊂

⊂-intro : ∀{ℓ} {a b : Ord ℓ} (cast : ∀ {c} → c ∈ a → c ∈ b) → a ⊂ b
⊂-intro {a = sup _ f} cast i = cast (i , ≅-refl _)

⊂-elim : ∀{ℓ} {a b c : Ord ℓ} (q : b ⊂ c) (p : a ∈ b) → a ∈ c
⊂-elim {ℓ} {a} {sup _ f} {sup _ g} q (i , d) = let
    j , e = q i
  in j , ≅-trans d e

-- Compatibility of elementhood with subset

∈-cong-⊂ : ∀{ℓ} {a b c : Ord ℓ} (p : a ∈ b) (q : b ⊂ c) → a ∈ c
∈-cong-⊂ p q = ⊂-elim q p

-- Compatibility of elementhood with equality

∈-congʳ : ∀{ℓ} {a b c : Ord ℓ} (p : a ∈ b) (e : b ≅ c) → a ∈ c
∈-congʳ p (q , _) = ∈-cong-⊂ p q

∈-congˡ : ∀{ℓ} {a b c : Ord ℓ} (d : a ≅ b) (q : b ∈ c) → a ∈ c
∈-congˡ {ℓ} {a} {b} {sup _ f} d (i , e) = i , ≅-trans d e

-- Foundation:  If  a ⊂ b  then  b ∉ a.

found : ∀{ℓ} {a b : Ord ℓ} (p : a ⊂ b) (q : b ∈ a) → ⊥
found {ℓ} {sup _ f} {b} p (i , q , _) = found q (p i)

-- Thus, a ∉ a.

irr : ∀{ℓ} {a : Ord ℓ} → a ∉ a
irr = found (⊂-refl _)

-- Predicates over sets (need to respect equality)

IsPred : ∀ {ℓ} (P : Ord ℓ → Set ℓ) → Set (lsuc ℓ)
IsPred {ℓ} P = ∀{a b : Ord ℓ} (e : a ≅ b) (p : P a) → P b

record Pred ℓ : Set (lsuc ℓ) where
  constructor pred
  field
    _!_  : Ord ℓ → Set ℓ
    resp : IsPred _!_


-- ∈ induction.

∈-ind : ∀{ℓ} {P} → IsPred P
      → (f : ∀ (a : Ord ℓ) → (∀ {b} → b ∈ a → P b) → P a)
      → ∀ a → P a
∈-ind P-transp f a@(sup _ ela) = f a λ where
  (i , eqv) → P-transp (≅-sym eqv) (∈-ind P-transp f (ela i))


-- Get a selection function from ⊂

sel-from-⊂ : ∀{ℓ} {a b : Ord ℓ} (p : a ⊂ b) → Br a → Br b
sel-from-⊂ {a = sup _ f} {b = sup _ g} p i = proj₁ (p i)

-- Restriction by selecting elements

select : ∀{ℓ} (a : Ord ℓ) {D : Set ℓ} (sel : D → Br a) → Ord ℓ
select (sup _ f) sel = sup _ λ d → f (sel d)

select-elim : ∀{ℓ} (a : Ord ℓ) {D : Set ℓ} (sel : D → Br a) → select a sel ⊂ a
select-elim (sup _ f) sel d = sel d , ≅-refl _

select-sel : ∀{ℓ} {a b : Ord ℓ} (p : a ⊂ b) → select b (sel-from-⊂ p) ≅ a
select-sel {a = sup _ f} {b = sup _ g} p =
  (λ i → i , ≅-sym (proj₂ (p i))) ,
  (λ i → i , proj₂ (p i))

-- Constructions on sets
------------------------------------------------------------------------

-- Empty set

∅ : ∀{ℓ} → Ord ℓ
∅ {ℓ} = sup Empty λ()
  where data Empty : Set ℓ where

IsEmpty : ∀{ℓ} (a : Ord ℓ) → Set (lsuc ℓ)
IsEmpty {ℓ} a = ∀ {c : Ord ℓ} → c ∉ a

∅-elim : ∀{ℓ} → IsEmpty (∅ {ℓ})
∅-elim (() , _)

IsInhabited : ∀{ℓ} (a : Ord ℓ) → Set (lsuc ℓ)
IsInhabited a = ∃ λ c → c ∈ a

emptyNotInhabited : ∀{ℓ} {a : Ord ℓ} → IsEmpty a → ¬ IsInhabited a
emptyNotInhabited p (c , q) = p q

inhabitedNotEmpty : ∀{ℓ} {a : Ord ℓ} → IsInhabited a → ¬ IsEmpty a
inhabitedNotEmpty (c , q) p = p q

-- Singleton set

sg : ∀{ℓ} (a : Ord ℓ) → Ord ℓ
sg {ℓ} a = sup Unit λ _ → a
  where record Unit : Set ℓ where

sg-intro : ∀{ℓ} (a : Ord ℓ) → a ∈ sg a
sg-intro a = _ , ≅-refl a

sg-elim : ∀{ℓ} {c a : Ord ℓ} (p : c ∈ sg a) → c ≅ a
sg-elim (_ , e) = e

sg-cong : ∀{ℓ} {a b : Ord ℓ} (e : a ≅ b) → sg a ≅ sg b
sg-cong e = (λ _ → _ , e) , (λ _ → _ , ≅-sym e)

sg-inhabited : ∀{ℓ} {a : Ord ℓ} → IsInhabited (sg a)
sg-inhabited {a = a} = a , sg-intro a

SubSingleton : ∀{ℓ} (a b : Ord ℓ) → Set ℓ
SubSingleton a b = a ⊂ sg b

IsSg : ∀{ℓ} (a : Ord ℓ) → Set (lsuc ℓ)
IsSg a = ∃ λ b → a ≅ sg b

-- Putting two elements into a set
-- Forms {a,b}; not to be confused with the tuple (a,b)

data Two {ℓ} : Set ℓ where
  true false : Two

pair : ∀{ℓ} (a b : Ord ℓ) → Ord ℓ
pair a b = sup Two λ where true → a; false → b

pair-introˡ : ∀{ℓ} {a b : Ord ℓ} → a ∈ pair a b
pair-introˡ = true , ≅-refl _

pair-introʳ : ∀{ℓ} {a b : Ord ℓ} → b ∈ pair a b
pair-introʳ = false , ≅-refl _

pair-elim :  ∀{ℓ} {c a b : Ord ℓ} (p : c ∈ pair a b) → (c ≅ a) ⊎ (c ≅ b)
pair-elim (true  , e) = inj₁ e
pair-elim (false , e) = inj₂ e

pair-cong : ∀{ℓ} {a a' b b' : Ord ℓ} (p : a ≅ a') (q : b ≅ b') → pair a b ≅ pair a' b'
pair-cong p q = (λ{ true → true , p       ; false → false , q      })
              , (λ{ true → true , ≅-sym p ; false → false , ≅-sym q})

pair-inhabited : ∀{ℓ} {a b : Ord ℓ} → IsInhabited (pair a b)
pair-inhabited {a = a} = a , true , ≅-refl a

-- Union of two sets

_∪_ : ∀{ℓ} (a b : Ord ℓ) → Ord ℓ
a ∪ b = sup (_ ⊎ _) λ where
  (inj₁ i) → a ` i
  (inj₂ j) → b ` j

∪-introˡ : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ a) → c ∈ (a ∪ b)
∪-introˡ {a = sup _ f} (i , e) = inj₁ i , e

∪-introʳ : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ b) → c ∈ (a ∪ b)
∪-introʳ {b = sup _ g} (i , e) = inj₂ i , e

∪-elim : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ (a ∪ b)) → (c ∈ a) ⊎ (c ∈ b)
∪-elim {a = sup _ f} (inj₁ i , e) = inj₁ (i , e)
∪-elim {b = sup _ g} (inj₂ i , e) = inj₂ (i , e)

∪-case : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ (a ∪ b)) {q} {Q : Set q} (left : c ∈ a → Q) (right : c ∈ b → Q) → Q
∪-case p left right = [ left , right ]′ (∪-elim p)

∪-split : ∀{ℓ q} {Q : Set q} {a b c : Ord ℓ} (left : c ∈ a → Q) (right : c ∈ b → Q) (p : c ∈ (a ∪ b)) → Q
∪-split left right p = ∪-case p left right

∪-mon : ∀{ℓ} {a a' b b' : Ord ℓ} (a⊂a' : a ⊂ a') (b⊂b' : b ⊂ b') → (a ∪ b) ⊂ (a' ∪ b')
∪-mon a⊂a' b⊂b' = ⊂-intro (∪-split (λ c∈a → ∪-introˡ (⊂-elim a⊂a' c∈a))
                                   (λ c∈b → ∪-introʳ (⊂-elim b⊂b' c∈b)))

∪-cong : ∀{ℓ} {a a' b b' : Ord ℓ} (a≅a' : a ≅ a') (b≅b' : b ≅ b') → (a ∪ b) ≅ (a' ∪ b')
∪-cong (a⊂a' , a'⊂a) (b⊂b' , b'⊂b) = ∪-mon a⊂a' b⊂b' , ∪-mon a'⊂a b'⊂b

-- Union of a family of sets

⋃ᶠ : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) → Ord ℓ
⋃ᶠ {ℓ} {I} f = sup (Σ I λ i → Br (f i)) λ p → f (proj₁ p) ` proj₂ p

⋃ᶠ-intro : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} {i : I} (p : c ∈ f i) → c ∈ ⋃ᶠ f
⋃ᶠ-intro f {c} {i} p = let
    j , e = ∈-elim p
  in (i , j) , e

⋃ᶠ-elim : ∀{ℓ} {I : Set ℓ} (f : I → Ord ℓ) {c : Ord ℓ} (p : c ∈ ⋃ᶠ f) → ∃ λ i → c ∈ f i
⋃ᶠ-elim _ ((i , j) , e) = i , ∈-intro (j , e)

⋃ᶠ-mon : ∀{ℓ} {I : Set ℓ} {f f' : I → Ord ℓ} (p : ∀ i → f i ⊂ f' i) → ⋃ᶠ f ⊂ ⋃ᶠ f'
⋃ᶠ-mon {f = f} {f'} p = ⊂-intro λ c∈⋃ᶠf → let
    i , q = ⋃ᶠ-elim f c∈⋃ᶠf
  in ⋃ᶠ-intro f' (⊂-elim (p i) q)

⋃ᶠ-cong : ∀{ℓ} {I : Set ℓ} {f f' : I → Ord ℓ} (p : ∀ i → f i ≅ f' i) → ⋃ᶠ f ≅ ⋃ᶠ f'
⋃ᶠ-cong p = ⋃ᶠ-mon (λ i → proj₁ (p i))
          , ⋃ᶠ-mon (λ i → proj₂ (p i))

-- Union of a set of sets

⋃ : ∀{ℓ} (a : Ord ℓ) → Ord ℓ
⋃ (sup _ f) = ⋃ᶠ f

⋃-intro : ∀{ℓ} {a b : Ord ℓ} (p : b ∈ a) → b ⊂ ⋃ a
⋃-intro {a = sup _ f} (i , b≅fi) = ⊂-intro λ c∈b → let
    j , d = ∈-elim (∈-congʳ c∈b b≅fi)
  in (i , j) , d

⋃-elim : ∀{ℓ} {a c : Ord ℓ} (p : c ∈ ⋃ a) → ∃ λ b → (b ∈ a) × (c ∈ b)
⋃-elim {a = sup _ f} ((i , j) , e) = f i , (i , ≅-refl _) , ∈-intro (j , e)


-- Comprehension (restriction)

_∣_ : ∀{ℓ} (a : Ord ℓ) (P : Ord ℓ → Set ℓ) → Ord ℓ
a ∣ P = sup (∃ λ i → P (a ` i)) λ p → a ` proj₁ p

compr-intro : ∀{ℓ} {a c : Ord ℓ} {P : Ord ℓ → Set ℓ} (resp : IsPred P)
  (q : c ∈ a) (p : P c) → c ∈ (a ∣ P)
compr-intro resp q p = let
    i , e = ∈-elim q
  in (i , resp e p) , e

compr-elimˡ : ∀{ℓ} {a c : Ord ℓ} {P : Ord ℓ → Set ℓ} (q : c ∈ (a ∣ P)) → c ∈ a
compr-elimˡ ((i , j) , e) = ∈-intro (i , e)

compr-elimʳ : ∀{ℓ} {a c : Ord ℓ} {P : Ord ℓ → Set ℓ} (resp : IsPred P) (q : c ∈ (a ∣ P)) → P c
compr-elimʳ resp ((i , j) , e) = resp (≅-sym e) j

-- Intersection of two sets

_∩_ : ∀{ℓ} (a b : Ord ℓ) → Ord ℓ
a ∩ b = a ∣ (_∈ b)

∩-intro : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ a) (q : c ∈ b) → c ∈ (a ∩ b)
∩-intro p q = let
    i , d = ∈-elim p
  in (i , ∈-congˡ (≅-sym d) q) , d

∩-elimˡ : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ (a ∩ b)) → c ∈ a
∩-elimˡ ((i , j) , e) = ∈-intro (i , e)

∩-elimʳ : ∀{ℓ} {a b c : Ord ℓ} (p : c ∈ (a ∩ b)) → c ∈ b
∩-elimʳ ((i , j) , e) = ∈-congˡ e j

-- Intersection of a non-empty family...

⋂ᶠ : ∀{ℓ} {I : Set ℓ} (i : I) (f : I → Ord ℓ) → Ord ℓ
⋂ᶠ i f = f i ∣ λ a → ∀ i′ → a ∈ f i′

⋂ᶠ-intro : ∀{ℓ} {I : Set ℓ} {i : I} {f : I → Ord ℓ} {a} (r : ∀ j → a ∈ f j) → a ∈ ⋂ᶠ i f
⋂ᶠ-intro {i = i} r = let
    k , p = ∈-elim (r i)
  in (k , λ j → ∈-congˡ (≅-sym p) (r j)) , p

-- Intersection of an inhabited set

⋂ : ∀{ℓ} (a : Ord ℓ) (inh : IsInhabited a) → Ord ℓ
⋂ (sup _ f) (b , i , b≅fi) = ⋂ᶠ i f

_∈∀∈_ : ∀{ℓ} (a b : Ord ℓ) → Set (lsuc ℓ)
c ∈∀∈ a = ∀ {b} → b ∈ a → c ∈ b

⋂-intro : ∀{ℓ} {a : Ord ℓ} {inh : IsInhabited a} {c} (r : c ∈∀∈ a) → c ∈ ⋂ a inh
⋂-intro {a = sup _ f} {b , i , b≅fi} r = ⋂ᶠ-intro λ j → r (j , ≅-refl _)
