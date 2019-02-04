{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Level using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel ; module Preorder)
  renaming (Preorder to Preorder')
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Function using (id; _∘_; _∘′_)

open import Data.Empty using (⊥) -- renaming (preorder to Zero)
open import Data.Unit using (⊤) renaming (preorder to One)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using
  (_×_; ∃; Σ; Σ-syntax ; ∃-syntax ; proj₁; proj₂ ; _,_; <_,_>)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Induction.WellFounded using (WellFounded; Acc; acc; module All)

import Data.Nat as ℕ


-- Symmetric-Transitive closure of a relation.
-- (There might be better choices of constructors).
data SymTrans {ℓ ℓ'} {A : Set ℓ} (R : A → A → Set ℓ') : A → A → Set (ℓ ⊔ ℓ') where
  `base : ∀ {x y} → R x y → SymTrans R x y
  `sym : ∀ {x y} → SymTrans R y x → SymTrans R x y
  `trans : ∀ {x y z} → SymTrans R x y → SymTrans R y z → SymTrans R x z

lone = lsuc lzero
Preorder = Preorder' lzero lzero lzero

-- Zero : Preorder
-- Zero .Preorder.Carrier = ⊥
-- Zero .Preorder._≈_ ()
-- Zero .Preorder._∼_ ()
-- Zero .Preorder.isPreorder .Relation.Binary.IsPreorder.isEquivalence .Relation.Binary.IsEquivalence.refl {}
-- Zero .Preorder.isPreorder .Relation.Binary.IsPreorder.isEquivalence .Relation.Binary.IsEquivalence.sym {}
-- Zero .Preorder.isPreorder .Relation.Binary.IsPreorder.isEquivalence .Relation.Binary.IsEquivalence.trans {}
-- Zero .Preorder.isPreorder .Relation.Binary.IsPreorder.reflexive {}
-- Zero .Preorder.isPreorder .Relation.Binary.IsPreorder.trans {}

_+̇_ : ∀{A B C D : Set} (f : A → C) (g : B → D) → A ⊎ B → C ⊎ D
f +̇ g = [ inj₁ ∘ f , inj₂ ∘ g ]

_×̇′_ : ∀{A B C D : Set} (f : A → C) (g : B → D) → A × B → C × D
f ×̇′ g = < f ∘ proj₁ , g ∘ proj₂ >

-- Trees branching over small preorders
-- Tree = 𝕎 Set id

data Tree : Set₁ where
  sup : (I : Set) (f : I → Tree) → Tree

data _≤_ (α : Tree) : (β : Tree) → Set where
  refl : α ≤ α
  lt   : ∀ {I f} i (le : α ≤ f i) → α ≤ sup I f

data _<_ (α : Tree) : (β : Tree) → Set where
  lt   : ∀ {I f} i (le : α ≤ f i) → α < sup I f

-- Tree≤ β ≅ ∃ (\ α → α ≤ β)   but in Set rather than Set₁
data Tree≤_ : (β : Tree) → Set where
  refl : ∀ {α} → Tree≤ α -- α gets forced
  lt   : ∀ {I f} i (le : Tree≤ f i) → Tree≤ sup I f

-- Tree< β ≅ ∃ (\ α → α < β)   but in Set rather than Set₁
data Tree<_ : (β : Tree) → Set where
  lt   : ∀ {I f} i (le : Tree≤ f i) → Tree< sup I f

theα≤ : ∀ {β} → Tree≤ β → Tree
theα≤ {β} refl = β
theα≤ (lt i le) = theα≤ le

theα< : ∀ {β} → Tree< β → Tree
theα< (lt i le) = theα≤ le

theproof≤ : ∀ {β} (le : Tree≤ β) → theα≤ le ≤ β
theproof≤ refl = refl
theproof≤ (lt i le) = lt i (theproof≤ le)

theproof< : ∀ {β} (lt : Tree< β) → theα< lt < β
theproof< (lt i le) = lt i (theproof≤ le)


≤-from-< : ∀{α β} (α<β : α < β) → α ≤ β
≤-from-< (lt i α≤fi) = lt i α≤fi


-- Wellfoundedness of _<_

acc-dest : ∀{I f} (h : Acc _<_ (sup I f)) i → Acc _<_ (f i)
acc-dest (acc h) i = acc λ α α<fi → h α (lt i (≤-from-< α<fi))

acc-down : ∀{α β} (α≤β : α ≤ β) → Acc _<_ β → Acc _<_ α
acc-down refl = id
acc-down (lt i α≤fi) h = acc-down α≤fi (acc-dest h i)

acc-sup : ∀{I f} (h : ∀ i → Acc _<_ (f i)) → Acc _<_ (sup I f)
acc-sup h = acc λ{ α (lt i α≤fi) → acc-down α≤fi (h i)}

wf : WellFounded _<_
wf (sup I f) = acc-sup λ i → wf (f i)

-- Tree recursion

mutual
  fix : ∀{ℓ} {C : Tree → Set ℓ}
    → (t : ∀ {α} (r : ∀ β (β<α : β < α) → C β) → C α)
    → ∀ α → C α
  fix {ℓ} {C} t α = t (fix< t)

  fix< : ∀{ℓ} {C : Tree → Set ℓ}
    → (t : ∀ {α} (r : ∀ β (β<α : β < α) → C β) → C α)
    → ∀ {α} β → β < α → C β
  fix< {ℓ} {C} t β (lt i le) = fix≤ t β le

  fix≤ : ∀{ℓ} {C : Tree → Set ℓ}
    → (t : ∀ {α} (r : ∀ β (β<α : β < α) → C β) → C α)
    → ∀ {α} β → β ≤ α → C β
  fix≤ {ℓ} {C} t β refl = fix t β
  fix≤ {ℓ} {C} t β (lt i le) = fix≤ t β le

  fix≤-unfold : ∀{ℓ} {C : Tree → Set ℓ}
    → (t : ∀ {α} (r : ∀ β (β<α : β < α) → C β) → C α)
    → ∀ {α} β → (le : β ≤ α) → fix≤ t β le ≡ fix t β
  fix≤-unfold {ℓ} {C} t β refl = refl
  fix≤-unfold {ℓ} {C} t β (lt i le) = fix≤-unfold t β le

  fix<-unfold : ∀{ℓ} {C : Tree → Set ℓ}
    → (t : ∀ {α} (r : ∀ β (β<α : β < α) → C β) → C α)
    → ∀ {α} β → (le : β < α) → fix< t β le ≡ fix t β
  fix<-unfold {ℓ} {C} t β (lt i le) = fix≤-unfold t β le


-- {-# TERMINATING #-}
-- fix t (sup I f) = t λ{ β (lt i β≤fi) → fix t β}

-- Irreflexivity from well-foundedness

irrefl' :  ∀{α} (α<α : α < α) (r : Acc _<_ α) → ⊥
irrefl' α<α (acc h) = irrefl' α<α (h _ α<α)

irrefl :  ∀{α} (α<α : α < α) → ⊥
irrefl {α} α<α = irrefl' α<α (wf α)

-- mutual
--   data _<_ (α : Tree) : (β : Tree) → Set where
--     <sup : ∀ {I} {f : Preorder.Carrier I → Tree} {i} (le : α ≤ f i) → α < sup I f

--   data _≤_ (α : Tree) : (β : Tree) → Set where
--     refl : α ≤ α
--     lt   : ∀{β} (lt : α < β) → α ≤ β

mutual
  predL : ∀{β I f i} (α≤β : sup I f ≤ β) → f i ≤ β
  predL = ≤-from-< ∘ predL<

  predL< : ∀{β I f i} (α≤β : sup I f ≤ β) → f i < β
  predL< refl       = lt _ refl
  predL< (lt i α≤β) = lt i (predL α≤β)

trans-≤ : ∀{α β γ} (α≤β : α ≤ β) (β≤γ : β ≤ γ) → α ≤ γ
trans-≤ α≤β refl    = α≤β
trans-≤ α≤β (lt i β≤γ) = lt i (trans-≤ α≤β β≤γ)

trans-≤-< : ∀{α β γ} (α≤β : α ≤ β) (β≤γ : β < γ) → α < γ
trans-≤-< α≤β (lt i β≤γ) = lt i (trans-≤ α≤β β≤γ)

trans-≤-refl : ∀{α β} (α≤β : α ≤ β) → trans-≤ refl α≤β ≡ α≤β
trans-≤-refl refl = refl
trans-≤-refl (lt i α≤β) = cong (lt i) (trans-≤-refl α≤β)

-- WRONG:
-- trans-≤-lt : ∀{I} {f : I → Tree} {i} {β γ} (fi≤β : f i ≤ β) (β≤γ : β ≤ γ) →
--   trans-≤ (lt i fi≤β) β≤γ ≡ lt i (trans-≤ fi≤β β≤γ)
-- trans-≤-lt = ?


-- Resp-PO : (I : Preorder) (f : Preorder.Carrier I → Tree) → Set
-- Resp-PO I f = ∀{i j} (i≤j : Preorder._∼_ I i j) → f i ≤ f j

-- data IsON : Tree → Set₁ where
--   sup : ∀{I f} (mon : Resp-PO I f) (node : ∀ i → IsON (f i)) → IsON (sup I f)

-- record ON : Set₂ where
--   constructor on; field
--     tree : Tree
--     isOn : IsON tree
-- open ON

-- on-≤ : ∀{a b}  (a≤b : a ≤ b) (β : IsON b) → IsON a
-- on-≤ refl     β              = β
-- on-≤ (lt i a≤b) (sup mon f) = on-≤ a≤b (f i)

-- Zero

tzero : Tree
tzero = sup ⊥ λ()

-- tzero : Tree
-- tzero = sup Zero λ()

-- iozero : IsON tzero
-- iozero = sup (λ{}) λ()

-- ozero : ON
-- ozero = on tzero iozero

-- Successor

tsuc : Tree → Tree
tsuc t = sup ⊤ (λ _ → t)

-- tsuc : Tree → Tree
-- tsuc t = sup One (λ _ → t)

-- iosuc : ∀{t : Tree} (α : IsON t) → IsON (tsuc t)
-- iosuc α = sup (λ _ → refl) (λ _ → α)

-- osuc : ON → ON
-- osuc (on t α) = on (tsuc t) (iosuc α)

-- ω

embℕ : (n : ℕ) → Tree
embℕ zero = tzero
embℕ (suc n) = tsuc (embℕ n)

tomega : Tree
tomega = sup ℕ embℕ

-- Not provable with current _≤_
-- cong-tsuc : ∀{a b : Tree} (a≤b : a ≤ b) → tsuc a ≤ tsuc b
-- cong-tsuc a≤b = {!!}

-- Category of sets and functions

HMap : ∀ ℓ (F G : Set ℓ → Set ℓ) → Set (lsuc ℓ)
HMap ℓ F G = ∀{A B} (g : A → B) → F A → G B

Map : ∀ ℓ (F : Set ℓ → Set ℓ) → Set (lsuc ℓ)
Map ℓ F = HMap ℓ F F

-- Inductive types

-- Sized Mu defined by structural recursion
Mu : ∀{ℓ} (α : Tree) (F : Set ℓ → Set ℓ) → Set ℓ
Mu (sup I f) F = ∃[ i ] F (Mu (f i) F)  -- This should be an irrelevant size (union type)

-- Sized Mu defined by well-founded recursion
◆ : ∀ {ℓ} → (Tree → Set ℓ) → Tree → Set ℓ
◆ A α = Σ (Tree< α) \ α< → A (theα< α<)

Mu^ : ∀{ℓ} (F : Set ℓ → Set ℓ) → (α : Tree) → Set ℓ
Mu^ F = fix (\ {α} rec → Σ (Tree< α) \ α< → F (rec (theα< α<) (theproof< α<)))

-- if we erased types these would just be the identity function
Mu^-fold : ∀{ℓ} {F : Set ℓ → Set ℓ} → (∀ {A B} → (A → B) → F A → F B)
  → ∀ α → (◆ (\ i → F (Mu^ F i)) α) → Mu^ F α
Mu^-fold {F = F} map
  = fix \ { {β} rec (γ , x) → γ , map (subst (λ A → A) (sym (fix<-unfold _ _ (theproof< γ)))) x }

Mu^-unfold : ∀{ℓ} {F : Set ℓ → Set ℓ} → (∀ {A B} → (A → B) → F A → F B)
  → ∀ α → Mu^ F α → (◆ (\ i → F (Mu^ F i)) α)
Mu^-unfold {F = F} map = fix \ { {β} rec (γ , x)
           → γ , map (subst (λ A → A) ((fix<-unfold _ _ (theproof< γ)))) x }

monMu^ : ∀{ℓ} {F : Set ℓ → Set ℓ} → (∀ {A B} → (A → B) → F A → F B)
              → ∀ {α β} → α ≤ β → Mu^ F α → Mu^ F β
monMu^ = {!!}

EqMu^ : ∀{ℓ} (F : Set ℓ → Set ℓ) (Frel : ∀ {A} → (R : A → A → Set ℓ) → F A → F A → Set ℓ)
                       (m : Map ℓ F) (α : Tree) (t t' : Mu^ F α) → Set ℓ
EqMu^ F Frel m = fix \ {α} rec → SymTrans \ t t' →
  let
     (β , t) = Mu^-unfold m α t
     (β' , t') = Mu^-unfold m α t'
   in Σ (theα< β ≤ theα< β') \ β≤β' → Frel (rec (theα< β') (theproof< β')) (m (monMu^ m β≤β') t) t'

-- for each strictly positive functor there should be a closure ordinal
-- postulate
--   closure : ∀{ℓ} (F : Set ℓ → Set ℓ) → {- StrPos F -} -> Tree

-- theMu : ∀{ℓ} (F : Set ℓ → Set ℓ) → Set ℓ
-- theMu F = Mu^ F (closure F)

-- conjecture: we should implement expand to get con
-- module _ {ℓ} (F : Set ℓ → Set ℓ) (map : ∀ {A B} → (A → B) → F A → F B) where
--   expand : F (theMu F) → {- StrPos F -} → ◆ (\ i → F (Mu^ F i)) (closure F)
--   expand x = {!!}

--   con : F (theMu F) → theMu F
--   con x = Mu^-fold map (closure F) (expand x)



-- Monotonicity

mapMu : ∀{ℓ F G} (m : HMap ℓ F G) α → Mu α F → Mu α G
mapMu m (sup I f) (i , x) = i , m (mapMu m (f i)) x

monMu : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β : α ≤ β) → Mu α F → Mu β F
monMu m refl = id
monMu m {sup I f} (lt i α≤β) (_ , x) = i , m (monMu m (predL α≤β)) x

monMuℕ : ∀ {ℓ} {F : Set ℓ → Set ℓ} (map : Map ℓ F) {n m}
  → n ℕ.≤ m
  → Mu (embℕ n) F
  → Mu (embℕ m) F
monMuℕ map ℕ.z≤n (() , _)
monMuℕ map (ℕ.s≤s n≤m) (_ , s) = _ , map (monMuℕ map n≤m) s

-- Equality
{-
   Given a functor "D : S → Set" we can build the colimit as the quotient
      Colim D = Σ S D / ~
   where the relation ~ is the least equivalence relation generated by
      (s , d) ~ (s' , d') = ∃ (f : s -> s'). mapD f d = d'.

   The "∃ β" in "∃ β < α. Mu β F" should be translated as a colimit,
   so I define EqMu by encoding the quotienting relation "~".

   The question of whether our sizes are a linear order or whether α
   is "directed" is dodged here by instead allowing the proof of the
   equivalence to tell us which of β or β' is larger.

-}

EqMu : ∀ {ℓ} (α : Tree) (F : Set ℓ → Set ℓ)
  → (Frel : ∀ {A} → (A → A → Set ℓ) → F A → F A → Set ℓ)
  → (map : Map ℓ F)
  → (t t′ : Mu α F)
  → Set ℓ
EqMu (sup I f) F Frel map = SymTrans λ where
  (i , t) (i′ , t′) →
    let β  = f i
        β′ = f i′ in
    Σ[ β≤β′ ∈ β ≤ β′ ] Frel (EqMu β′ F Frel map) (map (monMu map β≤β′) t) t′

monMu-trans : ∀ {ℓ F} (m : Map ℓ F) {α β γ} (α≤β : α ≤ β)
               (β≤γ : β ≤ γ) x →
             monMu m β≤γ (monMu m α≤β x) ≡ monMu m (trans-≤ α≤β β≤γ) x
monMu-trans m α≤β refl x = refl
monMu-trans m refl β≤γ x rewrite trans-≤-refl β≤γ = refl
monMu-trans m {sup I f} {sup J g} (lt i₁ α≤β) (lt i β≤γ) (j , x) = {!!}
  -- monMu-trans m α≤β β≤γ x

monMu-irr : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β α≤β' : α ≤ β) (x : Mu α F) → monMu m α≤β x ≡ monMu m α≤β' x
monMu-irr m refl refl x = refl
monMu-irr m refl (lt i α≤β') x = {!!}
monMu-irr m (lt i α≤β) refl x = {!!}
monMu-irr m {sup I f} (lt i α≤fi) (lt j α≤fj) x = {!!}
  -- Cannot prove this since size component of x is different
  -- (i ≠ j)

monMu-coh : ∀ {ℓ F} (m : Map ℓ F) {α β γ} (α≤β : α ≤ β)
               (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) x →
             monMu m β≤γ (monMu m α≤β x) ≡ monMu m α≤γ x
monMu-coh m refl β≤γ α≤γ x = {!refl!}
monMu-coh m (lt i α≤β) β≤γ α≤γ x = {!!}

-- Constructor

inMu₁ : ∀{ℓ α F} (x : F (Mu α F)) → Mu {ℓ} (tsuc α) F
inMu₁ x = _ , x

inMu : ∀{ℓ F} (m : Map ℓ F) {α β} (α<β : α < β) (x : F (Mu α F)) → Mu β F
inMu m (lt i α≤β) x = i , m (monMu m α≤β) x

-- Destructor

outMu : ∀{ℓ F α} (x : Mu {ℓ} (tsuc α) F) → F (Mu α F)
outMu (_ , x) = x

-- Wellfounded recursion

-- {-# TERMINATING #-}
-- fixMu : ∀{ℓ} {F : Set ℓ → Set ℓ} {C : Tree → Set ℓ}
--   → (t : ∀ {α} (r : ∀ β (β<α : β < α) (y : Mu β F) → C β) (x : Mu α F) → C α)
--   → ∀ α (x : Mu α F) → C α
-- fixMu t (sup I f) = t λ{ β (lt i β≤fi) → fixMu t β}

-- Fixed point

Mu∞ : ∀{ℓ} (F : Set ℓ → Set ℓ) → Set (ℓ ⊔ lone)
Mu∞ F = ∃ λ α → Mu α F

inMu∞ : ∀ (F : ∀{ℓ} → Set ℓ → Set ℓ) {ℓ} (x : F (Mu∞ {ℓ} F)) → Mu∞ {ℓ} F
inMu∞ F = {!!}

-- Coinductive types

Nu : ∀{ℓ} (α : Tree) (F : Set ℓ → Set ℓ) → Set ℓ
Nu (sup I f) F = ∀ i → F (Nu (f i) F)

mapNu : ∀{ℓ F G} (m : HMap ℓ F G) α → Nu α F → Nu α G
mapNu m (sup I f) x i = m (mapNu m (f i)) (x i)

monNu : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β : α ≤ β) → Nu β F → Nu α F
monNu m refl = id
monNu m {sup I f} (lt i α≤β) x _ = m (monNu m (predL α≤β)) (x i)

monNu-irr : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β α≤β' : α ≤ β) (x : Nu β F) → monNu m α≤β x ≡ monNu m α≤β' x
monNu-irr m refl refl x = refl
monNu-irr m refl (lt i α≤β') x = {!!}
monNu-irr m (lt i α≤β) refl x = {!!}
monNu-irr m {sup I f} (lt i α≤fi) (lt j α≤fj) x = {!x j!}

monNu-coh : ∀ {ℓ F} (m : Map ℓ F) {α β γ} (α≤β : α ≤ β)
               (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) x →
             monNu m α≤β (monNu m β≤γ x) ≡ monNu m α≤γ x
monNu-coh m refl β≤γ α≤γ x = {!refl!}
monNu-coh m (lt i α≤β) β≤γ α≤γ x = {!!}

-- A chain it a functor from Tree to Set

record IsChain {ℓ} (A : Tree → Set ℓ) : Set (ℓ ⊔ lone) where
  constructor isChain; field

    mapCh : ∀{α β} (α≤β : α ≤ β) → (A α → A β)

    cohCh : ∀{α β γ} (α≤β : α ≤ β) (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) →

      mapCh β≤γ ∘ mapCh α≤β ≡ mapCh α≤γ
open IsChain

muChain : ∀{ℓ F} (m : Map ℓ F) → IsChain (λ α → Mu α F)
muChain m .mapCh = monMu m
muChain m .cohCh = {!monMu-comp!}

record IsOpChain {ℓ} (A : Tree → Set ℓ) : Set (ℓ ⊔ lone) where
  constructor isChain; field

    mapOpCh : ∀{α β} (α≤β : α ≤ β) → (A β → A α)

    cohOpCh : ∀{α β γ} (α≤β : α ≤ β) (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) →

      mapOpCh α≤β ∘ mapOpCh β≤γ ≡ mapOpCh α≤γ
open IsOpChain

nuChain : ∀{ℓ F} (m : Map ℓ F) → IsOpChain (λ α → Nu α F)
nuChain m .mapOpCh = monNu m
nuChain m .cohOpCh = {!monMu-comp!}

{-
-- Strictly positive types

TyVar = Fin

data _≥_ : (n m : ℕ) → Set where
  id≥  : ∀{n} → n ≥ n
  weak : ∀{n m} (n≤m : n ≥ m) → suc n ≥ m
  lift : ∀{n m} (n≤m : n ≥ m) → suc n ≥ suc m

wkTyVar : ∀ {n m} → TyVar m → n ≥ m → TyVar n
wkTyVar X       id≥ = X
wkTyVar X       (weak n≥m) = Fin.suc (wkTyVar X n≥m)
wkTyVar zero    (lift n≥m) = zero
wkTyVar (suc X) (lift n≥m) = suc (wkTyVar X n≥m)

{-
module Refinement where

  data Ty (n : ℕ) : Set where
    Var : (X : TyVar n) → Ty n
    0̂ 1̂ : Ty n
    _+̂_ _×̂_ : (a b : Ty n) → Ty n
    _→̂_ : (a : Ty 0) (b : Ty n) → Ty n
    μ̂ ν̂ : (a : Ty (suc n)) → Ty n

  wkTy : ∀{n m} (a : Ty m) (n≥m : n ≥ m) → Ty n
  wkTy = {!!}

  -- Refined types with embedded ordinals

  data RTy {n : ℕ} : (a : Ty n) → Set₂ where
    Var : ∀{x} → RTy (Var x)
    0̂ : RTy 0̂
    1̂ : RTy 1̂
    _+̂_ : ∀{a b} (A : RTy a) (B : RTy b) → RTy (a +̂ b)
    _×̂_ : ∀{a b} (A : RTy a) (B : RTy b) → RTy (a ×̂ b)
    _→̂_ : ∀{a b} (A : RTy a) (B : RTy b) → RTy (a →̂ b)
    μ̂ : ∀{a} (A : RTy a) → RTy (μ̂ a)
    ν̂ : ∀{a} (A : RTy a) → RTy (ν̂ a)
    Inf  Sup : ∀{a} (F : ON → RTy a) → RTy a
    Inf< Sup< : ∀{a} (α : ON) (F : ∀ β (β<α : β < tree α) → RTy a) → RTy a
    -- Mu  : (α : ON) (F : Ty (suc n)) (∀ β (lt : β < α) → Ty n) → Ty n

  -- Subtyping refined types

  data _<:_ {n} : {a : Ty n} (A B : RTy a) → Set₂ where
    μ̂ : ∀{a}{A B : RTy (μ̂ a)} (A<:B : A <: B) → μ̂ A <: μ̂ B
    ν̂ : ∀{a}{A B : RTy (μ̂ a)} (A<:B : A <: B) → ν̂ A <: ν̂ B
    InfL : ∀{a} {F : ON → RTy a} {B : RTy a} {α} (Fα<:B : F α <: B) → Inf F <: B
    SupR : ∀{a} {F : ON → RTy a} {A : RTy a} {α} (A<:Fα : A <: F α) → A <: Sup F
    InfR : ∀{a} {F : ON → RTy a} {A : RTy a} (F<:A : ∀ α → A <: F α) → A <: Inf F
    SupL : ∀{a} {F : ON → RTy a} {B : RTy a} (F<:A : ∀ α → F α <: B) → Sup F <: B

  ⊥̂ : ∀{n} {a : Ty n} → RTy a
  ⊥̂ = Inf< ozero λ{ β (lt {i = ()} z) }
-}

data Ty (n : ℕ) : Set₂ where
  Var : (X : TyVar n) → Ty n
  0̂ 1̂ : Ty n
  _+̂_ _×̂_ : (a b : Ty n) → Ty n
  _→̂_ : (a : Ty 0) (b : Ty n) → Ty n
  μ̂ ν̂ : (α : Tree) (f : Ty (suc n)) → Ty n

wkTy : ∀{n m} (a : Ty m) (n≥m : n ≥ m) → Ty n
wkTy (Var X) n≥m = Var (wkTyVar X n≥m)
wkTy 0̂       n≥m = 0̂
wkTy 1̂       n≥m = 1̂
wkTy (a +̂ b) n≥m = wkTy a n≥m +̂ wkTy b n≥m
wkTy (a ×̂ b) n≥m = wkTy a n≥m ×̂ wkTy b n≥m
wkTy (a →̂ b) n≥m = a →̂ wkTy b n≥m
wkTy (μ̂ α a) n≥m = μ̂ α (wkTy a (lift n≥m))
wkTy (ν̂ α a) n≥m = ν̂ α (wkTy a (lift n≥m))

-- Type interpretation

⦅_⦆ : ∀{n} (a : Ty n) {ℓ} (ρ : Vec (Set ℓ) n) → Set ℓ
⦅ Var X ⦆ ρ = lookup X ρ
⦅ 0̂ ⦆ ρ = Lift ⊥
⦅ 1̂ ⦆ ρ = Lift ⊤
⦅ a +̂ b ⦆ ρ = ⦅ a ⦆ ρ ⊎ ⦅ b ⦆ ρ
⦅ a ×̂ b ⦆ ρ = ⦅ a ⦆ ρ × ⦅ b ⦆ ρ
⦅ a →̂ b ⦆ {ℓ} ρ = ⦅ a ⦆ {ℓ} [] → ⦅ b ⦆ ρ
⦅ μ̂ α f ⦆ ρ = Mu α λ X → ⦅ f ⦆ (X ∷ ρ)
⦅ ν̂ α f ⦆ ρ = Nu α λ X → ⦅ f ⦆ (X ∷ ρ)

-- Functoriality

data Arr {ℓ} : ∀ {n} (ρ₁ ρ₂ : Vec (Set ℓ) n) → Set ℓ where
  [] : Arr [] []
  _∷_ : ∀{n} {A B : Set ℓ} {ρ₁ ρ₂ : Vec _ n} (f : A → B) (fs : Arr {ℓ} ρ₁ ρ₂) → Arr (A ∷ ρ₁) (B ∷ ρ₂)

lookupArr : ∀ {n} {ρ ρ′ : Vec Set n} (X : Fin n) → Arr ρ ρ′ → lookup X ρ → lookup X ρ′
lookupArr zero    (f ∷ fs) = f
lookupArr (suc X) (f ∷ fs) = lookupArr X fs

map : ∀{n} (a : Ty n) {ρ ρ′} (fs : Arr ρ ρ′) → ⦅ a ⦆ ρ → ⦅ a ⦆ ρ′
map (Var X) fs = lookupArr X fs
map 0̂       fs ()
map 1̂       fs = _
map (a +̂ b) fs = map a fs +̇ map b fs
map (a ×̂ b) fs = map a fs ×̇′ map b fs
map (a →̂ b) fs g = map b fs ∘′ g
map (μ̂ α F) fs = mapMu (λ g → map F (g ∷ fs)) α
map (ν̂ α F) fs = mapNu (λ g → map F (g ∷ fs)) α


record IsBoundedChain (ω : Tree) (A : ∀{α}.(α<ω : α < ω) → Set) : Set₁ where
  constructor isBoundedChain; field

    mapCh : ∀{β}.(β<ω : β < ω){α}.(α≤β : α ≤ β) →
      let .α<ω : _; α<ω = trans-≤-< α≤β β<ω in
      (A α<ω → A β<ω)

    cohCh : ∀{γ}.(γ<ω : γ < ω){α β} .(α≤β : α ≤ β) .(β≤γ : β ≤ γ) .(α≤γ : α ≤ γ) →
      let .β<ω : _; β<ω = trans-≤-< β≤γ γ<ω in
      mapCh γ<ω β≤γ ∘ mapCh β<ω α≤β ≡ mapCh γ<ω α≤γ

-- Size expressions

mutual

  data SizeCxt : Set where
    ε : SizeCxt
    _∙_ : (Ξ : SizeCxt) (s : SizeBound Ξ) → SizeCxt

  data SizeExpr : (Ξ : SizeCxt) → Set where

  data SizeBound : (Ξ : SizeCxt) → Set where
    Size : ∀{Ξ} → SizeBound Ξ
    <_   : ∀{Ξ} (s : SizeExpr Ξ) → SizeBound Ξ
    wk   : ∀{Ξ} ({a} b : SizeBound Ξ) → SizeBound (Ξ ∙ a)

  data SizeVar : (Ξ : SizeCxt) (s : SizeBound Ξ) → Set where
    vz : ∀{Ξ} {s : SizeBound Ξ} → SizeVar (Ξ ∙ s) (wk s)


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
