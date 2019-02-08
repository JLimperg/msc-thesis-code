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

-- The → part of the isomorphism

the≤ : ∀ {β} → Tree≤ β → Tree
the≤ {β} refl = β
the≤ (lt i le) = the≤ le

the< : ∀ {β} → Tree< β → Tree
the< (lt i le) = the≤ le

theproof≤ : ∀ {β} (le : Tree≤ β) → the≤ le ≤ β
theproof≤ refl = refl
theproof≤ (lt i le) = lt i (theproof≤ le)

theproof< : ∀ {β} (lt : Tree< β) → the< lt < β
theproof< (lt i le) = lt i (theproof≤ le)

-- The ← part of the isomorphism

toTree≤ : ∀{β} → (∃ λ α → α ≤ β) → Tree≤ β
toTree≤ (α , refl) = refl
toTree≤ (α , lt i α≤β) = lt i (toTree≤ (α , α≤β))

toTree< : ∀{β} → (∃ λ α → α < β) → Tree< β
toTree< (α , lt i le) = lt i (toTree≤ (α , le))

-- Proof of isomorphism

isoTree≤₁ : ∀{β} (≤β : Tree≤ β) → toTree≤ (the≤ ≤β , theproof≤ ≤β) ≡ ≤β
isoTree≤₁ refl = refl
isoTree≤₁ (lt i ≤β) = cong (lt i) (isoTree≤₁ ≤β)

isoTree≤₂ₐ : ∀{α β} (α≤β : α ≤ β) → the≤ (toTree≤ (α , α≤β)) ≡ α
isoTree≤₂ₐ refl = refl
isoTree≤₂ₐ (lt i α≤β) = isoTree≤₂ₐ α≤β


isoTree<₁ : ∀{β} (<β : Tree< β) → toTree< (the< <β , theproof< <β) ≡ <β
isoTree<₁ (lt i ≤β) = cong (lt i) (isoTree≤₁ ≤β)

isoTree<₂ₐ : ∀{α β} (α<β : α < β) → the< (toTree< (α , α<β)) ≡ α
isoTree<₂ₐ (lt i α≤β) = isoTree≤₂ₐ α≤β



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
  → ∀ {α} β → (β<α : β < α) → fix< t β β<α ≡ fix t β
fix<-unfold {ℓ} {C} t β (lt i le) = fix≤-unfold t β le


-- Irreflexivity from well-foundedness

irrefl' :  ∀{α} (α<α : α < α) (r : Acc _<_ α) → ⊥
irrefl' α<α (acc h) = irrefl' α<α (h _ α<α)

irrefl :  ∀{α} (α<α : α < α) → ⊥
irrefl {α} α<α = irrefl' α<α (wf α)

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

trans-<-≤ : ∀{α β γ} (α<β : α < β) (β≤γ : β ≤ γ) → α < γ
trans-<-≤ α<β refl = α<β
trans-<-≤ α<β (lt i β≤γ) = lt i (≤-from-< (trans-<-≤ α<β β≤γ))

-- WRONG:
-- trans-≤-lt : ∀{I} {f : I → Tree} {i} {β γ} (fi≤β : f i ≤ β) (β≤γ : β ≤ γ) →
--   trans-≤ (lt i fi≤β) β≤γ ≡ lt i (trans-≤ fi≤β β≤γ)
-- trans-≤-lt = ?

castTree≤ : ∀{α β} (α≤β : α ≤ β) → Tree≤ α → Tree≤ β
castTree≤ α≤β ≤α = toTree≤ (the≤ ≤α , trans-≤ (theproof≤ ≤α) α≤β)

the≤-cast : ∀{α β} (α≤β : α ≤ β) (≤α : Tree≤ α) → the≤ (castTree≤ α≤β ≤α) ≡ the≤ ≤α
the≤-cast α≤β ≤α = isoTree≤₂ₐ {the≤ ≤α} (trans-≤ (theproof≤ ≤α) α≤β)

castTree< : ∀{α β} (α≤β : α ≤ β) → Tree< α → Tree< β
castTree< α≤β <α = toTree< (the< <α , trans-<-≤ (theproof< <α) α≤β)

the<-cast : ∀{α β} (α≤β : α ≤ β) (<α : Tree< α) → the< (castTree< α≤β <α) ≡ the< <α
the<-cast α≤β <α = isoTree<₂ₐ {the< <α} (trans-<-≤ (theproof< <α) α≤β)


-- Natural numbers and ω

tzero : Tree
tzero = sup ⊥ λ()

tsuc : Tree → Tree
tsuc t = sup ⊤ (λ _ → t)

embℕ : (n : ℕ) → Tree
embℕ zero = tzero
embℕ (suc n) = tsuc (embℕ n)

tomega : Tree
tomega = sup ℕ embℕ

-- Not provable with current _≤_
-- {-# TERMINATING #-}
-- cong-tsuc : ∀{a b : Tree} (a≤b : a ≤ b) → tsuc a ≤ tsuc b
-- cong-tsuc {a = sup I f} {b = sup I f} refl = refl
-- cong-tsuc {sup I f} {sup J g} (lt i a≤b)
--   = trans-≤
--       (cong-tsuc {a = sup I f} {b = g i} a≤b)
--       (cong-tsuc {a = g i} {b = sup J g} (lt i refl))
--
-- And thus probably also not provable:
--
-- ≤-tzero-embℕ : ∀ {n} → tzero ≤ embℕ n
-- ≤-tzero-embℕ {zero} = refl
-- ≤-tzero-embℕ {suc n} = lt _ ≤-tzero-embℕ
--
-- embℕ-≤ : ∀ {n m} → n ℕ.≤ m → embℕ n ≤ embℕ m
-- embℕ-≤ ℕ.z≤n = ≤-tzero-embℕ
-- embℕ-≤ (ℕ.s≤s n≤m) = {!!} -- needs cong-tsuc


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
◆ A α = Σ (Tree< α) \ <α → A (the< <α)

MuBody : ∀{ℓ} (F : Set ℓ → Set ℓ) {α} (rec : ∀ β (β<α : β < α) → Set ℓ) → Set ℓ
MuBody F {α} rec = Σ (Tree< α) \ <α → F (rec (the< <α) (theproof< <α))

Mu^ : ∀{ℓ} (F : Set ℓ → Set ℓ) → (α : Tree) → Set ℓ
Mu^ F = fix (MuBody F)

-- if we erased types these would just be the identity function
Mu^-fold : ∀{ℓ} {F : Set ℓ → Set ℓ} → (∀ {A B} → (A → B) → F A → F B)
  → ∀ α → (◆ (\ i → F (Mu^ F i)) α) → Mu^ F α
Mu^-fold {F = F} map
  = fix \ { {β} rec (γ , x) → γ , map (subst (λ A → A) (sym (fix<-unfold _ _ (theproof< γ)))) x }

Mu^-unfold : ∀{ℓ} {F : Set ℓ → Set ℓ} → (∀ {A B} → (A → B) → F A → F B)
  → ∀ α → Mu^ F α → (◆ (\ i → F (Mu^ F i)) α)
Mu^-unfold {F = F} map = fix \ { {β} rec (γ , x)
           → γ , map (subst (λ A → A) ((fix<-unfold _ _ (theproof< γ)))) x }

monMu^ : ∀{ℓ} (F : Set ℓ → Set ℓ) {α β} → α ≤ β → Mu^ F α → Mu^ F β
monMu^ F {β = β} α≤β (<α , FMu<α) .proj₁ = castTree< α≤β <α
monMu^ F {β = β} α≤β (<α , FMu<α) .proj₂ =
  subst F (sym (fix<-unfold (MuBody F) (the< (castTree< α≤β <α)) (theproof< (castTree< α≤β <α))))
 (subst (λ z → F (Mu^ F z)) (sym (the<-cast α≤β <α))
 (subst F (fix<-unfold (MuBody F) (the< <α) (theproof< <α))
  FMu<α))

EqMu^ : ∀{ℓ} (F : Set ℓ → Set ℓ) (Frel : ∀ {A} → (R : A → A → Set ℓ) → F A → F A → Set ℓ)
                       (m : Map ℓ F) (α : Tree) (t t' : Mu^ F α) → Set ℓ
EqMu^ F Frel m = fix \ {α} rec → SymTrans \ t t' →
  let
     (β , t) = Mu^-unfold m α t
     (β' , t') = Mu^-unfold m α t'
   in Σ (the< β ≤ the< β') \ β≤β' → Frel (rec (the< β') (theproof< β')) (m (monMu^ F β≤β') t) t'

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


module _ {ℓ} {F : Set ℓ → Set ℓ}
  (Frel : ∀ {A} → Rel A ℓ → Rel (F A) ℓ)
  (map : Map ℓ F)
  where

  private
    EqMu′ : ∀ {α} (t t′ : Mu α F) → Set ℓ
    EqMu′ = EqMu _ F Frel map


  EqMu-refl : ∀ {α} {t : Mu α F} → EqMu′ t t
  EqMu-refl {sup I f} {t} = `base (refl , {!!})


  monMu-mono : ∀ {α β} (α≤β : α ≤ β) {t t′}
    → EqMu′ t t′
    → EqMu′ (monMu map α≤β t) (monMu map α≤β t′)
  monMu-mono {sup I f} {sup .I .f} refl {sh , pos} {sh′ , pos′} eq = eq
  monMu-mono {sup I f} {sup I′ f′} (lt i α≤β) {sh , pos} {sh′ , pos′} (`base (fsh≤fsh′ , eq))
    = `base (refl , {!!})
  monMu-mono {sup I f} {sup I′ f′} α≤β (`sym eq)
    = `sym (monMu-mono α≤β eq)
  monMu-mono {sup I f} {sup I′ f′} α≤β (`trans eq₁ eq₂)
    = `trans (monMu-mono α≤β eq₁) (monMu-mono α≤β eq₂)


  monMu-trans : ∀ {α β γ} (α≤β : α ≤ β) (β≤γ : β ≤ γ) x
    → EqMu′
        (monMu map β≤γ (monMu map α≤β x))
        (monMu map (trans-≤ α≤β β≤γ) x)
  monMu-trans {α} {.(sup I f)} {sup I f} α≤β refl x = {!`base!}
  monMu-trans {α} {β} {sup I f} α≤β (lt i β≤γ) x = {!!}


monMu-irr : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β α≤β' : α ≤ β) (x : Mu α F) → monMu m α≤β x ≡ monMu m α≤β' x
monMu-irr m refl refl x = refl
monMu-irr m refl (lt i α≤β') x = {!!}
monMu-irr m (lt i α≤β) refl x = {!!}
monMu-irr m {sup I f} (lt i α≤fi) (lt j α≤fj) x = {!!}
  -- Cannot prove this since size component of x is different
  -- (i ≠ j)

monMu-coh : ∀ {ℓ F} (m : Map ℓ F) {α β γ}
  → ∀ (α≤β : α ≤ β) (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) x
  → monMu m β≤γ (monMu m α≤β x) ≡ monMu m α≤γ x
monMu-coh m refl refl refl x = refl
monMu-coh m refl refl (lt i α≤γ) (i′ , f) = {!!}
monMu-coh m refl (lt i β≤γ) α≤γ x = {!!}
monMu-coh m (lt i α≤β) β≤γ α≤γ x = {!!}


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

-- A chain is a functor from Tree to Set

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
