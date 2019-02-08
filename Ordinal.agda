{-# OPTIONS --postfix-projections #-}

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using
  (_×_; ∃; Σ; Σ-syntax ; ∃-syntax ; proj₁; proj₂ ; _,_; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function using (id; _∘_; _∘′_)
open import Induction.WellFounded using (WellFounded; Acc; acc; module All)
open import Level using (Level; _⊔_; Lift) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)

open import Util.Relation.Binary.PropositionalEquality using
  ( _≡_; refl; cong; subst; sym ; trans ; module ≡-Reasoning ; cast ; subst-trans
  ; subst-cong ; sym-cancel-l )

import Data.Nat as ℕ


-- Preliminaries

-- Symmetric-Transitive closure of a relation.
-- (There might be better choices of constructors).
data SymTrans {ℓ ℓ'} {A : Set ℓ} (R : A → A → Set ℓ') : A → A → Set (ℓ ⊔ ℓ') where
  `base : ∀ {x y} → R x y → SymTrans R x y
  `sym : ∀ {x y} → SymTrans R y x → SymTrans R x y
  `trans : ∀ {x y z} → SymTrans R x y → SymTrans R y z → SymTrans R x z

lone = lsuc lzero


-- Ordinals, ≤, <

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


-- Properties of ≤/<

≤-from-< : ∀{α β} (α<β : α < β) → α ≤ β
≤-from-< (lt i α≤fi) = lt i α≤fi

acc-dest : ∀{I f} (h : Acc _<_ (sup I f)) i → Acc _<_ (f i)
acc-dest (acc h) i = acc λ α α<fi → h α (lt i (≤-from-< α<fi))

acc-down : ∀{α β} (α≤β : α ≤ β) → Acc _<_ β → Acc _<_ α
acc-down refl = id
acc-down (lt i α≤fi) h = acc-down α≤fi (acc-dest h i)

acc-sup : ∀{I f} (h : ∀ i → Acc _<_ (f i)) → Acc _<_ (sup I f)
acc-sup h = acc λ{ α (lt i α≤fi) → acc-down α≤fi (h i)}

wf : WellFounded _<_
wf (sup I f) = acc-sup λ i → wf (f i)

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


-- Isomorphism between Tree≤ β and ∃[ α ] (α ≤ β)

the≤ : ∀ {β} → Tree≤ β → Tree
the≤ {β} refl = β
the≤ (lt i le) = the≤ le

theproof≤ : ∀ {β} (le : Tree≤ β) → the≤ le ≤ β
theproof≤ refl = refl
theproof≤ (lt i le) = lt i (theproof≤ le)

toTree≤ : ∀{β} → (∃[ α ] (α ≤ β)) → Tree≤ β
toTree≤ (α , refl) = refl
toTree≤ (α , lt i α≤β) = lt i (toTree≤ (α , α≤β))

isoTree≤₁ : ∀{β} (≤β : Tree≤ β) → toTree≤ (the≤ ≤β , theproof≤ ≤β) ≡ ≤β
isoTree≤₁ refl = refl
isoTree≤₁ (lt i ≤β) = cong (lt i) (isoTree≤₁ ≤β)

isoTree≤₂ₐ : ∀{α β} (α≤β : α ≤ β) → the≤ (toTree≤ (α , α≤β)) ≡ α
isoTree≤₂ₐ refl = refl
isoTree≤₂ₐ (lt i α≤β) = isoTree≤₂ₐ α≤β


-- Isomorphism between Tree< β and ∃[ α ] (α < β)

the< : ∀ {β} → Tree< β → Tree
the< (lt i le) = the≤ le

theproof< : ∀ {β} (lt : Tree< β) → the< lt < β
theproof< (lt i le) = lt i (theproof≤ le)

toTree< : ∀{β} → (∃[ α ] (α < β)) → Tree< β
toTree< (α , lt i le) = lt i (toTree≤ (α , le))

isoTree<₁ : ∀{β} (<β : Tree< β) → toTree< (the< <β , theproof< <β) ≡ <β
isoTree<₁ (lt i ≤β) = cong (lt i) (isoTree≤₁ ≤β)

isoTree<₂ₐ : ∀{α β} (α<β : α < β) → the< (toTree< (α , α<β)) ≡ α
isoTree<₂ₐ (lt i α≤β) = isoTree≤₂ₐ α≤β


-- Tree recursion

Rec : ∀ {ℓ} (C : Tree → Set ℓ) → Set (lone ⊔ ℓ)
Rec C = ∀ {α} (r : (<α : Tree< α) → C (the< <α)) → C α

module _ {ℓ} {C : Tree → Set ℓ} where

  mutual
    fix : Rec C → ∀ α → C α
    fix t _ = t (fix< t)

    fix< : Rec C → ∀ {α} (<α : Tree< α) → C (the< <α)
    fix< t (lt i le) = fix≤ t le

    fix≤ : Rec C → ∀ {α} (≤α : Tree≤ α) → C (the≤ ≤α)
    fix≤ t {α} refl = fix t α
    fix≤ t (lt i le) = fix≤ t le

  fix≤-unfold : ∀ (t : Rec C) {α} (≤α : Tree≤ α)
    → fix≤ t ≤α ≡ fix t (the≤ ≤α)
  fix≤-unfold t refl = refl
  fix≤-unfold t (lt i le) = fix≤-unfold t le

  fix<-unfold : ∀ (t : Rec C) {α} (<α : Tree< α)
    → fix< t <α ≡ fix t (the< <α)
  fix<-unfold t (lt i le) = fix≤-unfold t le

  fix≤-irr : ∀ (t : Rec C) {α β} (≤α : Tree≤ α) (≤β : Tree≤ β)
    → (eq : the≤ ≤α ≡ the≤ ≤β)
    → subst C eq (fix≤ t ≤α) ≡ fix≤ t ≤β
  fix≤-irr t ≤α ≤β eq = let open ≡-Reasoning in
    begin
      subst C eq (fix≤ t ≤α)
    ≡⟨ cong (subst C eq) (fix≤-unfold t ≤α) ⟩
      subst C eq (fix t (the≤ ≤α))
    ≡⟨ cong (subst C eq) (sym (subst-cong (fix t) (sym eq))) ⟩
      subst C eq (subst C (sym eq) (fix t (the≤ ≤β)))
    ≡⟨ subst-trans (sym eq) eq ⟩
      subst C (trans (sym eq) (eq)) (fix t (the≤ ≤β))
    ≡⟨ cong (λ eq → subst C eq (fix t (the≤ ≤β))) (sym-cancel-l eq) ⟩
      subst C refl (fix t (the≤ ≤β))
    ≡⟨⟩
      fix t (the≤ ≤β)
    ≡⟨ sym (fix≤-unfold t ≤β) ⟩
      fix≤ t ≤β
    ∎

  fix<-irr : ∀ (t : Rec C) {α β} (<α : Tree< α) (<β : Tree< β)
    → (eq : the< <α ≡ the< <β)
    → subst C eq (fix< t <α) ≡ fix< t <β
  fix<-irr t <α <β eq = let open ≡-Reasoning in
    begin
      subst C eq (fix< t <α)
    ≡⟨ cong (subst C eq) (fix<-unfold t <α) ⟩
      subst C eq (fix t (the< <α))
    ≡⟨ cong (subst C eq) (sym (subst-cong (fix t) (sym eq))) ⟩
      subst C eq (subst C (sym eq) (fix t (the< <β)))
    ≡⟨ subst-trans (sym eq) eq ⟩
      subst C (trans (sym eq) (eq)) (fix t (the< <β))
    ≡⟨ cong (λ eq → subst C eq (fix t (the< <β))) (sym-cancel-l eq) ⟩
      subst C refl (fix t (the< <β))
    ≡⟨⟩
      fix t (the< <β)
    ≡⟨ sym (fix<-unfold t <β) ⟩
      fix< t <β
    ∎


-- Upcasting Tree≤

castTree≤ : ∀{α β} (α≤β : α ≤ β) → Tree≤ α → Tree≤ β
castTree≤ α≤β ≤α = toTree≤ (the≤ ≤α , trans-≤ (theproof≤ ≤α) α≤β)

the≤-castTree≤ : ∀{α β} (α≤β : α ≤ β) (≤α : Tree≤ α) → the≤ (castTree≤ α≤β ≤α) ≡ the≤ ≤α
the≤-castTree≤ α≤β ≤α = isoTree≤₂ₐ {the≤ ≤α} (trans-≤ (theproof≤ ≤α) α≤β)


-- Upcasting Tree<

castTree< : ∀{α β} (α≤β : α ≤ β) → Tree< α → Tree< β
castTree< α≤β <α = toTree< (the< <α , trans-<-≤ (theproof< <α) α≤β)

the<-castTree< : ∀{α β} (α≤β : α ≤ β) (<α : Tree< α) → the< (castTree< α≤β <α) ≡ the< <α
the<-castTree< α≤β <α = isoTree<₂ₐ {the< <α} (trans-<-≤ (theproof< <α) α≤β)


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


-- Inductive types using structural recursion

Mu : ∀{ℓ} (α : Tree) (F : Set ℓ → Set ℓ) → Set ℓ
Mu (sup I f) F = ∃[ i ] F (Mu (f i) F)  -- This should be an irrelevant size (union type)

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


-- module _ {ℓ} {F : Set ℓ → Set ℓ}
--   (Frel : ∀ {A} → Rel A ℓ → Rel (F A) ℓ)
--   (map : Map ℓ F)
--   where

--   private
--     EqMu′ : ∀ {α} (t t′ : Mu α F) → Set ℓ
--     EqMu′ = EqMu _ F Frel map


  -- EqMu-refl : ∀ {α} {t : Mu α F} → EqMu′ t t
  -- EqMu-refl {sup I f} {t} = `base (refl , {!!})
  -- -- This requires some properties of Frel, which I can't be bothered with
  -- -- right now.


-- Properties of monMu

-- None of these seem to hold.

--   monMu-mono : ∀ {α β} (α≤β : α ≤ β) {t t′}
--     → EqMu′ t t′
--     → EqMu′ (monMu map α≤β t) (monMu map α≤β t′)
--   monMu-mono {sup I f} {sup .I .f} refl {sh , pos} {sh′ , pos′} eq = eq
--   monMu-mono {sup I f} {sup I′ f′} (lt i α≤β) {sh , pos} {sh′ , pos′} (`base (fsh≤fsh′ , eq))
--     = `base (refl , {!!})
--   monMu-mono {sup I f} {sup I′ f′} α≤β (`sym eq)
--     = `sym (monMu-mono α≤β eq)
--   monMu-mono {sup I f} {sup I′ f′} α≤β (`trans eq₁ eq₂)
--     = `trans (monMu-mono α≤β eq₁) (monMu-mono α≤β eq₂)


--   monMu-trans : ∀ {α β γ} (α≤β : α ≤ β) (β≤γ : β ≤ γ) x
--     → EqMu′
--         (monMu map β≤γ (monMu map α≤β x))
--         (monMu map (trans-≤ α≤β β≤γ) x)
--   monMu-trans {α} {.(sup I f)} {sup I f} α≤β refl x = {!`base!}
--   monMu-trans {α} {β} {sup I f} α≤β (lt i β≤γ) x = {!!}


-- monMu-irr : ∀{ℓ F} (m : Map ℓ F) {α β} (α≤β α≤β' : α ≤ β) (x : Mu α F)
--   → monMu m α≤β x ≡ monMu m α≤β' x
-- monMu-irr m refl refl x = refl
-- monMu-irr m refl (lt i α≤β') x = {!!}
-- monMu-irr m (lt i α≤β) refl x = {!!}
-- monMu-irr m {sup I f} (lt i α≤fi) (lt j α≤fj) x = {!!}
--   -- Cannot prove this since size component of x is different
--   -- (i ≠ j)

-- monMu-coh : ∀ {ℓ F} (m : Map ℓ F) {α β γ}
--   → ∀ (α≤β : α ≤ β) (β≤γ : β ≤ γ) (α≤γ : α ≤ γ) x
--   → monMu m β≤γ (monMu m α≤β x) ≡ monMu m α≤γ x
-- monMu-coh m refl refl refl x = refl
-- monMu-coh m refl refl (lt i α≤γ) (i′ , f) = {!!}
-- monMu-coh m refl (lt i β≤γ) α≤γ x = {!!}
-- monMu-coh m (lt i α≤β) β≤γ α≤γ x = {!!}


-- Inductive types using well-founded recursion

◆ : ∀ {ℓ} → (Tree → Set ℓ) → Tree → Set ℓ
◆ A α = Σ[ <α ∈ Tree< α ] A (the< <α)


module _ {ℓ} (F : Set ℓ → Set ℓ) where

  MuBody : ∀ {α} (rec : Tree< α → Set ℓ) → Set ℓ
  MuBody {α} rec = Σ[ <α ∈ Tree< α ] F (rec <α)

  Mu^ : (α : Tree) → Set ℓ
  Mu^ = fix MuBody

  monMu^ : ∀ {α β} → α ≤ β → Mu^ α → Mu^ β
  monMu^ {α} {β} α≤β (<α , FMu<α) .proj₁ = castTree< α≤β <α
  monMu^ {α} {β} α≤β (<α , FMu<α) .proj₂ =
    subst F (sym (fix<-unfold MuBody (castTree< α≤β <α)))
     (subst (λ z → F (Mu^ z)) (sym (the<-castTree< α≤β <α))
      (subst F (fix<-unfold MuBody <α) FMu<α))

  module _ (map : Map ℓ F) where

    -- if we erased types these would just be the identity function
    Mu^-fold : ∀ α → (◆ (\ i → F (Mu^ i)) α) → Mu^ α
    Mu^-fold = fix λ { rec (<α , x) → <α , map (cast (sym (fix<-unfold _ <α))) x }

    Mu^-unfold : ∀ α → Mu^ α → (◆ (\ i → F (Mu^ i)) α)
    Mu^-unfold = fix λ { rec (<α , x) → <α , map (cast (fix<-unfold _ <α)) x }

    module _ (Frel : ∀ {A} → Rel A ℓ → Rel (F A) ℓ) where

      EqMu^ : ∀ α (t t′ : Mu^ α) → Set ℓ
      EqMu^ = fix λ {α} rec → SymTrans λ t t′ →
        let (β , t)   = Mu^-unfold α t
            (β′ , t′) = Mu^-unfold α t′ in
        Σ[ β≤β′ ∈ the< β ≤ the< β′ ] Frel (rec β′) (map (monMu^ β≤β′) t) t′
