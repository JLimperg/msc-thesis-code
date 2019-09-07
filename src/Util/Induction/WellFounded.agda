{-# OPTIONS --without-K #-}
module Util.Induction.WellFounded where

open import Induction.WellFounded public using
  ( Acc ; acc ; WellFounded ; module Subrelation ; module InverseImage
  ; module TransitiveClosure ; module Lexicographic )

open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Intersection using (_∩_)

open import Util.HoTT.HLevel using (IsProp ; ∀-IsProp)
open import Util.HoTT.Univalence using (funext)
open import Util.Prelude


module _ {α β} {A : Set α} {_<_ : Rel A β} where


  Acc-IsProp : ∀ {x} → IsProp (Acc _<_ x)
  Acc-IsProp (acc rs₀) (acc rs₁)
    = cong acc (funext λ y → funext λ y<x → Acc-IsProp _ _)


  WellFounded-IsProp : IsProp (WellFounded _<_)
  WellFounded-IsProp = ∀-IsProp λ _ → Acc-IsProp


  wfInd-acc : ∀ {γ} (P : A → Set γ)
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → Acc _<_ x → P x
  wfInd-acc P f x (acc rs) = f x (λ y y<x → wfInd-acc P f y (rs y y<x))


  module Build (<-wf : WellFounded _<_) where

    wfInd : ∀ {γ} (P : A → Set γ)
      → (∀ x → (∀ y → y < x → P y) → P x)
      → ∀ x → P x
    wfInd P f x = wfInd-acc P f x (<-wf x)


    wfRec : ∀ {γ} {B : Set γ}
      → (∀ x → (∀ y → y < x → B) → B)
      → A → B
    wfRec = wfInd _


    wfInd-unfold : ∀ {γ} (P : A → Set γ)
      → (f : ∀ x → (∀ y → y < x → P y) → P x)
      → (x : A)
      → wfInd P f x ≡ f x (λ y _ → wfInd P f y)
    wfInd-unfold P f x with <-wf x
    ... | acc rs
      = cong (f x)
          (funext λ y → funext λ y<x →
            cong (wfInd-acc P f y) (Acc-IsProp (rs y y<x) (<-wf y)))


    wfRec-unfold : ∀ {γ} {B : Set γ}
      → (f : ∀ x → (∀ y → y < x → B) → B)
      → (x : A)
      → wfRec f x ≡ f x (λ y _ → wfRec f y)
    wfRec-unfold = wfInd-unfold _


    wfInd-ind : ∀ {γ} {P : A → Set γ}
      → (Q : ∀ x → P x → Set)
      → {f : ∀ x → (∀ y → y < x → P y) → P x}
      → (∀ x g
          → (∀ y y<x → Q y (g y y<x))
          → Q x (f x g))
      → {x : A}
      → Q x (wfInd P f x)
    wfInd-ind {P = P} Q {f} f-resp
      = wfInd (λ x → Q x (wfInd P f x))
          (λ x rec → subst (Q x) (sym (wfInd-unfold P f x))
            (f-resp _ _ rec))
          _

  open Build public


module _ {α β γ δ} {A : Set α} {B : Set β} where

  ×-Rel : Rel A γ → Rel B δ → Rel (A × B) (γ ⊔ℓ δ)
  ×-Rel R S (a , b) (a′ , b′) = R a a′ × S b b′


  ×-wellFounded : {R : Rel A γ} {S : Rel B δ}
    → WellFounded R → WellFounded S → WellFounded (×-Rel R S)
  ×-wellFounded {R} {S} R-wf S-wf (a , b) = ×-acc (R-wf a) (S-wf b)
    where
      ×-acc : ∀ {x y} → Acc R x → Acc S y → Acc (×-Rel R S) (x , y)
      ×-acc (acc rsa) (acc rsb)
        = acc (λ { (a , b) (a<x , b<y) → ×-acc (rsa a a<x) (rsb b b<y) })


-- This is not in Build because the implementation uses wfInd at
-- (×-Rel _<_ _<_), but within Build, we can only use wfInd at
-- _<_.
wfInd-ind₂ : ∀ {α β} {A : Set α} {_<_ : Rel A β}
  → (<-wf : WellFounded _<_)
  → ∀ {γ} {P : A → Set γ}
  → (R : ∀ x y → P x → P y → Set)
  → {f : ∀ x → (∀ y → y < x → P y) → P x}
  → (∀ x x′ g g′
      → (∀ y y′ y<x y′<x → R y y′ (g y y<x) (g′ y′ y′<x))
      → R x x′ (f x g) (f x′ g′))
  → {x x′ : A}
  → R x x′ (wfInd <-wf P f x) (wfInd <-wf P f x′)
wfInd-ind₂ <-wf {P = P} R {f} f-resp
  = wfInd (×-wellFounded <-wf <-wf)
      (λ { (x , x′) → R x x′ (wfInd <-wf P f x) (wfInd <-wf P f x′)})
      (λ where
        (x , y) rec
          → subst₂ (R x y)
              (sym (wfInd-unfold <-wf P f x))
              (sym (wfInd-unfold <-wf P f y))
              (f-resp x y _ _ λ x′ y′ x′<x y′<y → rec (x′ , y′) (x′<x , y′<y)))
      _
