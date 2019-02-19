{-# OPTIONS --allow-unsolved-metas #-}
-- We give a model of sized least fixed points of finitely branching container
-- functors (a subset of the inductive types). The plan is to eventually
-- generalise this model to indexed, infinitely branching containers (full
-- inductive types), and then perhaps to greatest fixed points (coinductive
-- types).

open import Relation.Binary.PropositionalEquality using
  (cong-app ; module ≡-Reasoning)
open import Size using (Size ; ↑_ ; ∞)

open import Axioms using (funext)
open import Ordinal.Tree using
  (sup ; _≤_ ; _<_ ; lt ; refl) renaming
  (Tree to Ordinal ; tomega to ω ; embℕ to ℕ→Ordinal)
open import Ordinal.Tree.Container.Finite.Structural using
  (Mu ; monMu ; monMuℕ ; _≈_)
open import Util.Container.Finite using
  (Container ; _▷_ ; Pos ; Shape ; ⟦_⟧ ; map ; map-id ; map-∘ ; Eqℂ ; Eqℂ-intro
  ; μ ; sup)
open import Util.Prelude hiding (module Vec)
open import Util.Relation.Binary.Closure.SymmetricTransitive using
  (SymTrans ; `base ; `sym ; `trans)
open import Util.Vec as Vec using (Vec ; [] ; _∷_ ; max ; All₂)

import Data.Nat as ℕ
import Data.Vec.Membership.Propositional.Properties as Vec


--------------------------------------------------------------------------------
-- The model

-- Height, first try: The height of a μ is its maximum depth (a ℕ).

height : ∀ {ℂ s} → μ ℂ s → ℕ
height {ℂ} .{↑ s} (sup {s} (sh , pos))
  = suc (max (Vec.map (height {s = s}) (Vec.tabulate pos)))
-- NOTE: This only passes the termination checker because of the sized types!


height≤ω : ∀ {ℂ s} (x : μ ℂ s) → ℕ→Ordinal (height x) ≤ ω
height≤ω x = lt (height x) refl


-- Height, second try: The height of a μ is the supremum of the heights of its
-- recursive components (an Ordinal).


height′ : ∀ {ℂ s} → μ ℂ s → Ordinal
height′ {ℂ} (sup (sh , pos)) = sup (Fin (ℂ .Pos sh)) λ n → height′ (pos n)


height′≤ω : ∀ {ℂ s} (x : μ ℂ s) → height′ x ≤ ω
height′≤ω (sup (sh , pos)) = lt {!!} {!!}
-- I suspect that we'll need a lemma
--   n ≤ m → ℕ→Ordinal n ≤ ℕ→Ordinal m
-- here, but that doesn't seem provable.


--------------------------------------------------------------------------------
-- The isomorphism


fwd : ∀ {ℂ} (x : μ ℂ ∞) → Mu (ℕ→Ordinal (height x)) ℂ
fwd {ℂ} (sup (sh , pos))
  = _
  , sh
  , λ p → monMuℕ
      (Vec.max-maximal-∈ (Vec.∈-map⁺ height (Vec.∈-tabulate⁺ pos p)))
      (fwd (pos p))

-- This works because we can use monMuℕ to map each recursive occurrence into
-- the biggest height among all the recursive occurrences. For infinitely
-- branching trees, this won't be so easy, since we can't compute the biggest
-- height. (There is, of course, an ordinal that we can map all the occurrences
-- into: the supremum of the component ordinals. Don't know if that helps much.)
--
-- Alternative type:
--   fwd : ∀ {ℂ s} (x : μ ℂ s) → Mu (ℕ→Ordinal (height x)) ⟦ ℂ ⟧


bwd : ∀ {ℂ α} → Mu α ℂ → μ ℂ ∞
bwd {ℂ} {sup I f} (i , pos) = sup (map (bwd {α = f i}) pos)


bwd-monMuℕ : ∀ ℂ {n m} (p : n ℕ.≤ m) (x : Mu (ℕ→Ordinal n) ℂ)
  → bwd (monMuℕ p x) ≡ bwd x
bwd-monMuℕ ℂ ℕ.z≤n (() , _)
bwd-monMuℕ ℂ (ℕ.s≤s p) (sh , pos)
  = cong sup
    (begin
      map bwd (map (monMuℕ p) pos)
    ≡⟨ cong-app (funext λ x → map-∘ bwd (monMuℕ p) {x}) pos ⟩
      map (bwd ∘ monMuℕ p) pos
    ≡⟨ cong-app (cong map (funext λ x → bwd-monMuℕ ℂ p x)) pos ⟩
      map bwd pos
    ∎)
  where
    open ≡-Reasoning


bwd-height : ∀ {ℂ n} (x : Mu (ℕ→Ordinal n) ℂ)
  → n ℕ.≤ height (bwd x)
bwd-height {ℂ} {zero} _ = ℕ.z≤n
bwd-height {ℂ} {suc n} (_ , pos) = ℕ.s≤s {!!}


bwd∘fwd : ∀ {ℂ} (x : μ ℂ ∞) → bwd (fwd x) ≡ x
bwd∘fwd (sup (sh , pos))
  = cong (sup ∘ (sh ,_))
      (funext λ p → trans (bwd-monMuℕ _ _ _) (bwd∘fwd _))


fwd∘bwd : ∀ {ℂ n} (x : Mu (ℕ→Ordinal n) ℂ)
  → fwd (bwd x) ≈ monMuℕ (bwd-height x) x
fwd∘bwd {S ▷ P} {zero} ((), _)
fwd∘bwd {ℂ@(S ▷ P)} {suc n} (_ , s , pos)
  = `base
  ( refl
  , Eqℂ-intro {!!}
  )
