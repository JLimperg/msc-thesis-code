-- The purpose of this universe construction is to get some definitional
-- equalities in the model. Specifically, if we define ⟦σ⟧ : ⟦Δ⟧ → ⟦Ω⟧
-- (a functor) for the above notion of subsitution, then we have
-- ⟦Wk⟧ (δ , m) ≡ δ propositionally, but *not* definitionally. This then
-- complicates proofs involving ⟦Wk⟧, and similar for the other substitutions.

{-# OPTIONS --without-K --safe #-}
module Source.Size.Substitution.Universe where

open import Relation.Binary using (IsEquivalence ; Setoid)

open import Source.Size
open import Util.Prelude

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

import Source.Size.Substitution.Canonical as Can


infix  4 _≈_
infixl 5 sub-syntax-Size
infixl 5 _>>_


mutual
  data Sub : (Δ Ω : Ctx) → Set where
    Id : Sub Δ Δ
    _>>_ : (σ : Sub Δ Δ′) (τ : Sub Δ′ Ω) → Sub Δ Ω
    Wk : Sub (Δ ∙ n) Δ
    Keep : ∀ (σ : Sub Δ Ω) → m ≡ sub σ n → Sub (Δ ∙ m) (Ω ∙ n)
    Fill : ∀ n {m} → n < m → Sub Δ (Δ ∙ m)
    Skip : Sub (Δ ∙ n ∙ v0) (Δ ∙ n)


  sub : (σ : Sub Δ Ω) (n : Size Ω) → Size Δ
  sub σ = Can.sub ⟨ σ ⟩


  ⟨_⟩ : Sub Δ Ω → Can.Sub Δ Ω
  ⟨ Id ⟩ = Can.Id
  ⟨ σ >> τ ⟩ = ⟨ σ ⟩ Can.>> ⟨ τ ⟩
  ⟨ Wk ⟩ = Can.Wk
  ⟨ Keep σ m≡n[σ] ⟩ = Can.Keep ⟨ σ ⟩ m≡n[σ]
  ⟨ Fill n n<m ⟩ = Can.Fill n n<m
  ⟨ Skip ⟩ = Can.Skip


Keep′ : (σ : Sub Δ Ω) → Sub (Δ ∙ sub σ n) (Ω ∙ n)
Keep′ σ = Keep σ refl


variable σ τ ι : Sub Δ Ω


subV : (σ : Sub Δ Ω) (x : Var Ω) → Size Δ
subV σ = Can.subV ⟨ σ ⟩


record _≈_ (σ τ : Sub Δ Ω) : Set where
  constructor ≈⁺
  field ≈⁻ : ⟨ σ ⟩ ≡ ⟨ τ ⟩

open _≈_ public


≈-refl : σ ≈ σ
≈-refl = ≈⁺ refl


≈-sym : σ ≈ τ → τ ≈ σ
≈-sym (≈⁺ p) = ≈⁺ (sym p)


≈-trans : σ ≈ τ → τ ≈ ι → σ ≈ ι
≈-trans (≈⁺ p) (≈⁺ q) = ≈⁺ (trans p q)


≈-isEquivalence : IsEquivalence (_≈_ {Δ} {Ω})
≈-isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }


Sub-setoid : (Δ Ω : Ctx) → Setoid 0ℓ 0ℓ
Sub-setoid Δ Ω = record
  { Carrier = Sub Δ Ω
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence
  }


module ≈-Reasoning {Δ} {Ω} = SetoidReasoning (Sub-setoid Δ Ω)


sub-resp-≈ : σ ≈ τ → ∀ n → sub σ n ≡ sub τ n
sub-resp-≈ (≈⁺ p) n = cong (λ σ → Can.sub σ n) p


>>-resp-≈ : {σ σ′ : Sub Δ Δ′} {τ τ′ : Sub Δ′ Δ″}
  → σ ≈ σ′ → τ ≈ τ′ → σ >> τ ≈ σ′ >> τ′
>>-resp-≈ (≈⁺ p) (≈⁺ q) = ≈⁺ (cong₂ Can._>>_ p q)


Keep-resp-≈ : (m≡n[σ] : m ≡ sub σ n) (m≡n[τ] : m ≡ sub τ n)
  → σ ≈ τ
  → Keep {n = n} σ m≡n[σ] ≈ Keep τ m≡n[τ]
Keep-resp-≈ m≡n[σ] m≡n[τ] (≈⁺ p) = ≈⁺ (Can.Snoc-≡⁺ (cong Can.Weaken p) refl)


sub-resp-< : (σ : Sub Δ Ω) → n < m → sub σ n < sub σ m
sub-resp-< σ = Can.sub-resp-< ⟨ σ ⟩


sub-syntax-Size = sub

syntax sub-syntax-Size σ n = n [ σ ]n


mutual
  subV′ : Sub Δ Ω → Var Ω → Size Δ
  subV′ Id x = var x
  subV′ (σ >> τ) x = sub′ σ (subV′ τ x)
  subV′ Wk x = var (suc x)
  subV′ (Keep σ eq) zero = var zero
  subV′ (Keep σ eq) (suc x) = wk (subV′ σ x)
  subV′ (Fill m m<n) zero = m
  subV′ (Fill m m<n) (suc x) = var x
  subV′ Skip zero = var zero
  subV′ Skip (suc x) = var (suc (suc x))


  sub′ : Sub Δ Ω → Size Ω → Size Δ
  sub′ σ (var x) = subV′ σ x
  sub′ σ ∞ = ∞
  sub′ σ ⋆ = ⋆
  sub′ σ zero = zero
  sub′ σ (suc n n<∞)
    = suc (sub′ σ n) (subst (_< ∞) (sym (sub′≡sub σ n)) (sub-resp-< σ n<∞))


  subV′≡subV : ∀ (σ : Sub Δ Ω) x → subV′ σ x ≡ subV σ x
  subV′≡subV Id x = sym (Can.subV-Id x)
  subV′≡subV (σ >> τ) x
    = trans (sub′≡sub σ (subV′ τ x))
        (trans (cong (sub σ) (subV′≡subV τ x))
          (sym (Can.subV->> ⟨ σ ⟩ ⟨ τ ⟩ x)))
  subV′≡subV Wk x = sym (Can.sub-Wk (var x))
  subV′≡subV (Keep σ eq) zero = refl
  subV′≡subV (Keep σ eq) (suc x)
    = trans (cong wk (subV′≡subV σ x)) (sym (Can.subV-Weaken ⟨ σ ⟩ x))
  subV′≡subV (Fill m m<n) zero = refl
  subV′≡subV (Fill m m<n) (suc x) = sym (Can.subV-Id x)
  subV′≡subV Skip zero = refl
  subV′≡subV Skip (suc x) = sym
    (trans (Can.subV-Weaken (Can.Weaken Can.Id) x) (cong wk (Can.sub-Wk (var x))))


  sub′≡sub : ∀ (σ : Sub Δ Ω) n → sub′ σ n ≡ sub σ n
  sub′≡sub σ (var x) = subV′≡subV σ x
  sub′≡sub σ ∞ = refl
  sub′≡sub σ ⋆ = refl
  sub′≡sub σ zero = refl
  sub′≡sub σ (suc n x) = suc-≡-intro (sub′≡sub σ n)
