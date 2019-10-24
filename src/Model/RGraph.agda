{-# OPTIONS --without-K #-}
module Model.RGraph where

open import Cats.Category
open import Relation.Binary using (IsEquivalence)

open import Util.HoTT.Equiv
open import Util.HoTT.HLevel
open import Util.HoTT.Univalence
open import Util.Prelude hiding (id) renaming (_∘_ to _∘F_)
open import Util.Relation.Binary.PropositionalEquality


infixr 0 _⇒_
infix 4 _≈_
infixr 9 _∘_


record RGraph : Set₁ where
  no-eta-equality
  field
    ObjHSet : HSet 0ℓ

  open HLevel ObjHSet public using () renaming
    ( type to Obj
    ; level to Obj-IsSet
    )

  field
    eqHProp : Obj → Obj → HProp 0ℓ

  private
    module M₀ x y = HLevel (eqHProp x y)
    module M₁ {x} {y} = HLevel (eqHProp x y)

  open M₀ public using () renaming
    ( type to eq )
  open M₁ public using () renaming
    ( level to eq-IsProp )

  field
    eq-refl : ∀ x → eq x x

open RGraph public


private
  variable Γ Δ Ψ : RGraph


record _⇒_ (Γ Δ : RGraph) : Set where
  no-eta-equality
  field
    fobj : Γ .Obj → Δ .Obj
    feq : ∀ {x y} → Γ .eq x y → Δ .eq (fobj x) (fobj y)

open _⇒_ public


private
  variable f g h i : Γ ⇒ Δ


⇒Canon : (Γ Δ : RGraph) → Set
⇒Canon Γ Δ
  = Σ[ fobj ∈ (Γ .Obj → Δ .Obj) ]
      (∀ {x y} → Γ .eq x y → Δ .eq (fobj x) (fobj y))


⇒≅⇒Canon : (Γ ⇒ Δ) ≅ (⇒Canon Γ Δ)
⇒≅⇒Canon = record
  { forth = λ f → f .fobj , f .feq
  ; isIso = record
    { back = λ f → record { fobj = proj₁ f ; feq = proj₂ f }
    ; back∘forth = λ where
        record { fobj = fobj ; feq = feq } → refl
    ; forth∘back = λ f → refl
    }
  }


⇒Canon-IsSet : ∀ Γ Δ → IsSet (⇒Canon Γ Δ)
⇒Canon-IsSet Γ Δ
  = Σ-IsSet
      (→-IsSet (Δ .Obj-IsSet))
      (λ _ → ∀∙-IsSet (λ _ → ∀∙-IsSet λ _ → →-IsSet (IsProp→IsSet (Δ .eq-IsProp))))


⇒-IsSet : IsSet (Γ ⇒ Δ)
⇒-IsSet {Γ} {Δ} = ≅-pres-IsOfHLevel 2 (≅-sym ⇒≅⇒Canon) (⇒Canon-IsSet Γ Δ)


record _≈_ (f g : Γ ⇒ Δ) : Set where
  no-eta-equality
  constructor ≈⁺
  field
    ≈⁻ : ∀ x → f .fobj x ≡ g .fobj x

open _≈_ public


≈→≡Canon : ∀ {Γ Δ} {f g : Γ ⇒ Δ}
  → f ≈ g
  → ⇒≅⇒Canon .forth f ≡ ⇒≅⇒Canon .forth g
≈→≡Canon {Δ = Δ} {f} {g} (≈⁺ f≈g) = Σ-≡⁺
  ( funext f≈g
  , funext∙ (funext∙ (funext λ x≈y → Δ .eq-IsProp _ _))
  )


≈→≡ : f ≈ g → f ≡ g
≈→≡ f≈g = ≅-Injective ⇒≅⇒Canon (≈→≡Canon f≈g)


≈-isEquivalence : ∀ Γ Δ → IsEquivalence (_≈_ {Γ} {Δ})
≈-isEquivalence Γ Δ = record
  { refl = ≈⁺ (λ x → refl)
  ; sym = λ f≈g → ≈⁺ (λ x → sym (f≈g .≈⁻ x))
  ; trans = λ f≈g g≈h → ≈⁺ (λ x → trans (f≈g .≈⁻ x) (g≈h .≈⁻ x))
  }


private
  open module M₀ {Γ} {Δ}
    = IsEquivalence (≈-isEquivalence Γ Δ) public using () renaming
    ( refl to ≈-refl
    ; sym to ≈-sym
    ; trans to ≈-trans
    ; reflexive to ≈-reflexive )


id : ∀ {Γ} → Γ ⇒ Γ
id = record { fobj = λ x → x ; feq = λ x → x }


_∘_ : ∀ {Γ Δ Ψ} → Δ ⇒ Ψ → Γ ⇒ Δ → Γ ⇒ Ψ
f ∘ g = record
  { fobj = f .fobj ∘F g .fobj
  ; feq = f .feq ∘F g .feq
  }


RGraphs : Category (lsuc 0ℓ) 0ℓ 0ℓ
RGraphs = record
  { Obj = RGraph
  ; _⇒_ = _⇒_
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; equiv = ≈-isEquivalence _ _
  ; ∘-resp = λ {Γ Δ Ψ f g h i} f≈g h≈i
      → ≈⁺ (λ x → trans (f≈g .≈⁻ _) (cong (g .fobj) (h≈i .≈⁻ x)))
  ; id-r = ≈⁺ (λ x → refl)
  ; id-l = ≈⁺ (λ x → refl)
  ; assoc = ≈⁺ (λ x → refl)
  }


module RGraphs = Category RGraphs
