{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Model.Type.Core where

open import Cats.Category
open import Relation.Binary using (IsEquivalence)

open import Model.RGraph as RG using (RGraph)
open import Util.HoTT.Equiv
open import Util.HoTT.HLevel
open import Util.HoTT.Univalence
open import Util.Prelude hiding (id) renaming (_∘_ to _∘F_)
open import Util.Relation.Binary.LogicalEquivalence using
  ( _↔_ ; forth ; back ; ↔-reflexive )
open import Util.Relation.Binary.PropositionalEquality

open Category._≅_ public
open RG._⇒_


infixr 0 _⇒_
infix  4 _≈_ _≈⟦Type⟧_
infixr 9 _∘_


private
  variable Δ Γ Ψ : RGraph


-- This is an RGraph-indexed family of RGraphs.
record ⟦Type⟧ (Δ : RGraph) : Set₁ where
  no-eta-equality
  field
    ObjHSet : Δ .RG.Obj → HSet 0ℓ

  private
    module M₀ δ = HLevel (ObjHSet δ)
    module M₁ {δ} = HLevel (ObjHSet δ)

  open M₀ public using () renaming
    ( type to Obj )
  open M₁ public using () renaming
    ( level to Obj-IsSet )

  field
    eqHProp : ∀ {δ δ′} → Δ .RG.eq δ δ′ → Obj δ → Obj δ′ → HProp 0ℓ

  private
    module M₂ {δ δ′} (δ≈δ′ : Δ .RG.eq δ δ′) x y   = HLevel (eqHProp δ≈δ′ x y)
    module M₃ {δ δ′} {δ≈δ′ : Δ .RG.eq δ δ′} {x y} = HLevel (eqHProp δ≈δ′ x y)

  open M₂ public using () renaming
    ( type to eq )
  open M₃ public using () renaming
    ( level to eq-IsProp )

  field
    eq-refl : ∀ {δ} (x : Obj δ) → eq (Δ .RG.eq-refl δ) x x

open ⟦Type⟧ public


private
  variable T U V W : ⟦Type⟧ Δ


open RGraph


transportEq : ∀ (T : ⟦Type⟧ Δ) {δ γ} {δ≈γ₀ δ≈γ₁ : Δ .eq δ γ} {x y}
  → T .eq δ≈γ₀ x y → T .eq δ≈γ₁ x y
transportEq {Δ} T = subst (λ p → T .eq p _ _) (Δ .eq-IsProp _ _)


transportObj : ∀ (T : ⟦Type⟧ Δ) {δ γ}
  → δ ≡ γ
  → T .Obj δ
  → T .Obj γ
transportObj T = subst (T .Obj)


transportObj-resp : ∀ (T : ⟦Type⟧ Δ) {δ γ}
  → (δ≡γ₀ δ≡γ₁ : δ ≡ γ)
  → ∀ {x y}
  → x ≡ y
  → transportObj T δ≡γ₀ x ≡ transportObj T δ≡γ₁ y
transportObj-resp {Δ} T refl δ≡γ₁ x≡y
  rewrite Δ .Obj-IsSet δ≡γ₁ refl = x≡y


transportObj-resp-eq : ∀ (T : ⟦Type⟧ Δ) {δ₀ γ₀ δ₁ γ₁}
  → (δ₀≡γ₀ : δ₀ ≡ γ₀) (δ₁≡γ₁ : δ₁ ≡ γ₁)
  → ∀ {x y} {δ₀≈δ₁ : Δ .eq δ₀ δ₁} {γ₀≈γ₁ : Δ .eq γ₀ γ₁}
  → T .eq δ₀≈δ₁ x y
  → T .eq γ₀≈γ₁ (transportObj T δ₀≡γ₀ x) (transportObj T δ₁≡γ₁ y)
transportObj-resp-eq {Δ} T refl refl {δ₀≈δ₁ = δ₀≈δ₁} {γ₀≈γ₁} x≈y
  = transportEq T x≈y


record _⇒_ (T U : ⟦Type⟧ Δ) : Set where
  no-eta-equality
  field
    fobj : ∀ {δ} → Obj T δ → Obj U δ
    feq : ∀ {δ δ′} (δ≈δ′ : Δ .RG.eq δ δ′) {x y}
      → eq T δ≈δ′ x y
      → eq U δ≈δ′ (fobj x) (fobj y)

open _⇒_ public


record _≈_ (f g : T ⇒ U) : Set where
  no-eta-equality
  constructor ≈⁺
  field
    ≈⁻ : ∀ δ (x : Obj T δ) → f .fobj x ≡ g .fobj x

open _≈_ public


≈-isEquivalence : (T U : ⟦Type⟧ Δ) → IsEquivalence (_≈_ {T = T} {U})
≈-isEquivalence T U = record
  { refl = ≈⁺ λ γ x → refl
  ; sym = λ f≈g → ≈⁺ λ γ x → sym (f≈g .≈⁻ γ x)
  ; trans = λ f≈g g≈h → ≈⁺ λ γ x → trans (f≈g .≈⁻ γ x) (g≈h .≈⁻ γ x)
  }


⇒Canon : (T U : ⟦Type⟧ Δ) → Set
⇒Canon {Δ} T U
  = Σ[ fobj ∈ (∀ {δ} → T .Obj δ → U .Obj δ) ]
      (∀ {δ δ′} (δ≈δ′ : Δ .RG.eq δ δ′) {x y}
        → T .eq δ≈δ′ x y → U .eq δ≈δ′ (fobj x) (fobj y))


⇒≅⇒Canon : (T ⇒ U) ≅ ⇒Canon T U
⇒≅⇒Canon = record
  { forth = λ f → f .fobj , f .feq
  ; isIso = record
    { back = λ f → record { fobj = f .proj₁ ; feq = f .proj₂ }
    ; back∘forth = λ where
        record { fobj = fo ; feq = fe } → refl
    ; forth∘back = λ x → refl
    }
  }


⇒Canon-IsSet : (T U : ⟦Type⟧ Δ) → IsSet (⇒Canon T U)
⇒Canon-IsSet T U = Σ-IsSet
  (∀∙-IsSet λ δ → →-IsSet (U .Obj-IsSet))
  (λ _ → ∀∙-IsSet λ δ → ∀∙-IsSet λ δ′ → ∀-IsSet λ δ≈δ′ → ∀∙-IsSet λ x
    → ∀∙-IsSet λ y → →-IsSet (IsProp→IsSet (U .eq-IsProp)))


⇒-IsSet : IsSet (T ⇒ U)
⇒-IsSet {T = T} {U} = ≅-pres-IsOfHLevel 2 (≅-sym ⇒≅⇒Canon) (⇒Canon-IsSet T U)


≈→≡Canon : {f g : T ⇒ U}
  → f ≈ g → ⇒≅⇒Canon .forth f ≡ ⇒≅⇒Canon .forth g
≈→≡Canon {U = U} f≈g = Σ-≡⁺
  ( (funext∙ (funext (λ x → f≈g .≈⁻ _ x)))
  , funext∙ (funext∙ (funext λ a → funext∙ (funext∙
      (funext λ eq → U .eq-IsProp _ _)))) )


≈→≡ : {f g : T ⇒ U} → f ≈ g → f ≡ g
≈→≡ f≈g = ≅-Injective ⇒≅⇒Canon (≈→≡Canon f≈g)


private
  open module M₀ {Δ} {T U : ⟦Type⟧ Δ}
    = IsEquivalence (≈-isEquivalence T U)
    public using () renaming
    ( refl to ≈-refl
    ; sym to ≈-sym
    ; trans to ≈-trans
    ; reflexive to ≈-reflexive )


id : {T : ⟦Type⟧ Δ} → T ⇒ T
id = record
  { fobj = λ x → x
  ; feq = λ γ≈γ′ x → x
  }


_∘_ : {T U V : ⟦Type⟧ Δ} → U ⇒ V → T ⇒ U → T ⇒ V
_∘_ {Γ} f g = record
  { fobj = f .fobj ∘F g .fobj
  ; feq = λ γ≈γ′ → f .feq γ≈γ′ ∘F g .feq γ≈γ′
  }


⟦Types⟧ : RGraph → Category (lsuc 0ℓ) 0ℓ 0ℓ
⟦Types⟧ Δ = record
  { Obj = ⟦Type⟧ Δ
  ; _⇒_ = _⇒_
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; equiv = ≈-isEquivalence _ _
  ; ∘-resp = λ {Δ Γ Ψ f g h i} f≈g h≈i
    → ≈⁺ λ γ x → trans (f≈g .≈⁻ γ (h .fobj x)) (cong (g .fobj) (h≈i .≈⁻ γ x))
  ; id-r = ≈⁺ λ γ x → refl
  ; id-l = ≈⁺ λ γ x → refl
  ; assoc = ≈⁺ λ γ x → refl
  }


module ⟦Types⟧ {Γ} = Category (⟦Types⟧ Γ)


_≈⟦Type⟧_ : (T U : ⟦Type⟧ Δ) → Set₁
_≈⟦Type⟧_ = ⟦Types⟧._≅_


private
  open module M₁ {Δ} = ⟦Types⟧.≅ {Δ} public using () renaming
    ( refl to ≈⟦Type⟧-refl
    ; sym to ≈⟦Type⟧-sym
    ; trans to ≈⟦Type⟧-trans
    ; reflexive to ≈⟦Type⟧-reflexive )

module ≅-Reasoning = ⟦Types⟧.≅-Reasoning
module ≈-Reasoning = ⟦Types⟧.≈-Reasoning


⟦Type⟧Canon : RGraph → Set₁
⟦Type⟧Canon Δ
  = Σ[ ObjHSet ∈ (Δ .Obj → HSet 0ℓ) ]
    Σ[ eq ∈ (∀ {δ δ′} (δ≈δ′ : Δ .eq δ δ′)
        → (x : ObjHSet δ .type) (y : ObjHSet δ′ .type) → HProp 0ℓ) ]
    (∀ {δ} (x : ObjHSet δ .type) → eq (Δ .eq-refl δ) x x .type)


⟦Type⟧≅⟦Type⟧Canon : ∀ {Δ} → ⟦Type⟧ Δ ≅ ⟦Type⟧Canon Δ
⟦Type⟧≅⟦Type⟧Canon {Δ} = record
  { forth = λ T → T .ObjHSet , T .eqHProp , T .eq-refl
  ; isIso = record
    { back = λ T → record
      { ObjHSet = T .proj₁
      ; eqHProp = T .proj₂ .proj₁
      ; eq-refl = T .proj₂ .proj₂
      }
    ; back∘forth = λ where
        record { ObjHSet = x ; eqHProp = y ; eq-refl = z } → refl
    ; forth∘back = λ x → refl
    }
  }


≈⟦Type⟧→≡Canon
  : T ≈⟦Type⟧ U
  → ⟦Type⟧≅⟦Type⟧Canon .forth T ≡ ⟦Type⟧≅⟦Type⟧Canon .forth U
≈⟦Type⟧→≡Canon {U = U} T≈U = Σ-≡⁺
  ( (funext λ δ → HLevel-≡⁺ _ _ (≅→≡ (record
      { forth = T≈U .forth .fobj
      ; isIso = record
        { back = T≈U .back .fobj
        ; back∘forth = λ x → T≈U .back-forth .≈⁻ _ _
        ; forth∘back = λ x → T≈U .forth-back .≈⁻ _ _
        }
      })))
  , Σ-≡⁺
    ( funext∙ (funext∙ (funext λ δ≈δ′ → funext λ x → funext λ y
        → {!!}))
    , funext∙ (funext (λ x → U .eq-IsProp _ _))
    )
  )


≈⟦Type⟧→≡ : T ≈⟦Type⟧ U → T ≡ U
≈⟦Type⟧→≡ T≈U = ≅-Injective ⟦Type⟧≅⟦Type⟧Canon (≈⟦Type⟧→≡Canon T≈U)


subT : ∀ {Δ Ω} → Δ RG.⇒ Ω → ⟦Type⟧ Ω → ⟦Type⟧ Δ
subT {Γ} {Ω} f T = record
  { ObjHSet = T .ObjHSet ∘F f .fobj
  ; eqHProp = T .eqHProp ∘F f .feq
  ; eq-refl = λ x
      → subst (λ p → T .eq p x x) (Ω .eq-IsProp _ _) (T .eq-refl x)
  }


subt : ∀ {Δ Ω} (f : Δ RG.⇒ Ω) {T U : ⟦Type⟧ Ω}
  → T ⇒ U
  → subT f T ⇒ subT f U
subt f g = record
  { fobj = g .fobj
  ; feq = λ γ≈γ′ → g .feq (f .feq γ≈γ′)
  }


subt-∘ : ∀ {Δ Ω} (f : Δ RG.⇒ Ω) {T U V : ⟦Type⟧ Ω}
  → (g : U ⇒ V) (h : T ⇒ U)
  → subt f (g ∘ h) ≈ subt f g ∘ subt f h
subt-∘ f g h = ≈⁺ λ δ γ → refl


subT∘subT : ∀ {Δ Γ Ψ}
  → {f : Δ RG.⇒ Ψ} {g : Γ RG.⇒ Δ} {T : ⟦Type⟧ Ψ}
  → subT g (subT f T) ≈⟦Type⟧ subT (f RG.∘ g) T
subT∘subT = record
  { forth = record { fobj = λ x → x ; feq = λ _ x → x }
  ; back = record { fobj = λ x → x ; feq = λ _ x → x }
  ; back-forth = ≈⁺ λ γ x → refl
  ; forth-back = ≈⁺ λ γ x → refl
  }


castObj : {T U : ⟦Type⟧ Δ} → T ≡ U → ∀ {δ} → Obj T δ → Obj U δ
castObj p {δ} = subst (λ T → Obj T δ) p


≡→≈⟦Type⟧ : {T U : ⟦Type⟧ Δ} → T ≡ U → T ≈⟦Type⟧ U
≡→≈⟦Type⟧ {Δ} {T} {U} T≡U = record
  { forth = record
    { fobj = λ {δ} → castObj T≡U
    ; feq = λ δ≈δ′ x≈y → go T≡U x≈y
    }
  ; back = record
    { fobj = λ {δ} → castObj (sym T≡U)
    ; feq = λ δ≈δ′ x≈y → go (sym T≡U) x≈y
    }
  ; back-forth = ≈⁺ λ δ x → subst-sym-subst T≡U
  ; forth-back = ≈⁺ λ δ x → subst-subst-sym T≡U
  }
  where
    go : {T U : ⟦Type⟧ Δ} (p : T ≡ U) → ∀ {δ δ′} {δ≈δ′ : Δ .eq δ δ′} {x y}
      → eq T δ≈δ′ x y
      → eq U δ≈δ′ (castObj p x) (castObj p y)
    go refl x≈y = x≈y
