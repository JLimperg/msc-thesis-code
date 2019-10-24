{-# OPTIONS --without-K #-}
module Model.Exponential where

open import Cats.Category

open import Model.RGraph as RG using (RGraph)
open import Model.Type.Core
open import Model.Product
open import Util.HoTT.HLevel
open import Util.Prelude hiding (_×_ ; id ; _∘_)

open RGraph
open RG._⇒_


private
  variable Δ : RGraph


infixr 9 _↝_


Ap : ⟦Type⟧ Δ → Δ .Obj → RGraph
Ap {Δ} T δ = record
  { ObjHSet = T .ObjHSet δ
  ; eqHProp = eqHProp T (Δ .eq-refl _)
  ; eq-refl = λ x → T .eq-refl x
  }


_↝_ : (T U : ⟦Type⟧ Δ) → ⟦Type⟧ Δ
_↝_ T U = record
  { ObjHSet = λ γ → HLevel⁺ (Ap T γ RG.⇒ Ap U γ) (RG.⇒-IsSet {Ap T γ} {Ap U γ})
  ; eqHProp = λ γ≈γ′ f g
      → ∀∙-HProp λ x
      → ∀∙-HProp λ y
      → T .eqHProp γ≈γ′ x y →-HProp′ U .eqHProp γ≈γ′ (f .RG.fobj x) (g .RG.fobj y)
  ; eq-refl = λ f → f .RG.feq
  }


curry : (T U V : ⟦Type⟧ Δ)
  → T × U ⇒ V → T ⇒ U ↝ V
curry {Δ} T U V f = record
  { fobj = λ {δ} t → record
    { fobj = λ u → f .fobj (t , u)
    ; feq = λ x≈y → f .feq (Δ .eq-refl δ) (T .eq-refl t , x≈y)
    }
  ; feq = λ γ≈γ′ x≈y v≈w → f .feq γ≈γ′ (x≈y , v≈w)
  }


eval : (T U : ⟦Type⟧ Δ)
  → (T ↝ U) × T ⇒ U
eval T U = record
  { fobj = λ { (f , x) → f .RG.fobj x }
  ; feq = λ { γ≈γ′ (f≈g , x≈y) → f≈g x≈y }
  }


eval∘curry : (T U V : ⟦Type⟧ Δ) {f : T × U ⇒ V}
  → eval U V ∘ ⟨_×_⟩ {B = U} (curry T U V f) id ≈ f
eval∘curry T U V = ≈⁺ λ γ x → refl


instance
  hasExponentials : ∀ {Δ} → HasExponentials (⟦Types⟧ Δ)
  hasExponentials .HasExponentials.hasBinaryProducts = hasBinaryProducts
  hasExponentials .HasExponentials._↝′_ T U = record
    { Cᴮ = T ↝ U
    ; eval = eval T U
    ; curry′ = λ {A} f → record
      { arr = curry A T U f
      ; prop = eval∘curry A T U
      ; unique = λ {g} g-prop → ≈⁺ λ γ h → RG.≈→≡ (RG.≈⁺ λ x
          → sym (g-prop .≈⁻ γ (h , x)))
      }
    }


module ⟦Types⟧↝ {Δ} = HasExponentials (hasExponentials {Δ})


↝-resp-≈⟦Type⟧ : ∀ {Δ} (T T′ U U′ : ⟦Type⟧ Δ)
  → T ≈⟦Type⟧ T′
  → U ≈⟦Type⟧ U′
  → T ↝ U ≈⟦Type⟧ T′ ↝ U′
↝-resp-≈⟦Type⟧ {Δ} T T′ U U′ T≈T′ U≈U′
  = ⟦Types⟧↝.↝-resp-≅ {Δ} {T} {T′} {U} {U′} T≈T′ U≈U′


subT-↝ : ∀ {Γ Δ} (f : Γ RG.⇒ Δ)
  → (T U : ⟦Type⟧ Δ)
  → subT f T ↝ subT f U ≈⟦Type⟧ subT f (T ↝ U)
subT-↝ {Γ} {Δ} f T U = record
  { forth = record
    { fobj = λ g → record
      { fobj = g .fobj
      ; feq = λ {x y} x≈y → transportEq U (g .feq (transportEq T x≈y))
      }
    ; feq = λ γ≈γ′ f≈g x≈y → f≈g x≈y
    }
  ; back = record
    { fobj = λ g → record
      { fobj = g .fobj
      ; feq = λ {x y} x≈y → transportEq U (g .feq (transportEq T x≈y))
      }
    ; feq = λ γ≈γ′ f≈g x≈y → f≈g x≈y
    }
  ; back-forth = ≈⁺ λ γ x → RG.≈→≡ (RG.≈⁺ λ y → refl)
  ; forth-back = ≈⁺ λ γ x → RG.≈→≡ (RG.≈⁺ λ y → refl)
  }
