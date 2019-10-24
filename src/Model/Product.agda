{-# OPTIONS --without-K #-}
module Model.Product where

open import Cats.Category
open import Data.Product using (<_,_>)

open import Model.Type.Core
open import Util.HoTT.HLevel
open import Util.Prelude hiding (_×_)


infixr 5 _×_


_×_ : ∀ {Γ} (T U : ⟦Type⟧ Γ) → ⟦Type⟧ Γ
T × U = record
  { ObjHSet = λ δ → T .ObjHSet δ ×-HSet U .ObjHSet δ
  ; eqHProp = λ where
      γ≈γ′ (x , x′) (y , y′) → T .eqHProp γ≈γ′ x y ×-HProp U .eqHProp γ≈γ′ x′ y′
  ; eq-refl = λ where
      (x , y) → T .eq-refl x , U .eq-refl y
  }


π₁ : ∀ {Γ} {T} (U : ⟦Type⟧ Γ) → T × U ⇒ T
π₁ U = record
  { fobj = proj₁
  ; feq = λ p → proj₁
  }


π₂ : ∀ {Γ} T {U : ⟦Type⟧ Γ} → T × U ⇒ U
π₂ T = record
  { fobj = proj₂
  ; feq = λ p → proj₂
  }


⟨_,_⟩ : ∀ {Γ} {X T U : ⟦Type⟧ Γ}
  → X ⇒ T → X ⇒ U → X ⇒ T × U
⟨ f , g ⟩ = record
  { fobj = < f .fobj , g .fobj >
  ; feq = λ γ≈γ′ → < f .feq γ≈γ′ , g .feq γ≈γ′ >
  }


instance
  hasBinaryProducts : ∀ {Γ} → HasBinaryProducts (⟦Types⟧ Γ)
  hasBinaryProducts .HasBinaryProducts._×′_ T U = record
    { prod = T × U
    ; proj = λ where
        true → π₁ U
        false → π₂ T
    ; isProduct = λ π′ → record
      { arr = ⟨ π′ true , π′ false ⟩
      ; prop = λ where
          true → ≈⁺ λ γ x → refl
          false → ≈⁺ λ γ x → refl
      ; unique = λ {f} f-prop → ≈⁺ λ γ x
          → cong₂ _,_ (f-prop true .≈⁻ γ x) (f-prop false .≈⁻ γ x)
      }
    }


open module ⟦Types⟧× {Γ}
  = HasBinaryProducts (hasBinaryProducts {Γ})
  public using
  ( ⟨_×_⟩ ) renaming
  ( ×-resp-≅ to ×-resp-≈⟦Type⟧ )
