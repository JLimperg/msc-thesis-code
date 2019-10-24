{-# OPTIONS --without-K #-}
module Model.Terminal where

open import Cats.Category

open import Model.Type.Core
open import Util.HoTT.HLevel
open import Util.Prelude hiding (⊤)


⊤ : ∀ {Δ} → ⟦Type⟧ Δ
⊤ = record
  { ObjHSet = λ _ → HLevel-suc ⊤-HProp
  ; eqHProp = λ _ _ _ → ⊤-HProp
  }


instance
  hasTerminal : ∀ {Δ} → HasTerminal (⟦Types⟧ Δ)
  hasTerminal = record
    { ⊤ = ⊤
    ; isTerminal = λ T → record
      { arr = record {}
      ; unique = λ _ → ≈⁺ λ γ x → refl
      }
    }


private
  open module HT {Δ} = HasTerminal (hasTerminal {Δ}) public using (! ; !-unique)
