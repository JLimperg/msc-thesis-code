{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Model.Quantification where

open import Model.RGraph as RG using (RGraph)
open import Model.Size as MS using (_<_ ; ⟦_⟧Δ ; ⟦_⟧n ; ⟦_⟧σ)
open import Model.Type.Core
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Universe as SS using (Sub⊢ᵤ)
open import Util.HoTT.Equiv
open import Util.HoTT.HLevel
open import Util.HoTT.Univalence
open import Util.Prelude hiding (_∘_)
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁺)

import Source.Size as SS
import Source.Type as ST

open RGraph
open RG._⇒_
open SS.Ctx
open SS.Sub⊢ᵤ


record ⟦∀⟧′ {Δ} n (T : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ) (δ : Obj ⟦ Δ ⟧Δ) : Set where
  no-eta-equality
  field
    arr : ∀ m (m<n : m < ⟦ n ⟧n .fobj δ) → Obj T (δ , m , m<n)
    param : ∀ m m<n m′ m′<n → eq T _ (arr m m<n) (arr m′ m′<n)

open ⟦∀⟧′ public


⟦∀⟧′Canon : ∀ {Δ} n (T : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ) (δ : Obj ⟦ Δ ⟧Δ) → Set
⟦∀⟧′Canon n T δ
  = Σ[ f ∈ (∀ m (m<n : m < ⟦ n ⟧n .fobj δ) → Obj T (δ , m , m<n)) ]
      (∀ m m<n m′ m′<n → eq T _ (f m m<n) (f m′ m′<n))


⟦∀⟧′≅⟦∀⟧′Canon : ∀ {Δ n T δ} → ⟦∀⟧′ {Δ} n T δ ≅ ⟦∀⟧′Canon n T δ
⟦∀⟧′≅⟦∀⟧′Canon = record
  { forth = λ { record { arr = x ; param = y } → x , y }
  ; isIso = record
    { back = λ x → record { arr = proj₁ x ; param = proj₂ x }
    ; back∘forth = λ { record {} → refl }
    ; forth∘back = λ _ → refl
    }
  }


abstract
  ⟦∀⟧′Canon-IsSet : ∀ {Δ n T δ} → IsSet (⟦∀⟧′Canon {Δ} n T δ)
  ⟦∀⟧′Canon-IsSet {T = T} = Σ-IsSet
    (∀-IsSet λ m → ∀-IsSet λ m<n → λ _ _ → T .Obj-IsSet _ _)
    (λ f → IsOfHLevel-suc 1 (∀-IsProp λ m → ∀-IsProp λ m<n → ∀-IsProp λ m′
      → ∀-IsProp λ m′<n → T .eq-IsProp))


  ⟦∀⟧′-IsSet : ∀ {Δ n T δ} → IsSet (⟦∀⟧′ {Δ} n T δ)
  ⟦∀⟧′-IsSet {Δ} {n} {T} {δ}
    = ≅-pres-IsOfHLevel 2 (≅-sym ⟦∀⟧′≅⟦∀⟧′Canon) (⟦∀⟧′Canon-IsSet {Δ} {n} {T} {δ})


  ⟦∀⟧′-≡⁺ : ∀ {Δ n T δ} (f g : ⟦∀⟧′ {Δ} n T δ)
    → (∀ m m<n → f .arr m m<n ≡ g .arr m m<n)
    → f ≡ g
  ⟦∀⟧′-≡⁺ {T = T} record{} record{} f≈g = ≅-Injective ⟦∀⟧′≅⟦∀⟧′Canon (Σ-≡⁺
    ( (funext λ m → funext λ m<n → f≈g m m<n)
    , funext λ m → funext λ m<n → funext λ m′ → funext λ m<n′ → T .eq-IsProp _ _))


⟦∀⟧′-resp-≈⟦Type⟧ : ∀ {Δ n T U}
  → T ≈⟦Type⟧ U
  → ∀ {δ} → ⟦∀⟧′ {Δ} n T δ ≅ ⟦∀⟧′ n U δ
⟦∀⟧′-resp-≈⟦Type⟧ T≈U = record
  { forth = λ f → record
    { arr = λ m m<n → T≈U .forth .fobj (f .arr m m<n)
    ; param = λ m m<n m′ m′<n → T≈U .forth .feq _ (f .param m m<n m′ m′<n)
    }
  ; isIso = record
    { back = λ f → record
      { arr = λ m m<n → T≈U .back .fobj (f .arr m m<n)
      ; param = λ m m<n m′ m′<n → T≈U .back .feq _ (f .param m m<n m′ m′<n)
      }
    ; back∘forth = λ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → T≈U .back-forth .≈⁻ _ _
    ; forth∘back = λ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → T≈U .forth-back .≈⁻ _ _
    }
  }


⟦∀⟧ : ∀ {Δ} n (T : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ) → ⟦Type⟧ ⟦ Δ ⟧Δ
⟦∀⟧ n T = record
  { ObjHSet = λ δ → HLevel⁺ (⟦∀⟧′ n T δ) ⟦∀⟧′-IsSet
  ; eqHProp = λ _ f g → ∀-HProp _ λ m → ∀-HProp _ λ m<n → ∀-HProp _ λ m′
      → ∀-HProp _ λ m′<n → T .eqHProp _ (f .arr m m<n) (g .arr m′ m′<n)
  ; eq-refl = λ f → f .param
  }


⟦∀⟧-resp-≈⟦Type⟧ : ∀ {Δ} n {T U : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ}
  → T ≈⟦Type⟧ U
  → ⟦∀⟧ n T ≈⟦Type⟧ ⟦∀⟧ n U
⟦∀⟧-resp-≈⟦Type⟧ n T≈U = record
  { forth = record
    { fobj = ⟦∀⟧′-resp-≈⟦Type⟧ T≈U .forth
    ; feq = λ δ≈δ′ x≈y a a₁ a₂ a₃ → T≈U .forth .feq _ (x≈y a a₁ a₂ a₃)
    }
  ; back = record
    { fobj = ⟦∀⟧′-resp-≈⟦Type⟧ T≈U .back
    ; feq = λ δ≈δ′ x≈y a a₁ a₂ a₃ → T≈U .back .feq _ (x≈y a a₁ a₂ a₃)
    }
  ; back-forth = ≈⁺ λ δ x → ⟦∀⟧′-resp-≈⟦Type⟧ T≈U .back∘forth _
  ; forth-back = ≈⁺ λ δ x → ⟦∀⟧′-resp-≈⟦Type⟧ T≈U .forth∘back _
  }


absₛ : ∀ {Δ n} {Γ : ⟦Type⟧ ⟦ Δ ⟧Δ} {T : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ}
  → subT ⟦ SS.Wk ⟧σ Γ ⇒ T
  → Γ ⇒ ⟦∀⟧ n T
absₛ {Δ} {n} {Γ} {T} f = record
  { fobj = λ {δ} x → record
    { arr = λ m m<n → f .fobj x
    ; param = λ m m<n m′ m′<n → f .feq _ (Γ .eq-refl x)
    }
  ; feq = λ _ x≈y m m′ m<nγ m′<nγ′ → f .feq ⊤.tt x≈y
  }


appₛ : ∀ {Δ n m} {Γ : ⟦Type⟧ ⟦ Δ ⟧Δ} {T : ⟦Type⟧ ⟦ Δ ∙ n ⟧Δ}
  → (m<n : m SS.< n)
  → Γ ⇒ ⟦∀⟧ n T
  → Γ ⇒ subT ⟦ SS.Fill m<n ⟧σ T
appₛ {m = m} {T = T} m<n f = record
  { fobj = λ {δ} x → f .fobj x .arr (⟦ m ⟧n .fobj δ) (MS.⟦<⟧ m<n)
  ; feq = λ δ≈δ′ {x y} x≈y → f .feq _ x≈y _ _ _ _
  }


{-
appₛ∘absₛ : ∀ {Δ n Γ T}
  → (⊢Fill : SS.Fill n ∶ Δ ⇒ᵤ (Δ ∙ n))
  → (⊢Wk : SS.Wk ∶ Δ ∙ n ⇒ᵤ Δ)
  → ∀ t
  → appₛ {Δ} {n} {Γ} {T} ⊢Fill (absₛ ⊢Wk t)
  ≈ subt ⟦ {!!} ⟧σ t
appₛ∘absₛ {Δ} {n} {Γ} {T} m m<n t .≈⁻ γ x = refl
-}


subT-⟦∀⟧ : ∀ {Δ Ω n σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (T : ⟦Type⟧ ⟦ Ω ∙ n ⟧Δ)
  → ⟦∀⟧ (n [ σ ]ᵤ)
      (subT (⟦_⟧σ {Ω = Ω ∙ n} (Lift ⊢σ refl)) T)
  ≈⟦Type⟧ subT ⟦ ⊢σ ⟧σ (⟦∀⟧ n T)
subT-⟦∀⟧ {Δ} {Ω} {n} {σ} ⊢σ T = record
  { forth = record
    { fobj = λ {γ} f → record
      { arr = λ m m<n
          → transportObj T
              (MS.⟦Δ∙n⟧-≡⁺ Ω n _ _ refl refl)
              (f .arr m (subst (m <_) (sym (MS.⟦sub⟧ ⊢σ n)) m<n))
      ; param = λ m m<n m′ m′<n
          → transportObj-resp-eq T _ _ (f .param _ _ _ _)
      }
    ; feq = λ γ≈γ′ f≈g a a₁ a₂ a₃ → transportObj-resp-eq T _ _ (f≈g _ _ _ _)
    }
  ; back = record
    { fobj = λ {γ} f → record
      { arr = λ m m<n
          → transportObj T
              (MS.⟦Δ∙n⟧-≡⁺ Ω n _ _ refl refl)
              (f .arr m (subst (m <_) (MS.⟦sub⟧ ⊢σ n) m<n))
      ; param = λ m m<n m′ m′<n
          → transportObj-resp-eq T _ _ (f .param _ _ _ _)
      }
    ; feq = λ γ≈γ′ f≈g a a₁ a₂ a₃ → transportObj-resp-eq T _ _ (f≈g _ _ _ _)
    }
  ; back-forth = ≈⁺ λ γ f → ⟦∀⟧′-≡⁺ _ _ λ m m<n
      → {!!}
  ; forth-back = {!!}
  }
