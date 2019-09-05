{-# OPTIONS --without-K #-}
module Util.HoTT.HLevel where

open import Util.HoTT.HLevel.Core public

open import Util.HoTT.Equiv
open import Util.HoTT.Univalence
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁺ ; Σ-≡⁻ ; Σ-≡⁺∘Σ-≡⁻ )
open import Util.Relation.Binary.LogicalEquivalence


private
  variable
    α β γ : Level
    A B C : Set α


infixr 0 _→-HProp_
infixr 2 _×-HProp_


⊤-IsContr : IsContr ⊤
⊤-IsContr = ⊤.tt , λ { ⊤.tt → refl }


⊤-IsProp : IsProp ⊤
⊤-IsProp = IsOfHLevel-suc 0 ⊤-IsContr


⊥-IsProp : IsProp ⊥
⊥-IsProp ()


∀-IsProp : {B : A → Set β} → (∀ a → IsProp (B a)) → IsProp (∀ a → B a)
∀-IsProp B-prop f g = funext λ a → B-prop _ _ _


∀∙-IsProp : {B : A → Set β} → (∀ a → IsProp (B a)) → IsProp (∀ {a} → B a)
∀∙-IsProp B-prop f g = funext∙ (B-prop _ _ _)


→-IsProp : IsProp B → IsProp (A → B)
→-IsProp B-prop = ∀-IsProp λ _ → B-prop


×-IsProp : IsProp A → IsProp B → IsProp (A × B)
×-IsProp A-prop B-prop (x , y) (x′ , y′) = cong₂ _,_ (A-prop _ _) (B-prop _ _)


⊤-HProp : HProp 0ℓ
⊤-HProp = HLevel⁺ ⊤ ⊤-IsProp


⊥-HProp : HProp 0ℓ
⊥-HProp = HLevel⁺ ⊥ ⊥-IsProp


_×-HProp_ : HProp α → HProp β → HProp (α ⊔ℓ β)
A ×-HProp B = HLevel⁺ (A .type × B .type) (×-IsProp (A .level) (B .level))


∀-HProp : (A : Set α) → ((a : A) → HProp β) → HProp (α ⊔ℓ β)
∀-HProp A B = HLevel⁺ (∀ a → B a .type) (∀-IsProp (λ a → B a .level))


∀∙-HProp : {A : Set α} → ((a : A) → HProp β) → HProp (α ⊔ℓ β)
∀∙-HProp B = HLevel⁺ (∀ {a} → B a .type) (∀∙-IsProp (λ a → B a .level))


_→-HProp_ : Set α → HProp β → HProp (α ⊔ℓ β)
A →-HProp B = HLevel⁺ (A → B .type) (→-IsProp (B .level))


_→-HProp′_ : HProp α → HProp β → HProp (α ⊔ℓ β)
A →-HProp′ B = A .type →-HProp B


IsContr-IsProp : IsProp (IsContr A)
IsContr-IsProp (x , x-unique) (y , y-unique)
  = Σ-≡⁺ (x-unique y , eq-prop _ _)
  where
  eq-prop : IsProp (∀ y′ → y ≡ y′)
  eq-prop = ∀-IsProp λ γ′ → IsOfHLevel-suc 1 (IsOfHLevel-suc 0 (x , x-unique))


IsProp-IsProp : IsProp (IsProp A)
IsProp-IsProp A-prop A-prop′
  = ∀-IsProp (λ x → ∀-IsProp λ y → IsOfHLevel-suc 1 A-prop) A-prop A-prop′


IsProp-ext : IsProp A → IsProp B → A ↔ B → A ≡ B
IsProp-ext A-prop B-prop A↔B = ≅→≡ record
  { forth = A↔B .forth
  ; isIso = record
    { back = A↔B .back
    ; back∘forth = λ _ → A-prop _ _
    ; forth∘back = λ _ → B-prop _ _
    }
  }


IsOfHLevel-IsProp : ∀ n → IsProp (IsOfHLevel n A)
IsOfHLevel-IsProp {A = A} zero = IsContr-IsProp
IsOfHLevel-IsProp (suc zero) = IsProp-IsProp
IsOfHLevel-IsProp (suc (suc n))
  = ∀∙-IsProp λ x → ∀∙-IsProp λ y → IsOfHLevel-IsProp (suc n)


HLevel-≡⁺ : ∀ {n} (A B : HLevel α n)
  → A .type ≡ B .type
  → A ≡ B
HLevel-≡⁺ (HLevel⁺ A A-level) (HLevel⁺ B B-level) refl
  = cong (HLevel⁺ A) (IsOfHLevel-IsProp _ _ _)


HProp-ext : (A B : HProp α) → A .type ↔ B .type → A ≡ B
HProp-ext A B A↔B = HLevel-≡⁺ A B (IsProp-ext (A .level) (B .level) A↔B)


Σ-IsSet : {A : Set α} {B : A → Set β}
  → IsSet A
  → (∀ a → IsSet (B a))
  → IsSet (Σ A B)
Σ-IsSet A-set B-set p q
  = trans (sym (Σ-≡⁺∘Σ-≡⁻ p))
      (sym (trans (sym (Σ-≡⁺∘Σ-≡⁻ q))
        (cong Σ-≡⁺ (Σ-≡⁺ (A-set _ _ , B-set _ _ _)))))
