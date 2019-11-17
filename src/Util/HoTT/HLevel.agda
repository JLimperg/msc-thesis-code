{-# OPTIONS --without-K #-}
module Util.HoTT.HLevel where

open import Util.HoTT.HLevel.Core public

open import Util.HoTT.Equiv
open import Util.HoTT.FunctionalExtensionality
open import Util.HoTT.Homotopy
open import Util.HoTT.Univalence.Axiom
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁺ ; Σ-≡⁻ ; Σ-≡⁺∘Σ-≡⁻ )
open import Util.Relation.Binary.LogicalEquivalence


private
  variable
    α β γ : Level
    A B C : Set α


infixr 0 _→-HProp_


-- Note that A and B must be at the same level. A more direct proof could
-- probably avoid this.
≃-pres-IsOfHLevel : ∀ {A B : Set α} n → A ≃ B → IsOfHLevel n A → IsOfHLevel n B
≃-pres-IsOfHLevel n A≃B = subst (IsOfHLevel n) (≃→≡ A≃B)


≅-pres-IsOfHLevel : ∀ {A B : Set α} n → A ≅ B → IsOfHLevel n A → IsOfHLevel n B
≅-pres-IsOfHLevel n A≅B = ≃-pres-IsOfHLevel n (≅→≃ A≅B)


∀-IsProp : {B : A → Set β} → (∀ a → IsProp (B a)) → IsProp (∀ a → B a)
∀-IsProp B-prop f g = funext λ a → B-prop _ _ _


∀∙-IsProp : {B : A → Set β} → (∀ a → IsProp (B a)) → IsProp (∀ {a} → B a)
∀∙-IsProp B-prop f g = funext∙ (B-prop _ _ _)


→-IsProp : IsProp B → IsProp (A → B)
→-IsProp B-prop = ∀-IsProp λ _ → B-prop


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


IsOfHLevel-IsProp : ∀ n → IsProp (IsOfHLevel n A)
IsOfHLevel-IsProp {A = A} zero = IsContr-IsProp
IsOfHLevel-IsProp (suc zero) = IsProp-IsProp
IsOfHLevel-IsProp (suc (suc n))
  = ∀∙-IsProp λ x → ∀∙-IsProp λ y → IsOfHLevel-IsProp (suc n)


IsSet-IsProp : IsProp (IsSet A)
IsSet-IsProp = IsOfHLevel-IsProp 2


∀-IsSet : {A : Set α} {B : A → Set β}
  → (∀ a → IsSet (B a))
  → IsSet (∀ a → B a)
∀-IsSet B-set {f} {g} p q = let open ≡-Reasoning in
  begin
    p
  ≡˘⟨ funext∘≡→~ p ⟩
    funext (≡→~ p)
  ≡⟨ cong funext (funext λ a → B-set a (≡→~ p a) (≡→~ q a)) ⟩
    funext (≡→~ q)
  ≡⟨ funext∘≡→~ q ⟩
    q
  ∎


∀∙-IsSet : {A : Set α} {B : A → Set β}
  → (∀ a → IsSet (B a))
  → IsSet (∀ {a} → B a)
∀∙-IsSet {A = A} {B = B} B-set = ≅-pres-IsOfHLevel 2 iso (∀-IsSet B-set)
  where
    iso : (∀ a → B a) ≅ (∀ {a} → B a)
    iso = record
      { forth = λ f {a} → f a
      ; isIso = record
        { back = λ f a → f {a}
        ; back∘forth = λ _ → refl
        ; forth∘back = λ _ → refl
        }
      }


→-IsSet : IsSet B → IsSet (A → B)
→-IsSet B-set = ∀-IsSet (λ _ → B-set)


∀-HSet : (A : Set α) → (A → HSet β) → HSet (α ⊔ℓ β)
∀-HSet A B = HLevel⁺ (∀ a → B a .type) (∀-IsSet (λ a → B a .level))


∀∙-HSet : {A : Set α} → (A → HSet β) → HSet (α ⊔ℓ β)
∀∙-HSet B = HLevel⁺ (∀ {a} → B a .type) (∀∙-IsSet (λ a → B a .level))


HLevel-≡⁺ : ∀ {n} (A B : HLevel α n)
  → A .type ≡ B .type
  → A ≡ B
HLevel-≡⁺ (HLevel⁺ A A-level) (HLevel⁺ B B-level) refl
  = cong (HLevel⁺ A) (IsOfHLevel-IsProp _ _ _)


IsContr-≅⁺ : IsContr A → IsContr B → A ≅ B
IsContr-≅⁺ (a , a-uniq) (b , b-uniq) = record
  { forth = λ _ → b
  ; isIso = record
    { back = λ _ → a
    ; back∘forth = λ _ → a-uniq _
    ; forth∘back = λ _ → b-uniq _
    }
  }


HContr-≡⁺ : (A B : HContr α) → A ≡ B
HContr-≡⁺ A B = HLevel-≡⁺ A B (≅→≡ (IsContr-≅⁺ (A .level) (B .level)))


IsProp-≅⁺ : IsProp A → IsProp B → A ↔ B → A ≅ B
IsProp-≅⁺ A-prop B-prop A↔B = record
  { forth = A↔B .forth
  ; isIso = record
    { back = A↔B .back
    ; back∘forth = λ _ → A-prop _ _
    ; forth∘back = λ _ → B-prop _ _
    }
  }


HProp-≡⁺ : (A B : HProp α) → A .type ↔ B .type → A ≡ B
HProp-≡⁺ A B A↔B = HLevel-≡⁺ A B (≅→≡ (IsProp-≅⁺ (A .level) (B .level) A↔B))
