{-# OPTIONS --without-K #-}
module Util.HoTT.HLevel where

open import Util.HoTT.HLevel.Core public

open import Level using (Lift ; lift ; lower)

open import Util.HoTT.Equiv
open import Util.HoTT.Univalence
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁺ ; Σ-≡⁻ ; Σ-≡⁺∘Σ-≡⁻ ; happly )
open import Util.Relation.Binary.LogicalEquivalence


private
  variable
    α β γ : Level
    A B C : Set α


infixr 0 _→-HProp_
infixr 2 _×-HProp_


-- Note that A and B must be at the same level. A more direct proof could
-- probably avoid this.
≃-pres-IsOfHLevel : ∀ {A B : Set α} n → A ≃ B → IsOfHLevel n A → IsOfHLevel n B
≃-pres-IsOfHLevel n A≃B = subst (IsOfHLevel n) (≃→≡ A≃B)


≅-pres-IsOfHLevel : ∀ {A B : Set α} n → A ≅ B → IsOfHLevel n A → IsOfHLevel n B
≅-pres-IsOfHLevel n A≅B = ≃-pres-IsOfHLevel n (≅→≃ A≅B)


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


Lift-IsProp : IsProp A → IsProp (Lift α A)
Lift-IsProp A-prop (lift x) (lift y) = cong lift (A-prop _ _)


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


Lift-HProp : ∀ α → HProp β → HProp (α ⊔ℓ β)
Lift-HProp α (HLevel⁺ A A-prop) = HLevel⁺ (Lift α A) (Lift-IsProp A-prop)


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


⊤-IsSet : IsSet ⊤
⊤-IsSet = IsOfHLevel-suc 1 ⊤-IsProp


⊥-IsSet : IsSet ⊥
⊥-IsSet = IsOfHLevel-suc 1 ⊥-IsProp


∀-IsSet : {A : Set α} {B : A → Set β}
  → (∀ a → IsSet (B a))
  → IsSet (∀ a → B a)
∀-IsSet B-set {f} {g} p q = let open ≡-Reasoning in
  begin
    p
  ≡⟨ ∀-≡-canon p ⟩
    funext (happly p)
  ≡⟨ cong funext (funext λ a → B-set a (happly p a) (happly q a)) ⟩
    funext (happly q)
  ≡˘⟨ ∀-≡-canon q ⟩
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


Σ-IsSet : {A : Set α} {B : A → Set β}
  → IsSet A
  → (∀ a → IsSet (B a))
  → IsSet (Σ A B)
Σ-IsSet A-set B-set p q
  = trans (sym (Σ-≡⁺∘Σ-≡⁻ p))
      (sym (trans (sym (Σ-≡⁺∘Σ-≡⁻ q))
      (cong Σ-≡⁺ (Σ-≡⁺ (A-set _ _ , B-set _ _ _)))))


×-IsSet : IsSet A → IsSet B → IsSet (A × B)
×-IsSet A-set B-set = Σ-IsSet A-set (λ _ → B-set)


Lift-IsSet : IsSet A → IsSet (Lift α A)
Lift-IsSet A-set p q
  = trans (sym (Lift-≡⁺∘Lift-≡⁻ p))
      (sym (trans (sym (Lift-≡⁺∘Lift-≡⁻ q)) (cong Lift-≡⁺ (A-set _ _))))
  where
    Lift-≡⁻ : {x y : Lift α A} → x ≡ y → lower x ≡ lower y
    Lift-≡⁻ refl = refl

    Lift-≡⁺ : {x y : Lift α A} → lower x ≡ lower y → x ≡ y
    Lift-≡⁺ refl = refl

    Lift-≡⁻∘Lift-≡⁺ : {x y : Lift α A} (p : lower x ≡ lower y)
      → Lift-≡⁻ {α = α} (Lift-≡⁺ p) ≡ p
    Lift-≡⁻∘Lift-≡⁺ refl = refl

    Lift-≡⁺∘Lift-≡⁻ : {x y : Lift α A} (p : x ≡ y)
      → Lift-≡⁺ {α = α} (Lift-≡⁻ p) ≡ p
    Lift-≡⁺∘Lift-≡⁻ refl = refl


⊤-HSet : HSet 0ℓ
⊤-HSet = HLevel⁺ ⊤ ⊤-IsSet


⊥-HSet : HSet 0ℓ
⊥-HSet = HLevel⁺ ⊥ ⊥-IsSet


∀-HSet : (A : Set α) → (A → HSet β) → HSet (α ⊔ℓ β)
∀-HSet A B = HLevel⁺ (∀ a → B a .type) (∀-IsSet (λ a → B a .level))


∀∙-HSet : {A : Set α} → (A → HSet β) → HSet (α ⊔ℓ β)
∀∙-HSet B = HLevel⁺ (∀ {a} → B a .type) (∀∙-IsSet (λ a → B a .level))


Σ-HSet : (A : HSet α) (B : A .type → HSet β) → HSet (α ⊔ℓ β)
Σ-HSet A B
  = HLevel⁺ (Σ (A .type) λ a → B a .type) (Σ-IsSet (A .level) (λ a → B a .level))


_×-HSet_ : HSet α → HSet β → HSet (α ⊔ℓ β)
A ×-HSet B = HLevel⁺ (A .type × B .type) (×-IsSet (A .level) (B .level))


Lift-HSet : ∀ α → HSet β → HSet (α ⊔ℓ β)
Lift-HSet α (HLevel⁺ B B-set) = HLevel⁺ (Lift α B) (Lift-IsSet B-set)


IsProp-ext : IsProp A → IsProp B → A ↔ B → A ≡ B
IsProp-ext A-prop B-prop A↔B = ≅→≡ record
  { forth = A↔B .forth
  ; isIso = record
    { back = A↔B .back
    ; back∘forth = λ _ → A-prop _ _
    ; forth∘back = λ _ → B-prop _ _
    }
  }


HLevel-≡⁺ : ∀ {n} (A B : HLevel α n)
  → A .type ≡ B .type
  → A ≡ B
HLevel-≡⁺ (HLevel⁺ A A-level) (HLevel⁺ B B-level) refl
  = cong (HLevel⁺ A) (IsOfHLevel-IsProp _ _ _)


HProp-ext : (A B : HProp α) → A .type ↔ B .type → A ≡ B
HProp-ext A B A↔B = HLevel-≡⁺ A B (IsProp-ext (A .level) (B .level) A↔B)


-- Special cases of ≃-pres-IsOfHLevel, but proven directly. Not sure if that
-- makes a difference; after all, IsOfHLevel is irrelevant anyway.

≅-pres-IsContr : A ≅ B → IsContr A → IsContr B
≅-pres-IsContr A≅B (a , canon) = A≅B .forth a , λ a′
  → trans (cong (A≅B .forth) (canon (A≅B .back a′))) (A≅B .forth∘back _)


≃-pres-IsContr : A ≃ B → IsContr A → IsContr B
≃-pres-IsContr A≃B = ≅-pres-IsContr (≃→≅ A≃B)


≅-pres-IsProp : A ≅ B → IsProp A → IsProp B
≅-pres-IsProp A≅B A-prop x y
  = trans (sym (A≅B .forth∘back x))
      (sym (trans (sym (A≅B .forth∘back y)) (cong (A≅B .forth) (A-prop _ _))))


≃-pres-IsProp : A ≃ B → IsProp A → IsProp B
≃-pres-IsProp A≃B = ≅-pres-IsProp (≃→≅ A≃B)
