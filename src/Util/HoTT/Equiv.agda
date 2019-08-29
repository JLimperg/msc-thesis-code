{-# OPTIONS --without-K --postfix-projections #-}
module Util.HoTT.Equiv where

open import Level using (Level ; _⊔_)
open import Relation.Binary using (Setoid ; IsEquivalence)

open import Util.HoTT.HLevel.Core using (IsContr)
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁻ ; Σ-≡⁺)


infix 4 _≅_ _≃_


private
  variable
    α β γ : Level
    A B C : Set α


record IsIso {A : Set α} {B : Set β} (forth : A → B) : Set (α ⊔ β)
  where
  field
    back : B → A
    back∘forth : ∀ x → back (forth x) ≡ x
    forth∘back : ∀ x → forth (back x) ≡ x


IsEquiv : {A : Set α} {B : Set β} (forth : A → B)
  → Set (α ⊔ β)
IsEquiv {A = A} {B} forth
  = ∀ b → IsContr (Σ[ a ∈ A ] forth a ≡ b)


IsEquiv→IsIso : {f : A → B} → IsEquiv f → IsIso f
IsEquiv→IsIso {A = A} {B = B} {forth} equiv = record
  { back = back ; back∘forth = back∘forth ; forth∘back = forth∘back }
  where
  back : B → A
  back b with equiv b
  ... | (a , _) , _ = a

  back∘forth : ∀ x → back (forth x) ≡ x
  back∘forth a with equiv (forth a)
  ... | (a′ , fortha′≡fortha) , unique = proj₁ (Σ-≡⁻ (unique (a , refl)))

  forth∘back : ∀ x → forth (back x) ≡ x
  forth∘back b with equiv b
  ... | (a , fortha≡b) , _ = fortha≡b


-- TODO
postulate
  IsIso→IsEquiv : {f : A → B} → IsIso f → IsEquiv f
-- IsIso→IsEquiv {A = A} {B} forth iso b = (back b , forth∘back b) , unique
--   where
--   open IsIso iso

--   unique : (y : Σ[ a ∈ A ] (forth a ≡ b)) → (back b , forth∘back b) ≡ y
--   unique (a , refl)
--     -- = Σ-≡⁺ (trans (cong back (sym p)) (back∘forth a) , {!trans (cong back (sym p)) (back∘forth a)!})
--     = Σ-≡⁺ (back∘forth a , trans (go forth (back∘forth a) (forth∘back (forth a))) go₂)
--     where
--       go : ∀ (f : A → B) {x y}
--         → (p : x ≡ y) (q : f x ≡ f y)
--         → subst (λ a → f a ≡ f y) p q ≡ trans (sym (cong f p)) q
--       go f refl q = refl

--       go₂ : trans (sym (cong forth (back∘forth a))) (forth∘back (forth a)) ≡
--               refl
--       go₂ = {!!}


record _≅_ (A : Set α) (B : Set β) : Set (α ⊔ β) where
  field
    forth : A → B
    isIso : IsIso forth

  open IsIso isIso public

open _≅_ public


≅-refl : A ≅ A
≅-refl .forth x = x
≅-refl .isIso .IsIso.back x = x
≅-refl .isIso .IsIso.forth∘back x = refl
≅-refl .isIso .IsIso.back∘forth x = refl


≅-sym : A ≅ B → B ≅ A
≅-sym A≅B .forth = A≅B .back
≅-sym A≅B .isIso .IsIso.back = A≅B .forth
≅-sym A≅B .isIso .IsIso.back∘forth = A≅B .forth∘back
≅-sym A≅B .isIso .IsIso.forth∘back = A≅B .back∘forth


≅-trans : A ≅ B → B ≅ C → A ≅ C
≅-trans A≅B B≅C .forth = B≅C .forth ∘ A≅B .forth
≅-trans A≅B B≅C .isIso .IsIso.back = A≅B .back ∘ B≅C .back
≅-trans A≅B B≅C .isIso .IsIso.back∘forth x
  = trans (cong (A≅B .back) (B≅C .back∘forth _)) (A≅B .back∘forth _)
≅-trans A≅B B≅C .isIso .IsIso.forth∘back x
  = trans (cong (B≅C .forth) (A≅B .forth∘back _)) (B≅C .forth∘back _)


≅-isEquivalence : IsEquivalence (_≅_ {α})
≅-isEquivalence .IsEquivalence.refl = ≅-refl
≅-isEquivalence .IsEquivalence.sym = ≅-sym
≅-isEquivalence .IsEquivalence.trans = ≅-trans


≅-setoid : ∀ α → Setoid (lsuc α) α
≅-setoid α .Setoid.Carrier = Set α
≅-setoid α .Setoid._≈_ = _≅_
≅-setoid α .Setoid.isEquivalence = ≅-isEquivalence


record _≃_ (A : Set α) (B : Set β) : Set (α ⊔ β) where
  field
    forth : A → B
    isEquiv : IsEquiv forth

open _≃_ public


≃→≅ : A ≃ B → A ≅ B
≃→≅ A≃B .forth = A≃B .forth
≃→≅ A≃B .isIso = IsEquiv→IsIso (A≃B .isEquiv)


≅→≃ : A ≅ B → A ≃ B
≅→≃ A≅B .forth = A≅B .forth
≅→≃ A≅B .isEquiv = IsIso→IsEquiv (A≅B .isIso)


≃-refl : A ≃ A
≃-refl = record
  { forth = λ x → x
  ; isEquiv = λ a → (a , refl) , λ { (b , refl) → refl }
  }


≃-reflexive : A ≡ B → A ≃ B
≃-reflexive refl = ≃-refl


≡→≃ = ≃-reflexive


≃-sym : A ≃ B → B ≃ A
≃-sym = ≅→≃ ∘ ≅-sym ∘ ≃→≅


≃-trans : A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C = ≅→≃ (≅-trans (≃→≅ A≃B) (≃→≅ B≃C))


≃-isEquivalence : IsEquivalence (_≃_ {α})
≃-isEquivalence .IsEquivalence.refl = ≃-refl
≃-isEquivalence .IsEquivalence.sym = ≃-sym
≃-isEquivalence .IsEquivalence.trans = ≃-trans


≃-setoid : ∀ α → Setoid (lsuc α) α
≃-setoid α .Setoid.Carrier = Set α
≃-setoid α .Setoid._≈_ = _≃_
≃-setoid α .Setoid.isEquivalence = ≃-isEquivalence
