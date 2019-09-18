{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Equiv where

open import Level using (Level ; _⊔_)
open import Relation.Binary using (Setoid ; IsEquivalence)

open import Util.HoTT.HLevel.Core using (IsContr ; IsContr-Singleton)
open import Util.HoTT.Section
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁻ ; Σ-≡⁺ ; sym-cancel-r ; trans-unassoc )


infix 4 _≅_ _≃_


private
  variable
    α β γ : Level
    A B C : Set α


Injective : (f : A → B) → Set _
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y


record IsIso {A : Set α} {B : Set β} (forth : A → B) : Set (α ⊔ β)
  where
  field
    back : B → A
    back∘forth : ∀ x → back (forth x) ≡ x
    forth∘back : ∀ x → forth (back x) ≡ x


IsIso→HasSection-forth : {f : A → B} → IsIso f → HasSection f
IsIso→HasSection-forth i = record
  { section = i .IsIso.back
  ; isSection = i .IsIso.forth∘back
  }


IsIso→HasSection-back : {f : A → B} → (i : IsIso f) → HasSection (i .IsIso.back)
IsIso→HasSection-back {f = f} i = record
  { section = f
  ; isSection = i .IsIso.back∘forth
  }


IsIso→Injective : {f : A → B} → IsIso f → Injective f
IsIso→Injective f-iso fx≡fy
  = trans (sym (f-iso .IsIso.back∘forth _))
      (trans (cong (f-iso .IsIso.back) fx≡fy)
        (f-iso .IsIso.back∘forth _))


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


-- This proof follows Martin Escardó's lecture notes
-- (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#fibersandequivalences).
IsIso→IsEquiv : {f : A → B} → IsIso f → IsEquiv f
IsIso→IsEquiv {A = A} {B = B} {forth} iso b
  = ◁-pres-IsContr (◁-trans ii iii) IsContr-Singleton
  where
    open IsIso iso

    A◁B : A ◁ B
    A◁B = record
      { retraction = back
      ; hasSection = IsIso→HasSection-back iso
      }


    i : ∀ b′ → (forth (back b′) ≡ b) ◁ (b′ ≡ b)
    i b′ = record
      { retraction = λ b′≡b → trans (forth∘back b′) b′≡b
      ; hasSection = record
        { section = λ eq → trans (sym (forth∘back b′)) eq
        ; isSection = λ x → let open ≡-Reasoning in
          begin
            trans (forth∘back b′) (trans (sym (forth∘back b′)) x)
          ≡⟨ trans-unassoc (forth∘back b′) ⟩
            trans (trans (forth∘back b′) (sym (forth∘back b′))) x
          ≡⟨ cong (λ p → trans p x) (sym-cancel-r (forth∘back b′)) ⟩
            x
          ∎
        }
      }


    ii : ∃[ a ] (forth a ≡ b) ◁ ∃[ b′ ] (forth (back b′) ≡ b)
    ii = Σ-◁-reindexing A◁B


    iii : ∃[ b′ ] (forth (back b′) ≡ b) ◁ ∃[ b′ ] (b′ ≡ b)
    --                                   aka Singleton b
    iii = Σ-◁ i


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


≅-Injective : (i : A ≅ B) → Injective (i .forth)
≅-Injective i = IsIso→Injective (i .isIso)


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
