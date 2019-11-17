{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Equiv where

open import Util.HoTT.Equiv.Core public

open import Relation.Binary using (Setoid ; IsEquivalence)

open import Util.Data.Product using (map₂)
open import Util.HoTT.HLevel.Core using (IsContr ; IsProp)
open import Util.HoTT.Section
open import Util.HoTT.Singleton using (IsContr-Singleton)
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( Σ-≡⁻ ; Σ-≡⁺ ; sym-cancel-r ; trans-unassoc )


private
  variable
    α β γ : Level
    A B C : Set α


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


IsEquiv→IsIso : {f : A → B} → IsEquiv f → IsIso f
IsEquiv→IsIso {A = A} {B = B} {forth} equiv = record
  { back = back′ ; back∘forth = back∘forth′ ; forth∘back = forth∘back′ }
  where
  back′ : B → A
  back′ b with equiv b
  ... | (a , _) , _ = a

  back∘forth′ : ∀ x → back′ (forth x) ≡ x
  back∘forth′ a with equiv (forth a)
  ... | (a′ , fortha′≡fortha) , unique = proj₁ (Σ-≡⁻ (unique (a , refl)))

  forth∘back′ : ∀ x → forth (back′ x) ≡ x
  forth∘back′ b with equiv b
  ... | (a , fortha≡b) , _ = fortha≡b


IsEquiv→Injective : {f : A → B} → IsEquiv f → Injective f
IsEquiv→Injective = IsIso→Injective ∘ IsEquiv→IsIso


-- This proof follows Martin Escardó's lecture notes
-- (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#fibersandequivalences).
IsIso→IsEquiv : {f : A → B} → IsIso f → IsEquiv f
IsIso→IsEquiv {A = A} {B = B} {forth} iso b
  = ◁-pres-IsContr (◁-trans ii iii) IsContr-Singleton
  where
    module I = IsIso iso

    A◁B : A ◁ B
    A◁B = record
      { retraction = I.back
      ; hasSection = IsIso→HasSection-back iso
      }


    i : ∀ b′ → (forth (I.back b′) ≡ b) ◁ (b′ ≡ b)
    i b′ = record
      { retraction = λ b′≡b → trans (I.forth∘back b′) b′≡b
      ; hasSection = record
        { section = λ eq → trans (sym (I.forth∘back b′)) eq
        ; isSection = λ x → let open ≡-Reasoning in
          begin
            trans (I.forth∘back b′) (trans (sym (I.forth∘back b′)) x)
          ≡⟨ trans-unassoc (I.forth∘back b′) ⟩
            trans (trans (I.forth∘back b′) (sym (I.forth∘back b′))) x
          ≡⟨ cong (λ p → trans p x) (sym-cancel-r (I.forth∘back b′)) ⟩
            x
          ∎
        }
      }


    ii : ∃[ a ] (forth a ≡ b) ◁ ∃[ b′ ] (forth (I.back b′) ≡ b)
    ii = Σ-◁-reindexing A◁B


    iii : ∃[ b′ ] (forth (I.back b′) ≡ b) ◁ ∃[ b′ ] (b′ ≡ b)
    --                                   aka Singleton b
    iii = Σ-◁ i


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


≅-reflexive : A ≡ B → A ≅ B
≅-reflexive refl = ≅-refl


≡→≅ = ≅-reflexive


≅-Injective : (i : A ≅ B) → Injective (i .forth)
≅-Injective i = IsIso→Injective (i .isIso)


≅→◁ : A ≅ B → A ◁ B
≅→◁ A≅B = record
  { retraction = A≅B .back
  ; hasSection = IsIso→HasSection-back (A≅B .isIso)
  }

≅→▷ : A ≅ B → B ◁ A
≅→▷ A≅B = record
  { retraction = A≅B .forth
  ; hasSection = IsIso→HasSection-forth (A≅B .isIso)
  }


≃→≅ : A ≃ B → A ≅ B
≃→≅ A≃B .forth = A≃B .forth
≃→≅ A≃B .isIso = IsEquiv→IsIso (A≃B .isEquiv)


≅→≃ : A ≅ B → A ≃ B
≅→≃ A≅B .forth = A≅B .forth
≅→≃ A≅B .isEquiv = IsIso→IsEquiv (A≅B .isIso)


id-IsEquiv : IsEquiv (id {A = A})
id-IsEquiv a = (a , refl) , λ { (b , refl) → refl }


≃-refl : A ≃ A
≃-refl = record { forth = id ; isEquiv = id-IsEquiv }


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


≃-Injective : (e : A ≃ B) → Injective (e .forth)
≃-Injective = ≅-Injective ∘ ≃→≅


≃→◁ : A ≃ B → A ◁ B
≃→◁ = ≅→◁ ∘ ≃→≅


≃→▷ : A ≃ B → B ◁ A
≃→▷ = ≅→▷ ∘ ≃→≅


-- Special cases of ≃-pres-IsOfHLevel (in Util.HoTT.HLevel), but proven
-- directly. This means that A and B can be at different levels.
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


Σ-≅⁺ : {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (∀ a → B a ≅ C a)
  → Σ A B ≅ Σ A C
Σ-≅⁺ eq = record
  { forth = λ { (a , b) → a , eq a .forth b }
  ; isIso = record
    { back = λ { (a , c) → a , eq a .back c }
    ; back∘forth = λ { (a , b) → Σ-≡⁺ (refl , eq a .back∘forth b) }
    ; forth∘back = λ { (a , c) → Σ-≡⁺ (refl , eq a .forth∘back c) }
    }
  }


Σ-≃⁺ : {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (∀ a → B a ≃ C a)
  → Σ A B ≃ Σ A C
Σ-≃⁺ eq = ≅→≃ (Σ-≅⁺ λ a → ≃→≅ (eq a))


map₂-fiber-≃ : {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (f : ∀ a → B a → C a)
  → ∀ a (c : C a)
  → ∃[ b ] (f a b ≡ c) ≃ ∃[ p ] (map₂ f p ≡ (a , c))
map₂-fiber-≃ f a c = ≅→≃ record
  { forth = λ { (b , refl) → (a , b) , refl }
  ; isIso = record
    { back = λ { ((.a , b) , refl) → b , refl }
    ; back∘forth = λ { (b , refl) → refl }
    ; forth∘back = λ { ((.a , b) , refl) → refl }
    }
  }


IsEquiv-map₂-f→IsEquiv-f : {A : Set α} {B : A → Set β} {C : A → Set γ}
  → (f : ∀ a → B a → C a)
  → IsEquiv (map₂ f)
  → ∀ a → IsEquiv (f a)
IsEquiv-map₂-f→IsEquiv-f {A = A} {B} {C} f equiv a c
  = ≃-pres-IsContr (≃-sym (map₂-fiber-≃ f a c)) (equiv (a , c))


sym-≅ : {x y : A} → (x ≡ y) ≅ (y ≡ x)
sym-≅ = record
  { forth = sym
  ; isIso = record
    { back = sym
    ; back∘forth = λ { refl → refl }
    ; forth∘back = λ { refl → refl }
    }
  }


sym-≃ : {x y : A} → (x ≡ y) ≃ (y ≡ x)
sym-≃ = ≅→≃ sym-≅


IsContr→IsIso : IsContr A → IsContr B → (f : A → B) → IsIso f
IsContr→IsIso (a , a-uniq) (b , b-uniq) f = record
  { back = λ _ → a
  ; back∘forth = λ _ → a-uniq _
  ; forth∘back = λ b′ → trans (sym (b-uniq (f a))) (b-uniq b′)
  }


IsContr→IsEquiv : IsContr A → IsContr B → (f : A → B) → IsEquiv f
IsContr→IsEquiv A-contr B-contr f
  = IsIso→IsEquiv (IsContr→IsIso A-contr B-contr f)


proj₁-IsIso : {A : Set α} {B : A → Set β}
  → (∀ a → IsContr (B a))
  → IsIso (proj₁ {A = A} {B})
proj₁-IsIso B-contr = record
  { back = λ a → (a , B-contr a .proj₁)
  ; back∘forth = λ { (a , b) → Σ-≡⁺ (refl , (B-contr a .proj₂ b)) }
  ; forth∘back = λ _ → refl
  }


proj₁-IsEquiv : {A : Set α} {B : A → Set β}
  → (∀ a → IsContr (B a))
  → IsEquiv (proj₁ {A = A} {B})
proj₁-IsEquiv B-contr = IsIso→IsEquiv (proj₁-IsIso B-contr)


Π-distr-Σ-≅ : (A : Set α) (B : A → Set β) (C : ∀ a → B a → Set γ)
  → (∀ a → Σ[ b ∈ B a ] (C a b))
  ≅ (Σ[ f ∈ (∀ a → B a) ] (∀ a → C a (f a)))
Π-distr-Σ-≅ A B C = record
  { forth = λ f → (λ a → f a .proj₁) , (λ a → f a .proj₂)
  ; isIso = record
    { back = λ { (f , g) → λ a → f a , g a }
    ; back∘forth = λ _ → refl
    ; forth∘back = λ _ → refl
    }
  }
