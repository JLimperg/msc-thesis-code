-- This module closely follows a section of Martín Escardó's HoTT lecture notes:
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#funextfromua
{-# OPTIONS --without-K #-}
module Util.HoTT.FunctionalExtensionality where

open import Axiom.Extensionality.Propositional using
  (ExtensionalityImplicit ; implicit-extensionality)

open import Util.Data.Product using (map₂)
open import Util.HoTT.Equiv
open import Util.HoTT.Equiv.Induction
open import Util.HoTT.HLevel.Core
open import Util.HoTT.Homotopy
open import Util.HoTT.Section
open import Util.HoTT.Singleton
open import Util.HoTT.Univalence
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using (Σ-≡⁻)


private
  variable
    α β γ : Level
    A B C : Set α


FunextNondep : ∀ α β → Set (lsuc (α ⊔ℓ β))
FunextNondep α β
  = {A : Set α} {B : Set β} {f g : A → B} → (∀ a → f a ≡ g a) → f ≡ g


IsContr-∀-Closure : ∀ α β → Set (lsuc (α ⊔ℓ β))
IsContr-∀-Closure α β
  = {A : Set α} {B : A → Set β} → (∀ a → IsContr (B a)) → IsContr (∀ a → B a)


FunextHapply : ∀ α β → Set (lsuc (α ⊔ℓ β))
FunextHapply α β
  = {A : Set α} {B : A → Set β} (f g : ∀ a → B a) → IsEquiv (≡→~ {f = f} {g})


Funext : ∀ α β → Set (lsuc (α ⊔ℓ β))
Funext α β
  = {A : Set α} {B : A → Set β} {f g : ∀ a → B a} → (∀ a → f a ≡ g a) → f ≡ g


abstract
  precomp-IsEquiv : {A B : Set α} (f : A → B)
    → IsEquiv f
    → {C : Set α}
    → IsEquiv (λ (g : B → C) → g ∘ f)
  precomp-IsEquiv f f-equiv {C}
    = J-IsEquiv (λ A B f → IsEquiv (λ (g : B → C) → g ∘ f)) (λ A → id-IsEquiv) f
        f-equiv


  funext-nondep : FunextNondep α β
  funext-nondep {α} {β} {A} {B} {f} {g} f~g
    = cong (λ π x → π (f x , g x , f~g x)) π₀≡π₁
    where
      Δ : Set β
      Δ = Σ[ b ∈ B ] Σ[ b′ ∈ B ] (b ≡ b′)

      δ : B → Δ
      δ b = b , b , refl

      π₀ π₁ : Δ → B
      π₀ (b , b′ , p) = b
      π₁ (b , b′ , p) = b′

      δ-IsEquiv : IsEquiv δ
      δ-IsEquiv = IsIso→IsEquiv record
        { back = π₀
        ; back∘forth = λ _ → refl
        ; forth∘back = λ { (b , b′ , refl) → refl }
        }

      φ : (Δ → B) → (B → B)
      φ = _∘ δ

      φ-IsEquiv : IsEquiv φ
      φ-IsEquiv = precomp-IsEquiv δ δ-IsEquiv

      φπ₀≡φπ₁ : φ π₀ ≡ φ π₁
      φπ₀≡φπ₁ = refl

      π₀≡π₁ : π₀ ≡ π₁
      π₀≡π₁ = IsEquiv→Injective φ-IsEquiv φπ₀≡φπ₁


  postcomp-IsIso : {A : Set α} {B : Set β} (f : B → C)
    → IsIso f
    → IsIso (λ (g : A → B) → f ∘ g)
  postcomp-IsIso {A = A} {B} f i = record
    { back = λ g a → i .IsIso.back (g a)
    ; back∘forth = λ g → funext-nondep λ a → i .IsIso.back∘forth (g a)
    ; forth∘back = λ g → funext-nondep λ a → i .IsIso.forth∘back (g a)
    }


  postcomp-IsEquiv : {A : Set α} {B : Set β} (f : B → C)
    → IsEquiv f
    → IsEquiv (λ (g : A → B) → f ∘ g)
  postcomp-IsEquiv f f-equiv
    = IsIso→IsEquiv (postcomp-IsIso f (IsEquiv→IsIso f-equiv))


  ∀-IsContr : IsContr-∀-Closure α β
  ∀-IsContr {A = A} {B} B-contr = ◁-pres-IsContr ΠB◁g-fiber g-fiber-IsContr
    where
      f : Σ A B → A
      f = proj₁

      f-IsEquiv : IsEquiv f
      f-IsEquiv = proj₁-IsEquiv B-contr

      g : (A → Σ A B) → (A → A)
      g = f ∘_

      g-IsEquiv : IsEquiv g
      g-IsEquiv = postcomp-IsEquiv f f-IsEquiv

      g-fiber-IsContr : IsContr (Σ[ h ∈ (A → Σ A B) ] (f ∘ h ≡ id))
      g-fiber-IsContr = g-IsEquiv id

      ΠB◁g-fiber : (∀ a → B a) ◁ (Σ[ h ∈ (A → Σ A B) ] (f ∘ h ≡ id))
      ΠB◁g-fiber = record
        { retraction = λ { (h , p) a → subst B (≡→~ p a) (proj₂ (h a)) }
        ; hasSection = record
          { section = λ h → (λ a → a , h a) , refl
          ; isSection = λ _ → refl
          }
        }

  ≡→~-IsEquiv : FunextHapply α β
  ≡→~-IsEquiv {A = A} {B} f = goal
    where
      i : ∀ a → IsContr (Σ[ b ∈ B a ] (f a ≡ b))
      i a = IsContr-Singleton′

      ii : IsContr (∀ a → Σ[ b ∈ B a ] (f a ≡ b))
      ii = ∀-IsContr i

      iii : (∃[ g ] (f ~ g)) ◁ (∀ a → Σ[ b ∈ B a ] (f a ≡ b))
      iii = ≅→▷ (Π-distr-Σ-≅ _ _ _)

      iv : IsContr (∃[ g ] (f ~ g))
      iv = ◁-pres-IsContr iii ii

      e : (∃[ g ] (f ≡ g)) → (∃[ g ] (f ~ g))
      e = map₂ (λ _ → ≡→~)

      e-IsEquiv : IsEquiv e
      e-IsEquiv = IsContr→IsEquiv IsContr-Singleton′ iv e

      goal : ∀ g → IsEquiv (≡→~ {f = f} {g})
      goal = IsEquiv-map₂-f→IsEquiv-f (λ _ → ≡→~) e-IsEquiv


funext : Funext α β
funext {f = f} {g} eq = ≡→~-IsEquiv f g eq .proj₁ .proj₁


funext∙ : ExtensionalityImplicit α β
funext∙ = implicit-extensionality funext


module _ {α β} {A : Set α} {B : A → Set β} {f g : ∀ a → B a} where

  ≡→~∘funext : (eq : ∀ a → f a ≡ g a)
    → ≡→~ (funext eq) ≡ eq
  ≡→~∘funext eq = ≡→~-IsEquiv f g eq .proj₁ .proj₂


  funext-unique′ : ∀ eq
    → (y : Σ-syntax (f ≡ g) (λ p → ≡→~ p ≡ eq))
    → (funext eq , ≡→~∘funext eq) ≡ y
  funext-unique′ eq = ≡→~-IsEquiv f g eq .proj₂


  funext-unique : ∀ eq (p : f ≡ g)
    → ≡→~ p ≡ eq
    → funext eq ≡ p
  funext-unique eq p q = proj₁ (Σ-≡⁻ (funext-unique′ eq (p , q)))


  funext∘≡→~ : ∀ (eq : f ≡ g)
    → funext (≡→~ eq) ≡ eq
  funext∘≡→~ eq = funext-unique (≡→~ eq) eq refl


subst-funext : ∀ {α β γ} {A : Set α} {B : A → Set β} {f g : ∀ a → B a}
  → (P : ∀ a → B a → Set γ)
  → (f≡g : ∀ x → f x ≡ g x)
  → ∀ {a} (Pf : P a (f a))
  → subst (λ f → P a (f a)) (funext f≡g) Pf ≡ subst (P a) (f≡g a) Pf
subst-funext P f≡g {a} Pf = sym
  (trans
    (cong (λ p → subst (P a) (p a) Pf) (sym (≡→~∘funext f≡g)))
    go)
  where
    go : subst (P a) (≡→~ (funext f≡g) a) Pf
        ≡ subst (λ f → P a (f a)) (funext f≡g) Pf
    go with funext f≡g
    ... | refl = refl
