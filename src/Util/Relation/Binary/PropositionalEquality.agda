{-# OPTIONS --without-K --safe #-}
module Util.Relation.Binary.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

open import Data.Product using (uncurry)

open import Util.Prelude


private
  variable
    α β γ γ′ δ : Level
    A B C A′ B′ C′ : Set α


happly = cong-app


trans-unassoc : {a b c d : A} (p : a ≡ b) {q : b ≡ c} {r : c ≡ d}
  → trans p (trans q r) ≡ trans (trans p q) r
trans-unassoc p = sym (trans-assoc p)


Σ-≡⁻ : {A : Set α} {B : A → Set β} {x y : Σ A B}
  → x ≡ y
  → Σ[ p ∈ (proj₁ x ≡ proj₁ y) ] subst B p (proj₂ x) ≡ proj₂ y
Σ-≡⁻ refl = refl , refl


Σ-≡⁺ : {A : Set α} {B : A → Set β} {x y : Σ A B}
  → Σ[ p ∈ (proj₁ x ≡ proj₁ y) ] subst B p (proj₂ x) ≡ proj₂ y
  → x ≡ y
Σ-≡⁺ (refl , refl) = refl


Σ-≡⁺∘Σ-≡⁻ : {A : Set α} {B : A → Set β} {x y : Σ A B}
  → (p : x ≡ y)
  → Σ-≡⁺ (Σ-≡⁻ p) ≡ p
Σ-≡⁺∘Σ-≡⁻ refl = refl


Σ-≡⁻∘Σ-≡⁺ : {A : Set α} {B : A → Set β} {x y : Σ A B}
  → (p : Σ[ p ∈ (proj₁ x ≡ proj₁ y) ] subst B p (proj₂ x) ≡ proj₂ y)
  → Σ-≡⁻ (Σ-≡⁺ p) ≡ p
Σ-≡⁻∘Σ-≡⁺ (refl , refl) = refl


cast : A ≡ B → A → B
cast = subst (λ x → x)


cast-refl : {x : A} → cast refl x ≡ x
cast-refl = refl


cast-trans : (B≡C : B ≡ C) (A≡B : A ≡ B) {x : A}
  → cast B≡C (cast A≡B x) ≡ cast (trans A≡B B≡C) x
cast-trans refl refl = refl


subst-trans : ∀ {P : A → Set β} {x y z : A} {p : P x}
  → (x≡y : x ≡ y) (y≡z : y ≡ z)
  → subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
subst-trans refl refl = refl


-- TODO remove
sym-cancel-r : {x y : A} (x≡y : x ≡ y)
  → trans x≡y (sym x≡y) ≡ refl
sym-cancel-r = trans-symʳ


-- TODO remove
sym-cancel-l : {x y : A} (x≡y : x ≡ y)
  → trans (sym x≡y) x≡y ≡ refl
sym-cancel-l = trans-symˡ


subst₂-trans : (C : A → B → Set γ)
  → {a₀ a₁ a₂ : A} (p : a₀ ≡ a₁) (p′ : a₁ ≡ a₂)
  → {b₀ b₁ b₂ : B} (q : b₀ ≡ b₁) (q′ : b₁ ≡ b₂)
  → {x : C a₀ b₀}
  → subst₂ C p′ q′ (subst₂ C p q x) ≡ subst₂ C (trans p p′) (trans q q′) x
subst₂-trans C refl refl refl refl = refl


subst₂-subst₂-sym : (C : A → B → Set γ)
  → {a a′ : A} (p : a ≡ a′)
  → {b b′ : B} (q : b ≡ b′)
  → {x : C a′ b′}
  → subst₂ C p q (subst₂ C (sym p) (sym q) x) ≡ x
subst₂-subst₂-sym C refl refl = refl


subst₂-sym-subst₂ : (C : A → B → Set γ)
  → {a a′ : A} (p : a ≡ a′)
  → {b b′ : B} (q : b ≡ b′)
  → {x : C a b}
  → subst₂ C (sym p) (sym q) (subst₂ C p q x) ≡ x
subst₂-sym-subst₂ C refl refl = refl


subst₂-cong : (C : A′ → B′ → Set γ)
  → (f : A → A′) (g : B → B′)
  → {a a′ : A} (p : a ≡ a′)
  → {b b′ : B} (q : b ≡ b′)
  → {x : C (f a) (g b)}
  → subst₂ C (cong f p) (cong g q) x ≡ subst₂ (λ a b → C (f a) (g b)) p q x
subst₂-cong C f g refl refl = refl


subst₂≡subst : ∀ {la} {A : Set la} {lb} {B : Set lb} {lc} (C : A → B → Set lc)
  → ∀ {a a′} (p : a ≡ a′) {b b′} (q : b ≡ b′) {x : C a b}
  → subst₂ C p q x ≡ subst (uncurry C) (cong₂ _,_ p q) x
subst₂≡subst C refl refl = refl


subst₂-application : (C : A → B → Set γ) {C′ : A′ → B′ → Set γ′}
  → {fa : A′ → A} {fb : B′ → B}
  → {a a′ : A′} {b b′ : B′} {c : C (fa a) (fb b)}
  → (g : ∀ a b → C (fa a) (fb b) → C′ a b)
  → (eqa : a ≡ a′)
  → (eqb : b ≡ b′)
  → subst₂ C′ eqa eqb (g a b c)
  ≡ g a′ b′ (subst₂ C (cong fa eqa) (cong fb eqb) c)
subst₂-application _ _ refl refl = refl


subst₂-application′ : {C : A → B → Set γ} (C′ : A′ → B′ → Set γ′)
  → {fa : A → A′} {fb : B → B′}
  → {a a′ : A} {b b′ : B} {c : C a b}
  → (g : ∀ a b → C a b → C′ (fa a) (fb b))
  → (eqa : a ≡ a′)
  → (eqb : b ≡ b′)
  → subst₂ C′ (cong fa eqa) (cong fb eqb) (g a b c)
  ≡ g a′ b′ (subst₂ C eqa eqb c)
subst₂-application′ _ _ refl refl = refl


cong₂-dep : {A : Set α} {B : A → Set β} {C : Set γ}
  → (f : (a : A) → B a → C)
  → {x y : A} (p : x ≡ y)
  → {u : B x} {v : B y} (q : subst B p u ≡ v)
  → f x u ≡ f y v
cong₂-dep f refl refl = refl


cong₃-dep : {A : Set α} {B : A → Set β} {C : (a : A) → B a → Set γ}
  → {D : Set δ}
  → (f : (a : A) (b : B a) → C a b → D)
  → {x y : A} (p : x ≡ y)
  → {u : B x} {v : B y} (q : subst B p u ≡ v)
  → {w : C x u} {z : C y v} (r : subst (λ i → C (proj₁ i) (proj₂ i)) (Σ-≡⁺ (p , q)) w ≡ z)
  → f x u w ≡ f y v z
cong₃-dep f refl refl refl = refl
