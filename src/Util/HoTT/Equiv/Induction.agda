-- This module closely follows a section of Martín Escardó's HoTT lecture notes:
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#equivalenceinduction
{-# OPTIONS --without-K #-}
module Util.HoTT.Equiv.Induction where

open import Util.HoTT.HLevel
open import Util.HoTT.Equiv
open import Util.HoTT.Univalence.ContrFormulation
open import Util.Prelude


private
  variable
    α β γ : Level


G-≃ : {A : Set α} (P : Σ[ B ∈ Set α ] (A ≃ B) → Set β)
  → P (A , ≃-refl)
  → ∀ {B} (A≃B : A ≃ B)
  → P (B , A≃B)
G-≃ {A = A} P p {B} A≃B = subst P (univalenceProp A (A , ≃-refl) (B , A≃B)) p


abstract
  G-≃-β : {A : Set α} (P : Σ[ B ∈ Set α ] (A ≃ B) → Set β)
    → (p : P (A , ≃-refl))
    → G-≃ P p ≃-refl ≡ p
  G-≃-β {A = A} P p = subst (λ q → subst P q p ≡ p) (sym go) refl
    where
      go : univalenceProp A (A , ≃-refl) (A , ≃-refl) ≡ refl
      go = IsContr→IsSet (univalenceContr A) _ _


H-≃ : {A : Set α} (P : (B : Set α) → A ≃ B → Set β)
  → P A ≃-refl
  → ∀ {B} (A≃B : A ≃ B)
  → P B A≃B
H-≃ P p A≃B = G-≃ (λ { (B , A≃B) → P B A≃B }) p A≃B


abstract
  H-≃-β : {A : Set α} (P : (B : Set α) → A ≃ B → Set β)
    → (p : P A ≃-refl)
    → H-≃ P p ≃-refl ≡ p
  H-≃-β P p = G-≃-β (λ { (B , A≃B) → P B A≃B }) p


J-≃ : (P : (A B : Set α) → A ≃ B → Set β)
  → (∀ A → P A A ≃-refl)
  → ∀ {A B} (A≃B : A ≃ B)
  → P A B A≃B
J-≃ P p {A} {B} A≃B = H-≃ (λ B A≃B → P A B A≃B) (p A) A≃B


abstract
  J-≃-β : (P : (A B : Set α) → A ≃ B → Set β)
    → (p : ∀ A → P A A ≃-refl)
    → ∀ {A}
    → J-≃ P p ≃-refl ≡ p A
  J-≃-β P p {A} = H-≃-β (λ B A≃B → P A B A≃B) (p A)
