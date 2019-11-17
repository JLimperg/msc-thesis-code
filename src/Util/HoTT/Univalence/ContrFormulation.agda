-- This module closely follows a section of Martín Escardó's HoTT lecture notes:
-- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#unicharac
{-# OPTIONS --without-K #-}
module Util.HoTT.Univalence.ContrFormulation where

open import Util.Data.Product using (map₂)
open import Util.Prelude
open import Util.HoTT.Equiv
open import Util.HoTT.HLevel
open import Util.HoTT.Singleton
open import Util.HoTT.Univalence.Axiom
open import Util.HoTT.Univalence.Statement


private
  variable
    α β γ : Level


UnivalenceContr : ∀ α → Set (lsuc α)
UnivalenceContr α = (A : Set α) → IsContr (Σ[ B ∈ Set α ] (A ≃ B))


UnivalenceProp : ∀ α → Set (lsuc α)
UnivalenceProp α = (A : Set α) → IsProp (Σ[ B ∈ Set α ] (A ≃ B))


abstract
  IsEquiv→Σ-IsContr : {A : Set α} {B : A → Set β} (x : A)
    → (f : ∀ y → x ≡ y → B y)
    → (∀ y → IsEquiv (f y))
    → IsContr (Σ A B)
  IsEquiv→Σ-IsContr {A = A} {B = B} x f f-equiv
    = ≃-pres-IsContr Singleton≃ΣB IsContr-Singleton′
    where
      ≡≃B : ∀ y → (x ≡ y) ≃ B y
      ≡≃B y .forth = f y
      ≡≃B y .isEquiv = f-equiv y

      Singleton≃ΣB : Singleton′ x ≃ Σ A B
      Singleton≃ΣB = Σ-≃⁺ ≡≃B


  Σ-IsContr→IsEquiv : {A : Set α} {B : A → Set β} (x : A)
    → (f : ∀ y → x ≡ y → B y)
    → IsContr (Σ A B)
    → ∀ y → IsEquiv (f y)
  Σ-IsContr→IsEquiv {A = A} {B = B} x f Σ-contr
    = IsEquiv-map₂-f→IsEquiv-f f f-equiv
    where
      f-equiv : IsEquiv (map₂ f)
      f-equiv = IsContr→IsEquiv IsContr-Singleton′ Σ-contr (map₂ f)


  Univalence→UnivalenceContr : Univalence α → UnivalenceContr α
  Univalence→UnivalenceContr ua A = IsEquiv→Σ-IsContr A (λ B → ≡→≃) (λ B → ua)


  UnivalenceContr→Univalence : UnivalenceContr α → Univalence α
  UnivalenceContr→Univalence ua {A} {B}
    = Σ-IsContr→IsEquiv A (λ B → ≡→≃) (ua A) B


  univalenceContr : (A : Set α) → IsContr (Σ[ B ∈ Set α ] (A ≃ B))
  univalenceContr = Univalence→UnivalenceContr univalence


  UnivalenceContr→UnivalenceProp : UnivalenceContr α → UnivalenceProp α
  UnivalenceContr→UnivalenceProp ua = IsContr→IsProp ∘ ua


  UnivalenceProp→UnivalenceContr : UnivalenceProp α → UnivalenceContr α
  UnivalenceProp→UnivalenceContr ua A
    = IsProp∧Pointed→IsContr (ua A) (A , ≃-refl)


  Univalence→UnivalenceProp : Univalence α → UnivalenceProp α
  Univalence→UnivalenceProp
    = UnivalenceContr→UnivalenceProp ∘ Univalence→UnivalenceContr


  UnivalenceProp→Univalence : UnivalenceProp α → Univalence α
  UnivalenceProp→Univalence
    = UnivalenceContr→Univalence ∘ UnivalenceProp→UnivalenceContr


  univalenceProp : ∀ {α} → UnivalenceProp α
  univalenceProp = Univalence→UnivalenceProp univalence
