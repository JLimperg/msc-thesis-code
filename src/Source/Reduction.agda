{-# OPTIONS --without-K --safe #-}
module Source.Reduction where

open import Source.Size as S using
  ( Size ; _<_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b
  ; n′ ; m′ ; o′ ; b′ ; v0 ; v1 )
open import Source.Size.Substitution.Theory
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; W ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ )
open import Source.Term
open import Util.Prelude hiding (id ; _∘_)

import Source.Size.Substitution.Canonical as SC
import Source.Size.Substitution.Universe as SU

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type


infix 0 _,_⊢_⟶_∶_ _,_⊢_=β_∶_


data _,_⊢_⟶_∶_ Δ (Γ : Ctx Δ) : (t u : Term Δ) (T : Type Δ) → Set where
  app-abs
    : ∀ t u
    → Δ , Γ ∙ T ⊢ t ∶ U
    → (⊢u : Δ , Γ ⊢ u ∶ T)
    → Δ , Γ ⊢ (Λ T , t) · u ⟶ t [ Fill Γ T u ]t ∶ U
  appₛ-absₛ
    : ∀ n {T : Type (Δ ∙ n)} t m
    → Δ ∙ n , Γ [ SC.Wk ] ⊢ t ∶ T
    → (m<n : m < n)
    → Δ , Γ ⊢ (Λₛ n , t) ·ₛ m ⟶ t [ SC.Fill m ]ₛ ∶ T [ SC.Fill m ]
  caseNat-zero
    : ∀ T n z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SC.Wk ]
    → n < ⋆
    → Δ , Γ ⊢ caseNat T n (zero n) z s ⟶ z ∶ T
  caseNat-suc
    : ∀ T n m i z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SC.Wk ]
    → Δ , Γ ⊢ i ∶ Nat m
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ caseNat T n (suc n m i) z s ⟶ s ·ₛ m · i ∶ T
  head-cons
    : ∀ n i is
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → n < ⋆
    → Δ , Γ ⊢ head n (cons i n is) ⟶ i ∶ Nat ∞
  tail-cons
    : ∀ n i is m
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ tail n (cons i n is) m ⟶ is ·ₛ m ∶ Stream m
  fix
    : ∀ (T : Type (Δ ∙ ⋆)) t n
    → Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , T [ SC.Skip ]) ⇒ T
    → (n<⋆ : n < ⋆)
    → Δ , Γ
        ⊢ fix T t n
        ⟶ t ·ₛ n · (Λₛ n , fix (T [ SC.Lift SC.Wk ]) (t [ SC.Wk ]ₛ) v0)
        ∶ T [ SC.Fill n ]
  cong-abs
    : ∀ T t t′
    → Δ , Γ ∙ T ⊢ t ⟶ t′ ∶ U
    → Δ , Γ ⊢ Λ T , t ⟶ Λ T , t′ ∶ T ⇒ U
  cong-appₗ
    : ∀ t t′ u
    → Δ , Γ ⊢ t ⟶ t′ ∶ T ⇒ U
    → Δ , Γ ⊢ u ∶ T
    → Δ , Γ ⊢ t · u ⟶ t′ · u ∶ U
  cong-appᵣ
    : ∀ t u u′
    → Δ , Γ ⊢ t ∶ T ⇒ U
    → Δ , Γ ⊢ u ⟶ u′ ∶ T
    → Δ , Γ ⊢ t · u ⟶ t · u′ ∶ U
  cong-absₛ
    : ∀ n {T : Type (Δ ∙ n)} t t′
    → Δ ∙ n , Γ [ SC.Wk ] ⊢ t ⟶ t′ ∶ T
    → Δ , Γ ⊢ Λₛ n , t ⟶ Λₛ n , t′ ∶ Π n , T
  cong-appₛ
    : Δ , Γ ⊢ t ⟶ t′ ∶ Π n , T
    → (m<n : m < n)
    → Δ , Γ ⊢ t ·ₛ m ⟶ t′ ·ₛ m ∶ T [ SC.Fill m ]
  cong-suc
    : ∀ n m i i′
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ i ⟶ i′ ∶ Nat m
    → Δ , Γ ⊢ suc n m i ⟶ suc n m i′ ∶ Nat n
  cong-cons₀
    : ∀ n i i′ is
    → n < ⋆
    → Δ , Γ ⊢ i ⟶ i′ ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → Δ , Γ ⊢ cons i n is ⟶ cons i′ n is ∶ Stream n
  cong-cons₁
    : ∀ n i is is′
    → n < ⋆
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ⟶ is′ ∶ Π n , Stream v0
    → Δ , Γ ⊢ cons i n is ⟶ cons i n is′ ∶ Stream n
  cong-head
    : ∀ n is is′
    → n < ⋆
    → Δ , Γ ⊢ is ⟶ is′ ∶ Stream n
    → Δ , Γ ⊢ head n is ⟶ head n is′ ∶ Nat ∞
  cong-tail
    : ∀ n m is is′
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ is ⟶ is′ ∶ Stream n
    → Δ , Γ ⊢ tail n is m ⟶ tail n is′ m ∶ Stream m
  cong-caseNat₀
    : ∀ T n i i′ z s
    → n < ⋆
    → Δ , Γ ⊢ i ⟶ i′ ∶ Nat n
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SC.Wk ]
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i′ z s ∶ T
  cong-caseNat₁
    : ∀ T n i z z′ s
    → n < ⋆
    → Δ , Γ ⊢ i ∶ Nat n
    → Δ , Γ ⊢ z ⟶ z′ ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SC.Wk ]
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i z′ s ∶ T
  cong-caseNat₂
    : ∀ T n i z s s′
    → n < ⋆
    → Δ , Γ ⊢ i ∶ Nat n
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ⟶ s′ ∶ Π n , Nat v0 ⇒ T [ SC.Wk ]
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i z s′ ∶ T
  cong-fix
    : ∀ T t t′ n
    → (n<⋆ : n < ⋆)
    → Δ , Γ ⊢ t ⟶ t′ ∶ Π ⋆ , (Π v0 , T [ SC.Skip ]) ⇒ T
    → Δ , Γ ⊢ fix T t n ⟶ fix T t′ n ∶ T [ SC.Fill n ]


data _,_⊢_=β_∶_ Δ (Γ : Ctx Δ) (t u : Term Δ) (T : Type Δ) : Set where
  step
    : Δ , Γ ⊢ t ⟶ u ∶ T
    → Δ , Γ ⊢ t =β u ∶ T
  reflexive
    : t ≡ u
    → Δ , Γ ⊢ t ∶ T
    → Δ , Γ ⊢ t =β u ∶ T
  symmetric
    : Δ , Γ ⊢ u =β t ∶ T
    → Δ , Γ ⊢ t =β u ∶ T
  transitive
    : Δ , Γ ⊢ t =β v ∶ T
    → Δ , Γ ⊢ v =β u ∶ T
    → Δ , Γ ⊢ t =β u ∶ T


pattern =β-refl = reflexive refl
