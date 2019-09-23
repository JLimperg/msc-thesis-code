{-# OPTIONS --without-K --safe #-}
module Source.Reduction where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b
  ; n′ ; m′ ; o′ ; b′ ; v0 ; v1 )
open import Source.Size.Substitution.Universe as SU using
  ( sub-syntax-Size )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; W ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; sub-syntax-Ctx
  ; sub-syntax-Type )
open import Source.Term
open import Util.Prelude hiding (id ; _∘_)

import Source.Size.Substitution.Canonical as SC

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
    → Δ , Γ ⊢ (Λ T , t) · u ⟶ t [ Fill u ⊢u ]t ∶ U
  appₛ-absₛ
    : ∀ n {T : Type (Δ ∙ n)} t m
    → Δ ∙ n , Γ [ SU.Wk ]Γ ⊢ t ∶ T
    → (m<n : m < n)
    → Δ , Γ ⊢ (Λₛ n , t) ·ₛ m ⟶ t [ SU.Fill m m<n ]tₛ ∶ T [ SU.Fill m m<n ]T
  caseNat-zero
    : ∀ T n z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
    → n < ⋆
    → Δ , Γ ⊢ caseNat T n (zero n) z s ⟶ z ∶ T
  caseNat-suc
    : ∀ T n m i z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
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
    → Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , T [ SU.Skip ]T) ⇒ T
    → (n<⋆ : n < ⋆)
    → Δ , Γ ⊢
        fix T t n
        ⟶ t ·ₛ n · (Λₛ n , fix (T [ SU.Keep′ SU.Wk ]T) (t [ SU.Wk ]tₛ) v0)
        ∶ T [ SU.Fill n n<⋆ ]T
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
    → Δ ∙ n , Γ [ SU.Wk ]Γ ⊢ t ⟶ t′ ∶ T
    → Δ , Γ ⊢ Λₛ n , t ⟶ Λₛ n , t′ ∶ Π n , T
  cong-appₛ
    : Δ , Γ ⊢ t ⟶ t′ ∶ Π n , T
    → (m<n : m < n)
    → Δ , Γ ⊢ t ·ₛ m ⟶ t′ ·ₛ m ∶ T [ SU.Fill m m<n ]T
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
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i′ z s ∶ T
  cong-caseNat₁
    : ∀ T n i z z′ s
    → n < ⋆
    → Δ , Γ ⊢ i ∶ Nat n
    → Δ , Γ ⊢ z ⟶ z′ ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i z′ s ∶ T
  cong-caseNat₂
    : ∀ T n i z s s′
    → n < ⋆
    → Δ , Γ ⊢ i ∶ Nat n
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ⟶ s′ ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
    → Δ , Γ ⊢ caseNat T n i z s ⟶ caseNat T n i z s′ ∶ T
  cong-fix
    : ∀ T t t′ n
    → (n<⋆ : n < ⋆)
    → Δ , Γ ⊢ t ⟶ t′ ∶ Π ⋆ , (Π v0 , T [ SU.Skip ]T) ⇒ T
    → Δ , Γ ⊢ fix T t n ⟶ fix T t′ n ∶ T [ SU.Fill n n<⋆ ]T


⟶→⊢ₗ : Δ , Γ ⊢ t ⟶ u ∶ T → Δ , Γ ⊢ t ∶ T
⟶→⊢ₗ (app-abs t u ⊢t ⊢u) = app _ _ (abs _ _ ⊢t) ⊢u
⟶→⊢ₗ (appₛ-absₛ n t m ⊢t m<n) = appₛ _ _ m<n (absₛ _ _ _ ⊢t refl) refl
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-zero T n z s ⊢z ⊢s n<⋆) = caseNat n<⋆ (zero n<⋆) ⊢z ⊢s refl
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = caseNat n<⋆ (suc n<⋆ m<n ⊢i) ⊢z ⊢s refl
⟶→⊢ₗ {Δ = Δ} {Γ} (head-cons n i is ⊢i ⊢is n<⋆)
  = head n<⋆ (cons n<⋆ ⊢i ⊢is)
⟶→⊢ₗ (tail-cons n i is m ⊢i ⊢is n<⋆ m<n)
  = tail n<⋆ m<n (cons n<⋆ ⊢i ⊢is)
⟶→⊢ₗ (fix T t n ⊢t n<⋆)
  = fix n<⋆ ⊢t refl refl
⟶→⊢ₗ (cong-abs T t t′ t→t′) = abs _ _ (⟶→⊢ₗ t→t′)
⟶→⊢ₗ (cong-appₗ t t′ u t→t′ ⊢u) = app _ _ (⟶→⊢ₗ t→t′) ⊢u
⟶→⊢ₗ (cong-appᵣ t u u′ ⊢t u→u′) = app _ _ ⊢t (⟶→⊢ₗ u→u′)
⟶→⊢ₗ (cong-absₛ n t t′ t→t′) = absₛ _ _ _ (⟶→⊢ₗ t→t′) refl
⟶→⊢ₗ (cong-appₛ t→t′ m<n) = appₛ _ _ m<n (⟶→⊢ₗ t→t′) refl
⟶→⊢ₗ (cong-suc n m i i′ n<⋆ m<n i→i′) = suc n<⋆ m<n (⟶→⊢ₗ i→i′)
⟶→⊢ₗ (cong-cons₀ n i i′ is n<⋆ i→i′ ⊢is) = cons n<⋆ (⟶→⊢ₗ i→i′) ⊢is
⟶→⊢ₗ (cong-cons₁ n i is is′ n<⋆ ⊢i is→is′) = cons n<⋆ ⊢i (⟶→⊢ₗ is→is′)
⟶→⊢ₗ (cong-head n is is′ n<⋆ is→is′) = head n<⋆ (⟶→⊢ₗ is→is′)
⟶→⊢ₗ (cong-tail n m is is′ n<⋆ m<n is→is′) = tail n<⋆ m<n (⟶→⊢ₗ is→is′)
⟶→⊢ₗ (cong-caseNat₀ T n i i′ z s n<⋆ i→i′ ⊢z ⊢s)
  = caseNat n<⋆ (⟶→⊢ₗ i→i′) ⊢z ⊢s refl
⟶→⊢ₗ (cong-caseNat₁ T n i z z′ s n<⋆ ⊢i z→z′ ⊢s)
  = caseNat n<⋆ ⊢i (⟶→⊢ₗ z→z′) ⊢s refl
⟶→⊢ₗ (cong-caseNat₂ T n i z s s′ n<⋆ ⊢i ⊢z s→s′)
  = caseNat n<⋆ ⊢i ⊢z (⟶→⊢ₗ s→s′) refl
⟶→⊢ₗ (cong-fix T t t′ n n<⋆ t→t′)
  = fix n<⋆ (⟶→⊢ₗ t→t′) refl refl


⟶→⊢ᵣ : Δ , Γ ⊢ t ⟶ u ∶ T → Δ , Γ ⊢ u ∶ T
⟶→⊢ᵣ (app-abs t u ⊢t ⊢u) = sub-resp-⊢ (Fill _ ⊢u) ⊢t
⟶→⊢ᵣ {Δ} {Γ} (appₛ-absₛ n {T} t m ⊢t m<n)
  = cast⊢Γ eq (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t)
  module ⟶→⊢ᵣ where
    abstract
      eq : T.subΓ (SU.Fill m m<n) (T.subΓ SU.Wk Γ) ≡ Γ
      eq = trans (sym (T.subΓ->> Γ SU.≈-refl))
        (T.subΓ-Id Γ (SU.≈⁺ (SC.Fill>>Wk _ _ _)))
⟶→⊢ᵣ (caseNat-zero T n z s ⊢z ⊢s n<⋆) = ⊢z
⟶→⊢ᵣ {Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = app _ _ (appₛ _ _ m<n ⊢s eq) ⊢i
  module ⟶→⊢ᵣ-caseNat-suc where
    eq : (Nat m ⇒ T) ≡ (Nat m ⇒ T.sub (SU.Fill m m<n) (T.sub SU.Wk T))
    eq = cong (Nat m ⇒_)
      (sym (trans (sym (T.sub->> T SU.≈-refl))
        (T.sub-Id T (SU.≈⁺ (SC.Fill>>Wk _ _ _)))))
⟶→⊢ᵣ (head-cons n i is ⊢i ⊢is n<⋆) = ⊢i
⟶→⊢ᵣ (tail-cons n i is m ⊢i ⊢is n<⋆ m<n) = appₛ is m m<n ⊢is refl
⟶→⊢ᵣ {Δ} {Γ} (fix T t n ⊢t n<⋆)
  = app _ _ (appₛ t n n<⋆ ⊢t refl)
      (absₛ n _ _
        (fix (S.var _ refl (S.<→≤ (S.wk-resp-< n<⋆)))
          (subₛ-resp-⊢ SU.Wk ⊢t) eq₀ eq₁)
        refl)
  module ⟶→⊢ᵣ-fix where
    abstract
      eq₀
        : T [ SU.Skip ]T [ SU.Keep′ (SU.Keep′ (SU.Wk {n = n})) ]T
        ≡ T [ SU.Keep′ SU.Wk ]T [ SU.Skip ]T
      eq₀ = T.sub->>′ (SU.≈⁺ (sym SC.Skip>>Keep′)) T

      eq₁
        : T [ SU.Skip ]T [ SU.Keep′ (SU.Fill n n<⋆) ]T
        ≡ T [ SU.Keep′ SU.Wk ]T [ SU.Fill v0 (S.var _ refl (S.<→≤ (S.wk-resp-< n<⋆))) ]T
      eq₁ = T.sub->>′ (SU.≈⁺ SC.Keep′Fill>>Skip) T
⟶→⊢ᵣ (cong-abs T t t′ t→t′) = abs _ _ (⟶→⊢ᵣ t→t′)
⟶→⊢ᵣ (cong-appₗ t t′ u t→t′ ⊢u) = app _ _ (⟶→⊢ᵣ t→t′) ⊢u
⟶→⊢ᵣ (cong-appᵣ t u u′ ⊢t u→u′) = app _ _ ⊢t (⟶→⊢ᵣ u→u′)
⟶→⊢ᵣ (cong-absₛ n t t′ t→t′) = absₛ _ _ _ (⟶→⊢ᵣ t→t′) refl
⟶→⊢ᵣ (cong-appₛ t→t′ m<n) = appₛ _ _ m<n (⟶→⊢ᵣ t→t′) refl
⟶→⊢ᵣ (cong-suc n m i i′ n<⋆ m<n i→i′) = suc n<⋆ m<n (⟶→⊢ᵣ i→i′)
⟶→⊢ᵣ (cong-cons₀ n i i′ is n<⋆ i→i′ ⊢is) = cons n<⋆ (⟶→⊢ᵣ i→i′) ⊢is
⟶→⊢ᵣ (cong-cons₁ n i is is′ n<⋆ ⊢i is→is′) = cons n<⋆ ⊢i (⟶→⊢ᵣ is→is′)
⟶→⊢ᵣ (cong-head n is is′ n<⋆ is→is′) = head n<⋆ (⟶→⊢ᵣ is→is′)
⟶→⊢ᵣ (cong-tail n m is is′ n<⋆ m<n is→is′) = tail n<⋆ m<n (⟶→⊢ᵣ is→is′)
⟶→⊢ᵣ (cong-caseNat₀ T n i i′ z s n<⋆ i→i′ ⊢z ⊢s)
  = caseNat n<⋆ (⟶→⊢ᵣ i→i′) ⊢z ⊢s refl
⟶→⊢ᵣ (cong-caseNat₁ T n i z z′ s n<⋆ ⊢i z→z′ ⊢s)
  = caseNat n<⋆ ⊢i (⟶→⊢ᵣ z→z′) ⊢s refl
⟶→⊢ᵣ (cong-caseNat₂ T n i z s s′ n<⋆ ⊢i ⊢z s→s′)
  = caseNat n<⋆ ⊢i ⊢z (⟶→⊢ᵣ s→s′) refl
⟶→⊢ᵣ (cong-fix T t t′ n n<⋆ t→t′)
  = fix n<⋆ (⟶→⊢ᵣ t→t′) refl refl


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
