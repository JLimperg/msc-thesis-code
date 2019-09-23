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
    → Δ , Γ ⊢ caseNat T ·ₛ n · (zero ·ₛ n) · z · s ⟶ z ∶ T
  caseNat-suc
    : ∀ T n m i z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ SU.Wk ]T
    → Δ , Γ ⊢ i ∶ Nat m
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ caseNat T ·ₛ n · (suc ·ₛ n ·ₛ m · i) · z · s ⟶ s ·ₛ m · i ∶ T
  head-cons
    : ∀ n i is
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → n < ⋆
    → Δ , Γ ⊢ head ·ₛ n · (cons ·ₛ n · i · is) ⟶ i ∶ Nat ∞
  tail-cons
    : ∀ n i is m
    → Δ , Γ ⊢ i ∶ Nat ∞
    → Δ , Γ ⊢ is ∶ Π n , Stream v0
    → n < ⋆
    → m < n
    → Δ , Γ ⊢ tail ·ₛ n · (cons ·ₛ n · i · is) ⟶ is ∶ Π n , Stream v0
  fix
    : ∀ (T : Type (Δ ∙ ⋆)) t n
    → Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , T [ SU.Skip ]T) ⇒ T
    → (n<⋆ : n < ⋆)
    → Δ , Γ ⊢
        fix T · t ·ₛ n
        ⟶ t ·ₛ n · (Λₛ n , fix (T [ SU.Keep′ SU.Wk ]T) · (t [ SU.Wk ]tₛ) ·ₛ v0)
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


⟶→⊢ₗ : Δ , Γ ⊢ t ⟶ u ∶ T → Δ , Γ ⊢ t ∶ T
⟶→⊢ₗ (app-abs t u ⊢t ⊢u) = app _ _ (abs _ _ ⊢t) ⊢u
⟶→⊢ₗ (appₛ-absₛ n t m ⊢t m<n) = appₛ _ _ m<n (absₛ _ _ _ ⊢t)
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-zero T n z s ⊢z ⊢s n<⋆)
  = app _ _ (app _ _ (app _ _
      (subst (λ U → Δ , Γ ⊢ caseNat T ·ₛ n ∶ Nat n ⇒ U)
        (cong₂ _⇒_
          (trans (sym (T.sub->> T SU.≈-refl))
            (T.sub-Id T (SU.≈⁺ (SC.Fill>>Wk _ _ _))))
          (cong₂ (λ U V → (Π n , Nat v0 ⇒ U) ⇒ V)
            (sym (T.sub->> T (SU.≈⁺ (sym SC.Keep′Fill>>Wk>>Wk))))
            (trans (sym (T.sub->> T SU.≈-refl)) (T.sub-Id T (SU.≈⁺ (SC.Fill>>Wk _ _ _))))
            ))
        (appₛ _ _ n<⋆ (caseNat T)))
      (appₛ _ _ n<⋆ zero)) ⊢z) ⊢s
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = app _ _ (app _ _ (app _ _
      (subst (λ U → Δ , Γ ⊢ caseNat T ·ₛ n ∶ U) go₄ (appₛ _ _ n<⋆ (caseNat T)))
      (app _ _ (appₛ _ _ m<n (appₛ _ _ n<⋆ suc)) ⊢i))
      ⊢z) ⊢s
  where
    go₁ : T [ SU.Wk ]T [ SU.Fill n n<⋆ ]T ≡ T
    go₁ = trans (sym (T.sub->> T SU.≈-refl)) (T.sub-Id T (SU.≈⁺ (SC.Fill>>Wk _ _ _)))

    go₂ : T [ SU.Wk SU.>> SU.Wk ]T [ SU.Keep′ {n = v0} (SU.Fill n n<⋆) ]T ≡ T [ SU.Wk ]T
    go₂ = trans (sym (T.sub->> T SU.≈-refl)) (T.sub-resp-≈ (SU.≈⁺ SC.Keep′Fill>>Wk>>Wk) T)

    go₃ : S.wk n [ SU.Fill m m<n ]n ≡ n
    go₃
      = trans (cong (SU.sub (SU.Fill m m<n)) (sym (SC.sub-Wk n)))
          (trans (sym (SC.sub->> n refl)) (SC.sub-Id n (SC.Fill>>Wk _ _ _)))

    go₄ : T.sub (SU.Fill n n<⋆)
           (Nat v0 ⇒
            T [ SU.Wk ]T ⇒
            (Π v0 , Nat v0 ⇒ T [ SU.Wk SU.>> SU.Wk ]T) ⇒
            T [ SU.Wk ]T)
           ≡
           (T.sub (SU.Fill m m<n) (T.sub (SU.Keep′ {n = v0} (SU.Fill n n<⋆)) (Nat v1))
            ⇒ T ⇒ (Π n , Nat v0 ⇒ T [ SU.Wk ]T) ⇒ T)
    go₄ rewrite go₁ | go₂ | go₃ = refl
⟶→⊢ₗ {Δ = Δ} {Γ} (head-cons n i is ⊢i ⊢is n<⋆)
  = app _ _ (appₛ _ _ n<⋆ head) (app _ _ (app _ _ (appₛ _ _ n<⋆ cons) ⊢i) ⊢is)
⟶→⊢ₗ (tail-cons n i is m ⊢i ⊢is n<⋆ m<n)
  = app _ _ (appₛ _ _ n<⋆ tail) (app _ _ (app _ _ (appₛ _ _ n<⋆ cons) ⊢i) ⊢is)
⟶→⊢ₗ (fix T t n ⊢t n<⋆) = appₛ _ _ n<⋆ (app _ _ (fix T ) ⊢t)
⟶→⊢ₗ (cong-abs T t t′ t→t′) = abs _ _ (⟶→⊢ₗ t→t′)
⟶→⊢ₗ (cong-appₗ t t′ u t→t′ ⊢u) = app _ _ (⟶→⊢ₗ t→t′) ⊢u
⟶→⊢ₗ (cong-appᵣ t u u′ ⊢t u→u′) = app _ _ ⊢t (⟶→⊢ₗ u→u′)
⟶→⊢ₗ (cong-absₛ n t t′ t→t′) = absₛ _ _ _ (⟶→⊢ₗ t→t′)
⟶→⊢ₗ (cong-appₛ t→t′ m<n) = appₛ _ _ m<n (⟶→⊢ₗ t→t′)


⟶→⊢ᵣ : Δ , Γ ⊢ t ⟶ u ∶ T → Δ , Γ ⊢ u ∶ T
⟶→⊢ᵣ (app-abs t u ⊢t ⊢u) = sub-resp-⊢ (Fill _ ⊢u) ⊢t
⟶→⊢ᵣ {Δ} {Γ} {T = T} (appₛ-absₛ n t m ⊢t m<n)
  = subst (λ Ψ → Δ , Ψ ⊢ t [ SU.Fill m m<n ]tₛ ∶ _)
      (trans (sym (T.subΓ->> Γ SU.≈-refl)) (T.subΓ-Id Γ (SU.≈⁺ (SC.Fill>>Wk _ _ _))))
      (subₛ-resp-⊢ (SU.Fill m m<n) ⊢t)
⟶→⊢ᵣ (caseNat-zero T n z s ⊢z ⊢s n<⋆) = ⊢z
⟶→⊢ᵣ {Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = app _ _
      (subst (λ U → Δ , Γ ⊢ s ·ₛ m ∶ Nat m ⇒ U)
        (trans (sym (T.sub->> T SU.≈-refl)) (T.sub-Id T (SU.≈⁺ (SC.Fill>>Wk _ _ _))))
        (appₛ _ _ m<n ⊢s))
      ⊢i
⟶→⊢ᵣ (head-cons n i is ⊢i ⊢is n<⋆) = ⊢i
⟶→⊢ᵣ (tail-cons n i is m ⊢i ⊢is n<⋆ m<n) = ⊢is
⟶→⊢ᵣ {Δ} {Γ} (fix T t n ⊢t n<⋆)
  = app _ _ (appₛ _ _ n<⋆ ⊢t)
      (absₛ _ _ _ (subst (λ U → Δ ∙ n , Γ [ SU.Wk ]Γ ⊢ fix (T [ SU.Keep′ SU.Wk ]T) · (t [ SU.Wk ]tₛ) ·ₛ v0 ∶ U)
      (T.sub->>′ (SU.≈⁺ (sym SC.Keep′Fill>>Skip)) T)
      (appₛ _ _ (S.var _ refl (S.<→≤ (S.wk-resp-< n<⋆)))
        (app _ _ (fix _)
          (subst (λ U → Δ ∙ n , Γ [ SU.Wk ]Γ ⊢ t [ SU.Wk ]tₛ
            ∶ Π ⋆ , (Π v0 , U) ⇒ T [ SU.Keep′ SU.Wk ]T)
            (T.sub->>′ (SU.≈⁺ (sym SC.Skip>>Keep′)) T)
            (subₛ-resp-⊢ SU.Wk ⊢t))))))
⟶→⊢ᵣ (cong-abs T t t′ t→t′) = abs _ _ (⟶→⊢ᵣ t→t′)
⟶→⊢ᵣ (cong-appₗ t t′ u t→t′ ⊢u) = app _ _ (⟶→⊢ᵣ t→t′) ⊢u
⟶→⊢ᵣ (cong-appᵣ t u u′ ⊢t u→u′) = app _ _ ⊢t (⟶→⊢ᵣ u→u′)
⟶→⊢ᵣ (cong-absₛ n t t′ t→t′) = absₛ _ _ _ (⟶→⊢ᵣ t→t′)
⟶→⊢ᵣ (cong-appₛ t→t′ m<n) = appₛ _ _ m<n (⟶→⊢ᵣ t→t′)


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
