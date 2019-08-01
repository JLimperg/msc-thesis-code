module Source.Reduction where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b
  ; sub-syntax-Size ; v0 ; v1 )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; sub-syntax-Ctx
  ; sub-syntax-Type )
open import Source.Term
open import Util.Prelude hiding (id ; _∘_)

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type


infix 0 _,_⊢_⟶_∶_  _,_⊢_=β_∶_


data _,_⊢_⟶_∶_ : ∀ Δ (Γ : Ctx Δ) (t u : Term Δ) (T : Type Δ) → Set where
  app-abs
    : ∀ t u
    → Δ , Γ ∙ T ⊢ t ∶ U
    → (⊢u : Δ , Γ ⊢ u ∶ T)
    → Δ , Γ ⊢ (Λ T , t) · u ⟶ t [ Fill u ⊢u ]t ∶ U
  appₛ-absₛ
    : ∀ n {T : Type (Δ ∙ n)} t m
    → Δ ∙ n , Γ [ S.Wk ]Γ ⊢ t ∶ T
    → (m<n : m < n)
    → Δ , Γ ⊢ (Λₛ n , t) ·ₛ m ⟶ t [ S.Fill m m<n ]tₛ ∶ T [ S.Fill m m<n ]T
  caseNat-zero
    : ∀ T n z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ S.Wk ]T
    → n < ⋆
    → Δ , Γ ⊢ caseNat T ·ₛ n · (zero ·ₛ n) · z · s ⟶ z ∶ T
  caseNat-suc
    : ∀ T n m i z s
    → Δ , Γ ⊢ z ∶ T
    → Δ , Γ ⊢ s ∶ Π n , Nat v0 ⇒ T [ S.Wk ]T
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
    → Δ , Γ ⊢ t ∶ Π ⋆ , (Π v0 , T [ S.Skip ]T) ⇒ T
    → (n<⋆ : n < ⋆)
    → Δ , Γ ⊢
        fix T · t ·ₛ n
        ⟶ t ·ₛ n · (Λₛ n , fix (T [ S.Keep′ S.Wk ]T) · (t [ S.Wk ]tₛ) ·ₛ v0)
        ∶ T [ S.Fill n n<⋆ ]T
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
    → Δ ∙ n , Γ [ S.Wk ]Γ ⊢ t ⟶ t′ ∶ T
    → Δ , Γ ⊢ Λₛ n , t ⟶ Λₛ n , t′ ∶ Π n , T
  cong-appₛ
    : Δ , Γ ⊢ t ⟶ t′ ∶ Π n , T
    → (m<n : m < n)
    → Δ , Γ ⊢ t ·ₛ m ⟶ t′ ·ₛ m ∶ T [ S.Fill m m<n ]T


⟶→⊢ₗ : Δ , Γ ⊢ t ⟶ u ∶ T → Δ , Γ ⊢ t ∶ T
⟶→⊢ₗ (app-abs t u ⊢t ⊢u) = app _ _ (abs _ _ ⊢t) ⊢u
⟶→⊢ₗ (appₛ-absₛ n t m ⊢t m<n) = appₛ _ _ m<n (absₛ _ _ _ ⊢t)
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-zero T n z s ⊢z ⊢s n<⋆)
  = app _ _ (app _ _ (app _ _
      (subst (λ U → Δ , Γ ⊢ caseNat T ·ₛ n ∶ Nat n ⇒ U)
        (cong₂ _⇒_
          (trans (sym (T.sub->> T refl)) (T.sub-Id T (S.Fill>>Wk _ _ _)))
          (cong₂ (λ U V → (Π n , Nat v0 ⇒ U) ⇒ V)
            (trans (sym (T.sub->> T refl))
              (cong (λ σ → T.sub σ T) S.Keep′Fill>>Wk>>Wk))
            (trans (sym (T.sub->> T refl)) (T.sub-Id T (S.Fill>>Wk _ _ _)))
            ))
        (appₛ _ _ n<⋆ (caseNat T)))
      (appₛ _ _ n<⋆ zero)) ⊢z) ⊢s
⟶→⊢ₗ {Δ = Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = app _ _ (app _ _ (app _ _
      (subst (λ U → Δ , Γ ⊢ caseNat T ·ₛ n ∶ U) go₄ (appₛ _ _ n<⋆ (caseNat T)))
      (app _ _ (appₛ _ _ m<n (appₛ _ _ n<⋆ suc)) ⊢i))
      ⊢z) ⊢s
  where
    go₁ : T [ S.Wk ]T [ S.Fill n n<⋆ ]T ≡ T
    go₁ = trans (sym (T.sub->> T refl)) (T.sub-Id T (S.Fill>>Wk _ _ _))

    go₂ : T [ S.Wk S.>> S.Wk ]T [ S.Keep′ {n = v0} (S.Fill n n<⋆) ]T ≡ T [ S.Wk ]T
    go₂ = trans (sym (T.sub->> T refl)) (cong (λ σ → T.sub σ T) S.Keep′Fill>>Wk>>Wk)

    go₃ : S.wk n [ S.Fill m m<n ]n ≡ n
    go₃
      = trans (cong (S.sub (S.Fill m m<n)) (sym (S.sub-Wk n)))
          (trans (sym (S.sub->> n refl)) (S.sub-Id n (S.Fill>>Wk _ _ _)))

    go₄ : T.sub (S.Fill n n<⋆)
           (Nat v0 ⇒
            T [ S.Wk ]T ⇒
            (Π v0 , Nat v0 ⇒ T [ S.Wk S.>> S.Wk ]T) ⇒
            T [ S.Wk ]T)
           ≡
           (T.sub (S.Fill m m<n) (T.sub (S.Keep′ {n = v0} (S.Fill n n<⋆)) (Nat v1))
            ⇒ T ⇒ (Π n , Nat v0 ⇒ T [ S.Wk ]T) ⇒ T)
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
  = subst (λ Ψ → Δ , Ψ ⊢ t [ S.Fill m m<n ]tₛ ∶ _)
      (trans (sym (T.subΓ->> Γ refl)) (T.subΓ-Id Γ (S.Fill>>Wk _ _ _)))
      (subₛ-resp-⊢ (S.Fill m m<n) ⊢t)
⟶→⊢ᵣ (caseNat-zero T n z s ⊢z ⊢s n<⋆) = ⊢z
⟶→⊢ᵣ {Δ} {Γ} (caseNat-suc T n m i z s ⊢z ⊢s ⊢i n<⋆ m<n)
  = app _ _
      (subst (λ U → Δ , Γ ⊢ s ·ₛ m ∶ Nat m ⇒ U)
        (trans (sym (T.sub->> T refl)) (T.sub-Id T (S.Fill>>Wk _ _ _)))
        (appₛ _ _ m<n ⊢s))
      ⊢i
⟶→⊢ᵣ (head-cons n i is ⊢i ⊢is n<⋆) = ⊢i
⟶→⊢ᵣ (tail-cons n i is m ⊢i ⊢is n<⋆ m<n) = ⊢is
⟶→⊢ᵣ {Δ} {Γ} (fix T t n ⊢t n<⋆)
  = app _ _ (appₛ _ _ n<⋆ ⊢t)
      (absₛ _ _ _ (subst (λ U → Δ ∙ n , Γ [ S.Wk ]Γ ⊢ fix (T [ S.Keep′ S.Wk ]T) · (t [ S.Wk ]tₛ) ·ₛ v0 ∶ U)
      (T.sub->>′ (sym S.Keep′Fill>>Skip)
        T)
        (appₛ _ _ (S.var _ refl (S.<→≤ (S.wk-resp-< n<⋆)))
          (app _ _ (fix _)
            (subst (λ U → Δ ∙ n , Γ [ S.Wk ]Γ ⊢ t [ S.Wk ]tₛ
              ∶ Π ⋆ , (Π v0 , U) ⇒ T [ S.Keep′ S.Wk ]T)
              (T.sub->>′ (sym S.Skip>>Keep′) T)
              (subₛ-resp-⊢ S.Wk ⊢t))))))
⟶→⊢ᵣ (cong-abs T t t′ t→t′) = abs _ _ (⟶→⊢ᵣ t→t′)
⟶→⊢ᵣ (cong-appₗ t t′ u t→t′ ⊢u) = app _ _ (⟶→⊢ᵣ t→t′) ⊢u
⟶→⊢ᵣ (cong-appᵣ t u u′ ⊢t u→u′) = app _ _ ⊢t (⟶→⊢ᵣ u→u′)
⟶→⊢ᵣ (cong-absₛ n t t′ t→t′) = absₛ _ _ _ (⟶→⊢ᵣ t→t′)
⟶→⊢ᵣ (cong-appₛ t→t′ m<n) = appₛ _ _ m<n (⟶→⊢ᵣ t→t′)


data _,_⊢_=β_∶_ : ∀ Δ (Γ : Ctx Δ) (t u : Term Δ) (T : Type Δ) → Set where
  step
    : Δ , Γ ⊢ t ⟶ u ∶ T
    → Δ , Γ ⊢ t =β u ∶ T
  reflexive
    : t ≡ u
    → Δ , Γ ⊢ t ∶ T
    → Δ , Γ ⊢ t =β u ∶ T
  transitive
    : Δ , Γ ⊢ t =β u ∶ T
    → Δ , Γ ⊢ u =β v ∶ T
    → Δ , Γ ⊢ t =β v ∶ T


pattern =β-refl = reflexive refl
