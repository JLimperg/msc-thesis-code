module Source.Reduction where

open import Source.Size as S using
  ( Size ; _<_ ; _≤_ ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; b
  ; n′ ; m′ ; o′ ; b′ ; sub-syntax-Size ; v0 ; v1 )
open import Source.Type as T using
  ( Type ; Ctx ; T ; U ; V ; W ; Γ ; Γ′ ; Γ″ ; Ψ ; Ψ′ ; Ψ″ ; sub-syntax-Ctx
  ; sub-syntax-Type )
open import Source.Term
open import Util.Prelude hiding (id ; _∘_)

open Ctx
open S.Ctx
open S.Size
open S.Var
open Type


infix 0 _,_⊢_⟶_∶_  _,_⊢_=β_∶_ _/_⊢_≃_ _/_⊢_≃Γ_ _,_/_,_⊢_≃_∶_/_


data _,_⊢_⟶_∶_ Δ (Γ : Ctx Δ) : (t u : Term Δ) (T : Type Δ) → Set where
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


data _/_⊢_≃_ Δ Ω : (T : Type Δ) (U : Type Ω) → Set where
  Nat
    : Δ / Ω ⊢ Nat n ≃ Nat m
  Stream
    : Δ / Ω ⊢ Stream n ≃ Stream m
  arrow
    : Δ / Ω ⊢ T ≃ V
    → Δ / Ω ⊢ U ≃ W
    → Δ / Ω ⊢ T ⇒ U ≃ V ⇒ W
  pi
    : Δ ∙ n / Ω ∙ m ⊢ T ≃ U
    → Δ / Ω ⊢ Π n , T ≃ Π m , U


data _/_⊢_≃Γ_ Δ Ω : (Γ : Ctx Δ) (Ψ : Ctx Ω) → Set where
  []
    : Δ / Ω ⊢ [] ≃Γ []
  snoc
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ / Ω ⊢ T ≃ U
    → Δ / Ω ⊢ Γ ∙ T ≃Γ Ψ ∙ U


sub-inj-≃T
  : (σ : S.Sub Δ Δ′)
  → (τ : S.Sub Ω Ω′)
  → Δ / Ω ⊢ T [ σ ]T ≃ U [ τ ]T
  → Δ′ / Ω′ ⊢ T ≃ U
sub-inj-≃T {T = Nat n} {Nat m} σ τ x = Nat
sub-inj-≃T {T = Stream n} {Stream m} σ τ x = Stream
sub-inj-≃T {T = T ⇒ U} {V ⇒ W} σ τ (arrow x x₁)
  = arrow (sub-inj-≃T σ τ x) (sub-inj-≃T σ τ x₁)
sub-inj-≃T {T = Π n , T} {Π m , U} σ τ (pi x)
  = pi (sub-inj-≃T (S.Keep′ σ) (S.Keep′ τ) x)


sub-inj-≃Γ
  : (σ : S.Sub Δ Δ′)
  → (τ : S.Sub Ω Ω′)
  → Δ / Ω ⊢ Γ [ σ ]Γ ≃Γ Ψ [ τ ]Γ
  → Δ′ / Ω′ ⊢ Γ ≃Γ Ψ
sub-inj-≃Γ {Γ = []} {[]} σ τ x = []
sub-inj-≃Γ {Γ = Γ ∙ T} {Ψ ∙ U} σ τ (snoc x x₁)
  = snoc (sub-inj-≃Γ σ τ x) (sub-inj-≃T σ τ x₁)


sub-resp-≃T
  : (σ : S.Sub Δ Δ′)
  → (τ : S.Sub Ω Ω′)
  → Δ′ / Ω′ ⊢ T ≃ U
  → Δ / Ω ⊢ T [ σ ]T ≃ U [ τ ]T
sub-resp-≃T σ τ Nat = Nat
sub-resp-≃T σ τ Stream = Stream
sub-resp-≃T σ τ (arrow x x₁) = arrow (sub-resp-≃T σ τ x) (sub-resp-≃T σ τ x₁)
sub-resp-≃T σ τ (pi x) = pi (sub-resp-≃T (S.Keep′ σ) (S.Keep′ τ) x)


sub-resp-≃Γ
  : (σ : S.Sub Δ Δ′)
  → (τ : S.Sub Ω Ω′)
  → Δ′ / Ω′ ⊢ Γ ≃Γ Ψ
  → Δ / Ω ⊢ Γ [ σ ]Γ ≃Γ Ψ [ τ ]Γ
sub-resp-≃Γ σ τ [] = []
sub-resp-≃Γ σ τ (snoc x x₁) = snoc (sub-resp-≃Γ σ τ x) (sub-resp-≃T σ τ x₁)


data _,_/_,_⊢_≃_∶_/_ Δ (Γ : Ctx Δ) Ω (Ψ : Ctx Ω)
  : (t : Term Δ) (u : Term Ω) (T : Type Δ) (U : Type Ω) → Set
  where
  var
    : ∀ x
    → Δ , Γ ⊢ var x ∶ T
    → Ω , Ψ ⊢ var x ∶ U
    → Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ / Ω ⊢ T ≃ U
    → Δ , Γ / Ω , Ψ ⊢ var x ≃ var x ∶ T / U
  abs
    : ∀ T t U u
    → Δ , Γ ∙ T / Ω , Ψ ∙ V ⊢ t ≃ u ∶ U / W
    → Δ , Γ / Ω , Ψ ⊢ Λ T , t ≃ Λ V , u ∶ T ⇒ U / V ⇒ W
  app
    : Δ , Γ / Ω , Ψ ⊢ t ≃ v ∶ T ⇒ U / V ⇒ W
    → Δ , Γ / Ω , Ψ ⊢ u ≃ w ∶ T / V
    → Δ , Γ / Ω , Ψ ⊢ t · u ≃ v · w ∶ U / W
  absₛ
    : Δ ∙ n , Γ [ S.Wk ]Γ / Ω ∙ m , Ψ [ S.Wk ]Γ ⊢ t ≃ u ∶ T / U
    → Δ , Γ / Ω , Ψ ⊢ Λₛ n , t ≃ Λₛ m , u ∶ Π n , T / Π m , U
  appₛ
    : ∀ t u m m<n m′ m′<n′
    → Δ , Γ / Ω , Ψ ⊢ t ≃ u ∶ Π n , T / Π n′ , U
    → Δ , Γ / Ω , Ψ ⊢ t ·ₛ m ≃ u ·ₛ m′
        ∶ T [ S.Fill m m<n ]T / U [ S.Fill m′ m′<n′ ]T
  zero
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ , Γ / Ω , Ψ ⊢ zero ≃ zero
      ∶ Π ⋆ , Nat v0
      / Π ⋆ , Nat v0
  suc
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ , Γ / Ω , Ψ ⊢ suc ≃ suc
      ∶ Π ⋆ , Π v0 , Nat v0 ⇒ Nat v1
      / Π ⋆ , Π v0 , Nat v0 ⇒ Nat v1
  cons
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ , Γ / Ω , Ψ ⊢ cons ≃ cons
      ∶ Π ⋆ , Nat ∞ ⇒ (Π v0 , Stream v0) ⇒ Stream v0
      / Π ⋆ , Nat ∞ ⇒ (Π v0 , Stream v0) ⇒ Stream v0
  head
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ , Γ / Ω , Ψ ⊢ head ≃ head
      ∶ Π ⋆ , Stream v0 ⇒ Nat ∞
      / Π ⋆ , Stream v0 ⇒ Nat ∞
  tail
    : Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ , Γ / Ω , Ψ ⊢ tail ≃ tail
      ∶ Π ⋆ , Stream v0 ⇒ (Π v0 , Stream v0)
      / Π ⋆ , Stream v0 ⇒ (Π v0 , Stream v0)
  caseNat
    : ∀ T U
    → Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ / Ω ⊢ T ≃ U
    → Δ , Γ / Ω , Ψ ⊢ caseNat T ≃ caseNat U
      ∶ Π ⋆ ,
        Nat v0 ⇒
        T [ S.Wk ]T ⇒
        (Π v0 , Nat v0 ⇒ T [ S.Wk S.>> S.Wk ]T) ⇒
        T [ S.Wk ]T
      / Π ⋆ ,
        Nat v0 ⇒
        U [ S.Wk ]T ⇒
        (Π v0 , Nat v0 ⇒ U [ S.Wk S.>> S.Wk ]T) ⇒
        U [ S.Wk ]T
  fix
    : ∀ T U
    → Δ / Ω ⊢ Γ ≃Γ Ψ
    → Δ ∙ ⋆ / Ω ∙ ⋆ ⊢ T ≃ U
    → Δ , Γ / Ω , Ψ ⊢ fix T ≃ fix U
      ∶ (Π ⋆ , (Π v0 , T [ S.Skip ]T) ⇒ T) ⇒ (Π ⋆ , T)
      / (Π ⋆ , (Π v0 , U [ S.Skip ]T) ⇒ U) ⇒ (Π ⋆ , U)


≃t→≃Γ
  : Δ , Γ / Ω , Ψ ⊢ t ≃ u ∶ T / U
  → Δ / Ω ⊢ Γ ≃Γ Ψ
≃t→≃Γ (var x x₁ x₂ x₃ x₄) = x₃
≃t→≃Γ (abs T t U u x) with ≃t→≃Γ x
... | snoc Γ≃Ψ _ = Γ≃Ψ
≃t→≃Γ (app x x₁) = ≃t→≃Γ x
≃t→≃Γ (absₛ x) = sub-inj-≃Γ _ _ (≃t→≃Γ x)
≃t→≃Γ (appₛ t u m m<n m′ m′<n′ x) = ≃t→≃Γ x
≃t→≃Γ (zero x) = x
≃t→≃Γ (suc x) = x
≃t→≃Γ (cons x) = x
≃t→≃Γ (head x) = x
≃t→≃Γ (tail x) = x
≃t→≃Γ (caseNat T U x x₁) = x
≃t→≃Γ (fix T U x x₁) = x


≃t→≃T
  : Δ , Γ / Ω , Ψ ⊢ t ≃ u ∶ T / U
  → Δ / Ω ⊢ T ≃ U
≃t→≃T (var x x₁ x₂ x₃ x₄) = x₄
≃t→≃T (abs T t U u x) with ≃t→≃Γ x
... | snoc _ T≃V = arrow T≃V (≃t→≃T x)
≃t→≃T (app x x₁) with ≃t→≃T x
... | arrow W≃V T≃U = T≃U
≃t→≃T (absₛ x) = pi (≃t→≃T x)
≃t→≃T (appₛ t u m m<n m′ m′<n′ x) with ≃t→≃T x
... | pi T≃U = sub-resp-≃T _ _ T≃U
≃t→≃T (zero x) = pi Nat
≃t→≃T (suc x) = pi (pi (arrow Nat Nat))
≃t→≃T (cons x) = pi (arrow Nat (arrow (pi Stream) Stream))
≃t→≃T (head x) = pi (arrow Stream Nat)
≃t→≃T (tail x) = pi (arrow Stream (pi Stream))
≃t→≃T (caseNat T U x x₁)
  = pi (arrow Nat (arrow (sub-resp-≃T _ _ x₁)
         (arrow (pi (arrow Nat (sub-resp-≃T _ _ x₁))) (sub-resp-≃T _ _ x₁))))
≃t→≃T (fix T U x x₁) = arrow (pi (arrow (pi (sub-resp-≃T _ _ x₁)) x₁)) (pi x₁)
