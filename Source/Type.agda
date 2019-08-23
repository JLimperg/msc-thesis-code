module Source.Type where

open import Source.Size as S using
  ( Size ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; p ; b ; σ ; τ ; ι)
open import Util.Prelude

open S.Ctx


infixr 3 Π_,_
infixr 4 _⇒_
infixl 4 _∙_
infixl 5 sub-syntax-Type sub-syntax-Ctx


data Type (Δ : S.Ctx) : Set where
  Nat : (n : Size Δ) → Type Δ
  Stream : (n : Size Δ) → Type Δ
  _⇒_ : (T U : Type Δ) → Type Δ
  Π_,_ : (n : Size Δ) (T : Type (Δ ∙ n)) → Type Δ


variable T U V W T′ U′ V′ W′ : Type Δ


Π-≡⁺ : ∀ {n m} {T : Type (Δ ∙ n)} {U : Type (Δ ∙ m)}
  → (n≡m : n ≡ m)
  → subst (λ n → Type (Δ ∙ n)) n≡m T ≡ U
  → (Π n , T) ≡ (Π m , U)
Π-≡⁺ refl refl = refl


data Ctx (Δ : S.Ctx) : Set where
  [] : Ctx Δ
  _∙_ : (Γ : Ctx Δ) (T : Type Δ) → Ctx Δ


variable Γ Γ′ Γ″ Ψ Ψ′ Ψ″ : Ctx Δ


sub : S.Sub Δ Ω → Type Ω → Type Δ
sub σ (Nat n) = Nat (S.sub σ n)
sub σ (Stream n) = Stream (S.sub σ n)
sub σ (T ⇒ U) = sub σ T ⇒ sub σ U
sub σ (Π n , T) = Π S.sub σ n , sub (S.Keep σ refl) T


sub-syntax-Type = sub


syntax sub-syntax-Type σ T = T [ σ ]T


subst-sub-Keep
  : (o≡p : o ≡ p)
  → (o≡n[σ] : o ≡ S.sub σ n)
  → subst (λ n → Type (Δ ∙ n)) o≡p (sub (S.Keep {n = n} σ o≡n[σ]) T)
  ≡ sub (S.Keep σ (trans (sym o≡p) o≡n[σ])) T
subst-sub-Keep refl o≡n[σ] = refl


sub->> : ∀ {ι : S.Sub Δ Δ″} {σ : S.Sub Δ Δ′} {τ : S.Sub Δ′ Δ″} T
  → ι ≡ σ S.>> τ
  → sub ι T ≡ sub σ (sub τ T)
sub->> (Nat n) p = cong Nat (S.sub->> n p)
sub->> (Stream n) p = cong Stream (S.sub->> n p)
sub->> (T ⇒ U) p = cong₂ _⇒_ (sub->> T p) (sub->> U p)
sub->> {Δ = Δ} {ι = ι} {σ = σ} {τ = τ} (Π n , T) refl
  = Π-≡⁺ (S.sub->> n refl) go
  where
    go : subst (λ k → Type (Δ ∙ k)) (S.sub->> n refl) (sub (S.Keep ι refl) T)
           ≡ sub (S.Keep σ refl) (sub (S.Keep τ refl) T)
    go = let open ≡-Reasoning in
      begin
        subst (λ k → Type (Δ ∙ k)) (S.sub->> n refl)
          (sub (S.Keep ι refl) T)
      ≡⟨ subst-sub-Keep (S.sub->> n refl) refl ⟩
        sub (S.Keep ι _) T
      ≡⟨ cong (λ σ → sub σ T) (sym (S.Keep>>Keep {n≡o = refl})) ⟩
        sub (S.Keep σ refl S.>> S.Keep τ refl) T
      ≡⟨ sub->> T refl ⟩
        sub (S.Keep σ refl) (sub (S.Keep τ refl) T)
      ∎


sub->>′ : {σ : S.Sub Δ Δ′} {τ : S.Sub Δ′ Δ″} {σ′ : S.Sub Δ Ω} {τ′ : S.Sub Ω Δ″}
  → σ S.>> τ ≡ σ′ S.>> τ′
  → ∀ T
  → sub σ (sub τ T) ≡ sub σ′ (sub τ′ T)
sub->>′ {σ = σ} {τ} {σ′} {τ′} eq T
  = trans (sym (sub->> T refl)) (trans (cong (λ σ → sub σ T) eq) (sub->> T refl))


sub-Id : ∀ T → σ ≡ S.Id → sub σ T ≡ T
sub-Id (Nat n) p = cong Nat (S.sub-Id n p)
sub-Id (Stream n) p = cong Stream (S.sub-Id n p)
sub-Id (T ⇒ U) p = cong₂ _⇒_ (sub-Id T p) (sub-Id U p)
sub-Id (Π n , T) refl
  = Π-≡⁺ (S.sub-Id n refl)
      (trans (subst-sub-Keep (S.sub-Id n refl) refl)
        (trans (cong (λ σ → sub σ T) S.Keep-Id) (sub-Id _ refl)))


subΓ : S.Sub Δ Ω → Ctx Ω → Ctx Δ
subΓ σ [] = []
subΓ σ (Γ ∙ T) = subΓ σ Γ ∙ sub σ T


sub-syntax-Ctx = subΓ


syntax sub-syntax-Ctx σ Γ = Γ [ σ ]Γ


subΓ->> : ∀ Γ → ι ≡ σ S.>> τ
  → subΓ ι Γ ≡ subΓ σ (subΓ τ Γ)
subΓ->> [] _ = refl
subΓ->> (Γ ∙ T) p = cong₂ _∙_ (subΓ->> Γ p) (sub->> T p)


subΓ->>′ : {σ : S.Sub Δ Δ′} {τ : S.Sub Δ′ Δ″} {σ′ : S.Sub Δ Ω} {τ′ : S.Sub Ω Δ″}
  → σ S.>> τ ≡ σ′ S.>> τ′
  → ∀ Γ
  → subΓ σ (subΓ τ Γ) ≡ subΓ σ′ (subΓ τ′ Γ)
subΓ->>′ {σ = σ} {τ} {σ′} {τ′} eq Γ
  = trans (sym (subΓ->> Γ refl)) (trans (cong (λ σ → subΓ σ Γ) eq) (subΓ->> Γ refl))


subΓ-Id : ∀ Γ → σ ≡ S.Id → subΓ σ Γ ≡ Γ
subΓ-Id [] _ = refl
subΓ-Id (Γ ∙ T) p = cong₂ _∙_ (subΓ-Id Γ p) (sub-Id T p)
