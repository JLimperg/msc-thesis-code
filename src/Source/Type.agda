{-# OPTIONS --without-K --safe #-}
module Source.Type where

open import Source.Size as S using
  ( Size ; Δ ; Δ′ ; Δ″ ; Ω ; Ω′ ; Ω″ ; n ; m ; o ; p ; b)
open import Source.Size.Substitution.Universe as SU using
  ( σ ; τ ; ι ; ⟨_⟩ )
open import Util.Prelude

import Source.Size.Substitution.Canonical as SC

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


sub : SU.Sub Δ Ω → Type Ω → Type Δ
sub σ (Nat n) = Nat (SU.sub σ n)
sub σ (Stream n) = Stream (SU.sub σ n)
sub σ (T ⇒ U) = sub σ T ⇒ sub σ U
sub σ (Π n , T) = Π SU.sub σ n , sub (SU.Keep σ refl) T


sub-syntax-Type = sub


syntax sub-syntax-Type σ T = T [ σ ]T


subst-sub-Keep
  : (o≡p : o ≡ p)
  → (o≡n[σ] : o ≡ SU.sub σ n)
  → subst (λ n → Type (Δ ∙ n)) o≡p (sub (SU.Keep {n = n} σ o≡n[σ]) T)
  ≡ sub (SU.Keep σ (trans (sym o≡p) o≡n[σ])) T
subst-sub-Keep refl o≡n[σ] = refl


sub-resp-≈ : σ SU.≈ τ → ∀ T → sub σ T ≡ sub τ T
sub-resp-≈ p (Nat n) = cong Nat (SU.sub-resp-≈ p n)
sub-resp-≈ p (Stream n) = cong Stream (SU.sub-resp-≈ p n)
sub-resp-≈ p (T ⇒ U) = cong₂ _⇒_ (sub-resp-≈ p T) (sub-resp-≈ p U)
sub-resp-≈ p (Π n , T) = Π-≡⁺ (SU.sub-resp-≈ p n)
  (trans (subst-sub-Keep (SU.sub-resp-≈ p n) refl)
    (sub-resp-≈ (SU.Keep-resp-≈ _ _ p) T))


sub->> : ∀ {ι : SU.Sub Δ Δ″} {σ : SU.Sub Δ Δ′} {τ : SU.Sub Δ′ Δ″} T
  → ι SU.≈ σ SU.>> τ
  → sub ι T ≡ sub σ (sub τ T)
sub->> (Nat n) p = cong Nat (SC.sub->> n (SU.≈⁻ p))
sub->> (Stream n) p = cong Stream (SC.sub->> n (SU.≈⁻ p))
sub->> (T ⇒ U) p = cong₂ _⇒_ (sub->> T p) (sub->> U p)
sub->> {Δ = Δ} {ι = ι} {σ = σ} {τ = τ} (Π n , T) p = Π-≡⁺ (SC.sub->> n (SU.≈⁻ p)) go
  where
    go
      : subst (λ n → Type (Δ ∙ n)) (SC.sub->> n (SU.≈⁻ p))
          (sub (SU.Keep ι refl) T)
      ≡ sub (SU.Keep σ refl) (sub (SU.Keep τ refl) T)
    go = let open ≡-Reasoning in
      begin
        subst (λ n → Type (Δ ∙ n)) (SC.sub->> n (SU.≈⁻ p))
          (sub (SU.Keep ι refl) T)
      ≡⟨ subst-sub-Keep (SC.sub->> n (SU.≈⁻ p)) refl ⟩
        sub (SU.Keep ι (trans (sym (SC.sub->> n (SU.≈⁻ p))) refl)) T
      ≡⟨ sub-resp-≈ (SU.Keep-resp-≈ _ (sym (SC.sub->> n refl)) p) T ⟩
        sub (SU.Keep (σ SU.>> τ) (sym (SC.sub->> n refl))) T
      ≡⟨ sub-resp-≈ (SU.≈-sym (SU.≈⁺ (SC.Keep>>Keep {n≡o = refl}))) T ⟩
        sub (SU.Keep σ refl SU.>> SU.Keep τ refl) T
      ≡⟨ sub->> T SU.≈-refl ⟩
        sub (SU.Keep σ refl) (sub (SU.Keep τ refl) T)
      ∎


sub->>′ : {σ : SU.Sub Δ Δ′} {τ : SU.Sub Δ′ Δ″} {σ′ : SU.Sub Δ Ω} {τ′ : SU.Sub Ω Δ″}
  → σ SU.>> τ SU.≈ σ′ SU.>> τ′
  → ∀ T
  → sub σ (sub τ T) ≡ sub σ′ (sub τ′ T)
sub->>′ {σ = σ} {τ} {σ′} {τ′} eq T
  = trans (sym (sub->> T SU.≈-refl)) (trans (sub-resp-≈ eq T) (sub->> T SU.≈-refl))


sub-Id : ∀ T → σ SU.≈ SU.Id → sub σ T ≡ T
sub-Id (Nat n) (SU.≈⁺ p) = cong Nat (SC.sub-Id n p)
sub-Id (Stream n) (SU.≈⁺ p) = cong Stream (SC.sub-Id n p)
sub-Id (T ⇒ U) p = cong₂ _⇒_ (sub-Id T p) (sub-Id U p)
sub-Id (Π n , T) (SU.≈⁺ p)
  = Π-≡⁺ (SC.sub-Id n p)
      (trans (subst-sub-Keep (SC.sub-Id n p) refl)
        (sub-Id T
          (SU.≈-trans
            (SU.Keep-resp-≈ {τ = SU.Id} _ (sym (SC.sub-Id n refl)) (SU.≈⁺ p))
            (SU.≈⁺ SC.Keep-Id))))


subΓ : SU.Sub Δ Ω → Ctx Ω → Ctx Δ
subΓ σ [] = []
subΓ σ (Γ ∙ T) = subΓ σ Γ ∙ sub σ T


sub-syntax-Ctx = subΓ


syntax sub-syntax-Ctx σ Γ = Γ [ σ ]Γ


subΓ-resp-≈ : σ SU.≈ τ → ∀ Γ → subΓ σ Γ ≡ subΓ τ Γ
subΓ-resp-≈ p [] = refl
subΓ-resp-≈ p (Γ ∙ T) = cong₂ _∙_ (subΓ-resp-≈ p Γ) (sub-resp-≈ p T)


subΓ->> : ∀ Γ → ι SU.≈ σ SU.>> τ
  → subΓ ι Γ ≡ subΓ σ (subΓ τ Γ)
subΓ->> [] _ = refl
subΓ->> (Γ ∙ T) p = cong₂ _∙_ (subΓ->> Γ p) (sub->> T p)


subΓ->>′ : {σ : SU.Sub Δ Δ′} {τ : SU.Sub Δ′ Δ″} {σ′ : SU.Sub Δ Ω} {τ′ : SU.Sub Ω Δ″}
  → σ SU.>> τ SU.≈ σ′ SU.>> τ′
  → ∀ Γ
  → subΓ σ (subΓ τ Γ) ≡ subΓ σ′ (subΓ τ′ Γ)
subΓ->>′ {σ = σ} {τ} {σ′} {τ′} eq Γ
  = trans (sym (subΓ->> Γ SU.≈-refl)) (trans (subΓ-resp-≈ eq Γ) (subΓ->> Γ SU.≈-refl))


subΓ-Id : ∀ Γ → σ SU.≈ SU.Id → subΓ σ Γ ≡ Γ
subΓ-Id [] _ = refl
subΓ-Id (Γ ∙ T) p = cong₂ _∙_ (subΓ-Id Γ p) (sub-Id T p)
