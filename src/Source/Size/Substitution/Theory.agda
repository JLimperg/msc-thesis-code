{-# OPTIONS --safe --without-K #-}
module Source.Size.Substitution.Theory where

open import Source.Size
open import Source.Size.Substitution.Canonical as SC using (Sub⊢)
open import Source.Size.Substitution.Universe as SU using (⟨_⟩ ; Sub⊢ᵤ)
open import Util.Prelude


record SubTheory (A : Ctx → Set) (A⊢ : ∀ {Δ} → A Δ → Set) : Set where
  infixl 5 _[_] _[_]ᵤ
  field
    _[_] : A Ω → SC.Sub Δ Ω → A Δ
    []-resp-⊢ : ∀ {Δ Ω a σ}
      → A⊢ a
      → σ ∶ Δ ⇒ Ω
      → A⊢ (a [ σ ])
    [Id] : ∀ {Δ} (a : A Δ) → a [ SC.Id ] ≡ a
    [>>] : ∀ {Δ Δ′ Δ″} (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) a
      → a [ σ SC.>> τ ] ≡ a [ τ ] [ σ ]


  abstract
    [Id]′ : ∀ {Δ} {σ : SC.Sub Δ Δ} a
      → σ ≡ SC.Id
      → a [ σ ] ≡ a
    [Id]′ a refl = [Id] a


    [>>]′ : ∀ {Δ Δ′ Δ″} (ι : SC.Sub Δ Δ″) (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″) a
      → ι ≡ σ SC.>> τ
      → a [ ι ] ≡ a [ τ ] [ σ ]
    [>>]′ ι σ τ a refl = [>>] σ τ a


    [>>]″ :  ∀ {Δ Δ′ Δ″} (σ : SC.Sub Δ Δ′) (τ : SC.Sub Δ′ Δ″)
      → ∀ (σ′ : SC.Sub Δ Ω) (τ′ : SC.Sub Ω Δ″) a
      → σ SC.>> τ ≡ σ′ SC.>> τ′
      → a [ τ ] [ σ ] ≡ a [ τ′ ] [ σ′ ]
    [>>]″ σ τ σ′ τ′ a eq
      = trans (sym ([>>] σ τ a)) (trans (cong (λ σ → a [ σ ]) eq) ([>>] σ′ τ′ a))


  _[_]ᵤ : A Ω → SU.Sub Δ Ω → A Δ
  a [ σ ]ᵤ = a [ ⟨ σ ⟩ ]


  abstract
    []ᵤ-resp-≈ : ∀ {Δ Ω} {σ τ : SU.Sub Δ Ω}
      → σ SU.≈ τ
      → ∀ a
      → a [ σ ]ᵤ ≡ a [ τ ]ᵤ
    []ᵤ-resp-≈ (SU.≈⁺ p) a = cong (λ σ → a [ σ ]) p


    []ᵤ-resp-⊢ : ∀ {Δ Ω σ a}
      → σ ∶ Δ ⇒ᵤ Ω
      → A⊢ a
      → A⊢ (a [ σ ]ᵤ)
    []ᵤ-resp-⊢ σ ⊢a = []-resp-⊢ ⊢a (SU.⟨⟩-resp-⊢ σ)


    [Id]ᵤ : ∀ {Δ} (a : A Δ) (⊢Δ : ⊢ Δ) → a [ SU.Id ]ᵤ ≡ a
    [Id]ᵤ a ⊢Δ = [Id] a


    [Id]ᵤ′ : ∀ {Δ} {σ : SU.Sub Δ Δ} (a : A Δ) (⊢Δ : ⊢ Δ)
      → σ SU.≈ SU.Id
      → a [ σ ]ᵤ ≡ a
    [Id]ᵤ′ a ⊢Δ (SU.≈⁺ p) = [Id]′ a p


    [>>]ᵤ : ∀ {Δ Δ′ Δ″} (σ : SU.Sub Δ Δ′) (τ : SU.Sub Δ′ Δ″) (a : A Δ″)
      → a [ σ SU.>> τ ]ᵤ ≡ a [ τ ]ᵤ [ σ ]ᵤ
    [>>]ᵤ σ τ a = [>>] _ _ _


    [>>]ᵤ′ : ∀ {Δ Δ′ Δ″} (ι : SU.Sub Δ Δ″) (σ : SU.Sub Δ Δ′) (τ : SU.Sub Δ′ Δ″) a
      → ι SU.≈ σ SU.>> τ
      → a [ ι ]ᵤ ≡ a [ τ ]ᵤ [ σ ]ᵤ
    [>>]ᵤ′ ι σ τ a (SU.≈⁺ p) = [>>]′ ⟨ ι ⟩ ⟨ σ ⟩ ⟨ τ ⟩ a p


    [>>]ᵤ″ :  ∀ {Δ Δ′ Δ″} (σ : SU.Sub Δ Δ′) (τ : SU.Sub Δ′ Δ″)
      → ∀ (σ′ : SU.Sub Δ Ω) (τ′ : SU.Sub Ω Δ″) a
      → σ SU.>> τ SU.≈ σ′ SU.>> τ′
      → a [ τ ]ᵤ [ σ ]ᵤ ≡ a [ τ′ ]ᵤ [ σ′ ]ᵤ
    [>>]ᵤ″ σ τ σ′ τ′ a (SU.≈⁺ p) = [>>]″ ⟨ σ ⟩ ⟨ τ ⟩ ⟨ σ′ ⟩ ⟨ τ′ ⟩ a p


open SubTheory {{...}} public


instance
  SubTheory-Size : SubTheory Size (λ {Δ} n → Δ ⊢ n)
  SubTheory-Size = record
    { _[_] = λ n σ → SC.sub σ n
    ; []-resp-⊢ = λ ⊢n ⊢σ → SC.sub-resp-⊢ ⊢σ ⊢n
    ; [Id] = λ n → SC.sub-Id n refl
    ; [>>] = λ σ τ n → SC.sub->> n refl
    }
