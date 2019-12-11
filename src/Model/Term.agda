{-# OPTIONS --without-K #-}
module Model.Term where

open import Cats.Category

open import Model.Size as MS using (_<_ ; ⟦_⟧Δ ; ⟦_⟧n ; ⟦_⟧σ)
open import Model.Type as MT
open import Util.HoTT.Equiv
open import Util.Prelude hiding (id ; _∘_ ; _×_)
open import Source.Size as SS using (v0 ; v1 ; ⋆)
open import Source.Size.Substitution.Theory
open import Source.Size.Substitution.Universe as SU using (Sub⊢ᵤ)
open import Source.Term

import Model.RGraph as RG
import Source.Type as ST

open Category._≅_
open MS.Size
open MS._<_
open MS._≤_
open RG._⇒_
open SS.Size
open SS.Ctx
open ST.Ctx


⟦_⟧x : ∀ {Δ Γ x T}
  → Δ , Γ ⊢ₓ x ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦_⟧x {Γ = Γ ∙ T} zero = π₂ ⟦ Γ ⟧Γ
⟦ suc {U = U} x ⟧x = ⟦ x ⟧x ∘ π₁ ⟦ U ⟧T


⟦abs⟧ : ∀ Δ (Γ : ST.Ctx Δ) T U
  → ⟦ Γ ∙ T ⟧Γ ⇒ ⟦ U ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T ↝ ⟦ U ⟧T
⟦abs⟧ Δ Γ T U t = curry ⟦ Γ ⟧Γ ⟦ T ⟧T ⟦ U ⟧T t


⟦app⟧ : ∀ Δ (Γ : ST.Ctx Δ) T U
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T ↝ ⟦ U ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ U ⟧T
⟦app⟧ Δ Γ T U t u = eval ⟦ T ⟧T ⟦ U ⟧T ∘ ⟨ t , u ⟩


⟦absₛ⟧ : ∀ Δ n (Γ : ST.Ctx Δ) (T : ST.Type (Δ ∙ n))
  → ⟦ Γ [ SU.Wk ]ᵤ ⟧Γ ⇒ ⟦ T ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Π n , T ⟧T
⟦absₛ⟧ Δ n Γ T t = MT.absₛ (t ∘ ⟦subΓ⟧ SU.Wk Γ .back)


⟦appₛ⟧ : ∀ Δ m n (Γ : ST.Ctx Δ) T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Π n , T ⟧T
  → m SS.< n
  → ⟦ Γ ⟧Γ ⇒ ⟦ T [ SU.Sing m ]ᵤ ⟧T
⟦appₛ⟧ Δ m n Γ T t m<n = ⟦subT⟧ (SU.Sing m<n) T .back ∘ MT.appₛ m<n t


⟦zero⟧ : ∀ Δ (Γ : ST.Ctx Δ) n
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat n ⟧T
⟦zero⟧ Δ Γ n = record
  { fobj = λ {δ} γ → zero≤ (⟦ n ⟧n .fobj δ)
  ; feq = λ δ≈δ′ x≈y → refl
  }


⟦suc⟧ : ∀ Δ (Γ : ST.Ctx Δ) {m n}
  → m SS.< n
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat m ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat n ⟧T
⟦suc⟧ Δ Γ m<n i = record
  { fobj = λ γ → suc≤ _ _ (MS.⟦<⟧ m<n) (i .fobj γ)
  ; feq = λ δ≈δ′ x≈y → cong suc (i .feq _ x≈y)
  }


⟦caseNat⟧ : ∀ Δ (Γ : ST.Ctx Δ) n T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat n ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Π n , ST.Nat v0 ST.⇒ T [ SU.Wk ]ᵤ ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦caseNat⟧ Δ Γ n T i z s = record
  { fobj = λ γ → caseℕ≤ (i .fobj γ) (z .fobj γ)
      λ m m<n i
        → ⟦subT⟧ SU.Wk T .forth .fobj
            (s .fobj γ .arr m m<n .fobj i)
  ; feq = λ {δ δ′} δ≈δ′ {γ γ′} γ≈γ′
      → caseℕ≤-pres (⟦ T ⟧T .eq δ≈δ′) (i .fobj γ) (i .fobj γ′)
          (z .fobj γ) (z .fobj γ′) _ _ (i .feq _ γ≈γ′)
          (z .feq _ γ≈γ′)
          λ m m<n m′ m′<n′ j j′ j≡j′
            → ⟦subT⟧ SU.Wk T .forth .feq _
                (s .feq _ γ≈γ′ m m<n m′ m′<n′ j≡j′)
  }


⟦cons⟧ : ∀ Δ (Γ : ST.Ctx Δ) n
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat ∞ ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Π n , ST.Stream v0 ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Stream n ⟧T
⟦cons⟧ Δ Γ n i is = record
  { fobj = λ γ → MT.cons (i .fobj γ .proj₁) (is .fobj γ .arr)
  ; feq = λ δ≈δ′ γ≈γ′ k k≤nδ k≤nδ′
      → cons-≡⁺ (i .feq _ γ≈γ′)
          (λ m m<n m<n′ k k≤m → is .feq _ γ≈γ′ m m<n m m<n′ k k≤m k≤m)
          k k≤nδ k≤nδ′
  }


⟦head⟧ : ∀ Δ (Γ : ST.Ctx Δ) n
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Stream n ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Nat ∞ ⟧T
⟦head⟧ Δ Γ n is = record
  { fobj = λ γ → MT.head (is .fobj γ) , MS.<→≤ MS.zero<∞
  ; feq = λ δ≈δ′ γ≈γ′ → head-≡⁺ (is .feq ⊤.tt γ≈γ′)
  }


⟦tail⟧ : ∀ Δ (Γ : ST.Ctx Δ) {m n}
  → m SS.< n
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Stream n ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Stream m ⟧T
⟦tail⟧ Δ Γ m<n is = record
  { fobj = λ γ → MT.tail (is .fobj γ) _ (MS.⟦<⟧ m<n)
  ; feq = λ δ≈δ′ γ≈γ′ i i≤mδ i≤mδ′
      → tail-≡⁺ (is .feq _ γ≈γ′) _ _ (MS.⟦<⟧ m<n) (MS.⟦<⟧ m<n) i i≤mδ i≤mδ′
  }


⟦fix⟧ : ∀ Δ (Γ : ST.Ctx Δ) n T
  → n SS.< ⋆
  → ⟦ Γ ⟧Γ ⇒ ⟦ ST.Π ⋆ , (ST.Π v0 , T [ SU.Skip ]ᵤ) ST.⇒ T ⟧T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T [ SU.Sing n ]ᵤ ⟧T
⟦fix⟧ Δ Γ n T n<⋆ t = ⟦subT⟧ (SU.Sing n<⋆) T .back ∘ term⇒
  module ⟦fix⟧ where
    go
      : Σ[ f ∈ (∀ n n<⋆ δ → ⟦ Γ ⟧Γ .Obj δ → ⟦ T ⟧T .Obj (δ , n , n<⋆)) ]
        Σ[ f-param ∈ (∀ n n′ n<⋆ n′<⋆ δ δ′ (γ : ⟦ Γ ⟧Γ .Obj δ) (γ′ : ⟦ Γ ⟧Γ .Obj δ′)
          → ⟦ Γ ⟧Γ .eq _ γ γ′ → ⟦ T ⟧T .eq _ (f n n<⋆ δ γ) (f n′ n′<⋆ δ′ γ′)) ]
          (∀ {n} → f n ≡ _)
    go = MS.<-indΣ′
      (λ n → ∀ n<⋆ δ (γ : ⟦ Γ ⟧Γ .Obj δ) → ⟦ T ⟧T .Obj (δ , n , n<⋆))
      (λ n m f g → ∀ n<⋆ m<⋆ δ δ′ γ γ′ (γ≈γ′ : ⟦ Γ ⟧Γ .eq _ γ γ′)
        → ⟦ T ⟧T .eq _ (f n<⋆ δ γ) (g m<⋆ δ′ γ′))
      (λ n rec rec-resp n<⋆ δ γ
        → t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → rec m m<n (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → rec-resp m m<n m′ m′<n _ _ δ δ γ γ (⟦ Γ ⟧Γ .eq-refl γ)
              }))
      λ n g g-resp m h h-resp g≈h n<⋆ m<⋆ δ δ′ γ γ′ γ≈γ′
        → t .feq _ γ≈γ′ n n<⋆ m m<⋆ λ k k<n k′ k′<m
            → ⟦subT⟧ SU.Skip T .back .feq _
                (g≈h k k<n k′ k′<m _ _ δ δ′ γ γ′ γ≈γ′)

    term : ∀ n n<⋆ δ → ⟦ Γ ⟧Γ .Obj δ → ⟦ T ⟧T .Obj (δ , n , n<⋆)
    term = go .proj₁

    term-param : ∀ n n′ n<⋆ n′<⋆ δ δ′ (γ : ⟦ Γ ⟧Γ .Obj δ) (γ′ : ⟦ Γ ⟧Γ .Obj δ′)
      → ⟦ Γ ⟧Γ .eq _ γ γ′
      → ⟦ T ⟧T .eq _ (term n n<⋆ δ γ) (term n′ n′<⋆ δ′ γ′)
    term-param = go .proj₂ .proj₁

    term⇒ : ⟦ Γ ⟧Γ ⇒ subT ⟦ SU.Sing n<⋆ ⟧σ ⟦ T ⟧T
    term⇒ = record
      { fobj = term _ _ _
      ; feq = λ δ≈δ′ → term-param _ _ _ _ _ _ _ _
      }

    term-unfold₀ : ∀ {n}
      → term n
      ≡ λ n<⋆ δ γ → t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
              })
    term-unfold₀ = go .proj₂ .proj₂

    term-unfold : ∀ {n n<⋆ δ γ}
      → term n n<⋆ δ γ
      ≡ t .fobj γ .arr n n<⋆ .fobj
          (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
            { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
            ; param = λ m m<n m′ m′<n
                → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
            })
    term-unfold {n} {n<⋆} {δ} {γ} = cong (λ f → f n<⋆ δ γ) term-unfold₀


⟦_⟧t : ∀ {Δ Γ t T}
  → Δ , Γ ⊢ t ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦ var ⊢x ⟧t = ⟦ ⊢x ⟧x
⟦ abs {Δ = Δ} {Γ} {T} {t} {U} ⊢t ⟧t = ⟦abs⟧ Δ Γ T U ⟦ ⊢t ⟧t
⟦ app {Δ} {Γ} {T = T} {U = U} ⊢t ⊢u ⟧t = ⟦app⟧ Δ Γ T U ⟦ ⊢t ⟧t ⟦ ⊢u ⟧t
⟦ absₛ {Δ} {n} {T = T} ⊢t refl ⟧t = ⟦absₛ⟧ Δ n _ T ⟦ ⊢t ⟧t
⟦ appₛ {Δ} {m} {n} {Γ} {T = T} m<n ⊢t refl ⟧t = ⟦appₛ⟧ Δ m n Γ T ⟦ ⊢t ⟧t m<n
⟦ zero {Δ} {n} {Γ} n<⋆ ⟧t = ⟦zero⟧ Δ Γ n
⟦ suc {Δ} {Γ = Γ} n<⋆ m<n ⊢i ⟧t = ⟦suc⟧ Δ Γ m<n ⟦ ⊢i ⟧t
⟦ cons {Δ} {n} {Γ} n<⋆ ⊢i ⊢is ⟧t = ⟦cons⟧ Δ Γ n ⟦ ⊢i ⟧t ⟦ ⊢is ⟧t
⟦ head {Δ} {n} {Γ} n<⋆ ⊢is ⟧t = ⟦head⟧ Δ Γ n ⟦ ⊢is ⟧t
⟦ tail {Δ} {n} {m} {Γ} n<⋆ m<n ⊢is ⟧t = ⟦tail⟧ Δ Γ m<n ⟦ ⊢is ⟧t
⟦ caseNat {Δ} {n} {Γ} {T = T} n<⋆ ⊢i ⊢z ⊢s refl ⟧t
  = ⟦caseNat⟧ Δ Γ n T ⟦ ⊢i ⟧t ⟦ ⊢z ⟧t ⟦ ⊢s ⟧t
⟦ fix {Δ} {n} {Γ} {T = T} n<⋆ ⊢t refl refl ⟧t
  = ⟦fix⟧ Δ Γ n T n<⋆ ⟦ ⊢t ⟧t


⟦_⟧ν : ∀ {Δ} {Γ Ψ : ST.Ctx Δ} {ν} → ν ∶ Γ ⇛ Ψ → ⟦ Γ ⟧Γ ⇒ ⟦ Ψ ⟧Γ
⟦ [] ⟧ν = ! _
⟦ Snoc ⊢ν ⊢t ⟧ν = ⟨ ⟦ ⊢ν ⟧ν , ⟦ ⊢t ⟧t ⟩
