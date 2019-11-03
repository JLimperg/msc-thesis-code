{-# OPTIONS --without-K --allow-unsolved-metas #-} -- TODO
module Model.Term where

open import Cats.Category

open import Model.Size as MS using (_<_ ; ⟦_⟧Δ ; ⟦_⟧n ; ⟦_⟧σ)
open import Model.Type as MT
open import Util.HoTT.Equiv
open import Util.Relation.Binary.PropositionalEquality using (happly)
open import Util.Prelude hiding (id ; _∘_ ; _×_)
open import Source.Size as SS using (v0 ; v1)
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
open ST.Ctx


⟦_⟧x : ∀ {Δ Γ x T}
  → Δ , Γ ⊢ₓ x ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦_⟧x {Γ = Γ ∙ T} zero = π₂ ⟦ Γ ⟧Γ
⟦ suc {U = U} x ⟧x = ⟦ x ⟧x ∘ π₁ ⟦ U ⟧T


⟦_⟧t : ∀ {Δ Γ t T}
  → Δ , Γ ⊢ t ∶ T
  → ⟦ Γ ⟧Γ ⇒ ⟦ T ⟧T
⟦ var ⊢x ⟧t = ⟦ ⊢x ⟧x
⟦ abs {Γ = Γ} {T} {t} {U} ⊢t ⟧t
  = curry ⟦ Γ ⟧Γ ⟦ T ⟧T ⟦ U ⟧T ⟦ ⊢t ⟧t
⟦ app {T = T} {U = U} ⊢t ⊢u ⟧t
  = eval ⟦ T ⟧T ⟦ U ⟧T ∘ ⟨ ⟦ ⊢t ⟧t , ⟦ ⊢u ⟧t ⟩
⟦ absₛ {Γ = Γ} ⊢t refl ⟧t
  = MT.absₛ (⟦ ⊢t ⟧t ∘ ⟦subΓ⟧ SU.Wk Γ .back)
⟦ appₛ {Δ} {n} {Γ} {T = T} m<n ⊢t refl ⟧t
  = ⟦subT⟧ (SU.Fill m<n) T .back ∘ MT.appₛ m<n ⟦ ⊢t ⟧t
⟦ zero n<⋆ ⟧t = record
  { fobj = λ γ → zero≤ _
  ; feq = λ δ≈δ′ x → refl
  }
⟦ suc n<⋆ m<n ⊢i ⟧t = record
  { fobj = λ γ → suc≤ _ _ (MS.⟦<⟧ m<n) (⟦ ⊢i ⟧t .fobj γ)
  ; feq = λ δ≈δ′ x → cong suc (⟦ ⊢i ⟧t .feq ⊤.tt x)
  }
⟦ cons n<⋆ ⊢i ⊢is ⟧t = record
  { fobj = λ γ → MT.cons (⟦ ⊢i ⟧t .fobj γ .proj₁) (⟦ ⊢is ⟧t .fobj γ .arr)
  ; feq = λ δ≈δ′ γ≈γ′ i i≤nδ i≤nδ′
      → cons-≡⁺ (⟦ ⊢i ⟧t .feq _ γ≈γ′)
          (λ m m<n m<n′ k k≤m → ⟦ ⊢is ⟧t .feq _ γ≈γ′ m m<n m m<n′ k k≤m k≤m)
          i i≤nδ i≤nδ′
  }
⟦ head n<⋆ ⊢is ⟧t = record
  { fobj = λ γ → MT.head (⟦ ⊢is ⟧t .fobj γ) , MS.<→≤ MS.nat<∞
  ; feq = λ δ≈δ′ γ≈γ′ → head-≡⁺ (⟦ ⊢is ⟧t .feq ⊤.tt γ≈γ′)
  }
⟦ tail n<⋆ m<n ⊢is ⟧t = record
  { fobj = λ γ → MT.tail (⟦ ⊢is ⟧t .fobj γ) _ (MS.⟦<⟧ m<n)
  ; feq = λ δ≈δ′ γ≈γ′ i i≤mδ i≤mδ′
      → tail-≡⁺ (⟦ ⊢is ⟧t .feq _ γ≈γ′) _ _ (MS.⟦<⟧ m<n) (MS.⟦<⟧ m<n) i i≤mδ i≤mδ′
  }
⟦ caseNat {Δ} {n} {T = T} n<⋆ ⊢i ⊢z ⊢s refl ⟧t = record
  { fobj = λ γ → caseℕ≤ (⟦ ⊢i ⟧t .fobj γ) (⟦ ⊢z ⟧t .fobj γ)
      λ m m<n i
        → ⟦subT⟧ SU.Wk T .forth .fobj
            (⟦ ⊢s ⟧t .fobj γ .arr m m<n .fobj i)
  ; feq = λ δ≈δ′ γ≈γ′ → {!!}
  }
⟦ fix {Δ} {n} {Γ} {T = T} n<⋆ ⊢t refl refl ⟧t
  = ⟦subT⟧ (SU.Fill n<⋆) T .back ∘ term⇒
  module ⟦⟧t-fix where
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
        → ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → rec m m<n (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → rec-resp m m<n m′ m′<n _ _ δ δ γ γ (⟦ Γ ⟧Γ .eq-refl γ)
              }))
      λ n g g-resp m h h-resp g≈h n<⋆ m<⋆ δ δ′ γ γ′ γ≈γ′
        → ⟦ ⊢t ⟧t .feq _ γ≈γ′ n n<⋆ m m<⋆ λ k k<n k′ k′<m
            → ⟦subT⟧ SU.Skip T .back .feq _
                (g≈h k k<n k′ k′<m _ _ δ δ′ γ γ′ γ≈γ′)

    term : ∀ n n<⋆ δ → ⟦ Γ ⟧Γ .Obj δ → ⟦ T ⟧T .Obj (δ , n , n<⋆)
    term = go .proj₁

    term-param : ∀ n n′ n<⋆ n′<⋆ δ δ′ (γ : ⟦ Γ ⟧Γ .Obj δ) (γ′ : ⟦ Γ ⟧Γ .Obj δ′)
      → ⟦ Γ ⟧Γ .eq _ γ γ′
      → ⟦ T ⟧T .eq _ (term n n<⋆ δ γ) (term n′ n′<⋆ δ′ γ′)
    term-param = go .proj₂ .proj₁

    term⇒ : ⟦ Γ ⟧Γ ⇒ subT ⟦ SU.Fill n<⋆ ⟧σ ⟦ T ⟧T
    term⇒ = record
      { fobj = term _ _ _
      ; feq = λ δ≈δ′ → term-param _ _ _ _ _ _ _ _
      }

    term-unfold₀ : ∀ {n}
      → term n
      ≡ λ n<⋆ δ γ → ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
            (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
              { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
              ; param = λ m m<n m′ m′<n
                  → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
              })
    term-unfold₀ = go .proj₂ .proj₂

    term-unfold : ∀ {n n<⋆ δ γ}
      → term n n<⋆ δ γ
      ≡ ⟦ ⊢t ⟧t .fobj γ .arr n n<⋆ .fobj
          (⟦∀⟧′-resp-≈⟦Type⟧ (⟦subT⟧ SU.Skip T) .back record
            { arr = λ m m<n → term m (MS.<-trans m<n n<⋆) δ γ
            ; param = λ m m<n m′ m′<n
                → term-param _ _ _ _ _ _ _ _ (⟦ Γ ⟧Γ .eq-refl γ)
            })
    term-unfold {n} {n<⋆} {δ} {γ} = cong (λ f → f n<⋆ δ γ) term-unfold₀


⟦_⟧ν : ∀ {Δ} {Γ Ψ : ST.Ctx Δ} {ν} → ν ∶ Γ ⇛ Ψ → ⟦ Γ ⟧Γ ⇒ ⟦ Ψ ⟧Γ
⟦ [] ⟧ν = ! _
⟦ Snoc ⊢ν ⊢t ⟧ν = ⟨ ⟦ ⊢ν ⟧ν , ⟦ ⊢t ⟧t ⟩


⟦sub⟧ : ∀ {Δ Γ Ψ ν t T}
  → (⊢ν : ν ∶ Γ ⇛ Ψ)
  → (⊢t : Δ , Ψ ⊢ t ∶ T)
  → ⟦ sub-resp-⊢ ⊢ν ⊢t ⟧t ≈ ⟦ ⊢t ⟧t ∘ ⟦ ⊢ν ⟧ν
⟦sub⟧ ⊢ν ⊢t = {!!}


{-
⟦subₛ⟧ : ∀ {Δ Ω Γ t T}
  → (σ : SU.Sub Δ Ω)
  → (⊢t : Ω , Γ ⊢ t ∶ T)
  → ⟦ subₛ-resp-⊢ σ ⊢t ⟧t ≈ MT.subₛ Γ T σ ⟦ ⊢t ⟧t
⟦subₛ⟧ σ (var x ⊢x) = {!!}
⟦subₛ⟧ σ (abs T t ⊢t)
  = ≈⁺ λ δ γ → RG.≈→≡ (RG.≈⁺ λ x → ⟦subₛ⟧ σ ⊢t .≈⁻ δ (γ , x))
⟦subₛ⟧ σ (app {Γ = Γ} {T = T} {U = U} t u ⊢t ⊢u) = ≈⁺ λ δ γ
  → let open ≡-Reasoning in
    begin
      ⟦ subₛ-resp-⊢ σ ⊢t ⟧t .fobj γ .RG.fobj
        (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ)
    ≡⟨ cong (λ f → f .RG.fobj (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ))
        (⟦subₛ⟧ σ ⊢t .≈⁻ δ γ) ⟩
      MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj
        (⟦ subₛ-resp-⊢ σ ⊢u ⟧t .fobj γ)
    ≡⟨ cong (MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj)
        (⟦subₛ⟧ σ ⊢u .≈⁻ δ γ) ⟩
      MT.subₛ Γ (T ST.⇒ U) σ ⟦ ⊢t ⟧t .fobj γ .RG.fobj
        (MT.subₛ Γ T σ ⟦ ⊢u ⟧t .fobj γ)
    ≡⟨ {!!} ⟩
      ⟦subT⟧ σ U .back .fobj
        (⟦ ⊢t ⟧t .fobj (⟦subΓ⟧ σ Γ .forth .fobj γ) .RG.fobj
         (⟦ ⊢u ⟧t .fobj (⟦subΓ⟧ σ Γ .forth .fobj γ)))
    ∎
⟦subₛ⟧ σ (absₛ {Γ = Γ} n T t ⊢t refl) = ≈⁺ λ δ x
  → ⟦∀⟧′-≡⁺ _ _ λ m m<n
      → trans (⟦subₛ⟧ (SU.Keep′ σ) ⊢t .≈⁻ _ _)
          (cong (⟦subT⟧ (SU.Keep′ σ) T .back .fobj) {!!})
  -- = let open ≈-Reasoning in
  --   begin
  --     ⟦ subₛ-resp-⊢ σ (_,_⊢_∶_.absₛ n T t ⊢t p) ⟧t
  --     -- MT.absₛ
  --     -- (⟦ subₛ-resp-⊢ (SU.Keep′ σ) ⊢t ⟧t ∘
  --     --  ≡→≈⟦Type⟧Γ (subₛ-resp-⊢-absₛ.eq n t T σ ⊢t p) .back ∘
  --     --  ⟦subΓ⟧ SU.Wk (Γ [ σ ]Γ) .back)
  --   ≈⟨ cong (λ f → MT.absₛ (f ∘ ≡→≈⟦Type⟧Γ (subₛ-resp-⊢-absₛ.eq n t T σ ⊢t p) .back ∘
  --      ⟦subΓ⟧ SU.Wk (sub-syntax-Ctx σ Γ) .back)) ? ⟩
  --     ?
  --   ≈⟨ {!!} ⟩
  --     MT.subₛ Γ (ST.Π n , T) σ
  --       (MT.absₛ (⟦ ⊢t ⟧t ∘ ≡→≈⟦Type⟧Γ p .back ∘ ⟦subΓ⟧ SU.Wk Γ .back))
  --   ∎
-- ⟦subₛ⟧ σ (absₛ n T t ⊢t p) = ≈⁺ λ δ γ → ⟦∀⟧′-≡⁺ _ _ λ m m<n
--   → trans (⟦subₛ⟧ (SU.Keep′ σ) ⊢t .≈⁻ _ _) {!!}
⟦subₛ⟧ σ (appₛ t m m<n ⊢t x) = {!!}
⟦subₛ⟧ σ (zero x) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _ refl
⟦subₛ⟧ σ (suc {Γ = Γ} x x₁ ⊢t) = ≈⁺ λ δ γ → ℕ≤-≡⁺ _ _
  (cong suc (cong proj₁ (⟦subₛ⟧ σ ⊢t .≈⁻ δ γ)))
⟦subₛ⟧ σ (cons x ⊢i ⊢is) = ≈⁺ λ δ γ → Colist-≡⁺ λ m m≤n → {!!}
⟦subₛ⟧ σ (head x ⊢t) = {!!}
⟦subₛ⟧ σ (tail x x₁ ⊢t) = {!!}
⟦subₛ⟧ σ (caseNat x ⊢t ⊢t₁ ⊢t₂ x₁) = ≈⁺ λ δ γ
  → {!!}
⟦subₛ⟧ σ (fix n<⋆ ⊢t x x₁) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (var x x₁) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (abs T t ⊢t) = ≈↝⁺ λ γ x → RGraphMor-≡⁺ λ γ₁
--   → ⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ γ (x , γ₁)
-- ⟦subₛ-resp-⊢⟧ {Γ = Γ} {T = T} σ (app t u ⊢t ⊢u) = ≈↝⁺ λ γ x
--   -- → {!⟦subₛ-resp-⊢⟧ σ ⊢u!}
--   → trans
--       (cong (λ y → ⟦ subₛ-resp-⊢ σ ⊢t ⟧t .fObj x .fObj y)
--         (⟦subₛ-resp-⊢⟧ σ ⊢u .≈↝⁻ γ x))
--       -- {!cong (λ u → u .fObj (⟦subₛ⟧ Γ T σ ⟦ ⊢u ⟧t .fObj x)) (⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ ? ?)!}
--       (trans (cong (λ u → u .fObj _) (⟦subₛ-resp-⊢⟧ σ ⊢t .≈↝⁻ γ x)) {!!})
-- ⟦subₛ-resp-⊢⟧ σ (absₛ n T t ⊢t) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (appₛ t m m<n ⊢t) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ zero = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → ℕ≤-≡⁺ _ _ {!proj₁-!}
-- ⟦subₛ-resp-⊢⟧ σ suc = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ n n<⋆ → ⟦∀⟧′-≡⁺ _ _ λ m m<n
--   → RGraphMor-≡⁺ λ γ₁ → ℕ≤-≡⁺ _ _ {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.cons = ≈↝⁺ λ γ x → ⟦∀⟧′-≡⁺ _ _ λ m m<n → RGraphMor-≡⁺ λ γ₁ → RGraphMor-≡⁺ λ γ₂ → {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.head = {!!}
-- ⟦subₛ-resp-⊢⟧ σ _,_⊢_∶_.tail = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (caseNat T) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (fix T) = {!!}
-- ⟦subₛ-resp-⊢⟧ σ (cast⊢ x x₁ ⊢t) = {!!}

-- -} -- TODO
