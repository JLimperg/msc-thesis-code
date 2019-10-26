module Source.Examples where

open import Source.Size
open import Source.Size.Substitution.Theory
open import Source.Term
open import Source.Type
open import Util.Prelude

import Source.Size.Substitution.Canonical as SC


{-
liftℕ : (n < ⋆) (m < n) → Nat m → Nat n
liftℕ ≔ λ (n < ⋆) (m < n) (i : Nat m).
  caseNat (Nat n) m i
    zero n
    (λ (k < m) (i′ : Nat k). suc n k i′)
-}
liftNat : ∀ {Δ} → Term Δ
liftNat = Λₛ ⋆ , Λₛ v0 , Λ (Nat v0) ,
  caseNat (Nat v1) v0 (var 0)
    (zero v1)
    (Λₛ v0 , Λ (Nat v0) , suc v2 v0 (var 0))


liftNat⊢ : ∀ {Δ Γ}
  → Δ , Γ ⊢ liftNat ∶ Π ⋆ , Π v0 , Nat v0 ⇒ Nat v1
liftNat⊢
  = absₛ
      (absₛ
        (abs
          (caseNat (<-trans (var _ refl) (var _ refl))
            (var zero)
            (zero (var _ refl))
            (absₛ
              (abs
                (suc (var _ refl) (<-trans (var _ refl) (var _ refl)) (var zero)))
              refl)
            refl))
        refl)
      refl


{-
half : (n < ⋆) → Nat n → Nat n
half ≔ λ (n < ⋆). fix (λ (m < ⋆). Nat m → Nat m)
  (λ (n < ⋆) (rec : (m < n) → Nat m → Nat m).
    λ (i : Nat n). caseNat (Nat n) n i
      (zero n)
      (λ (m < n) (i′ : Nat m). caseNat (Nat n) m i′
        (zero n)
        (λ (k < m) (i″ : Nat k). liftNat n k (rec k i″)))
  n
-}
half : ∀ {Δ} → Term Δ
half = Λₛ ⋆ , fix (Nat v0 ⇒ Nat v0)
  (Λₛ ⋆ , Λ (Π v0 , Nat v0 ⇒ Nat v0) ,
    Λ Nat v0 , caseNat (Nat v0) v0 (var 0)
      (zero v0)
      (Λₛ v0 , Λ (Nat v0) , caseNat (Nat v1) v0 (var 0)
        (zero v1)
        (Λₛ v0 , Λ (Nat v0) , liftNat ·ₛ v2 ·ₛ v0 · (var 3 ·ₛ v0 · var 0))))
  v0


half⊢ : ∀ {Δ Γ} → Δ , Γ ⊢ half ∶ Π ⋆ , Nat v0 ⇒ Nat v0
half⊢
  = absₛ
      (fix (var _ refl)
        (absₛ
          (abs
            (abs
              (caseNat (var _ refl) (var zero) (zero (var _ refl))
                (absₛ
                  (abs
                    (caseNat (<-trans (var _ refl) (var _ refl))
                      (var zero)
                      (zero (var _ refl))
                      (absₛ
                        (abs
                          (app
                            (appₛ (<-trans (var _ refl) (var _ refl))
                              (appₛ (var _ refl) liftNat⊢ refl)
                              refl)
                            (app
                              (appₛ
                                (<-trans (var _ refl) (var _ refl))
                                (var (suc (suc (suc zero))))
                                refl)
                              (var zero))))
                        refl)
                      refl))
                  refl)
                refl)))
          refl)
        refl
        refl)
      refl


{-
suc∞ : ℕ ∞ → ℕ ∞
suc∞ ≔ λ i : ℕ ∞. caseℕ[ℕ ∞] ∞ i
  (suc ∞ 0 (zero 0))
  (Λ m < ∞. λ i′ : ℕ m. suc ∞ (↑ m) (suc (↑ m) m i′))
-}
suc∞ : ∀ {Δ} → Term Δ
suc∞ = Λ (Nat ∞) , caseNat (Nat ∞) ∞ (var 0)
  (suc ∞ zero (zero zero))
  (Λₛ ∞ , Λ (Nat v0) , suc ∞ (suc v0) (suc (suc v0) v0 (var 0)))


suc∞⊢ : ∀ {Δ Γ} → Δ , Γ ⊢ suc∞ ∶ Nat ∞ ⇒ Nat ∞
suc∞⊢
  = abs
      (caseNat ∞<⋆ (var zero) (suc ∞<⋆ zero<∞ (zero (<-trans zero<∞ ∞<⋆)))
        (absₛ
          (abs
            (suc ∞<⋆ (suc<∞ _ (var _ refl))
              (suc (<-trans (suc<∞ _ (var _ refl)) ∞<⋆) (<suc v0 (var _ refl))
                (var zero))))
          refl)
        refl)


-- TODO decide on a consistent concrete syntax.
{-
plus : ∀ n < ⋆. ℕ n → ℕ ∞ → ℕ ∞
plus ≔ Λ n < ⋆. fix[∀ m < ⋆. ℕ m → ℕ ∞ → ℕ ∞]
  (Λ n < ⋆. λ rec : (Λ m < n. ℕ m → ℕ ∞ → ℕ ∞).
    λ i : ℕ n. λ j : ℕ ∞. caseℕ[ℕ ∞] n i
      j
      (Λ m < n. λ i′ : ℕ m. suc∞ (rec m i′ j)))
  n
-}
plus : ∀ {Δ} → Term Δ
plus = Λₛ ⋆ , fix (Nat v0 ⇒ Nat ∞ ⇒ Nat ∞)
  (Λₛ ⋆ , Λ (Π v0 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞) ,
    Λ (Nat v0) , Λ (Nat ∞) , caseNat (Nat ∞) v0 (var 1)
      (var 0)
      (Λₛ v0 , Λ (Nat v0) , suc∞ · (var 3 ·ₛ v0 · var 0 · var 1)))
  v0


plus⊢ : ∀ {Δ Γ} → Δ , Γ ⊢ plus ∶ Π ⋆ , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞
plus⊢
  = absₛ
      (fix (var _ refl)
        (absₛ
          (abs
            (abs
              (abs
                (caseNat (var _ refl) (var (suc zero)) (var zero)
                  (absₛ
                    (abs
                      (app
                        suc∞⊢
                        (app
                          (app
                            (appₛ (var _ refl)
                              (var (suc (suc (suc zero))))
                              refl)
                            (var zero))
                          (var (suc zero)))))
                    refl)
                  refl))))
          refl)
        refl
        refl)
      refl
