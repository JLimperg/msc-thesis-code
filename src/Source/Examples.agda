module Source.Examples where

open import Source.Size
open import Source.Size.Substitution.Theory
open import Source.Term
open import Source.Type
open import Util.Prelude

import Source.Size.Substitution.Canonical as SC


{-
liftℕ : ∀ n < ⋆. ∀ m < n. Nat m → Nat n
liftℕ ≔ Λ n < ⋆. Λ m < n. λ i : Nat m.
  caseNat[Nat n] m i
    zero n
    (Λ k < m. λ i′ : Nat k. suc n k i′)
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
half : ∀ n < ⋆. Nat n → Nat n
half ≔ λ n < ⋆. fix[Nat ∙ → Nat ∙]
  (Λ n < ⋆. λ rec : (∀ m < n. Nat m → Nat m). λ i : Nat n.
    caseNat[Nat n] n i
      (zero n)
      (Λ m < n. λ i′ : Nat m. caseNat[Nat n] m i′
        (zero n)
        (Λ k < m. λ i″ : Nat k. liftNat n k (rec k i″)))
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
suc∞ : Nat ∞ → Nat ∞
suc∞ ≔ λ i : Nat ∞. caseNat[Nat ∞] ∞ i
  (suc ∞ 0 (zero 0))
  (Λ m < ∞. λ i′ : Nat m. suc ∞ (↑ m) (suc (↑ m) m i′))
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


{-
plus : ∀ n < ⋆. Nat n → Nat ∞ → Nat ∞
plus ≔ Λ n < ⋆. fix[Nat ∙ → Nat ∞ → Nat ∞]
  (Λ n < ⋆. λ rec : (∀ m < n. Nat m → Nat ∞ → Nat ∞).
    λ i : Nat n. λ j : Nat ∞. caseNat[Nat ∞] n i
      j
      (Λ m < n. λ i′ : Nat m. suc∞ (rec m i′ j)))
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


{-
zeros : ∀ n < ⋆. Stream n
zeros ≔ Λ n < ⋆. fix[Stream ∙]
  (Λ n < ⋆. λ rec : (∀ m < n. Stream m).
    cons (zero ∞) n rec)
  n
-}
zeros : ∀ {Δ} → Term Δ
zeros = Λₛ ⋆ , fix (Stream v0)
  (Λₛ ⋆ , Λ (Π v0 , Stream v0) , cons (zero ∞) v0 (var 0))
  v0


zeros⊢ : ∀ {Δ Γ} → Δ , Γ ⊢ zeros ∶ Π ⋆ , Stream v0
zeros⊢
  = absₛ
      (fix (var _ refl)
        (absₛ
          (abs
            (cons (var _ refl) (zero ∞<⋆) (var zero)))
          refl)
        refl
        refl)
      refl


{-
map : (Nat ∞ → Nat ∞) → ∀ n < ⋆. Stream n → Stream n
map ≔ λ f : Nat ∞ → Nat ∞. Λ n < ⋆. fix[Stream ∙ → Stream ∙]
  (Λ n < ⋆. λ rec : (∀ m < n. Stream m → Stream m). λ xs : Stream n.
    cons (f (head n xs)) n (Λ m < n. rec m (tail n xs m)))
  n
-}
map : ∀ {Δ} → Term Δ
map = Λ (Nat ∞ ⇒ Nat ∞) , Λₛ ⋆ , fix (Stream v0 ⇒ Stream v0)
  (Λₛ ⋆ , Λ (Π v0 , Stream v0 ⇒ Stream v0) , Λ Stream v0 ,
    cons (var 2 · head v0 (var 0)) v0
      (Λₛ v0 , var 1 ·ₛ v0 · tail v1 (var 0) v0))
  v0


map⊢ : ∀ {Δ Γ} → Δ , Γ ⊢ map ∶ (Nat ∞ ⇒ Nat ∞) ⇒ (Π ⋆ , Stream v0 ⇒ Stream v0)
map⊢
  = abs
      (absₛ
        (fix (var _ refl)
          (absₛ
            (abs
              (abs
                (cons
                  (var _ refl)
                  (app (var (suc (suc zero))) (head (var _ refl) (var zero)))
                  (absₛ (app (appₛ (var _ refl) (var (suc zero)) refl)
                      (tail (var _ refl) (var _ refl) (var zero)))
                  refl))))
            refl)
          refl
          refl)
        refl)
