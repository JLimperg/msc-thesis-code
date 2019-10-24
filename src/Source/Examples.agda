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
  → Δ ⊢ Γ ctx
  → Δ , Γ ⊢ liftNat ∶ Π ⋆ , Π v0 , Nat v0 ⇒ Nat v1
liftNat⊢ {Δ} {Γ} ⊢Γ
  = absₛ _ _ _ (⋆ ⊢Δ) ⊢Γ
      (absₛ _ _ _ (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))
        go₀
        (abs _ _
          (caseNat (<-trans (var _ refl) (var _ refl))
            (var _ (zero go₁ (Nat _ (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ))
              (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))))))
            (zero (var _ refl)
              (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))))
              (Snoc go₁ (Nat _ (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))))))
            (absₛ _ _ _
              (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))))
              (Snoc go₁ (Nat _ (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))))))
              (abs _ _
                (suc (var _ refl) (<-trans (var _ refl) (var _ refl))
                  (var _ (Snoc (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))
                    (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))))))
                  (var _
                    (zero go₂
                      (Nat _ (var _ (Snoc
                        (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))
                        (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))))))))))
              refl)
            refl))
        refl)
      refl
  where
    ⊢Δ : ⊢ Δ
    ⊢Δ = Δ⊢Γ→⊢Δ ⊢Γ

    go₀ : Δ ∙ ⋆ ⊢ Γ [ SC.Wk ] ctx
    go₀ = []-resp-⊢ ⊢Γ (SC.Wk⊢ (⋆ ⊢Δ))

    go₁ : Δ ∙ ⋆ ∙ v0 ⊢ Γ [ SC.Wk ] [ SC.Wk ] ctx
    go₁ = []-resp-⊢ go₀ (SC.Wk⊢ (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))

    go₂ : Δ ∙ ⋆ ∙ v0 ∙ v0 ⊢ Γ [ SC.Wk ] [ SC.Wk ] [ SC.Wk ] ∙ Nat v1 ctx
    go₂ = Snoc
      ([]-resp-⊢ go₁
        (SC.Wk⊢ (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ)))))))
      (Nat _ (var _ (Snoc
        (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))
        (var _ (Snoc (Snoc ⊢Δ (⋆ ⊢Δ)) (var _ (Snoc ⊢Δ (⋆ ⊢Δ))))))))


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
half : Term []
half = Λₛ ⋆ , fix (Nat v0 ⇒ Nat v0)
  (Λₛ ⋆ , Λ (Π v0 , Nat v0 ⇒ Nat v0) ,
    Λ Nat v0 , caseNat (Nat v0) v0 (var 0)
      (zero v0)
      (Λₛ v0 , Λ (Nat v0) , caseNat (Nat v1) v0 (var 0)
        (zero v1)
        (Λₛ v0 , Λ (Nat v0) , liftNat ·ₛ v2 ·ₛ v0 · (var 3 ·ₛ v0 · var 0))))
  v0


half⊢ : [] , [] ⊢ half ∶ Π ⋆ , Nat v0 ⇒ Nat v0
half⊢
  = absₛ _ _ _ (⋆ []) ([] [])
      (fix (var _ refl) (var zero (Snoc [] (⋆ [])))
        (absₛ _ _ _
          (⋆ (Snoc [] (⋆ [])))
          ([] (Snoc [] (⋆ [])))
          (abs _ _
            (abs _ _
              (caseNat
                (var ⋆ refl)
                (var 0
                  (zero
                    (Snoc ([] (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                      (pi _ _ (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                      (arr _ _
                        (Nat _ (var _ (Snoc
                          (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                          (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                        (Nat _ (var _ (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                    (Nat _ (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                (zero (var _ refl)
                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                  (Snoc
                    (Snoc
                      ([] (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                      (pi _ _
                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                        (arr _ _
                          (Nat _ (var _ (Snoc
                            (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                          (Nat v0
                             (var zero
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                    (Nat _ (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                (absₛ _ _ _
                  (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                  (Snoc
                    (Snoc
                      ([] (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                      (pi v0 (Nat v0 ⇒ Nat v0)
                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))
                        (arr (Nat v0) (Nat v0)
                          (Nat v0
                             (var zero
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                          (Nat v0
                             (var zero
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                    (Nat v0 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                  (abs _ _
                    (caseNat (<-trans (var _ refl) (var ⋆ refl))
                      (var _ (zero
                        (Snoc
                          (Snoc
                            ([]
                               (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                            (pi _ _
                             (var (suc zero)
                                (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                             (arr _ _
                               (Nat _ (var _ (Snoc
                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                 (var (suc zero)
                                    (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                     (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))
                               (Nat _ (var _ (Snoc
                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                 (var (suc zero)
                                    (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                     (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))
                          (Nat v1
                             (var (suc zero)
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                        (Nat v0 (var zero (Snoc
                          (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))
                      (zero
                        (var _ refl)
                        (var _ (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                          (var _ (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                        (Snoc (Snoc (Snoc
                          ([] (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                          (pi _ _
                            (var (suc zero)
                               (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                            (arr _ _
                              (Nat _ (var _ (Snoc
                                (Snoc
                                  (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                (var (suc zero)
                                   (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))
                              (Nat _ (var _ (Snoc
                                (Snoc
                                  (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                (var (suc zero)
                                   (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))
                          (Nat v1
                             (var (suc zero)
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                          (Nat v0
                             (var zero
                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))
                      (absₛ _ _ _
                        (var zero
                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                        (Snoc
                          (Snoc
                            (Snoc
                              ([]
                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                              (pi _ _
                                (var (suc zero)
                                   (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))
                                (arr _ _
                                  (Nat _
                                    (var _
                                      (Snoc
                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                        (var (suc zero)
                                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))
                                  (Nat _
                                    (var _
                                      (Snoc
                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                        (var (suc zero)
                                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))
                            (Nat _
                              (var (suc zero)
                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                          (Nat _
                            (var zero
                               (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                        (abs _ _
                          (app _ _
                            (appₛ _ _
                              (<-trans (var _ refl) (var _ refl))
                              (var _
                                (Snoc
                                   (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                    (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                   (var zero
                                    (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                     (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                              (appₛ _ _ (var _ refl)
                                (var _
                                  (Snoc
                                    (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                       (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                    (var zero
                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                (liftNat⊢
                                  (Snoc
                                    (Snoc
                                      (Snoc
                                        (Snoc
                                          ([] (Snoc
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                 (var zero
                                                  (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                   (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                          (pi _ _
                                            (var _
                                              (Snoc
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                 (var zero
                                                  (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                   (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                            (arr _ _
                                              (Nat _
                                                (var _
                                                  (Snoc
                                                    (Snoc
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                       (var zero
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                    (var _
                                                      (Snoc
                                                         (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                         (var zero
                                                          (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))))
                                              (Nat _
                                                (var _
                                                  (Snoc
                                                    (Snoc
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                       (var zero
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                    (var _
                                                      (Snoc
                                                         (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                         (var zero
                                                          (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))))
                                        (Nat _
                                          (var _
                                            (Snoc
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                              (var zero
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                      (Nat _
                                        (var _
                                          (Snoc
                                             (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                              (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                             (var zero
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                    (Nat _
                                      (var _
                                        (Snoc
                                          (Snoc
                                            (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                          (var _
                                            (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))))
                                refl)
                              refl)
                            (app _ _
                              (appₛ _ _ (<-trans (var _ refl) (var _ refl))
                                (var _
                                  (Snoc
                                     (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                      (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                     (var zero
                                      (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                       (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                (var _
                                  (suc
                                    (suc
                                      (suc
                                        (zero
                                          ([] (Snoc
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                 (var zero
                                                  (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                   (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                          (pi _ _
                                            (var _
                                              (Snoc
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                 (var zero
                                                  (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                   (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                            (arr _ _
                                              (Nat _
                                                (var _
                                                  (Snoc
                                                    (Snoc
                                                      (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                      (var zero
                                                         (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                    (var _
                                                      (Snoc
                                                         (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                          (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                         (var zero
                                                          (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))))
                                              (Nat _
                                                (var _
                                                  (Snoc
                                                    (Snoc
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                       (var zero
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                    (var _
                                                      (Snoc
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                        (var zero
                                                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))))
                                        (Nat _
                                          (var _
                                            (Snoc
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                              (var zero
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                      (Nat _
                                        (var _
                                          (Snoc
                                             (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                              (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                             (var zero
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                    (Nat _
                                      (var _
                                        (Snoc
                                          (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                             (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                          (var zero
                                             (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                              (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))))
                                refl)
                              (var _
                                (zero
                                  (Snoc
                                    (Snoc
                                      (Snoc
                                        ([] (Snoc
                                               (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                               (var zero
                                                (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                        (pi _ _
                                          (var _
                                            (Snoc
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                 (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                              (var zero
                                                 (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                  (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))
                                          (arr _ _
                                            (Nat _
                                              (var _
                                                (Snoc
                                                  (Snoc
                                                    (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                       (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                    (var zero
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                  (var _
                                                    (Snoc
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                       (var zero
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))))))
                                            (Nat _
                                              (var _
                                                (Snoc
                                                  (Snoc
                                                     (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                      (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                     (var zero
                                                      (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                       (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))))
                                                  (var _
                                                    (Snoc
                                                       (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                        (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                                       (var zero
                                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                                         (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))))
                                      (Nat _
                                        (var _
                                          (Snoc
                                             (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                              (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                             (var zero
                                              (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                               (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                    (Nat _
                                      (var _
                                        (Snoc
                                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                           (var zero
                                            (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                             (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))
                                  (Nat _
                                    (var _
                                      (Snoc
                                        (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                           (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))))
                                        (var zero
                                           (Snoc (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ []))))
                                            (var zero (Snoc (Snoc [] (⋆ [])) (⋆ (Snoc [] (⋆ [])))))))))))))))
                        refl)
                      refl))
                  refl)
                refl)))
          refl)
        refl
        refl)
      refl
