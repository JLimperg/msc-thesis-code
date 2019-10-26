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


suc∞⊢ : ∀ {Δ Γ}
  → Δ ⊢ Γ ctx
  → Δ , Γ ⊢ suc∞ ∶ Nat ∞ ⇒ Nat ∞
suc∞⊢ {Δ} {Γ} ⊢Γ
  = abs _ _
      (caseNat ∞<⋆ (var _ (zero ⊢Γ ⊢Nat∞))
        (suc ∞<⋆ zero<∞ (∞ ⊢Δ) (zero (<-trans zero<∞ ∞<⋆) (zero ⊢Δ) ⊢Γ∙Nat∞))
        (absₛ _ _ _ (∞ ⊢Δ)
          ⊢Γ∙Nat∞
          (abs _ _
            (suc ∞<⋆ (suc<∞ _ (var _ refl)) (∞ ⊢Δ∙∞)
              (suc (<-trans (suc<∞ _ (var _ refl)) ∞<⋆)
                (<suc _ (var _ refl)) (suc (var _ refl) (var _ ⊢Δ∙∞))
                (var _
                  (zero (Snoc ([]-resp-⊢ ⊢Γ (SC.Wk⊢ (∞ ⊢Δ))) (Nat _ (∞ ⊢Δ∙∞)))
                    (Nat _ (var _ ⊢Δ∙∞)))))))
          refl)
        refl)
  where
    ⊢Δ : ⊢ Δ
    ⊢Δ = Δ⊢Γ→⊢Δ ⊢Γ

    ⊢Δ∙∞ : ⊢ Δ ∙ ∞
    ⊢Δ∙∞ = Snoc ⊢Δ (∞ ⊢Δ)

    ⊢Nat∞ : Δ ⊢ Nat ∞ type
    ⊢Nat∞ = Nat _ (∞ ⊢Δ)

    ⊢Γ∙Nat∞ : Δ ⊢ Γ ∙ Nat ∞ ctx
    ⊢Γ∙Nat∞ = Snoc ⊢Γ ⊢Nat∞


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


plus⊢ : ∀ {Δ Γ}
  → Δ ⊢ Γ ctx
  → Δ , Γ ⊢ plus ∶ Π ⋆ , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞
plus⊢ {Δ} {Γ} ⊢Γ
  = absₛ _ _ _ ⊢⋆ ⊢Γ
      (fix (var _ refl) (var _ ⊢Δ₀)
        (absₛ _ _ _ (⋆ ⊢Δ₀) ⊢Γ₀
          (abs _ _
            (abs _ _
              (abs _ _
                (caseNat (var _ refl)
                  (var _
                    (suc
                      (zero ⊢Γ₁ (Nat _ (var _ ⊢Δ₁)))
                      (Nat _ (∞ ⊢Δ₁))))
                  (var _ (zero ⊢Γ₂ (Nat _ (∞ ⊢Δ₁))))
                  (absₛ _ _ _
                    (var _ ⊢Δ₁)
                    ⊢Γ₃
                    (abs _ _
                      (app _ _
                        (suc∞⊢ ⊢Γ₅)
                        (app _ _
                          (app _ _
                            (appₛ _ _ (var _ refl)
                              (var _ ⊢Δ₂)
                              (var _
                                (suc
                                  (suc
                                    (suc
                                      (zero ⊢Γ₄ ⊢Π₁)
                                      (Nat _ (var _ ⊢Δ₂)))
                                    (Nat _ (∞ ⊢Δ₂)))
                                  (Nat _ (var _ ⊢Δ₂))))
                              refl)
                            (var _
                              (zero ([]-resp-⊢ ⊢Γ₃ (SC.Wk⊢ (var _ ⊢Δ₁)))
                                (Nat _ (var _ ⊢Δ₂)))))
                          (var _
                            (suc
                              (zero ([]-resp-⊢ ⊢Γ₂ (SC.Wk⊢ (var _ ⊢Δ₁)))
                                (Nat _ (∞ ⊢Δ₂)))
                              (Nat _ (var _ ⊢Δ₂)))))))
                    refl)
                  refl))))
          refl)
        refl
        refl)
      refl
  where
    ⊢Δ : ⊢ Δ
    ⊢Δ = Δ⊢Γ→⊢Δ ⊢Γ

    ⊢⋆ : Δ ⊢ ⋆
    ⊢⋆ = ⋆ ⊢Δ

    ⊢Δ₀ : ⊢ Δ ∙ ⋆
    ⊢Δ₀ = Snoc ⊢Δ ⊢⋆

    ⊢Δ₁ : ⊢ Δ ∙ ⋆ ∙ ⋆
    ⊢Δ₁ = Snoc ⊢Δ₀ (⋆ ⊢Δ₀)

    ⊢Δ₂ : ⊢ Δ ∙ ⋆ ∙ ⋆ ∙ v0
    ⊢Δ₂ = Snoc ⊢Δ₁ (var _ ⊢Δ₁)

    ⊢Π₀ : Δ ∙ ⋆ ∙ ⋆ ⊢ Π v0 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞ type
    ⊢Π₀ = pi _ _ (var _ ⊢Δ₁)
      (arr _ _ (Nat _ (var _ ⊢Δ₂))
        (arr _ _ (Nat _ (∞ ⊢Δ₂)) (Nat _ (∞ ⊢Δ₂))))

    ⊢Π₁ : Δ ∙ ⋆ ∙ ⋆ ∙ v0 ⊢ Π v1 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞ type
    ⊢Π₁ = []-resp-⊢ ⊢Π₀ (SC.Wk⊢ (var _ ⊢Δ₁))

    ⊢Γ₀ : Δ ∙ ⋆ ⊢ Γ [ SC.Wk ] ctx
    ⊢Γ₀ = []-resp-⊢ ⊢Γ (SC.Wk⊢ ⊢⋆)

    ⊢Γ₁ : Δ ∙ ⋆ ∙ ⋆
        ⊢ Γ [ SC.Wk ] [ SC.Wk ] ∙ (Π v0 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞) ctx
    ⊢Γ₁ = Snoc ([]-resp-⊢ ⊢Γ₀ (SC.Wk⊢ (⋆ ⊢Δ₀))) ⊢Π₀

    ⊢Γ₂ : Δ ∙ ⋆ ∙ ⋆
        ⊢ Γ [ SC.Wk ] [ SC.Wk ] ∙ (Π v0 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞) ∙ Nat v0 ctx
    ⊢Γ₂ = Snoc ⊢Γ₁ (Nat _ (var _ ⊢Δ₁))

    ⊢Γ₃ : Δ ∙ ⋆ ∙ ⋆
        ⊢ Γ [ SC.Wk ] [ SC.Wk ] ∙ (Π v0 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞) ∙ Nat v0 ∙ Nat ∞ ctx
    ⊢Γ₃ = Snoc ⊢Γ₂ (Nat _ (∞ ⊢Δ₁))

    ⊢Γ₄ : Δ ∙ ⋆ ∙ ⋆ ∙ v0
        ⊢ Γ [ SC.Wk ] [ SC.Wk ] [ SC.Wk ] ctx
    ⊢Γ₄ = []-resp-⊢ ([]-resp-⊢ ⊢Γ₀ (SC.Wk⊢ (⋆ ⊢Δ₀))) (SC.Wk⊢ (var _ ⊢Δ₁))

    ⊢Γ₅ : Δ ∙ ⋆ ∙ ⋆ ∙ v0
        ⊢ Γ [ SC.Wk ] [ SC.Wk ] [ SC.Wk ]
        ∙ (Π v1 , Nat v0 ⇒ Nat ∞ ⇒ Nat ∞)
        ∙ Nat v1
        ∙ Nat ∞
        ∙ Nat v0 ctx
    ⊢Γ₅ = Snoc ([]-resp-⊢ ⊢Γ₃ (SC.Wk⊢ (var _ ⊢Δ₁))) (Nat _ (var _ ⊢Δ₂))
