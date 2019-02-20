{-# OPTIONS --allow-unsolved-metas #-}
module Ordinal.Plump.Shulman.Mu.Finite where

open import Ordinal.Plump.Shulman public

open import Relation.Binary using (Rel)

open import Util.Container.Finite using
  (Container ; _▷_ ; ⟦_⟧ ; map ; map-id ; map-∘ ; Eqℂ ; Eqℂ-intro)
open import Util.Prelude


module _ {ℓ : Level} (ℂ : Container) where

  -- Could also define this by <-induction
  data Mu (β : Ord ℓ) : Set (lsuc ℓ) where
    sup : ∀ {α} → α < β → ⟦ ℂ ⟧ (Mu α) → Mu β


  Mu-elim : ∀ {β} → Mu β → ∃[ α ] ((α < β) × (⟦ ℂ ⟧ (Mu α)))
  Mu-elim (sup α<β ℂMuα) = _ , α<β , ℂMuα



module _ {ℓ} where

  Mu-mon : ∀ {ℂ} {β γ : Ord ℓ} → β ≤ γ → Mu ℂ β → Mu ℂ γ
  Mu-mon β≤γ (sup α<β ℂMua) = sup (<-trans-≤ α<β β≤γ) ℂMua


  -- Could also define this by <-induction
  -- Should we lift the two components into β instead of α ⊔ α′?
  data _≈_ {β : Ord ℓ} {ℂ} : Rel (Mu ℂ β) (lsuc ℓ) where
    sup
      : ∀ {α}  {α<β  : α  < β} {t : ⟦ ℂ ⟧ (Mu ℂ α )}
      → ∀ {α′} {α′<β : α′ < β} {u : ⟦ ℂ ⟧ (Mu ℂ α′)}
      → Eqℂ _≈_
          (map (Mu-mon (⊔-≤-introˡ′ α′)) t)
          (map (Mu-mon (⊔-≤-introʳ′ α)) u)
      → sup α<β t ≈ sup α′<β u


  Mu-mon-irr : ∀ {ℂ} {β γ : Ord ℓ} {β≤γ₁ β≤γ₂ : β ≤ γ} {t : Mu ℂ β}
    → Mu-mon β≤γ₁ t ≈ Mu-mon β≤γ₂ t
  Mu-mon-irr {t = sup _ _} = sup (Eqℂ-intro λ i → Mu-mon-irr)


  Mu-mon-coh : ∀ {ℂ} {β γ δ : Ord ℓ} {β≤γ : β ≤ γ} {γ≤δ : γ ≤ δ} {t : Mu ℂ β}
    → Mu-mon γ≤δ (Mu-mon β≤γ t) ≈ Mu-mon (≤-trans β≤γ γ≤δ) t
  Mu-mon-coh {t = sup _ _} = sup (Eqℂ-intro (λ i → Mu-mon-irr))


  Mu-mon-cong : ∀ {ℂ} {β γ : Ord ℓ} {β≤γ : β ≤ γ} {t u : Mu ℂ β}
    → t ≈ u
    → Mu-mon β≤γ t ≈ Mu-mon β≤γ u
  Mu-mon-cong (sup (Eqℂ-intro eqP)) = sup (Eqℂ-intro eqP)


  Mu-mon-irr-cong : ∀ {ℂ} {β γ : Ord ℓ} {β≤γ₁ β≤γ₂ : β ≤ γ} {t u : Mu ℂ β}
    → t ≈ u
    → Mu-mon β≤γ₁ t ≈ Mu-mon β≤γ₂ u
  Mu-mon-irr-cong (sup (Eqℂ-intro eqP)) = sup (Eqℂ-intro eqP)


  ≈-refl : ∀ {ℂ} {β : Ord ℓ} {t : Mu ℂ β} → t ≈ t
  ≈-refl {t = sup _ _} = sup (Eqℂ-intro λ i → Mu-mon-irr)


  ≈-sym : ∀ {ℂ} {β : Ord ℓ} {t u : Mu ℂ β} → t ≈ u → u ≈ t
  ≈-sym {ℂ} {β}
    = <-ind (λ β → ∀ {t u : Mu ℂ β} → t ≈ u → u ≈ t) go β
    where
      lem : ∀ {ℂ} {α α′ : Ord ℓ} {t : Mu ℂ α} {u : Mu ℂ α′}
        → Mu-mon (⊔-≤-introˡ′ α′) t ≈ Mu-mon (⊔-≤-introʳ′ α) u
        → Mu-mon (⊔-≤-introʳ′ α′) t ≈ Mu-mon (⊔-≤-introˡ′ α) u
      lem {t = sup _ _} {sup _ _} (sup (Eqℂ-intro eq)) = sup (Eqℂ-intro eq)

      -- Probably not provable. :( Should hold classically.
      lem′ : ∀ {ℓ} {a b c : Ord ℓ} → a < c → b < c → (a ⊔ b) < c
      lem′ {c = limSuc C fc} (i , a≤fci) (j , b≤fcj) = i , λ where
        (inj₁ x) → {!!}
        (inj₂ y) → {!!}

      go : ∀ β
        → (∀ α → α < β → {t u : Mu ℂ α} → t ≈ u → u ≈ t)
        → {t u : Mu ℂ β} → t ≈ u → u ≈ t
      go β IH (sup {_} {α<β} {_} {_} {α′<β} (Eqℂ-intro eqP))
          = sup (Eqℂ-intro (λ i → IH _ (lem′ α′<β α<β) (lem (eqP i))))


  ≈-trans : ∀ {ℂ} {β : Ord ℓ} {t u v : Mu ℂ β} → t ≈ u → u ≈ v → t ≈ v
  ≈-trans {ℂ} {β}
    = <-ind (λ β → ∀ {t u v : Mu ℂ β} → t ≈ u → u ≈ v → t ≈ v) go β
    where
      go : ∀ β
        → (∀ α → α < β → {t u v : Mu ℂ α} → t ≈ u → u ≈ v → t ≈ v)
        → {t u v : Mu ℂ β} → t ≈ u → u ≈ v → t ≈ v
      go β IH (sup (Eqℂ-intro eqP₁)) (sup (Eqℂ-intro eqP₂))
        = sup (Eqℂ-intro λ i → {!!})
