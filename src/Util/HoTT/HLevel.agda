{-# OPTIONS --without-K --safe #-}
module Util.HoTT.HLevel where

open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality


private
  variable
    a b c : Level
    A B C : Set a


IsContr : Set a → Set a
IsContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)


IsProp : Set a → Set a
IsProp A = (x y : A) → x ≡ y


IsProp′ : Set a → Set a
IsProp′ A = (x y : A) → IsContr (x ≡ y)


IsProp→IsProp′ : IsProp A → IsProp′ A
IsProp→IsProp′ {A = A} A-prop x y = (A-prop x y) , canon
  where
    go : (p : x ≡ y) → trans p (A-prop y y) ≡ A-prop x y
    go refl = refl

    canon : (p : x ≡ y) → A-prop x y ≡ p
    canon refl = trans-injectiveˡ (A-prop y y) (go (A-prop y y))


IsProp′→IsProp : IsProp′ A → IsProp A
IsProp′→IsProp A-prop x y = proj₁ (A-prop x y)


IsSet : Set a → Set a
IsSet A = {x y : A} → IsProp (x ≡ y)


IsOfHLevel : ℕ → Set a → Set a
IsOfHLevel zero A = IsContr A
IsOfHLevel (suc n) A = (x y : A) → IsOfHLevel n (x ≡ y)


IsContr→IsProp : IsContr A → IsProp A
IsContr→IsProp (c , c-canon) x y = trans (sym (c-canon x)) (c-canon y)


IsOfHLevel-suc : ∀ {n} → IsOfHLevel n A → IsOfHLevel (suc n) A
IsOfHLevel-suc {n = zero} A-contr = IsProp→IsProp′ (IsContr→IsProp A-contr)
IsOfHLevel-suc {n = suc n} A-level-n x y = IsOfHLevel-suc (A-level-n x y)


IsProp→IsSet : IsProp A → IsSet A
IsProp→IsSet A-prop p q
  = IsProp′→IsProp (IsOfHLevel-suc (IsProp→IsProp′ A-prop) _ _) _ _
