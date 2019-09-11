{-# OPTIONS --without-K --safe #-}
module Util.HoTT.HLevel.Core where

open import Util.Prelude
open import Util.Relation.Binary.LogicalEquivalence using (_↔_ ; forth ; back)
open import Util.Relation.Binary.PropositionalEquality using
  ( trans-injectiveˡ )


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


IsProp↔IsProp′ : IsProp A ↔ IsProp′ A
IsProp↔IsProp′ .forth = IsProp→IsProp′
IsProp↔IsProp′ .back = IsProp′→IsProp


IsSet : Set a → Set a
IsSet A = {x y : A} → IsProp (x ≡ y)


IsOfHLevel : ℕ → Set a → Set a
IsOfHLevel 0 A = IsContr A
IsOfHLevel 1 A = IsProp A
IsOfHLevel (suc (suc n)) A = {x y : A} → IsOfHLevel (suc n) (x ≡ y)


IsOfHLevel′ : ℕ → Set a → Set a
IsOfHLevel′ zero A = IsContr A
IsOfHLevel′ (suc n) A = ∀ {x y : A} → IsOfHLevel′ n (x ≡ y)


IsOfHLevel′→IsOfHLevel : ∀ n → IsOfHLevel′ n A → IsOfHLevel n A
IsOfHLevel′→IsOfHLevel zero A-contr = A-contr
IsOfHLevel′→IsOfHLevel (suc zero) A-prop = IsProp′→IsProp λ _ _ → A-prop
IsOfHLevel′→IsOfHLevel (suc (suc n)) A-level
  = IsOfHLevel′→IsOfHLevel (suc n) A-level


IsOfHLevel→IsOfHLevel′ : ∀ n → IsOfHLevel n A → IsOfHLevel′ n A
IsOfHLevel→IsOfHLevel′ zero A-contr = A-contr
IsOfHLevel→IsOfHLevel′ (suc zero) A-prop = IsProp→IsProp′ A-prop _ _
IsOfHLevel→IsOfHLevel′ (suc (suc n)) A-level
  = IsOfHLevel→IsOfHLevel′ (suc n) A-level


IsOfHLevel↔IsOfHLevel′ : ∀ n → IsOfHLevel n A ↔ IsOfHLevel′ n A
IsOfHLevel↔IsOfHLevel′ n .forth = IsOfHLevel→IsOfHLevel′ n
IsOfHLevel↔IsOfHLevel′ n .back = IsOfHLevel′→IsOfHLevel n


IsContr→IsProp : IsContr A → IsProp A
IsContr→IsProp (c , c-canon) x y = trans (sym (c-canon x)) (c-canon y)


IsOfHLevel-suc : ∀ n → IsOfHLevel n A → IsOfHLevel (suc n) A
IsOfHLevel-suc 0 A-contr = IsContr→IsProp A-contr
IsOfHLevel-suc 1 A-prop = IsOfHLevel-suc 0 (IsProp→IsProp′ A-prop _ _)
IsOfHLevel-suc (suc (suc n)) A-level-n = IsOfHLevel-suc (suc n) A-level-n


IsProp→IsSet : IsProp A → IsSet A
IsProp→IsSet = IsOfHLevel-suc 1


record HLevel α n : Set (lsuc α) where
  constructor HLevel⁺
  field
    type : Set α
    level : IsOfHLevel n type

open HLevel public


HContr : ∀ α → Set (lsuc α)
HContr α = HLevel α 0


HProp : ∀ α → Set (lsuc α)
HProp α = HLevel α 1


HSet : ∀ α → Set (lsuc α)
HSet α = HLevel α 2


HLevel-suc : ∀ {α n} → HLevel α n → HLevel α (suc n)
HLevel-suc (HLevel⁺ A A-level) = HLevel⁺ A (IsOfHLevel-suc _ A-level)


Singleton : {A : Set a} (x : A) → Set a
Singleton x = ∃[ y ] (y ≡ x)


IsContr-Singleton : {x : A} → IsContr (Singleton x)
IsContr-Singleton {x = x} = (x , refl) , λ { (x′ , refl) → refl }


Singleton-HContr : {A : Set a} (x : A) → HContr a
Singleton-HContr x = HLevel⁺ (Singleton x) IsContr-Singleton
