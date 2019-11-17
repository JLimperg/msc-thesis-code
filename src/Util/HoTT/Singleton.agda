{-# OPTIONS --without-K --safe #-}
module Util.HoTT.Singleton where


open import Util.HoTT.HLevel.Core
open import Util.Prelude


private
  variable
    α : Level
    A : Set α


Singleton : {A : Set α} (x : A) → Set α
Singleton x = ∃[ y ] (y ≡ x)


IsContr-Singleton : {x : A} → IsContr (Singleton x)
IsContr-Singleton {x = x} = (x , refl) , λ { (x′ , refl) → refl }


Singleton-HContr : {A : Set α} (x : A) → HContr α
Singleton-HContr x = HLevel⁺ (Singleton x) IsContr-Singleton


Singleton′ : {A : Set α} (x : A) → Set α
Singleton′ x = ∃[ y ] (x ≡ y)


IsContr-Singleton′ : {x : A} → IsContr (Singleton′ x)
IsContr-Singleton′ {x = x} = (x , refl) , λ { (x′ , refl) → refl }


Singleton′-HContr : {A : Set α} (x : A) → HContr α
Singleton′-HContr x = HLevel⁺ (Singleton′ x) IsContr-Singleton′
