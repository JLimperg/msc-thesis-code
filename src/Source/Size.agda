{-# OPTIONS --without-K --safe #-}
module Source.Size where

open import Relation.Binary using (Decidable)

open import Util.HoTT.HLevel.Core
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( trans-injectiveˡ ; cong₂-dep )


infix  4 _<_ _≤_
infixl 4 _∙_


mutual
  data Ctx : Set where
    [] : Ctx
    _∙_ : (Δ : Ctx) (n : Size Δ) → Ctx


  data Var : (Δ : Ctx) → Set where
    zero : ∀ {Δ n} → Var (Δ ∙ n)
    suc : ∀ {Δ n} (x : Var Δ) → Var (Δ ∙ n)


  data Size : (Δ : Ctx) → Set where
    var : ∀ {Δ} (x : Var Δ) → Size Δ
    ∞ ⋆ zero : ∀ {Δ} → Size Δ
    suc : ∀ {Δ} (n : Size Δ) → Size Δ


variable
  Δ Ω Δ′ Ω′ Δ″ Ω″ : Ctx
  x y z : Var Δ
  n m o p b n′ m′ o′ p′ b′ : Size Δ


wk : Size Δ → Size (Δ ∙ n)
wk (var x) = var (suc x)
wk ∞ = ∞
wk ⋆ = ⋆
wk zero = zero
wk (suc m) = suc (wk m)


bound : Var Δ → Size Δ
bound (zero {Δ} {n}) = wk n
bound (suc x) = wk (bound x)


data _<_ {Δ} : (n m : Size Δ) → Set where
  var : ∀ b (b≡bx : b ≡ bound x) → var x < b
  <suc : ∀ n (n<∞ : n < ∞) → n < suc n
  zero<∞ : zero < ∞
  suc<∞ : ∀ n (n<∞ : n < ∞) → suc n < ∞
  ∞<⋆ : ∞ < ⋆
  <-trans : n < m → m < o → n < o


data _≤_ {Δ} : (n m : Size Δ) → Set where
  <→≤ : n < m → n ≤ m
  reflexive : n ≡ m → n ≤ m


_≥_ : (n m : Size Δ) → Set
n ≥ m = m ≤ n


pattern ≤-refl = reflexive refl
pattern v0 = var zero
pattern v1 = var (suc zero)
pattern v2 = var (suc (suc zero))


abstract
  suc-inj-Var : Var.suc {n = n} x ≡ suc y → x ≡ y
  suc-inj-Var refl = refl


  suc≡-prop-Var : (p : Var.suc {n = n} x ≡ suc y) → p ≡ cong suc (suc-inj-Var p)
  suc≡-prop-Var refl = refl


  Var-IsSet : (p q : x ≡ y) → p ≡ q
  Var-IsSet {x = zero} {zero} refl refl = refl
  Var-IsSet {x = suc x} {suc .x} p refl
    = trans (suc≡-prop-Var p) (cong (cong suc) (Var-IsSet _ _))


  suc-inj-Size : Size.suc n ≡ suc m → n ≡ m
  suc-inj-Size refl = refl


  suc≡-prop-Size : (p : Size.suc n ≡ suc m) → p ≡ cong suc (suc-inj-Size p)
  suc≡-prop-Size refl = refl


  var-inj-Size : Size.var x ≡ var y → x ≡ y
  var-inj-Size refl = refl


  var≡-prop-Size : (p : Size.var x ≡ var y) → p ≡ cong var (var-inj-Size p)
  var≡-prop-Size refl = refl


  Size-IsSet : (p q : n ≡ m) → p ≡ q
  Size-IsSet {n = var x} {var .x} p refl
    = trans (var≡-prop-Size p) (cong (cong var) (Var-IsSet _ _))
  Size-IsSet {n = ∞} {∞} refl refl = refl
  Size-IsSet {n = ⋆} {⋆} refl refl = refl
  Size-IsSet {n = zero} {zero} refl refl = refl
  Size-IsSet {n = suc n} {suc .n} p refl
    = trans (suc≡-prop-Size p) (cong (cong suc) (Size-IsSet _ _))


  wk-resp-< : n < m → wk {n = o} n < wk m
  wk-resp-< (var b b≡bx) = var (wk b) (cong wk b≡bx)
  wk-resp-< (<suc n n<∞) = <suc (wk n) (wk-resp-< n<∞)
  wk-resp-< zero<∞ = zero<∞
  wk-resp-< (suc<∞ n n<∞) = suc<∞ (wk n) (wk-resp-< n<∞)
  wk-resp-< ∞<⋆ = ∞<⋆
  wk-resp-< (<-trans n<m m<o) = <-trans (wk-resp-< n<m) (wk-resp-< m<o)


  wk-resp-≤ : n ≤ m → wk {n = o} n ≤ wk m
  wk-resp-≤ (<→≤ n<m) = <→≤ (wk-resp-< n<m)
  wk-resp-≤ ≤-refl = ≤-refl


  ≤→<→< : n ≤ m → m < o → n < o
  ≤→<→< (<→≤ n<m) m<o = <-trans n<m m<o
  ≤→<→< ≤-refl m<o = m<o


  <→≤→< : n < m → m ≤ o → n < o
  <→≤→< n<m (<→≤ m<o) = <-trans n<m m<o
  <→≤→< n<m ≤-refl = n<m


  ≤-trans : n ≤ m → m ≤ o → n ≤ o
  ≤-trans (<→≤ n<m) m≤o = <→≤ (<→≤→< n<m m≤o)
  ≤-trans ≤-refl n≤o = n≤o


  wk≢varzero : wk {n = o} n ≢ var zero
  wk≢varzero {n = var x} ()
  wk≢varzero {n = ∞} ()
  wk≢varzero {n = ⋆} ()
  wk≢varzero {n = zero} ()
  wk≢varzero {n = suc n} ()
