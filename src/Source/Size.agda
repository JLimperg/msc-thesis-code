{-# OPTIONS --without-K --safe #-}
module Source.Size where

open import Util.HoTT.HLevel.Core
open import Util.Prelude


infix  4 _<_
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
  var : n ≡ bound x → var x < n
  zero<suc : zero < suc n
  zero<∞ : zero < ∞
  suc<suc : (n<m : n < m) → suc n < suc m
  suc<∞ : (n<∞ : n < ∞) → suc n < ∞
  suc<⋆ : (n<⋆ : n < ⋆) → suc n < ⋆
  ∞<⋆ : ∞ < ⋆
  <-trans : n < m → m < o → n < o
  <suc : n < suc n


data _≤_ {Δ} : (n m : Size Δ) → Set where
  reflexive : n ≡ m → n ≤ m
  <→≤ : n < m → n ≤ m


pattern ≤-refl = reflexive refl

pattern v0 = var zero
pattern v1 = var (suc zero)
pattern v2 = var (suc (suc zero))


abstract
  n<m→n<Sm : n < m → n < suc m
  n<m→n<Sm n<m = <-trans n<m <suc


  n≤m→n<Sm : n ≤ m → n < suc m
  n≤m→n<Sm ≤-refl = <suc
  n≤m→n<Sm (<→≤ n<m) = n<m→n<Sm n<m


  var<suc : var x ≤ n → var x < suc n
  var<suc = n≤m→n<Sm


  zero<⋆ : zero {Δ} < ⋆
  zero<⋆ = <-trans zero<∞ ∞<⋆


  ∞<suc : ∞ ≤ n → ∞ < suc n
  ∞<suc = n≤m→n<Sm


  ⋆<suc : ⋆ ≤ n → ⋆ < suc n
  ⋆<suc = n≤m→n<Sm


  Sn<m→n<m : suc n < m → n < m
  Sn<m→n<m (suc<suc n<m) = <-trans n<m <suc
  Sn<m→n<m (suc<∞ n<∞) = n<∞
  Sn<m→n<m (suc<⋆ n<⋆) = n<⋆
  Sn<m→n<m (<-trans Sn<o o<m) = <-trans (Sn<m→n<m Sn<o) o<m
  Sn<m→n<m <suc = <-trans <suc (suc<suc <suc)


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
  wk-resp-< (var p) = var (cong wk p)
  wk-resp-< zero<suc = zero<suc
  wk-resp-< zero<∞ = zero<∞
  wk-resp-< (suc<suc n<m) = suc<suc (wk-resp-< n<m)
  wk-resp-< (suc<∞ n<∞) = suc<∞ (wk-resp-< n<∞)
  wk-resp-< (suc<⋆ n<⋆) = suc<⋆ (wk-resp-< n<⋆)
  wk-resp-< ∞<⋆ = ∞<⋆
  wk-resp-< (<-trans n<o o<m) = <-trans (wk-resp-< n<o) (wk-resp-< o<m)
  wk-resp-< <suc = <suc
