{-# OPTIONS --without-K --safe #-}
module Source.Size where

open import Relation.Binary using (Decidable)

open import Util.HoTT.HLevel.Core
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality using
  ( trans-injectiveˡ ; cong₂-dep )


infix  0 _⊢_ ⊢_
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


mutual
  data _<_ {Δ} : (n m : Size Δ) → Set where
    var : ∀ b (b≡bx : b ≡ bound x) (b≤n : b ≤ n) → var x < n
    zero<suc : ∀ n (n<∞ : n < ∞) → zero < suc n
    zero<∞ : zero < ∞
    suc<∞ : ∀ n (n<∞ : n < ∞) → suc n < ∞
    zero<⋆ : zero < ⋆
    suc<⋆ : ∀ n (n<∞ : n < ∞) → suc n < ⋆
    ∞<⋆ : ∞ < ⋆


  data _≤_ {Δ} : (n m : Size Δ) → Set where
    <→≤ : n < m → n ≤ m
    reflexive : n ≡ m → n ≤ m


_≥_ : (n m : Size Δ) → Set
n ≥ m = m ≤ n


pattern ≤-refl = reflexive refl
pattern v0 = var zero
pattern v1 = var (suc zero)


abstract
  suc-inj-Size : Size.suc n ≡ suc m → n ≡ m
  suc-inj-Size refl = refl


  suc≡-prop-Size : (p : Size.suc n ≡ suc m) → p ≡ cong suc (suc-inj-Size p)
  suc≡-prop-Size refl = refl


  mutual
    wk-resp-< : n < m → wk {n = o} n < wk m
    wk-resp-< (var {x} _ refl b≤m) = var (wk (bound x)) refl (wk-resp-≤ b≤m)
    wk-resp-< (zero<suc n n<∞) = zero<suc (wk n) (wk-resp-< n<∞)
    wk-resp-< zero<∞ = zero<∞
    wk-resp-< (suc<∞ n n<∞) = suc<∞ (wk n) (wk-resp-< n<∞)
    wk-resp-< zero<⋆ = zero<⋆
    wk-resp-< (suc<⋆ n n<∞) = suc<⋆ (wk n) (wk-resp-< n<∞)
    wk-resp-< ∞<⋆ = ∞<⋆


    wk-resp-≤ : n ≤ m → wk {n = o} n ≤ wk m
    wk-resp-≤ (<→≤ n<m) = <→≤ (wk-resp-< n<m)
    wk-resp-≤ ≤-refl = ≤-refl


  mutual
    ≤→<→< : n ≤ m → m < o → n < o
    ≤→<→< (<→≤ n<m) m<o = <-trans n<m m<o
    ≤→<→< ≤-refl m<o = m<o


    <-trans : n < m → m < o → n < o
    <-trans (var b b≡bx b≤m) m<o = var b b≡bx (<→≤ (≤→<→< b≤m m<o))
    <-trans (zero<suc n n<∞) (suc<∞ .n n<∞₀) = zero<∞
    <-trans (zero<suc n n<∞) (suc<⋆ .n n<∞₀) = zero<⋆
    <-trans zero<∞ ∞<⋆ = zero<⋆
    <-trans (suc<∞ n n<∞) ∞<⋆ = suc<⋆ n n<∞


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


  mutual
    wk≮varzero : n ≡ wk {n = o} m → ¬ (n < var zero)
    wk≮varzero n≡wkm (var {zero} _ refl b≤n) = wk≰varzero refl b≤n
    wk≮varzero n≡wkm (var {suc x} _ refl b≤n) = wk≰varzero refl b≤n


    wk≰varzero : n ≡ wk {n = o} m → ¬ (n ≤ var zero)
    wk≰varzero n≡wkm (<→≤ n<v0) = wk≮varzero n≡wkm n<v0
    wk≰varzero n≡wkm (reflexive refl) = wk≢varzero (sym n≡wkm)


  suc-inj-Var : Var.suc {n = n} x ≡ suc y → x ≡ y
  suc-inj-Var refl = refl


  suc≡-prop-Var : (p : Var.suc {n = n} x ≡ suc y) → p ≡ cong suc (suc-inj-Var p)
  suc≡-prop-Var refl = refl


  Var-IsSet : (p q : x ≡ y) → p ≡ q
  Var-IsSet {x = zero} {zero} refl refl = refl
  Var-IsSet {x = suc x} {suc .x} p refl
    = trans (suc≡-prop-Var p) (cong (cong suc) (Var-IsSet _ _))


  var-inj-Size : Size.var x ≡ var y → x ≡ y
  var-inj-Size refl = refl


  var≡-prop-Size : (p : Size.var x ≡ var y) → p ≡ cong var (var-inj-Size p)
  var≡-prop-Size refl = refl


  wk-inj : wk {n = o} n ≡ wk m → n ≡ m
  wk-inj {n = var x} {var .x} refl = refl
  wk-inj {n = ∞} {∞} refl = refl
  wk-inj {n = ⋆} {⋆} refl = refl
  wk-inj {n = zero} {zero} refl = refl
  wk-inj {n = suc n} {suc m} wkSn≡wkSm
    = cong suc (wk-inj (suc-inj-Size wkSn≡wkSm))


  mutual
    wk-inj-≤ : wk {n = o} n ≤ wk m → n ≤ m
    wk-inj-≤ (<→≤ wkn<wkm) = <→≤ (wk-inj-< wkn<wkm)
    wk-inj-≤ (reflexive wkn≡wkm) = reflexive (wk-inj wkn≡wkm)


    wk-inj-< : wk {n = o} n < wk m → n < m
    wk-inj-< {n = var x} {m} (var _ refl b≤n) = var (bound x) refl (wk-inj-≤ b≤n)
    wk-inj-< {n = ∞} {⋆} ∞<⋆ = ∞<⋆
    wk-inj-< {n = zero} {∞} zero<∞ = zero<∞
    wk-inj-< {n = zero} {⋆} zero<⋆ = zero<⋆
    wk-inj-< {n = zero} {suc n} (zero<suc _ wkn<∞) = zero<suc n (wk-inj-< wkn<∞)
    wk-inj-< {n = suc n} {∞} (suc<∞ .(wk n) wkn<∞) = suc<∞ n (wk-inj-< wkn<∞)
    wk-inj-< {n = suc n} {⋆} (suc<⋆ .(wk n) wkn<∞) = suc<⋆ n (wk-inj-< wkn<∞)


  boundx≰x : ¬ (bound x ≤ var x)
  boundx≰x {x = zero} wkn≤v0 = wk≰varzero refl wkn≤v0
  boundx≰x {x = suc x} wkbx≤x+1 = boundx≰x (wk-inj-≤ wkbx≤x+1)


  <→¬≤ : n < m → ¬ (n ≥ m)
  <→¬≤ (var _ refl (<→≤ bx<m)) m≤x = <→¬≤ bx<m (<→≤ (≤→<→< m≤x (var _ refl ≤-refl)))
  <→¬≤ (var _ refl ≤-refl) m≤x = boundx≰x m≤x
  <→¬≤ (zero<suc n n<∞) (<→≤ ())
  <→¬≤ (zero<suc n n<∞) (reflexive ())
  <→¬≤ zero<∞ (<→≤ ())
  <→¬≤ zero<∞ (reflexive ())
  <→¬≤ (suc<∞ n n<m) (<→≤ ())
  <→¬≤ (suc<∞ n n<m) (reflexive ())
  <→¬≤ zero<⋆ (<→≤ ())
  <→¬≤ zero<⋆ (reflexive ())
  <→¬≤ (suc<⋆ n n<m) (<→≤ ())
  <→¬≤ (suc<⋆ n n<m) (reflexive ())
  <→¬≤ ∞<⋆ (<→≤ ())
  <→¬≤ ∞<⋆ (reflexive ())


  <-antisym : n < m → ¬ (m < n)
  <-antisym n<m m<n = <→¬≤ n<m (<→≤ m<n)


  <-irrefl : ¬ (n < n)
  <-irrefl n<n = <-antisym n<n n<n


  <-irreflexive : n ≡ m → ¬ (n < m)
  <-irreflexive refl = <-irrefl


  Size-IsSet : (p q : n ≡ m) → p ≡ q
  Size-IsSet {n = var x} {var .x} p refl
    = trans (var≡-prop-Size p) (cong (cong var) (Var-IsSet _ _))
  Size-IsSet {n = ∞} {∞} refl refl = refl
  Size-IsSet {n = ⋆} {⋆} refl refl = refl
  Size-IsSet {n = zero} {zero} refl refl = refl
  Size-IsSet {n = suc n} {suc .n} p refl
    = trans (suc≡-prop-Size p) (cong (cong suc) (Size-IsSet _ _))


mutual
  data _⊢_ (Δ : Ctx) : (x : Size Δ) → Set where
    var : ∀ x (⊢Δ : ⊢ Δ) → Δ ⊢ var x
    ∞ : (⊢Δ : ⊢ Δ) → Δ ⊢ ∞
    ⋆ : (⊢Δ : ⊢ Δ) → Δ ⊢ ⋆
    zero : (⊢Δ : ⊢ Δ) → Δ ⊢ zero
    suc : (n<∞ : n < ∞) (⊢n : Δ ⊢ n) → Δ ⊢ suc n


  data ⊢_ : (Δ : Ctx) → Set where
    [] : ⊢ []
    Snoc : ⊢ Δ → Δ ⊢ n → ⊢ Δ ∙ n


abstract
  Δ⊢n→⊢Δ : Δ ⊢ n → ⊢ Δ
  Δ⊢n→⊢Δ (var x ⊢Δ) = ⊢Δ
  Δ⊢n→⊢Δ (∞ ⊢Δ) = ⊢Δ
  Δ⊢n→⊢Δ (⋆ ⊢Δ) = ⊢Δ
  Δ⊢n→⊢Δ (zero ⊢Δ) = ⊢Δ
  Δ⊢n→⊢Δ (suc n<∞ Δ⊢n) = Δ⊢n→⊢Δ Δ⊢n


  Δ⊢n→⊢Δ∙n : Δ ⊢ n → ⊢ Δ ∙ n
  Δ⊢n→⊢Δ∙n ⊢n = Snoc (Δ⊢n→⊢Δ ⊢n) ⊢n


  wk-resp-⊢ : Δ ⊢ n → Δ ⊢ m → Δ ∙ m ⊢ wk n
  wk-resp-⊢ {n = var x} ⊢n ⊢m = var (suc x) (Δ⊢n→⊢Δ∙n ⊢m)
  wk-resp-⊢ {n = ∞} ⊢n ⊢m = ∞ (Δ⊢n→⊢Δ∙n ⊢m)
  wk-resp-⊢ {n = ⋆} ⊢n ⊢m = ⋆ (Δ⊢n→⊢Δ∙n ⊢m)
  wk-resp-⊢ {n = zero} ⊢n ⊢m = zero (Δ⊢n→⊢Δ∙n ⊢m)
  wk-resp-⊢ {n = suc n} (suc n<∞ ⊢n) ⊢m = suc (wk-resp-< n<∞) (wk-resp-⊢ ⊢n ⊢m)
