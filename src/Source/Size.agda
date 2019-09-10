{-# OPTIONS --without-K --safe #-}
module Source.Size where

open import Relation.Binary using (Decidable)

open import Util.HoTT.HLevel.Core
open import Util.Prelude hiding (id ; _∘_)
open import Util.Relation.Binary.PropositionalEquality using
  ( trans-injectiveˡ ; cong₂-dep )


infix  4 _<_ _≤_
infixl 4 _∙_


-- begin implicit mutual block

data Ctx : Set
data Var : (Δ : Ctx) → Set
data Size : (Δ : Ctx) → Set
data _<_ {Δ} : (n m : Size Δ) → Set
data _≤_ {Δ} : (n m : Size Δ) → Set


variable
  Δ Ω Δ′ Ω′ Δ″ Ω″ : Ctx
  x y z : Var Δ
  n m o p b n′ m′ o′ p′ b′ : Size Δ


data Ctx where
  [] : Ctx
  _∙_ : (Δ : Ctx) (n : Size Δ) → Ctx


data Var where
  zero : Var (Δ ∙ n)
  suc : (x : Var Δ) → Var (Δ ∙ n)


data Size where
  var : Var Δ → Size Δ
  ∞ ⋆ zero : Size Δ
  suc : (n : Size Δ) → n < ∞ → Size Δ


wk : Size Δ → Size (Δ ∙ n)
wk-resp-< : n < m → wk {n = o} n < wk m
wk-resp-≤ : n ≤ m → wk {n = o} n ≤ wk m


wk (var x) = var (suc x)
wk ∞ = ∞
wk ⋆ = ⋆
wk zero = zero
wk (suc m m<∞) = suc (wk m) (wk-resp-< m<∞)


bound : Var Δ → Size Δ
bound (zero {Δ} {n}) = wk n
bound (suc x) = wk (bound x)


data _<_ where
  var : ∀ b (b≡bx : b ≡ bound x) (b≤n : b ≤ n) → var x < n
  zero<suc : ∀ n (n<∞ : n < ∞) → zero < suc n n<∞
  zero<∞ : zero < ∞
  suc<∞ : ∀ n (n<∞ : n < ∞) → suc n n<∞ < ∞
  zero<⋆ : zero < ⋆
  suc<⋆ : ∀ n (n<∞ : n < ∞) → suc n n<∞ < ⋆
  ∞<⋆ : ∞ < ⋆


data _≤_ where
  <→≤ : n < m → n ≤ m
  reflexive : n ≡ m → n ≤ m

-- end implicit mutual block


_≥_ : (n m : Size Δ) → Set
n ≥ m = m ≤ n


pattern ≤-refl = reflexive refl


v0 : Size (Δ ∙ n)
v0 = var zero


v1 : Size (Δ ∙ n ∙ m)
v1 = var (suc zero)


wk-resp-< (var {x} _ refl b≤m) = var (wk (bound x)) refl (wk-resp-≤ b≤m)
wk-resp-< (zero<suc n n<∞) = zero<suc (wk n) (wk-resp-< n<∞)
wk-resp-< zero<∞ = zero<∞
wk-resp-< (suc<∞ n n<∞) = suc<∞ (wk n) (wk-resp-< n<∞)
wk-resp-< zero<⋆ = zero<⋆
wk-resp-< (suc<⋆ n n<∞) = suc<⋆ (wk n) (wk-resp-< n<∞)
wk-resp-< ∞<⋆ = ∞<⋆


wk-resp-≤ (<→≤ n<m) = <→≤ (wk-resp-< n<m)
wk-resp-≤ ≤-refl = ≤-refl


mutual
  ≤→<→< : n ≤ m → m < o → n < o
  ≤→<→< (<→≤ n<m) m<o = <-trans n<m m<o
  ≤→<→< ≤-refl m<o = m<o


  <-trans : n < m → m < o → n < o
  <-trans (var b b≡bx b≤m) m<o = var b b≡bx (<→≤ (≤→<→< b≤m m<o))
  <-trans (zero<suc n n<∞) (suc<∞ .n .n<∞) = zero<∞
  <-trans (zero<suc n n<∞) (suc<⋆ .n .n<∞) = zero<⋆
  <-trans zero<∞ ∞<⋆ = zero<⋆
  <-trans (suc<∞ n n<∞) ∞<⋆ = suc<⋆ n n<∞


<→≤→< : n < m → m ≤ o → n < o
<→≤→< n<m (<→≤ m<o) = <-trans n<m m<o
<→≤→< n<m ≤-refl = n<m


≤-trans : n ≤ m → m ≤ o → n ≤ o
≤-trans (<→≤ n<m) m≤o = <→≤ (<→≤→< n<m m≤o)
≤-trans ≤-refl n≤o = n≤o


suc-≡-elim : {n<∞ : n < ∞} {m<∞ : m < ∞}
  → Size.suc n n<∞ ≡ suc m m<∞
  → Σ[ n≡m ∈ n ≡ m ]
    (n<∞ ≡ subst (_< ∞) (sym n≡m) m<∞)
suc-≡-elim refl = refl , refl


wk≢varzero : wk {n = o} n ≢ var zero
wk≢varzero {n = var x} ()
wk≢varzero {n = ∞} ()
wk≢varzero {n = ⋆} ()
wk≢varzero {n = zero} ()
wk≢varzero {n = suc n x} ()


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


Var-set : (p q : x ≡ y) → p ≡ q
Var-set {x = zero} {zero} refl refl = refl
Var-set {x = suc x} {suc .x} p refl
  = trans (suc≡-prop-Var p) (cong (cong suc) (Var-set _ _))


var-inj-Size : Size.var x ≡ var y → x ≡ y
var-inj-Size refl = refl


var≡-prop-Size : (p : Size.var x ≡ var y) → p ≡ cong var (var-inj-Size p)
var≡-prop-Size refl = refl


suc-inj-Size : ∀ {n<∞ m<∞} (p : Size.suc n n<∞ ≡ suc m m<∞)
  → Σ[ p ∈ (n ≡ m) ] subst (_< ∞) p n<∞ ≡ m<∞
suc-inj-Size refl = refl , refl


suc≡-prop-Size : ∀ {n<∞ m<∞} (p : Size.suc n n<∞ ≡ suc m m<∞)
  → let (q , r) = suc-inj-Size p
    in p ≡ cong₂-dep suc q r
suc≡-prop-Size refl = refl


mutual
  wk-inj : wk {n = o} n ≡ wk m → n ≡ m
  wk-inj {n = var x} {var .x} refl = refl
  wk-inj {n = ∞} {∞} refl = refl
  wk-inj {n = ⋆} {⋆} refl = refl
  wk-inj {n = zero} {zero} refl = refl
  wk-inj {n = suc n n<∞} {suc m m<∞} wkSn≡wkSm with suc-≡-elim wkSn≡wkSm
  ... | wkn≡wkm , _ with wk-inj wkn≡wkm
  ... | refl = cong (suc n) (<-prop _ _)


  wk-inj-≤ : wk {n = o} n ≤ wk m → n ≤ m
  wk-inj-≤ (<→≤ wkn<wkm) = <→≤ (wk-inj-< wkn<wkm)
  wk-inj-≤ (reflexive wkn≡wkm) = reflexive (wk-inj wkn≡wkm)


  wk-inj-< : wk {n = o} n < wk m → n < m
  wk-inj-< {n = var x} {m} (var _ refl b≤n) = var (bound x) refl (wk-inj-≤ b≤n)
  wk-inj-< {n = ∞} {⋆} ∞<⋆ = ∞<⋆
  wk-inj-< {n = zero} {∞} zero<∞ = zero<∞
  wk-inj-< {n = zero} {⋆} zero<⋆ = zero<⋆
  wk-inj-< {n = zero} {suc n n<∞} (zero<suc .(wk n) .(wk-resp-< n<∞)) = zero<suc n n<∞
  wk-inj-< {n = suc n x} {∞} (suc<∞ .(wk n) .(wk-resp-< x)) = suc<∞ n x
  wk-inj-< {n = suc n x} {⋆} (suc<⋆ .(wk n) .(wk-resp-< x)) = suc<⋆ n x


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


  boundx≰x : ¬ (bound x ≤ var x)
  boundx≰x {x = zero} wkn≤v0 = wk≰varzero refl wkn≤v0
  boundx≰x {x = suc x} wkbx≤x+1 = boundx≰x (wk-inj-≤ wkbx≤x+1)


  <-prop : IsProp (n < m)
  <-prop (var {x} .(bound x) refl b≤n) (var .(bound x) refl b≤n₁)
    = cong (var (bound x) refl) (≤-prop b≤n b≤n₁)
  <-prop (zero<suc n n<∞) (zero<suc .n .n<∞) = refl
  <-prop zero<∞ zero<∞ = refl
  <-prop (suc<∞ n p) (suc<∞ .n .p) = refl
  <-prop zero<⋆ zero<⋆ = refl
  <-prop (suc<⋆ n p) (suc<⋆ .n .p) = refl
  <-prop ∞<⋆ ∞<⋆ = refl


  -- This is a consequence of <-prop, but applying the general lemma annoys the
  -- termination checker, so we essentially inline the lemma.
  <-set : IsSet (n < m)
  <-set {n = n} {m} {n<m} {n<m′} p q = trans (sym (canon p)) (canon q)
    where
      go : (r : n<m ≡ n<m′) → trans r (<-prop n<m′ n<m′) ≡ <-prop n<m n<m′
      go refl = refl

      canon : (r : n<m ≡ n<m′) → <-prop n<m n<m′ ≡ r
      canon refl = trans-injectiveˡ (<-prop n<m′ n<m′) (go (<-prop n<m n<m))


  ≤-prop : IsProp (n ≤ m)
  ≤-prop (<→≤ n<m) (<→≤ n<m₁) = cong <→≤ (<-prop _ _)
  ≤-prop (<→≤ n<m) (reflexive n≡m) = ⊥-elim (<-irreflexive n≡m n<m)
  ≤-prop (reflexive n≡m) (<→≤ n<m) = ⊥-elim (<-irreflexive n≡m n<m)
  ≤-prop (reflexive n≡m) (reflexive n≡m₁) = cong reflexive (Size-set _ _)


  Size-set : (p q : n ≡ m) → p ≡ q
  Size-set {n = var x} {var .x} p refl
    = trans (var≡-prop-Size p) (cong (cong var) (Var-set _ _))
  Size-set {n = ∞} {∞} refl refl = refl
  Size-set {n = ⋆} {⋆} refl refl = refl
  Size-set {n = zero} {zero} refl refl = refl
  Size-set {n = suc n n<∞} {suc .n .n<∞} p refl
    = trans (suc≡-prop-Size p)
        (cong₂-dep (λ p q → cong₂-dep suc p q) (Size-set _ _) (<-set _ _))


suc-≡-intro : n ≡ m → {n<∞ : n < ∞} {m<∞ : m < ∞} → Size.suc n n<∞ ≡ suc m m<∞
suc-≡-intro refl = cong (suc _) (<-prop _ _)
