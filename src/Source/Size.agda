{-# OPTIONS --without-K --safe #-}
module Source.Size where

open import Relation.Binary using (Decidable)

open import Util.HoTT.HLevel
open import Util.Prelude hiding (id ; _∘_)
open import Util.Relation.Binary.PropositionalEquality using
  ( inspect ; [_] ; trans-injectiveˡ )


infix  4 _<_ _≤_
infixl 4 _∙_
infixl 5 _>>_
infixl 5 sub-syntax-Size


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


cong₂-dep : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c}
  → (f : (a : A) → B a → C)
  → {x y : A} (p : x ≡ y)
  → {v : B x} {w : B y} (q : subst B p v ≡ w)
  → f x v ≡ f y w
cong₂-dep f refl refl = refl


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


-- begin implicit mutual block

data Sub (Δ : Ctx) : (Ω : Ctx) → Set
sub : (σ : Sub Δ Ω) (n : Size Ω) → Size Δ
subV : (σ : Sub Δ Ω) (x : Var Ω) → Size Δ
subV-resp-<∞ : (σ : Sub Δ Ω) → var x < ∞ → subV σ x < ∞
sub-resp-<∞ : (σ : Sub Δ Ω) → n < ∞ → sub σ n < ∞
sub-resp-≤∞ : (σ : Sub Δ Ω) → n ≤ ∞ → sub σ n ≤ ∞


data Sub Δ where
  [] : Sub Δ []
  Snoc : (σ : Sub Δ Ω) (n : Size Δ) (n<m : n < sub σ m)
    → Sub Δ (Ω ∙ m)


variable σ τ σ′ τ′ ι ι′ : Sub Δ Ω


subV (Snoc σ n n<m) zero = n
subV (Snoc σ n n<m) (suc x) = subV σ x


sub σ (var x) = subV σ x
sub σ ∞ = ∞
sub σ ⋆ = ⋆
sub σ zero = zero
sub σ (suc n n<∞) = suc (sub σ n) (sub-resp-<∞ σ n<∞)


-- This is a special case of subV-resp-< below. We don't prove the more general
-- statement right away because it doesn't termination-check here. It *does*
-- termination-check below because there, it isn't defined mutually with sub.
subV-resp-<∞ {x = zero {n = b}} (Snoc σ n n<b[σ]) (var _ refl b≤∞)
  = <→≤→< n<b[σ] (sub-resp-≤∞ σ (wk-inj-≤ b≤∞))
subV-resp-<∞ {x = suc {n = b} x} (Snoc σ n n<b[σ]) (var _ refl b≤∞)
  = subV-resp-<∞ σ (var (bound x) refl (wk-inj-≤ b≤∞))


sub-resp-<∞ σ (var b b≡bx b≤n) = subV-resp-<∞ σ (var b b≡bx b≤n)
sub-resp-<∞ σ zero<∞ = zero<∞
sub-resp-<∞ σ (suc<∞ n n<∞) = suc<∞ (sub σ n) (sub-resp-<∞ σ n<∞)

sub-resp-≤∞ σ (<→≤ n<∞) = <→≤ (sub-resp-<∞ σ n<∞)
sub-resp-≤∞ σ ≤-refl = ≤-refl

-- end implicit mutual block


Snoc-≡⁺ : σ ≡ τ → n ≡ m → {n<o : n < sub σ o} {m<o : m < sub τ o}
  → Snoc {m = o} σ n n<o ≡ Snoc τ m m<o
Snoc-≡⁺ {σ = σ} {n = n} refl refl = cong (Snoc σ n) (<-prop _ _)


sub-Snoc : ∀ (σ : Sub Δ Ω) n (n<m : n < sub σ m) o
  → sub (Snoc {m = m} σ n n<m) (wk o) ≡ sub σ o
sub-Snoc σ n n<m (var x) = refl
sub-Snoc σ n n<m ∞ = refl
sub-Snoc σ n n<m ⋆ = refl
sub-Snoc σ n n<m zero = refl
sub-Snoc σ n n<m (suc o o<∞) = suc-≡-intro (sub-Snoc σ n n<m o)


mutual
  subV-resp-< : (σ : Sub Δ Ω) → var x < n → subV σ x < sub σ n
  subV-resp-< {x = zero {n = b}} {n} (Snoc σ k k<b[σ]) (var _ refl b≤n)
    = <→≤→< k<b[σ]
        (subst (_≤ sub (Snoc σ k k<b[σ]) n) (sub-Snoc σ k k<b[σ] b)
          (sub-resp-≤ (Snoc σ k k<b[σ]) b≤n))
  subV-resp-< {x = suc {n = b} x} {n} (Snoc σ k k<b[σ]) (var _ refl b≤n)
    = <→≤→< (subV-resp-< σ (var _ refl ≤-refl))
        (subst (_≤ sub (Snoc σ k k<b[σ]) n) (sub-Snoc σ k k<b[σ] (bound x))
          (sub-resp-≤ (Snoc σ k k<b[σ]) b≤n))


  sub-resp-< : (σ : Sub Δ Ω) → n < m → sub σ n < sub σ m
  sub-resp-< σ (var b b≡bx b≤n) = subV-resp-< σ (var b b≡bx b≤n)
  sub-resp-< σ (zero<suc n n<∞) = zero<suc (sub σ n) (sub-resp-<∞ σ n<∞)
  sub-resp-< σ zero<∞ = zero<∞
  sub-resp-< σ (suc<∞ n n<m) = suc<∞ (sub σ n) (sub-resp-<∞ σ n<m)
  sub-resp-< σ zero<⋆ = zero<⋆
  sub-resp-< σ (suc<⋆ n n<m) = suc<⋆ (sub σ n) (sub-resp-<∞ σ n<m)
  sub-resp-< σ ∞<⋆ = ∞<⋆


  sub-resp-≤ : (σ : Sub Δ Ω) → n ≤ m → sub σ n ≤ sub σ m
  sub-resp-≤ σ (<→≤ n<m) = <→≤ (sub-resp-< σ n<m)
  sub-resp-≤ σ ≤-refl = ≤-refl


mutual
  Weaken : Sub Δ Ω → Sub (Δ ∙ n) Ω
  Weaken [] = []
  Weaken (Snoc {m = b} σ m m<n)
    = Snoc (Weaken σ) (wk m)
        (subst (wk m <_) (sym (sub-Weaken σ b)) (wk-resp-< m<n))


  subV-Weaken : ∀ (σ : Sub Δ Ω) x → subV (Weaken {n = o} σ) x ≡ wk (subV σ x)
  subV-Weaken (Snoc σ n n<m) zero = refl
  subV-Weaken (Snoc σ n n<m) (suc x) = subV-Weaken σ x


  sub-Weaken : ∀ (σ : Sub Δ Ω) n → sub (Weaken {n = o} σ) n ≡ wk (sub σ n)
  sub-Weaken σ (var x) = subV-Weaken σ x
  sub-Weaken σ ∞ = refl
  sub-Weaken σ ⋆ = refl
  sub-Weaken σ zero = refl
  sub-Weaken σ (suc n x) = suc-≡-intro (sub-Weaken σ n)


Keep : (σ : Sub Δ Ω) → m ≡ sub σ n → Sub (Δ ∙ m) (Ω ∙ n)
Keep {n = n} σ m≡n
  = Snoc (Weaken σ) (var zero)
      (var (wk (sub σ n)) (cong wk (sym m≡n)) (reflexive (sym (sub-Weaken σ n))))


Keep′ : (σ : Sub Δ Ω) → Sub (Δ ∙ sub σ n) (Ω ∙ n)
Keep′ σ = Keep σ refl


mutual
  -- The recursive case can be defined in terms of Keep, but that's more
  -- trouble than it's worth.
  Id : Sub Δ Δ
  Id {[]} = []
  Id {Δ ∙ n}
    = Snoc (Weaken Id) (var zero)
        (var (wk n) refl
          (reflexive (sym (trans (sub-Weaken Id n) (cong wk (sub-Id _ refl))))))


  subV-Id : ∀ x → subV (Id {Δ}) x ≡ var x
  subV-Id zero = refl
  subV-Id (suc x) = trans (subV-Weaken Id x) (cong wk (subV-Id x))


  sub-Id : ∀ n → σ ≡ Id → sub σ n ≡ n
  sub-Id (var x) refl  = subV-Id x
  sub-Id ∞ _ = refl
  sub-Id ⋆ _ = refl
  sub-Id zero _ = refl
  sub-Id (suc n x) p = suc-≡-intro (sub-Id n p)


Wk : Sub (Δ ∙ n) Δ
Wk = Weaken Id


sub-Wk : ∀ n → sub (Wk {Δ} {o}) n ≡ wk n
sub-Wk n = trans (sub-Weaken Id n) (cong wk (sub-Id _ refl))


Fill : ∀ n {m} → n < m → Sub Δ (Δ ∙ m)
Fill n {m} n<m = Snoc Id n (subst (n <_) (sym (sub-Id _ refl)) n<m)


mutual
  _>>_ : Sub Δ Δ′ → Sub Δ′ Δ″ → Sub Δ Δ″
  σ >> [] = []
  σ >> Snoc {m = m} τ n n<m
    = Snoc (σ >> τ) (sub σ n)
        (subst (sub σ n <_) (sym (sub->> m refl)) (sub-resp-< σ n<m))


  subV->> : ∀ (σ : Sub Δ Δ′) (τ : Sub Δ′ Δ″) x
    → subV (σ >> τ) x ≡ sub σ (subV τ x)
  subV->> σ (Snoc τ n n<m) zero = refl
  subV->> σ (Snoc τ n n<m) (suc x) = subV->> σ τ x


  sub->> : ∀ n → ι ≡ σ >> τ
    → sub ι n ≡ sub σ (sub τ n)
  sub->> {σ = σ} {τ} (var x) refl = subV->> σ τ x
  sub->> ∞ _ = refl
  sub->> ⋆ _ = refl
  sub->> zero _ = refl
  sub->> {σ = σ} {τ} (suc n x) p = suc-≡-intro (sub->> n p)


Skip : Sub (Δ ∙ n ∙ var zero) (Δ ∙ n)
Skip {Δ} {n} = Snoc (Weaken Wk) (var zero)
  (var (bound zero) refl
    (<→≤ (var (bound (suc zero)) refl
      (reflexive (sym (trans (sub-Weaken Wk n) (cong wk (sub-Wk n))))))))


Weaken>> : Weaken σ >> τ ≡ Weaken {n = n} (σ >> τ)
Weaken>> {τ = []} = refl
Weaken>> {σ = σ} {τ = Snoc τ n n<m} = Snoc-≡⁺ Weaken>> (sub-Weaken σ n)


Snoc>>Weaken : {n<m : n < sub σ m}
  → Snoc {m = m} σ n n<m >> Weaken τ ≡ σ >> τ
Snoc>>Weaken {τ = []} = refl
Snoc>>Weaken {n = n} {σ = σ} {τ = Snoc τ k k<m} {n<m}
  = Snoc-≡⁺ Snoc>>Weaken (sub-Snoc σ n n<m k)


id-l : Id >> σ ≡ σ
id-l {σ = []} = refl
id-l {σ = Snoc σ n n<m} = Snoc-≡⁺ id-l (sub-Id _ refl)


id-r : {σ : Sub Δ Ω} → σ >> Id ≡ σ
id-r {σ = []} = refl
id-r {σ = Snoc σ n n<m} = Snoc-≡⁺ (trans Snoc>>Weaken id-r) refl


>>-assoc : σ >> (τ >> ι) ≡ σ >> τ >> ι
>>-assoc {ι = []} = refl
>>-assoc {σ = σ} {τ = τ} {ι = Snoc ι n n<m}
  = Snoc-≡⁺ >>-assoc (sym (sub->> n refl))


Wk>> : Wk >> σ ≡ Weaken {n = n} σ
Wk>> = trans Weaken>> (cong Weaken id-l)


Snoc>>Wk : {n<m : n < sub σ m}
  → Snoc {m = m} σ n n<m >> Wk ≡ σ
Snoc>>Wk = trans Snoc>>Weaken id-r


Keep>>Weaken : {m≡n : m ≡ sub σ n}
  → Keep {n = n} σ m≡n >> Weaken τ ≡ Weaken (σ >> τ)
Keep>>Weaken = trans Snoc>>Weaken Weaken>>


Keep>>Wk : {m≡n : m ≡ sub σ n} → Keep {n = n} σ m≡n >> Wk ≡ Wk >> σ
Keep>>Wk = trans Keep>>Weaken (trans (sym Wk>>) (cong (Wk >>_) id-r))


Fill>>Weaken : ∀ n m (n<m : n < m)
  → Fill n n<m >> Weaken σ ≡ σ
Fill>>Weaken _ _ _ = trans Snoc>>Weaken id-l


Fill>>Wk : (n m : Size Δ) (n<m : n < m)
  → Fill n n<m >> Wk ≡ Id
Fill>>Wk _ _ _ = trans Snoc>>Weaken id-r


Fill>>Keep′ : {σ : Sub Δ Ω} {n m : Size Ω}
  → (n<m : n < m) (n[σ]<m[σ] : sub σ n < sub σ m)
  → Fill (sub σ n) n[σ]<m[σ] >> Keep′ σ ≡ σ >> Fill n n<m
Fill>>Keep′ {σ = σ} {n} {m} n<m n[σ]<m[σ]
  = Snoc-≡⁺ (trans (Fill>>Weaken _ _ n[σ]<m[σ]) (sym id-r)) refl


Keep>>Keep : {m≡n : m ≡ sub σ n} {n≡o : n ≡ sub τ o} {m≡o : m ≡ sub (σ >> τ) o}
  → Keep {n = n} σ m≡n >> Keep {n = o} τ n≡o
  ≡ Keep (σ >> τ) m≡o
Keep>>Keep = Snoc-≡⁺ Keep>>Weaken refl


Skip>>Weaken : Skip {n = n} >> Weaken σ ≡ Weaken (Weaken σ)
Skip>>Weaken = trans Snoc>>Weaken (trans Weaken>> (cong Weaken Wk>>))


Skip>>Keep′ : Skip >> Keep′ {n = n} σ ≡ Keep′ (Keep′ σ) >> Skip
Skip>>Keep′
  = Snoc-≡⁺
      (trans Skip>>Weaken (sym (trans Keep>>Weaken
        (cong Weaken (trans Snoc>>Weaken id-r)))))
      refl


Keep-Id : {m≡m : m ≡ sub Id m} → Keep Id m≡m ≡ Id
Keep-Id = Snoc-≡⁺ refl refl


Keep′Fill>>Wk>>Wk : {n<m : n < m} → Keep′ {n = o} (Fill n n<m) >> (Wk >> Wk) ≡ Wk
Keep′Fill>>Wk>>Wk {n = n} {m} {n<m = n<m} = let open ≡-Reasoning in
  begin
    Keep′ (Fill n n<m) >> (Wk >> Wk)
  ≡⟨ cong (Keep′ (Fill n n<m) >>_) Wk>>  ⟩
    Keep′ (Fill n n<m) >> (Weaken Wk)
  ≡⟨ Keep>>Weaken  ⟩
    Weaken (Fill n n<m >> Weaken Id)
  ≡⟨ cong Weaken (Fill>>Weaken n m n<m) ⟩
    Wk
  ∎


Keep′Fill>>Skip : {n<m : n < m} {v0<m : var zero < sub Wk m}
  → Keep′ (Fill n n<m) >> Skip ≡ Fill (var zero) v0<m >> Keep′ Wk
Keep′Fill>>Skip {n = n} {n<m = n<m} {v0<m} = Snoc-≡⁺ go refl
  where
    go : Keep′ (Fill n n<m) >> Weaken Wk ≡ Fill (var zero) v0<m >> Weaken Wk
    go = let open ≡-Reasoning in
      begin
        Keep′ (Fill n n<m) >> Weaken Wk
      ≡⟨ Keep>>Weaken ⟩
        Weaken (Fill n n<m >> Weaken Id)
      ≡⟨ cong Weaken (Fill>>Wk _ _ _) ⟩
        Wk
      ≡⟨ sym (Fill>>Weaken _ _ _) ⟩
        Fill (var zero) v0<m >> Weaken Wk
      ∎


sub->>′ : σ >> τ ≡ σ′ >> τ′ → sub σ (sub τ n) ≡ sub σ′ (sub τ′ n)
sub->>′ {σ = σ} {τ = τ} {σ′ = σ′} {τ′} {n} eq
  = trans (sym (sub->> n refl))
      (trans (cong (λ σ → sub σ n) eq) (sub->> n refl))


sub-syntax-Size = sub


syntax sub-syntax-Size σ n = n [ σ ]n
