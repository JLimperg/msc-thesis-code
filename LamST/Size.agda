module LamST.Size where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using
  (Σ ; ∃ ; Σ-syntax ; ∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as ≡ using
  (_≡_ ; refl; module ≡-Reasoning)


infix  4 _⊇_ _<_ _≤_
infixl 5 _∷_ _∷[_]_
infixr 6 _∙_ _∙ₛ_


mutual
  -- Size contexts are iterated dependent sums of size bounds.
  data SC : Set where
    [] : SC
    _∷_ : (Δ : SC) (n : Si∞ Δ) → SC


  -- Size variables are indexes into a size context.
  data SV : (Δ : SC) → Set where
    zero : ∀ {Δ n} → SV (Δ ∷ n)
    suc : ∀ {Δ n} (α : SV Δ) → SV (Δ ∷ n)


  -- Sizes (without ∞) with variables in a given context.
  data Si Δ : Set where
    var : (α : SV Δ) → Si Δ
    suc : (i : Si Δ) → Si Δ


  -- Sizes (with ∞) with variables in a given context.
  data Si∞ Δ : Set where
    si : (i : Si Δ) → Si∞ Δ
    ∞ : Si∞ Δ


variable
  Δ Δ′ Δ″ : SC
  i j k : Si Δ
  n m o : Si∞ Δ
  α β : SV Δ


si-inj : _≡_ {A = Si∞ Δ} (si i) (si j) → i ≡ j
si-inj refl = refl


suc-inj : _≡_ {A = Si Δ} (suc i) (suc j) → i ≡ j
suc-inj refl = refl


suc-inj′ : _≡_ {A = SV (Δ ∷ n)} (suc α) (suc β) → α ≡ β
suc-inj′ refl = refl


var-inj : var α ≡ var β → α ≡ β
var-inj refl = refl


suc∞ : Si∞ Δ → Si∞ Δ
suc∞ (si i) = si (suc i)
suc∞ ∞ = ∞


var∞ : SV Δ → Si∞ Δ
var∞ α = si (var α)


--------------------------------------------------------------------------------
-- The structural order on size variables
--------------------------------------------------------------------------------


data _<V_ : (α β : SV Δ) → Set where
  zero : zero {n = n} <V suc β
  suc  : (α<β : α <V β) → suc {n = n} α <V suc β


acc-<V-zero : Acc _<V_ (zero {n = n})
acc-<V-zero = acc λ _ ()


acc-<V-suc : Acc _<V_ α → Acc _<V_ (suc {n = n} α)
acc-<V-suc (acc h) = acc λ where
  _ zero    → acc-<V-zero
  _ (suc p) → acc-<V-suc (h _ p)


wf-<V : WellFounded (_<V_ {Δ = Δ})
wf-<V β = acc λ where
  _ zero → acc-<V-zero
  _ (suc {α = α} α<β) → acc-<V-suc (wf-<V α)



--------------------------------------------------------------------------------
-- Renamings
--------------------------------------------------------------------------------


mutual
  -- Renamings.
  data _⊇_ : (Δ Δ′ : SC) → Set where
    []   : [] ⊇ []
    weak : (θ : Δ ⊇ Δ′) → Δ ∷ n ⊇ Δ′
    lift : (θ : Δ ⊇ Δ′) (p : renSi∞ θ m ≡ n) → Δ ∷ n ⊇ Δ′ ∷ m


  renSi∞ : Δ ⊇ Δ′ → Si∞ Δ′ → Si∞ Δ
  renSi∞ θ (si i) = si (renSi θ i)
  renSi∞ θ ∞ = ∞


  renSi : Δ ⊇ Δ′ → Si Δ′ → Si Δ
  renSi θ (var α) = var (renSV θ α)
  renSi θ (suc i) = suc (renSi θ i)


  renSV : Δ ⊇ Δ′ → SV Δ′ → SV Δ
  renSV (weak θ)  α        = suc (renSV θ α)
  renSV (lift θ p) zero    = zero
  renSV (lift θ p) (suc α) = suc (renSV θ α)


variable
  θ ι : Δ′ ⊇ Δ


-- K ahoy!
lift-cong : ∀ {p q} → θ ≡ ι → lift {m = m} {n} θ p ≡ lift ι q
lift-cong {p = refl} {refl} refl = refl


mutual
  idR : Δ ⊇ Δ
  idR {[]}    = []
  idR {Δ ∷ i} = lift idR renSi∞-id


  renSi∞-id : renSi∞ idR n ≡ n
  renSi∞-id {n = si i} = ≡.cong si renSi-id
  renSi∞-id {n = ∞} = refl


  renSi-id : renSi idR i ≡ i
  renSi-id {i = var α} = ≡.cong var renSV-id
  renSi-id {i = suc i} = ≡.cong suc renSi-id


  renSV-id : renSV idR α ≡ α
  renSV-id {α = zero}  = refl
  renSV-id {α = suc α} = ≡.cong suc renSV-id


mutual
  _∙_ : Δ ⊇ Δ′ → Δ′ ⊇ Δ″ →  Δ ⊇ Δ″
  [] ∙ ι = ι
  weak θ ∙ ι = weak (θ ∙ ι)
  lift θ p ∙ weak ι = weak (θ ∙ ι)
  lift θ p ∙ lift ι q
    = lift (θ ∙ ι) (≡.trans renSi∞-∙ (≡.trans (≡.cong (renSi∞ θ) q) p))


  renSi∞-∙ : renSi∞ (θ ∙ ι) n ≡ renSi∞ θ (renSi∞ ι n)
  renSi∞-∙ {n = si i} = ≡.cong si renSi-∙
  renSi∞-∙ {n = ∞} = refl


  renSi-∙ : renSi (θ ∙ ι) i ≡ renSi θ (renSi ι i)
  renSi-∙ {i = var α} = ≡.cong var renSV-∙
  renSi-∙ {i = suc i} = ≡.cong suc renSi-∙


  renSV-∙ : renSV (θ ∙ ι) α ≡ renSV θ (renSV ι α)
  renSV-∙ {θ = []} {ι = []} {()}
  renSV-∙ {θ = weak θ} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = weak ι} = ≡.cong suc renSV-∙
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {zero} = refl
  renSV-∙ {θ = lift θ refl} {ι = lift ι refl} {suc α} = ≡.cong suc renSV-∙


∙-id-l : idR ∙ θ ≡ θ
∙-id-l {θ = []} = refl
∙-id-l {θ = weak θ} = ≡.cong weak ∙-id-l
∙-id-l {θ = lift θ p} = lift-cong ∙-id-l


∙-id-r : θ ∙ idR ≡ θ
∙-id-r {θ = []} = refl
∙-id-r {θ = weak θ} = ≡.cong weak ∙-id-r
∙-id-r {θ = lift θ p} = lift-cong ∙-id-r


weak′ : Δ ∷ n ⊇ Δ
weak′ = weak idR


lift∙weak′ : {θ : Δ ⊇ Δ′} {p : renSi∞ θ n ≡ m} → lift θ p ∙ weak′ ≡ weak θ
lift∙weak′ = ≡.cong weak ∙-id-r


weak′∙ : {θ : Δ ⊇ Δ′} → weak′ {n = n} ∙ θ ≡ weak θ
weak′∙ = ≡.cong weak ∙-id-l


wkSV : SV Δ → SV (Δ ∷ n)
wkSV = suc


wkSV≡renSV : wkSV {n = n} α ≡ renSV weak′ α
wkSV≡renSV = ≡.cong suc (≡.sym renSV-id)


wkSi : Si Δ → Si (Δ ∷ n)
wkSi (var α) = var (suc α)
wkSi (suc x) = suc (wkSi x)


wkSi≡renSi : wkSi {n = n} i ≡ renSi weak′ i
wkSi≡renSi {i = var α} = ≡.cong (λ z → var (suc z)) (≡.sym renSV-id)
wkSi≡renSi {i = suc i} = ≡.cong suc wkSi≡renSi


wkSi∞ : Si∞ Δ → Si∞ (Δ ∷ n)
wkSi∞ (si i) = si (wkSi i)
wkSi∞ ∞ = ∞


wkSi∞≡renSi∞ : wkSi∞ {n = n} m ≡ renSi∞ weak′ m
wkSi∞≡renSi∞ {m = si i} = ≡.cong si wkSi≡renSi
wkSi∞≡renSi∞ {m = ∞} = refl


wkSi∞≡si⁻ : wkSi∞ n ≡ si i → ∃[ j ] (n ≡ si j × i ≡ wkSi j)
wkSi∞≡si⁻ {n = si i} refl = i , refl , refl


wkSi≢varzero : wkSi {n = n} i ≡ var zero → ⊥
wkSi≢varzero {i = var zero} ()
wkSi≢varzero {i = var (suc α)} ()
wkSi≢varzero {i = suc i} ()


wkSi≡suc-inv : wkSi {n = n} i ≡ var (suc β) → i ≡ var β
wkSi≡suc-inv {i = var zero} refl = refl
wkSi≡suc-inv {i = var (suc α)} refl = refl


wkSi-inj : wkSi {n = n} i ≡ wkSi j → i ≡ j
wkSi-inj {i = var zero} {var zero} x = refl
wkSi-inj {i = var (suc α)} {var (suc β)} x
  = ≡.cong var (suc-inj′ (var-inj x))
wkSi-inj {i = suc i} {suc j} x
  = ≡.cong suc (wkSi-inj (suc-inj x))


--------------------------------------------------------------------------------
-- Variable bounds
--------------------------------------------------------------------------------


data Bound : (α : SV Δ) (i : Si Δ) → Set where
  zero : n ≡ si i → wkSi i ≡ j → Bound {Δ = Δ ∷ n} zero j
  suc  : wkSi i ≡ j → Bound α i → Bound {Δ = Δ ∷ n} (suc α) j


data Bound∞ : (α : SV Δ) (n : Si∞ Δ) → Set where
  zero : wkSi∞ n ≡ m → Bound∞ {Δ = Δ ∷ n} zero m
  suc  : wkSi∞ n ≡ m → Bound∞ α n → Bound∞ (suc α) m


Bound→Bound∞ : Bound α i → Bound∞ α (si i)
Bound→Bound∞ (zero refl x) = zero (≡.cong si x)
Bound→Bound∞ (suc x x₁) = suc (≡.cong si x) (Bound→Bound∞ x₁)


Bound∞→Bound : Bound∞ α (si i) → Bound α i
Bound∞→Bound {i} (zero x₁) with wkSi∞≡si⁻ x₁
... | j , refl , refl = zero refl refl
Bound∞→Bound (suc x₁ x₂) with wkSi∞≡si⁻ x₁
... | j , refl , refl = suc refl (Bound∞→Bound x₂)


bound : (α : SV Δ) → Si∞ Δ
bound (zero {n = n}) = wkSi∞ n
bound (suc α) = wkSi∞ (bound α)


Bound∞-bound : Bound∞ α (bound α)
Bound∞-bound {α = zero} = zero refl
Bound∞-bound {α = suc α} = suc refl Bound∞-bound


Bound∞-bound′ : n ≡ bound α → Bound∞ α n
Bound∞-bound′ refl = Bound∞-bound


Bound-bound : si i ≡ bound α → Bound α i
Bound-bound {α = zero} x with wkSi∞≡si⁻ (≡.sym x)
... | j , refl , refl = zero refl refl
Bound-bound {α = suc α} x with wkSi∞≡si⁻ (≡.sym x)
... | j , x₁ , x₂ = suc (≡.sym x₂) (Bound-bound (≡.sym x₁))


Bound∞≡bound : Bound∞ α n → n ≡ bound α
Bound∞≡bound (zero x) = ≡.sym x
Bound∞≡bound (suc x x₁) = ≡.trans (≡.sym x) (≡.cong wkSi∞ (Bound∞≡bound x₁))


Bound≡bound : Bound α i → si i ≡ bound α
Bound≡bound (zero refl refl) = refl
Bound≡bound (suc refl x₁) rewrite ≡.sym (Bound≡bound x₁) = refl


Bound-suc-inv : Bound (suc {n = n} α) (wkSi i) → Bound α i
Bound-suc-inv (suc x x₁) rewrite wkSi-inj x = x₁


bound-renSV : bound (renSV θ α) ≡ renSi∞ θ (bound α)
bound-renSV {θ = weak θ} {α} =
  let open ≡-Reasoning in
  begin
    wkSi∞ (bound (renSV θ α))
  ≡⟨ ≡.cong wkSi∞ bound-renSV ⟩
    wkSi∞ (renSi∞ θ (bound α))
  ≡⟨ wkSi∞≡renSi∞ ⟩
    renSi∞ weak′ (renSi∞ θ (bound α))
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (weak′ ∙ θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) weak′∙ ⟩
    renSi∞ (weak θ) (bound α)
  ∎
bound-renSV {θ = lift {m = m} {n} θ p} {zero} =
  let open ≡-Reasoning in
  ≡.sym (begin
    renSi∞ (lift θ p) (wkSi∞ m)
  ≡⟨ ≡.cong (renSi∞ (lift θ p)) wkSi∞≡renSi∞ ⟩
    renSi∞ (lift θ p) (renSi∞ weak′ m)
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (lift θ p ∙ weak′) m
  ≡⟨ ≡.cong (λ z → renSi∞ z m) (lift∙weak′ {p = p}) ⟩
    renSi∞ (weak θ) m
  ≡⟨ ≡.cong (λ z → renSi∞ z m) (≡.sym weak′∙) ⟩
    renSi∞ (weak′ ∙ θ) m
  ≡⟨ renSi∞-∙ ⟩
    renSi∞ weak′ (renSi∞ θ m)
  ≡˘⟨ wkSi∞≡renSi∞ ⟩
    wkSi∞ (renSi∞ θ m)
  ≡⟨ ≡.cong wkSi∞ p ⟩
    wkSi∞ n
  ∎)
bound-renSV {θ = lift θ p} {suc α} =
  let open ≡-Reasoning in
  begin
    wkSi∞ (bound (renSV θ α))
  ≡⟨ ≡.cong wkSi∞ (bound-renSV) ⟩
    wkSi∞ (renSi∞ θ (bound α))
  ≡⟨ wkSi∞≡renSi∞ ⟩
    renSi∞ weak′ (renSi∞ θ (bound α))
  ≡˘⟨ renSi∞-∙ ⟩
    renSi∞ (weak′ ∙ θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) weak′∙ ⟩
    renSi∞ (weak θ) (bound α)
  ≡⟨ ≡.cong (λ z → renSi∞ z (bound α)) (≡.sym (lift∙weak′ {p = p})) ⟩
    renSi∞ (lift θ p ∙ weak′) (bound α)
  ≡⟨ renSi∞-∙ ⟩
    renSi∞ (lift θ p) (renSi∞ weak′ (bound α))
  ≡⟨ ≡.cong (renSi∞ (lift θ p)) (≡.sym wkSi∞≡renSi∞) ⟩
    renSi∞ (lift θ p) (wkSi∞ (bound α))
  ∎


Bound∞-ren : Bound∞ α n → Bound∞ (renSV θ α) (renSi∞ θ n)
Bound∞-ren {θ = θ} x
  = Bound∞-bound′ (≡.trans (≡.cong (renSi∞ θ) (Bound∞≡bound x)) (≡.sym bound-renSV))


si≡-inv : si i ≡ n → ∃[ j ] (n ≡ si j)
si≡-inv refl = _ , refl


Bound-ren : Bound α i → Bound (renSV θ α) (renSi θ i)
Bound-ren {α = α} {θ = θ} x
  = Bound-bound (≡.sym
      (≡.trans (bound-renSV {θ = θ} {α})
        (≡.cong (renSi∞ θ) (≡.sym (Bound≡bound x)))))


--------------------------------------------------------------------------------
-- Relations on sizes
--------------------------------------------------------------------------------


mutual
  -- A preorder on sizes.
  data _≤_ {Δ} : (i j : Si Δ) → Set where
    refl
      : i ≤ i
    <→≤
      : i < j
      → i ≤ j


  -- A strict order on sizes.
  data _<_ {Δ} : (i j : Si Δ) → Set where
    var
      : Bound α i
      → i ≤ j
      → var α < j
    ≤→<S
      : i ≤ j
      → i < suc j
    suc-cong
      : i < j
      → suc i < suc j


-- The extension of ≤ to sizes with ∞.
data _≤∞_ {Δ} : (n m : Si∞ Δ) → Set where
  si
    : i ≤ j
    → si i ≤∞ si j
  ∞
    : ∞ ≤∞ ∞


-- The extension of < to sizes with ∞.
data _<∞_ {Δ} : (i : Si Δ) (n : Si∞ Δ) → Set where
  si
    : i < j
    → i <∞ si j
  ∞
    : i <∞ ∞


≤-reflexive : i ≡ j → i ≤ j
≤-reflexive refl = refl


≤∞-reflexive : n ≡ m → n ≤∞ m
≤∞-reflexive {n = si i} refl = si refl
≤∞-reflexive {n = ∞} refl = ∞


mutual
  <→<S : i < j → i < suc j
  <→<S x = ≤→<S (<→≤ x)


  ≤→≤S : i ≤ j → i ≤ suc j
  ≤→≤S x = <→≤ (≤→<S x)


  suc-inj-≤ : suc i ≤ suc j → i ≤ j
  suc-inj-≤ refl = refl
  suc-inj-≤ (<→≤ x) = <→≤ (suc-inj-< x)


  suc-inj-< : suc i < suc j → i < j
  suc-inj-< (≤→<S x) = S≤→< x
  suc-inj-< (suc-cong x) = x


  S≤→< : suc i ≤ j → i < j
  S≤→< refl = ≤→<S refl
  S≤→< (<→≤ x) = S<→< x


  S≤→≤ : suc i ≤ j → i ≤ j
  S≤→≤ x = <→≤ (S≤→< x)


  S<→< : suc i < j → i < j
  S<→< x = <-trans (≤→<S refl) x


  suc-resp-≤ : i ≤ j → suc i ≤ suc j
  suc-resp-≤ refl = refl
  suc-resp-≤ (<→≤ x) = <→≤ (suc-cong x)


  suc-resp-< : i < j → suc i < suc j
  suc-resp-< = suc-cong


  <→≤→< : i < j → j ≤ k → i < k
  <→≤→< x refl = x
  <→≤→< x (<→≤ x₁) = <-trans x x₁


  ≤→<→< : i ≤ j → j < k → i < k
  ≤→<→< refl x₁ = x₁
  ≤→<→< (<→≤ x) x₁ = <-trans x x₁


  <-trans : i < j → j < k → i < k
  <-trans (var x x₂) x₁ = var x (<→≤ (≤→<→< x₂ x₁))
  <-trans (≤→<S x) (≤→<S x₁) = ≤→<S (≤→<→≤ x (S≤→< x₁))
  <-trans (≤→<S x) (suc-cong x₁) = ≤→<S (≤→<→≤ x x₁)
  <-trans (suc-cong x) (≤→<S x₁) = suc-cong (<-trans x (S≤→< x₁))
  <-trans (suc-cong x) (suc-cong x₁) = suc-cong (<-trans x x₁)


  ≤-trans : i ≤ j → j ≤ k → i ≤ k
  ≤-trans refl x₁ = x₁
  ≤-trans (<→≤ x) x₁ = <→≤→≤ x x₁


  ≤∞-trans : n ≤∞ m → m ≤∞ o → n ≤∞ o
  ≤∞-trans (si x) (si x₁) = si (≤-trans x x₁)
  ≤∞-trans ∞ x₁ = x₁


  <→≤→≤ : i < j → j ≤ k → i ≤ k
  <→≤→≤ x x₁ = <→≤ (<→≤→< x x₁)


  ≤→<→≤ : i ≤ j → j < k → i ≤ k
  ≤→<→≤ x x₁ = <→≤ (≤→<→< x x₁)


  <∞-var : Bound∞ α n → n ≤∞ m → var α <∞ m
  <∞-var x (si x₁) = si (var (Bound∞→Bound x) x₁)
  <∞-var x ∞ = ∞


  ≤∞-refl : n ≤∞ n
  ≤∞-refl {n = si i} = si refl
  ≤∞-refl {n = ∞} = ∞


  <∞-var′ : Bound∞ α n → var α <∞ n
  <∞-var′ x = <∞-var x ≤∞-refl


  <∞→≤∞→≤ : i <∞ n → n ≤∞ si j → i ≤ j
  <∞→≤∞→≤ (si x) (si x₁) = <→≤→≤ x x₁


wkSi≮varzero : wkSi {n = n} i < var zero → ⊥
wkSi≮varzero {i = var α} (var (suc x x₁) refl) = wkSi≢varzero x
wkSi≮varzero {i = var α} (var (suc refl x₂) (<→≤ x₁)) = wkSi≮varzero x₁


≮varzero : i < var zero → ⊥
≮varzero (var (zero p x) refl)       = ⊥-elim (wkSi≢varzero x)
≮varzero (var (zero p refl) (<→≤ x)) = ⊥-elim (wkSi≮varzero x)
≮varzero (var (suc x x₁) refl)       = ⊥-elim (wkSi≢varzero x)
≮varzero (var (suc refl x₂) (<→≤ x)) = ⊥-elim (wkSi≮varzero x)


mutual
  wkSi-inj-≤ : wkSi {n = n} i ≤ wkSi j → i ≤ j
  wkSi-inj-≤ {i = var α} {var .α} refl = refl
  wkSi-inj-≤ {i = var α} {var β} (<→≤ (var (suc refl x₂) x₁))
    = <→≤ (var x₂ (wkSi-inj-≤ x₁))
  wkSi-inj-≤ {i = var α} {suc j} (<→≤ x) = <→≤ (wkSi-inj-< x)
  wkSi-inj-≤ {i = suc i} {var α} (<→≤ x) = <→≤ (wkSi-inj-< x)
  wkSi-inj-≤ {i = suc i} {suc j} x
    = suc-resp-≤ (wkSi-inj-≤ {i = i} {j = j} (suc-inj-≤ x))


  wkSi-inj-< : wkSi {n = n} i < wkSi j → i < j
  wkSi-inj-< {i = var α} {var β} (var (suc refl x₁) x₂)
    = var x₁ (wkSi-inj-≤ x₂)
  wkSi-inj-< {i = var α} {suc j} (var (suc {i = i} refl x₂) x₁)
    = var x₂ (wkSi-inj-≤ {i = i} {j = suc j} x₁)
  wkSi-inj-< {i = var α} {suc j} (≤→<S x) = ≤→<S (wkSi-inj-≤ x)
  wkSi-inj-< {i = suc i} {suc j} x
    = suc-resp-< (wkSi-inj-< (suc-inj-< x))


Bound→<V : Bound α (var β) → α <V β
Bound→<V {β = zero} (zero p x) = ⊥-elim (wkSi≢varzero x)
Bound→<V {β = suc β} (zero p x) = zero
Bound→<V {β = zero} (suc x x₁) = ⊥-elim (wkSi≢varzero x)
Bound→<V {β = suc β} (suc x x₁) rewrite wkSi≡suc-inv x = suc (Bound→<V x₁)


Bound<→<V : Bound α i → i < var β → α <V β
Bound<→<V {β = zero} (zero p x) x₁ = ⊥-elim (≮varzero x₁)
Bound<→<V {β = suc β} (zero p x) x₁ = zero
Bound<→<V {β = zero} (suc x x₂) x₁ = ⊥-elim (≮varzero x₁)
Bound<→<V {β = suc {n = n} β} (suc {i = i} refl x₂) x₁
  = suc (Bound<→<V x₂ (wkSi-inj-< x₁))


<var-inv : i < var β → ∃[ α ] (i ≡ var α × α <V β)
<var-inv {β = β} (var {α} x refl) = α , refl , Bound→<V x
<var-inv (var {γ} x (<→≤ x₁)) = γ , refl , Bound<→<V x x₁


mutual
  renSi-resp-≤ : (θ : Δ′ ⊇ Δ) → i ≤ j → renSi θ i ≤ renSi θ j
  renSi-resp-≤ θ refl = refl
  renSi-resp-≤ θ (<→≤ i<j) = <→≤ (renSi-resp-< θ i<j)


  renSi-resp-< : (θ : Δ′ ⊇ Δ) → i < j → renSi θ i < renSi θ j
  renSi-resp-< {j = j} θ (var {α} bαi i≤j) = var (Bound-ren bαi) (renSi-resp-≤ θ i≤j)
  renSi-resp-< θ (≤→<S i≤j) = ≤→<S (renSi-resp-≤ θ i≤j)
  renSi-resp-< θ (suc-cong i<j) = suc-cong (renSi-resp-< θ i<j)


  renSi-resp-≤∞ : (θ : Δ′ ⊇ Δ) → n ≤∞ m → renSi∞ θ n ≤∞ renSi∞ θ m
  renSi-resp-≤∞ θ (si i≤j) = si (renSi-resp-≤ θ i≤j)
  renSi-resp-≤∞ θ ∞ = ∞


renSi-resp-<∞ : (θ : Δ′ ⊇ Δ) → i <∞ n → renSi θ i <∞ renSi∞ θ n
renSi-resp-<∞ θ (si i<j) = si (renSi-resp-< θ i<j)
renSi-resp-<∞ θ ∞ = ∞


wkSi-resp-< : i < j → wkSi {n = n} i < wkSi j
wkSi-resp-< {i = i} {j} {n} i<j
  rewrite wkSi≡renSi {n = n} {i} | wkSi≡renSi {n = n} {j}
  = renSi-resp-< weak′ i<j


wkSi-resp-≤ : i ≤ j → wkSi {n = n} i ≤ wkSi j
wkSi-resp-≤ {i = i} {j} {n} i≤j
  rewrite wkSi≡renSi {n = n} {i} | wkSi≡renSi {n = n} {j}
  = renSi-resp-≤ weak′ i≤j


wkSi-resp-<∞ : i <∞ n → wkSi {n = m} i <∞ wkSi∞ n
wkSi-resp-<∞ {i = i} {n} {m} i<n
  rewrite wkSi≡renSi {n = m} {i} | wkSi∞≡renSi∞ {n = m} {n}
  = renSi-resp-<∞ weak′ i<n


wkSi-resp-≤∞ : n ≤∞ m → wkSi∞ {n = o} n ≤∞ wkSi∞ m
wkSi-resp-≤∞ {n = n} {m} {o} n≤m
  rewrite wkSi∞≡renSi∞ {n = o} {n} | wkSi∞≡renSi∞ {n = o} {m}
  = renSi-resp-≤∞ weak′ n≤m


--------------------------------------------------------------------------------
-- Substitutions
--------------------------------------------------------------------------------


mutual
  -- Size substitutions. SS Δ Δ′ is a morphism from Δ to Δ′, viewing both as
  -- product categories.
  data SS : (Δ Δ′ : SC) → Set where
    [] : SS Δ []
    _∷[_]_
      : (σ : SS Δ Δ′)
      → (i : Si Δ) {n : Si∞ Δ′} (i<n : i <∞ subSi∞ σ n)
      → SS Δ (Δ′ ∷ n)


  subSV : (σ : SS Δ Δ′) (α : SV Δ′) → Si Δ
  subSV (σ ∷[ i ] i<j) zero    = i
  subSV (σ ∷[ i ] i<j) (suc α) = subSV σ α


  subSi : (σ : SS Δ Δ′) (i : Si Δ′) → Si Δ
  subSi σ (var α) = subSV σ α
  subSi σ (suc i) = suc (subSi σ i)


  subSi∞ : (σ : SS Δ Δ′) (n : Si∞ Δ′) → Si∞ Δ
  subSi∞ σ (si i) = si (subSi σ i)
  subSi∞ σ ∞ = ∞


variable
  σ τ : SS Δ Δ′


subSi-[] : (i : Si []) → subSi [] i ≡ renSi [] i
subSi-[] (suc i) = ≡.cong suc (subSi-[] i)


mutual
  weakS : SS Δ Δ′ → SS (Δ ∷ n) Δ′
  weakS [] = []
  weakS (_∷[_]_ σ i {j} i<j)
    = weakS σ ∷[ wkSi i ]
      ≡.subst (λ z → wkSi i <∞ z) (≡.sym (subSi∞-weakS σ j)) (wkSi-resp-<∞ i<j)


  subSi∞-weakS : ∀ (σ : SS Δ Δ′) m
    → subSi∞ (weakS {n = n} σ) m ≡ wkSi∞ (subSi∞ σ m)
  subSi∞-weakS σ (si i) = ≡.cong si (subSi-weakS σ i)
  subSi∞-weakS σ ∞ = refl


  subSi-weakS : ∀ (σ : SS Δ Δ′) i
    → subSi (weakS {n = n} σ) i ≡ wkSi (subSi σ i)
  subSi-weakS σ (var α) = subSV-weakS σ α
  subSi-weakS σ (suc i) = ≡.cong suc (subSi-weakS σ i)


  subSV-weakS :  ∀ (σ : SS Δ Δ′) α
    →  subSV (weakS {n = n} σ) α ≡ wkSi (subSV σ α)
  subSV-weakS (σ ∷[ i ] i<j) zero = refl
  subSV-weakS (σ ∷[ i ] i<j) (suc α) = subSV-weakS σ α


mutual
  idS : SS Δ Δ
  idS {[]} = []
  idS {Δ ∷ n}
    = weakS idS ∷[ var zero ]
      <∞-var′
        (≡.subst (Bound∞ zero)
          (≡.sym
            (≡.trans (subSi∞-weakS idS n) (≡.cong wkSi∞ subSi∞-id))) (zero refl))


  subSi∞-id : subSi∞ idS n ≡ n
  subSi∞-id {n = si i} = ≡.cong si subSi-id
  subSi∞-id {n = ∞} = refl


  subSi-id : subSi idS i ≡ i
  subSi-id {i = var α} = subSV-id
  subSi-id {i = suc i} = ≡.cong suc subSi-id


  subSV-id : subSV idS α ≡ var α
  subSV-id {α = zero} = refl
  subSV-id {α = suc {n = n} α}
    rewrite subSV-weakS {n = n} idS α
          | subSV-id {α = α}
    = refl


weakS′ : SS (Δ ∷ n) Δ
weakS′ = weakS idS


subSi-∷-wk : (σ : SS Δ Δ′) {i : Si Δ}  {i<n : i <∞ subSi∞ σ n} (j : Si Δ′)
  → subSi (σ ∷[ i ] i<n) (wkSi j) ≡ subSi σ j
subSi-∷-wk σ (var α) = refl
subSi-∷-wk σ (suc j) = ≡.cong suc (subSi-∷-wk σ j)


mutual
  subSi-resp-≤ : (σ : SS Δ Δ′) → i ≤ j → subSi σ i ≤ subSi σ j
  subSi-resp-≤ σ refl = refl
  subSi-resp-≤ σ (<→≤ i<j) = <→≤ (subSi-resp-< σ i<j)


  subSi-resp-< : (σ : SS Δ Δ′) → i < j → subSi σ i < subSi σ j
  subSi-resp-< {i = var α} {j} σ i<j = subSV-subSi-resp-< σ i<j
  subSi-resp-< {i = suc i} {suc j} σ (≤→<S Si≤j) = suc-cong (subSi-resp-< σ (S≤→< Si≤j))
  subSi-resp-< {i = suc i} {suc j} σ (suc-cong i<j) = suc-cong (subSi-resp-< σ i<j)


  subSV-subSi-resp-≤ : (σ : SS Δ Δ′) → var α ≤ i → subSV σ α ≤ subSi σ i
  subSV-subSi-resp-≤ σ refl = refl
  subSV-subSi-resp-≤ σ (<→≤ α<i) = <→≤ (subSV-subSi-resp-< σ α<i)


  subSV-subSi-resp-< : (σ : SS Δ Δ′) → var α < i → subSV σ α < subSi σ i
  subSV-subSi-resp-< {i = i} σ (var x x₁) = <→≤→< (subSi-resp-<-var σ x) (subSi-resp-≤ σ x₁)
  subSV-subSi-resp-< {i = .(suc _)} σ (≤→<S x) = ≤→<S (subSV-subSi-resp-≤ σ x)


  subSi-resp-<-var : (σ : SS Δ Δ′) → Bound α i → subSV σ α < subSi σ i
  subSi-resp-<-var {α = zero} (σ ∷[ i ] si i<k) (zero {i = j}refl refl)
    = ≡.subst (i <_) (≡.sym (subSi-∷-wk σ j)) i<k
  subSi-resp-<-var {α = suc α} (σ ∷[ i ] i<n) (suc {i = j} refl p)
    = ≡.subst (subSV σ α <_) (≡.sym (subSi-∷-wk σ j)) (subSi-resp-<-var σ p)


subSi∞-resp-≤ : (σ : SS Δ Δ′) → n ≤∞ m → subSi∞ σ n ≤∞ subSi∞ σ m
subSi∞-resp-≤ σ (si i≤j) = si (subSi-resp-≤ σ i≤j)
subSi∞-resp-≤ σ ∞ = ≤∞-refl


subSi∞-resp-< : (σ : SS Δ Δ′) → i <∞ n → subSi σ i <∞ subSi∞ σ n
subSi∞-resp-< σ (si i<j) = si (subSi-resp-< σ i<j)
subSi∞-resp-< σ ∞ = ∞


mutual
  _∙ₛ_ : (σ : SS Δ′ Δ″) (τ : SS Δ Δ′) → SS Δ Δ″
  [] ∙ₛ τ = []
  (_∷[_]_ σ i {n} i<n) ∙ₛ τ
    = σ ∙ₛ τ ∷[ subSi τ i ]
      ≡.subst (subSi τ i <∞_) (≡.sym (subSi∞-∙ₛ σ τ n)) (subSi∞-resp-< τ i<n)


  subSi∞-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) n
    → subSi∞ (σ ∙ₛ θ) n ≡ subSi∞ θ (subSi∞ σ n)
  subSi∞-∙ₛ σ θ (si i) = ≡.cong si (subSi-∙ₛ σ θ i)
  subSi∞-∙ₛ σ θ ∞ = refl


  subSi-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) i
    → subSi (σ ∙ₛ θ) i ≡ subSi θ (subSi σ i)
  subSi-∙ₛ σ θ (var α) = subSV-∙ₛ σ θ α
  subSi-∙ₛ σ θ (suc i) = ≡.cong suc (subSi-∙ₛ σ θ i)


  subSV-∙ₛ : ∀ (σ : SS Δ′ Δ″) (θ : SS Δ Δ′) α
    → subSV (σ ∙ₛ θ) α ≡ subSi θ (subSV σ α)
  subSV-∙ₛ (σ ∷[ i ] i<n) θ zero = refl
  subSV-∙ₛ (σ ∷[ i ] i<n) θ (suc α) = subSV-∙ₛ σ θ α


liftS : (σ : SS Δ Δ′) → subSi∞ σ m ≡ n → SS (Δ ∷ n) (Δ′ ∷ m)
liftS σ p
  = weakS σ ∷[ var zero ]
    <∞-var′ (zero (≡.sym (≡.trans (subSi∞-weakS σ _) (≡.cong wkSi∞ p))))


mutual
  ⊇→SS : Δ ⊇ Δ′ → SS Δ Δ′
  ⊇→SS [] = []
  ⊇→SS (weak θ) = weakS (⊇→SS θ)
  ⊇→SS (lift θ p) = liftS (⊇→SS θ) (≡.trans (subSi∞-⊇→SS θ _) p)


  subSi∞-⊇→SS : ∀ (θ : Δ ⊇ Δ′) n
    → subSi∞ (⊇→SS θ) n ≡ renSi∞ θ n
  subSi∞-⊇→SS θ (si i) = ≡.cong si (subSi-⊇→SS θ i)
  subSi∞-⊇→SS θ ∞ = refl


  subSi-⊇→SS : ∀ (θ : Δ ⊇ Δ′) i
    → subSi (⊇→SS θ) i ≡ renSi θ i
  subSi-⊇→SS θ (var α) = subSV-⊇→SS θ α
  subSi-⊇→SS θ (suc i) = ≡.cong suc (subSi-⊇→SS θ i)


  subSV-⊇→SS : ∀ (θ : Δ ⊇ Δ′) α
    → subSV (⊇→SS θ) α ≡ var (renSV θ α)
  subSV-⊇→SS (weak θ) α
    = ≡.trans (subSV-weakS (⊇→SS θ) α) (≡.cong wkSi (subSV-⊇→SS θ α))
  subSV-⊇→SS (lift θ p) zero = refl
  subSV-⊇→SS (lift θ p) (suc α)
    = ≡.trans (subSV-weakS (⊇→SS θ) α) (≡.cong wkSi (subSV-⊇→SS θ α))


mutual
  _ₛ∙ᵣ_ : (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) → SS Δ Δ″
  [] ₛ∙ᵣ θ = []
  (_∷[_]_ σ i {j} i<j) ₛ∙ᵣ θ
    = (σ ₛ∙ᵣ θ) ∷[ renSi θ i ]
      ≡.subst (renSi θ i <∞_) (≡.sym (subSi∞-ₛ∙ᵣ σ θ j)) (renSi-resp-<∞ θ i<j)


  subSi∞-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) n
    → subSi∞ (σ ₛ∙ᵣ θ) n ≡ renSi∞ θ (subSi∞ σ n)
  subSi∞-ₛ∙ᵣ σ θ (si i) = ≡.cong si (subSi-ₛ∙ᵣ σ θ i)
  subSi∞-ₛ∙ᵣ σ θ ∞ = refl


  subSi-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) j
    → subSi (σ ₛ∙ᵣ θ) j ≡ renSi θ (subSi σ j)
  subSi-ₛ∙ᵣ σ θ (var α) = subSV-ₛ∙ᵣ σ θ α
  subSi-ₛ∙ᵣ σ θ (suc j) = ≡.cong suc (subSi-ₛ∙ᵣ σ θ j)


  subSV-ₛ∙ᵣ : ∀ (σ : SS Δ′ Δ″) (θ : Δ ⊇ Δ′) α
    → subSV (σ ₛ∙ᵣ θ) α ≡ renSi θ (subSV σ α)
  subSV-ₛ∙ᵣ (σ ∷[ i ] i<j) θ zero = refl
  subSV-ₛ∙ᵣ (σ ∷[ i ] i<j) θ (suc α) = subSV-ₛ∙ᵣ σ θ α
