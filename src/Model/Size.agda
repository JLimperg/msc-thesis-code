{-# OPTIONS --without-K #-} --TODO
module Model.Size where

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Fun using (Fun)
open import Cats.Category.Fun.Facts using (≅→≈ ; ≈→≅)
open import Cats.Category.One using (One)
open import Cats.Category.Preorder using (preorderAsCategory)
open import Cats.Functor using (Functor)
open import Cats.Functor.Const using (Const)
open import Cats.Trans.Iso using (NatIso)
open import Relation.Binary using (Rel ; Preorder ; IsPreorder)

import Data.Nat as ℕ
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.Construct.On as On

open import Model.RGraph as RG using (RGraph)
open import Source.Size as S using (Δ ; Ω ; _⊢_ ; ⊢_)
open import Source.Size.Substitution.Universe using (⟨_⟩ ; Sub⊢ᵤ)
open import Util.HoTT.HLevel
open import Util.HoTT.Univalence
open import Util.Induction.WellFounded as WFInd using (Acc ; acc ; WellFounded)
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality as ≡ using (cong₂-dep)

import Source.Size.Substitution.Canonical as SC
import Source.Size.Substitution.Universe as S

open Functor
open S.Ctx
open S.Size
open S.Sub
open S.Sub⊢ᵤ
open S.Var
open S._<_
open S._≤_


infix 4 _<_ _≤_
infixr 5 _ₙ⊓_ _⊓_


private
  module Fun {lo la l≈ lo′ la′ l≈′}
    {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    = Category (Fun C D)


  module Cat {lo la l≈} = Category (Cat lo la l≈)


data Size : Set where
  nat : (n : ℕ) → Size
  ∞ ⋆ : Size


variable n m o : Size


abstract
  nat-inj-Size : ∀ {n m} → nat n ≡ nat m → n ≡ m
  nat-inj-Size refl = refl


  nat≡-prop-Size : ∀ {n m} (p : nat n ≡ nat m) → p ≡ cong nat (nat-inj-Size p)
  nat≡-prop-Size refl = refl


Size-IsSet : IsSet Size
Size-IsSet {nat n} {.(nat n)} p refl
  = trans (nat≡-prop-Size p) (cong (cong nat) (ℕ.≡-irrelevant _ _))
Size-IsSet {∞} {.∞} refl refl = refl
Size-IsSet {⋆} {.⋆} refl refl = refl


data _<_ : (n m : Size) → Set where
  nat : ∀ {n m} → n ℕ.< m → nat n < nat m
  nat<∞ : ∀ {n} → nat n < ∞
  nat<⋆ : ∀ {n} → nat n < ⋆
  ∞<⋆ : ∞ < ⋆


data _≤_ : (n m : Size) → Set where
  reflexive : n ≡ m → n ≤ m
  <→≤ : n < m → n ≤ m


pattern ≤-refl = reflexive refl


abstract
  <-trans : n < m → m < o → n < o
  <-trans (nat n<m) (nat m<o) = nat (ℕ.<-trans n<m m<o)
  <-trans (nat n<m) nat<∞ = nat<∞
  <-trans (nat n<m) nat<⋆ = nat<⋆
  <-trans nat<∞ ∞<⋆ = nat<⋆


  ≤→<→< : n ≤ m → m < o → n < o
  ≤→<→< ≤-refl m<o = m<o
  ≤→<→< (<→≤ n<m) m<o = <-trans n<m m<o


  <→≤→< : n < m → m ≤ o → n < o
  <→≤→< n<m ≤-refl = n<m
  <→≤→< n<m (<→≤ m<o) = <-trans n<m m<o


  ≤-trans : n ≤ m → m ≤ o → n ≤ o
  ≤-trans n≤m ≤-refl = n≤m
  ≤-trans n≤m (<→≤ m<o) = <→≤ (≤→<→< n≤m m<o)


≤-IsPreorder : IsPreorder _≡_ _≤_
≤-IsPreorder = record
  { isEquivalence = ≡.isEquivalence
  ; reflexive = λ { refl → ≤-refl }
  ; trans = ≤-trans
  }


≤-Preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-Preorder = record { isPreorder = ≤-IsPreorder }


abstract
  <-irrefl : ¬ (n < n)
  <-irrefl (nat n<n) = ℕ.<-irrefl refl n<n


  ≤-antisym : n ≤ m → m ≤ n → n ≡ m
  ≤-antisym ≤-refl m≤n = refl
  ≤-antisym (<→≤ n<m) m≤n = ⊥-elim (<-irrefl (<→≤→< n<m m≤n))


  <ℕ-acc→<-acc : ∀ {n} → Acc ℕ._<_ n → Acc _<_ (nat n)
  <ℕ-acc→<-acc (acc rs) = acc λ where
    (nat m) (nat m<n) → <ℕ-acc→<-acc (rs m m<n)


  <-acc-nat : ∀ {n} → Acc _<_ (nat n)
  <-acc-nat = <ℕ-acc→<-acc (ℕ.<-wellFounded _)


  <-acc : n < m → Acc _<_ n
  <-acc {nat n} {nat m} (nat n<m) = <-acc-nat
  <-acc {nat n} {∞} nat<∞ = <-acc-nat
  <-acc {nat n} {⋆} nat<⋆ = <-acc-nat
  <-acc {∞} {.⋆} ∞<⋆ = acc λ where
    .(nat _) nat<∞ → <-acc-nat


  <-wf : WellFounded _<_
  <-wf x = acc (λ y y<x → <-acc y<x)


open WFInd.Build <-wf public using () renaming
  ( wfInd to <-ind
  ; wfRec to <-rec
  ; wfInd-unfold to <-ind-unfold
  ; wfRec-unfold to <-rec-unfold
  ; wfInd-ind to <-ind-ind
  ; wfIndΣ to <-indΣ
  ; wfIndΣ-unfold to <-indΣ-unfold
  ; wfIndΣ′ to <-indΣ′
  )


<-ind-ind₂ = WFInd.wfInd-ind₂ <-wf


abstract
  <-prop : (p q : n < m) → p ≡ q
  <-prop (nat p) (nat q) = cong nat (ℕ.<-irrelevant p q)
  <-prop nat<∞ nat<∞ = refl
  <-prop nat<⋆ nat<⋆ = refl
  <-prop ∞<⋆ ∞<⋆ = refl


  nat-inj-< : ∀ {n m} → nat n < nat m → n ℕ.< m
  nat-inj-< (nat n<m) = n<m


  nat-inj-≤ : ∀ {n m} → nat n ≤ nat m → n ℕ.≤ m
  nat-inj-≤ ≤-refl = ℕ.≤-refl
  nat-inj-≤ (<→≤ n<m) = ℕ.<⇒≤ (nat-inj-< n<m)


  n≤n-contr : (p : n ≤ n) → p ≡ reflexive refl
  n≤n-contr (reflexive x) = cong reflexive (Size-IsSet _ _)
  n≤n-contr (<→≤ n<n) = ⊥-elim (<-irrefl n<n)


  ≤-prop : (p q : n ≤ m) → p ≡ q
  ≤-prop ≤-refl q = sym (n≤n-contr q)
  ≤-prop (<→≤ n<n) ≤-refl = ⊥-elim (<-irrefl n<n)
  ≤-prop (<→≤ n<m) (<→≤ n<m₁) = cong <→≤ (<-prop _ _)


  ≤-nat⁺ : ∀ {n m} → n ℕ.≤ m → nat n ≤ nat m
  ≤-nat⁺ {m = zero} ℕ.z≤n = ≤-refl
  ≤-nat⁺ {m = suc m} ℕ.z≤n = <→≤ (nat (ℕ.s≤s ℕ.z≤n))
  ≤-nat⁺ (ℕ.s≤s n≤m) with ≤-nat⁺ n≤m
  ... | ≤-refl = ≤-refl
  ... | <→≤ (nat n<m) = <→≤ (nat (ℕ.s≤s n<m))


  0≤n : nat 0 ≤ n
  0≤n {nat zero} = ≤-refl
  0≤n {nat (suc n)} = <→≤ (nat (ℕ.s≤s ℕ.z≤n))
  0≤n {∞} = <→≤ nat<∞
  0≤n {⋆} = <→≤ nat<⋆


Sizes : Category 0ℓ 0ℓ 0ℓ
Sizes = preorderAsCategory ≤-Preorder


module Sizes = Category Sizes


abstract
  Sizes-univalent : n Sizes.≅ m → n ≡ m
  Sizes-univalent n≅m = ≤-antisym (Category._≅_.forth n≅m) (Category._≅_.back n≅m)


-- The following two lemmas could be generalised to functors into any
-- thin/univalent category.
≅F⁺ : ∀ {lo la l≈} {C : Category lo la l≈} {F G : Functor C Sizes}
  → (∀ {c} → fobj F c ≡ fobj G c)
  → F Fun.≅ G
≅F⁺ F≡G = ≈→≅ (record { iso = Sizes.≅.reflexive F≡G })


≅F⁻ : ∀ {lo la l≈} {C : Category lo la l≈} {F G : Functor C Sizes}
  → F Fun.≅ G
  → ∀ {c} → fobj F c ≡ fobj G c
≅F⁻ F≅G = Sizes-univalent (NatIso.iso (≅→≈ F≅G))


Size< : Size → Set
Size< n = ∃[ m ] (m < n)


abstract
  Size<-≡⁺ : (m k : Size< n) → proj₁ m ≡ proj₁ k → m ≡ k
  Size<-≡⁺ (m , _) (k , _) refl = cong (m ,_) (<-prop _ _)


Size<-IsSet : ∀ {n} → IsSet (Size< n)
Size<-IsSet = Σ-IsSet Size-IsSet (λ _ → IsOfHLevel-suc 1 <-prop)


≤-Preorder-< : Size → Preorder 0ℓ 0ℓ 0ℓ
≤-Preorder-< n = record
  { Carrier = Size< n
  ; isPreorder = On.isPreorder proj₁ ≤-IsPreorder
  }


Sizes< : Size → Category 0ℓ 0ℓ 0ℓ
Sizes< n = preorderAsCategory (≤-Preorder-< n)


module Sizes< {n} = Category (Sizes< n)


Sizes<-≅⁺
  : n ≡ m
  → {n<o : n < o} {m<o : m < o}
  → (n , n<o) Sizes<.≅ (m , m<o)
Sizes<-≅⁺ n≡m = record
  { forth = reflexive n≡m
  ; back = reflexive (sym n≡m)
  }


Sizes<F : Functor Sizes (Cat 0ℓ 0ℓ 0ℓ)
Sizes<F = record
  { fobj = Sizes<
  ; fmap = λ n≤m → record
    { fobj = λ { (o , o<n) → o , <→≤→< o<n n≤m }
    ; fmap = id
    }
  ; fmap-resp = λ _ → record { iso = Sizes<-≅⁺ refl }
  ; fmap-id = record { iso = Sizes<-≅⁺ refl }
  ; fmap-∘ = record { iso = Sizes<-≅⁺ refl }
  }


Sizes<→Sizes : ∀ {n} → Functor (Sizes< n) Sizes
Sizes<→Sizes = record
  { fobj = proj₁
  ; fmap = id
  }


szero : Size
szero = nat zero


ssuc : Size → Size
ssuc (nat n) = nat (suc n)
ssuc ∞ = ∞
ssuc ⋆ = ⋆


abstract
  ssuc-resp-< : n < m → ssuc n < ssuc m
  ssuc-resp-< (nat n<m) = nat (ℕ.+-mono-≤-< ℕ.≤-refl n<m)
  ssuc-resp-< nat<∞ = nat<∞
  ssuc-resp-< nat<⋆ = nat<⋆
  ssuc-resp-< ∞<⋆ = ∞<⋆


  ssuc-resp-≤ : n ≤ m → ssuc n ≤ ssuc m
  ssuc-resp-≤ ≤-refl = ≤-refl
  ssuc-resp-≤ (<→≤ n<m) = <→≤ (ssuc-resp-< n<m)


  szero<ssuc : n < ∞ → szero < ssuc n
  szero<ssuc nat<∞ = nat (ℕ.s≤s ℕ.z≤n)


ssucF : Functor Sizes Sizes
ssucF = record
  { fobj = ssuc
  ; fmap = ssuc-resp-≤
  }


_ₙ⊓_ : ℕ → Size → ℕ
n ₙ⊓ nat m = n ℕ.⊓ m
n ₙ⊓ ∞ = n
n ₙ⊓ ⋆ = n


_⊓_ : Size → Size → Size
nat n ⊓ m = nat (n ₙ⊓ m)
∞ ⊓ nat n = nat n
∞ ⊓ ∞ = ∞
∞ ⊓ ⋆ = ∞
⋆ ⊓ m = m


abstract
  nₙ⊓m≤m : ∀ n m → nat (n ₙ⊓ m) ≤ m
  nₙ⊓m≤m n (nat m) = ≤-nat⁺ (ℕ.m⊓n≤n n m)
  nₙ⊓m≤m n ∞ = <→≤ nat<∞
  nₙ⊓m≤m n ⋆ = <→≤ nat<⋆


  n≤m→nₙ⊓m≡n : ∀ {n m} → nat n ≤ m → n ₙ⊓ m ≡ n
  n≤m→nₙ⊓m≡n ≤-refl = ℕ.m≤n⇒m⊓n≡m ℕ.≤-refl
  n≤m→nₙ⊓m≡n (<→≤ (nat n<m)) = ℕ.m≤n⇒m⊓n≡m (ℕ.<⇒≤ n<m)
  n≤m→nₙ⊓m≡n (<→≤ nat<∞) = refl
  n≤m→nₙ⊓m≡n (<→≤ nat<⋆) = refl


  ₙ⊓-assoc : ∀ n m o → (n ₙ⊓ m) ₙ⊓ o ≡ n ₙ⊓ (m ⊓ o)
  ₙ⊓-assoc n (nat m) (nat o) = ℕ.⊓-assoc n m o
  ₙ⊓-assoc n (nat m) ∞ = refl
  ₙ⊓-assoc n (nat m) ⋆ = refl
  ₙ⊓-assoc n ∞ (nat o) = refl
  ₙ⊓-assoc n ∞ ∞ = refl
  ₙ⊓-assoc n ∞ ⋆ = refl
  ₙ⊓-assoc n ⋆ o = refl


  n≤m→n⊓m≡n : ∀ {n m} → n ≤ m → n ⊓ m ≡ n
  n≤m→n⊓m≡n {nat n} {m} n≤m = cong nat (n≤m→nₙ⊓m≡n n≤m)
  n≤m→n⊓m≡n {∞} {.∞} ≤-refl = refl
  n≤m→n⊓m≡n {∞} {.⋆} (<→≤ ∞<⋆) = refl
  n≤m→n⊓m≡n {⋆} {.⋆} ≤-refl = refl


  ⊓-comm : ∀ n m → n ⊓ m ≡ m ⊓ n
  ⊓-comm (nat n) (nat m) = cong nat (ℕ.⊓-comm n m)
  ⊓-comm (nat n) ∞ = refl
  ⊓-comm (nat n) ⋆ = refl
  ⊓-comm ∞ (nat n) = refl
  ⊓-comm ∞ ∞ = refl
  ⊓-comm ∞ ⋆ = refl
  ⊓-comm ⋆ (nat n) = refl
  ⊓-comm ⋆ ∞ = refl
  ⊓-comm ⋆ ⋆ = refl


  m≤n→n⊓m≡m : ∀ {n m} → m ≤ n → n ⊓ m ≡ m
  m≤n→n⊓m≡m {n} {m} m≤n = trans (⊓-comm n m) (n≤m→n⊓m≡n m≤n)


  0ₙ⊓n≡0 : ∀ n → 0 ₙ⊓ n ≡ 0
  0ₙ⊓n≡0 (nat n) = refl
  0ₙ⊓n≡0 ∞ = refl
  0ₙ⊓n≡0 ⋆ = refl


  n<m→Sn≤m : ∀ {n} → nat n < m → nat (suc n) ≤ m
  n<m→Sn≤m (nat (ℕ.s≤s n≤m)) = ≤-nat⁺ (ℕ.s≤s n≤m)
  n<m→Sn≤m nat<∞ = <→≤ nat<∞
  n<m→Sn≤m nat<⋆ = <→≤ nat<⋆


  Sn≤m→n<m : ∀ {n} → nat (suc n) ≤ m → nat n < m
  Sn≤m→n<m ≤-refl = nat (ℕ.s≤s ℕ.≤-refl)
  Sn≤m→n<m (<→≤ (nat Sn<m)) = nat (ℕ.<-trans (ℕ.s≤s ℕ.≤-refl) Sn<m)
  Sn≤m→n<m (<→≤ nat<∞) = nat<∞
  Sn≤m→n<m (<→≤ nat<⋆) = nat<⋆


mutual
  ⟦_⟧Δ : S.Ctx → Category 0ℓ 0ℓ 0ℓ
  ⟦ [] ⟧Δ = One _ _ _
  ⟦ Δ ∙ n ⟧Δ = record
    { Obj = Σ[ δ ∈ Δ.Obj ] Category.Obj (Sizes< (fobj ⟦ n ⟧n δ))
    ; _⇒_ = λ { (δ , m , m<n) (γ , o , o<n) → (δ Δ.⇒ γ) × m ≤ o }
    ; _≈_ = λ _ _ → ⊤
    ; id = Δ.id , ≤-refl
    ; _∘_ = λ { (f , p) (g , q) → f Δ.∘ g , ≤-trans q p }
    }
    where
      module Δ = Category (⟦ Δ ⟧Δ)


  π₂ : ∀ n → Functor ⟦ Δ ∙ n ⟧Δ Sizes
  π₂ n = record
    { fobj = λ { (δ , m , m<n) → m }
    ; fmap = λ { (f , p) → p }
    }


  ⟦_⟧x : S.Var Δ → Functor ⟦ Δ ⟧Δ Sizes
  ⟦ zero ⟧x = π₂ _
  ⟦ suc x ⟧x = record
    { fobj = λ { (δ , m , m<n) → fobj ⟦ x ⟧x δ }
    ; fmap = λ { (f , p) → fmap ⟦ x ⟧x f }
    }
    -- This is ⟦ x ⟧x Cat.∘ π₁, but the termination checker doesn't like that.


  ⟦_⟧n : S.Size Δ → Functor ⟦ Δ ⟧Δ Sizes
  ⟦ var x ⟧n = ⟦ x ⟧x
  ⟦ ∞ ⟧n = Const _ ∞
  ⟦ ⋆ ⟧n = Const _ ⋆
  ⟦ zero ⟧n = Const _ szero
  ⟦ suc n ⟧n = ssucF Cat.∘ ⟦ n ⟧n



abstract
  ⟦Δ⟧-StronglyThin : ∀ Δ → StronglyThin ⟦ Δ ⟧Δ
  ⟦Δ⟧-StronglyThin [] {f = lift tt} {lift tt} = refl
  ⟦Δ⟧-StronglyThin (Δ ∙ n) {f = f , p} {g , q}
    = cong₂ _,_ (⟦Δ⟧-StronglyThin Δ) (≤-prop p q)


  ⟦Δ⟧-Thin : ∀ Δ → Thin ⟦ Δ ⟧Δ
  ⟦Δ⟧-Thin Δ = StronglyThin→Thin {C = ⟦ Δ ⟧Δ} (⟦Δ⟧-StronglyThin Δ)


  ⟦Δ⟧-IsSet : ∀ Δ → IsSet (⟦ Δ ⟧Δ .Category.Obj)
  ⟦Δ⟧-IsSet [] = Lift-IsSet ⊤-IsSet
  ⟦Δ⟧-IsSet (Δ ∙ n) = Σ-IsSet (⟦Δ⟧-IsSet Δ) λ _ → Size<-IsSet


⟦Δ⟧-HSet : S.Ctx → HSet 0ℓ
⟦Δ⟧-HSet Δ = HLevel⁺ (⟦ Δ ⟧Δ .Category.Obj) (⟦Δ⟧-IsSet Δ)


abstract
  ⟦Δ∙n⟧-≡⁺ : ∀ Δ (n : S.Size Δ) {δ δ′ : ⟦ Δ ⟧Δ .Category.Obj} {m m′ : Size}
    → (m<n : m < ⟦ n ⟧n .fobj δ)
    → (m′<n : m′ < ⟦ n ⟧n .fobj δ′)
    → δ ≡ δ′
    → m ≡ m′
    → (δ , m , m<n) ≡ (δ′ , m′ , m′<n)
  ⟦Δ∙n⟧-≡⁺  Δ n {δ} _ _ refl eq₂
    = cong (δ ,_) (Size<-≡⁺ _ _ eq₂)


π₁ : ∀ n → Functor ⟦ Δ ∙ n ⟧Δ ⟦ Δ ⟧Δ
π₁ {Δ} n = record
  { fobj = proj₁
  ; fmap = proj₁
  ; fmap-resp = λ _ → ⟦Δ⟧-Thin Δ
  ; fmap-id = ⟦Δ⟧-Thin Δ
  ; fmap-∘ = ⟦Δ⟧-Thin Δ
  }


_<F_ : ∀ {lo la l≈} {C : Category lo la l≈} → Rel (Functor C Sizes) lo
F <F G = ∀ {δ} → fobj F δ < fobj G δ


_≤F_ : ∀ {lo la l≈} {C : Category lo la l≈} → Rel (Functor C Sizes) lo
F ≤F G = ∀ {δ} → fobj F δ ≤ fobj G δ


⟦wk⟧≅π₁ : (n m : S.Size Δ) → ⟦ S.wk {n = n} m ⟧n Fun.≅ ⟦ m ⟧n Cat.∘ π₁ n
⟦wk⟧≅π₁ n (var x) = ≅F⁺ refl
⟦wk⟧≅π₁ n ∞ = ≅F⁺ refl
⟦wk⟧≅π₁ n ⋆ = ≅F⁺ refl
⟦wk⟧≅π₁ n zero = ≅F⁺ refl
⟦wk⟧≅π₁ n (suc m) = ≈→≅
  let open Cat.≈-Reasoning in
  begin
    ssucF Cat.∘ ⟦ S.wk m ⟧n
  ≈⟨ Cat.∘-resp-r {f = ssucF} (≅→≈ (⟦wk⟧≅π₁ n m)) ⟩
    ssucF Cat.∘ ⟦ m ⟧n Cat.∘ π₁ n
  ≈⟨ Cat.unassoc {f = ssucF} {⟦ m ⟧n} {π₁ n} ⟩
    (ssucF Cat.∘ ⟦ m ⟧n) Cat.∘ π₁ n
  ∎


⟦suc⟧≅π₁ : {n : S.Size Δ} {x : S.Var Δ}
  → ⟦ suc {n = n} x ⟧x Fun.≅ ⟦ x ⟧x Cat.∘ π₁ n
⟦suc⟧≅π₁ = ≅F⁺ refl


abstract
  ⟦<⟧ₓ : (x : S.Var Δ) → ⟦ x ⟧x <F ⟦ S.bound x ⟧n
  ⟦<⟧ₓ (zero {n = n}) {δ , m , m<n}
    = subst (m <_) (sym (≅F⁻ (⟦wk⟧≅π₁ _ n))) m<n
  ⟦<⟧ₓ (suc x) {δ , m , m<n}
    = subst (fobj ⟦ x ⟧x δ <_) (sym (≅F⁻ (⟦wk⟧≅π₁ _ (S.bound x)))) (⟦<⟧ₓ x)


  mutual
    ⟦<⟧ : {n m : S.Size Δ} → n S.< m → ⟦ n ⟧n <F ⟦ m ⟧n
    ⟦<⟧ (var {x = x} b refl b≤n) = <→≤→< (⟦<⟧ₓ x) (⟦≤⟧ b≤n)
    ⟦<⟧ (zero<suc n n<∞) = szero<ssuc (⟦<⟧ n<∞)
    ⟦<⟧ zero<∞ = nat<∞
    ⟦<⟧ (suc<∞ n n<∞) = ssuc-resp-< (⟦<⟧ n<∞)
    ⟦<⟧ zero<⋆ = nat<⋆
    ⟦<⟧ (suc<⋆ n n<∞) = ssuc-resp-< (<-trans (⟦<⟧ n<∞) ∞<⋆)
    ⟦<⟧ ∞<⋆ = ∞<⋆


    ⟦≤⟧ : {n m : S.Size Δ} → n S.≤ m → ⟦ n ⟧n ≤F ⟦ m ⟧n
    ⟦≤⟧ (<→≤ n<m) = <→≤ (⟦<⟧ n<m)
    ⟦≤⟧ S.≤-refl = ≤-refl


mutual
  ⟦_⟧σ : ∀ {σ} → σ ∶ Δ ⇒ᵤ Ω → Functor ⟦ Δ ⟧Δ ⟦ Ω ⟧Δ
  ⟦ Id _ ⟧σ = Cat.id
  ⟦ comp σ τ ⟧σ = ⟦ τ ⟧σ Cat.∘ ⟦ σ ⟧σ
  ⟦ Wk {n = n} ⊢n ⟧σ = π₁ n
  ⟦ Fill {n = n} ⊢n ⊢m n<m ⟧σ = record
    { fobj = λ δ → δ , ⟦ n ⟧n .fobj δ , ⟦<⟧ n<m
    ; fmap = λ δ≤δ′ → δ≤δ′ , ⟦ n ⟧n .fmap δ≤δ′
    }
  ⟦ Keep {σ = σ} {n = n} ⊢σ ⊢n refl ⟧σ = record
    { fobj = λ where
        (δ , m , m<n)
          → ⟦ ⊢σ ⟧σ .fobj δ , m
          , subst (m <_) (⟦sub⟧ ⊢σ n) m<n
    ; fmap = λ { (δ≤δ′ , m≤m′)
        → ⟦ ⊢σ ⟧σ .fmap δ≤δ′ , m≤m′ }
    }
  ⟦ Skip {n = n} ⊢n ⟧σ = record
    { fobj = λ { ((δ , m , m<n) , k , k<m)  → δ , k , <-trans k<m m<n }
    ; fmap = λ { ((δ≤δ′ , m≤m′) , k≤k′) → δ≤δ′ , k≤k′ }
    }


  abstract
    ⟦subV′⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (x : S.Var Ω) {δ}
      → ⟦ S.subV′ σ x ⟧n .fobj δ ≡ ⟦ x ⟧x .fobj (⟦ ⊢σ ⟧σ .fobj δ)
    ⟦subV′⟧ (Id _) x = refl
    ⟦subV′⟧ (comp {σ = σ} {τ = τ} ⊢σ ⊢τ) x
      = trans (⟦sub′⟧ ⊢σ (S.subV′ τ x)) (⟦subV′⟧ ⊢τ x)
    ⟦subV′⟧ (Wk ⊢n) x = refl
    ⟦subV′⟧ (Keep {σ = σ} ⊢σ ⊢n refl) zero = refl
    ⟦subV′⟧ (Keep {σ = σ} {n = n} ⊢σ ⊢n refl) (suc x) {δ}
      rewrite ≅F⁻ (⟦wk⟧≅π₁ (S.sub σ n) (S.subV′ σ x)) {δ}
      = ⟦subV′⟧ ⊢σ x
      -- If we write `trans ? ?` instead of the rewrite, the termination checker
      -- complains.
    ⟦subV′⟧ (Fill ⊢n ⊢m n<m) zero = refl
    ⟦subV′⟧ (Fill ⊢n ⊢m n<m) (suc x) = refl
    ⟦subV′⟧ (Skip ⊢n) zero = refl
    ⟦subV′⟧ (Skip ⊢n) (suc x) = refl


    ⟦sub′⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (n : S.Size Ω) {δ}
      → ⟦ S.sub′ σ n ⟧n .fobj δ ≡ ⟦ n ⟧n .fobj (⟦ ⊢σ ⟧σ .fobj δ)
    ⟦sub′⟧ σ (var x) = ⟦subV′⟧ σ x
    ⟦sub′⟧ σ ∞ = refl
    ⟦sub′⟧ σ ⋆ = refl
    ⟦sub′⟧ σ zero = refl
    ⟦sub′⟧ σ (suc n) = cong ssuc (⟦sub′⟧ σ n)


    ⟦sub⟧ :  ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (n : S.Size Ω) {δ}
      → ⟦ S.sub σ n ⟧n .fobj δ ≡ ⟦ n ⟧n .fobj (⟦ ⊢σ ⟧σ .fobj δ)
    ⟦sub⟧ {σ = σ} ⊢σ n {δ}
      = trans (cong (λ k → ⟦ k ⟧n .fobj δ) (sym (S.sub′≡sub σ n))) (⟦sub′⟧ ⊢σ n)


abstract
  ⟦subV⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (x : S.Var Ω) {δ}
    → ⟦ S.subV σ x ⟧n .fobj δ ≡ ⟦ x ⟧x .fobj (⟦ ⊢σ ⟧σ .fobj δ)
  ⟦subV⟧ {σ = σ} ⊢σ x {δ}
    = trans (cong (λ k → ⟦ k ⟧n .fobj δ) (sym (S.subV′≡subV σ x))) (⟦subV′⟧ ⊢σ x)


  ⟦⟧σ-param : ∀ {σ} (p q : σ ∶ Δ ⇒ᵤ Ω) {δ}
    → ⟦ p ⟧σ .fobj δ ≡ ⟦ q ⟧σ .fobj δ
  ⟦⟧σ-param {σ = Id} (Id ⊢Δ) (Id ⊢Δ₁) = refl
  ⟦⟧σ-param {σ = σ >> τ} (comp p p′) (comp q q′)
    = trans (⟦⟧σ-param p′ q′) (cong (⟦ q′ ⟧σ .fobj) (⟦⟧σ-param p q))
  ⟦⟧σ-param {σ = Wk} (Wk ⊢n) (Wk ⊢n₁) = refl
  ⟦⟧σ-param {Ω = Ω ∙ m} {σ = Keep σ} (Keep p ⊢n refl) (Keep q ⊢n₁ m≡n[σ]₁)
    rewrite S.Size-IsSet m≡n[σ]₁ refl
    = ⟦Δ∙n⟧-≡⁺ Ω m _ _ (⟦⟧σ-param p q) refl
  ⟦⟧σ-param {Δ = Δ} {σ = Fill {m = m} n} (Fill ⊢n ⊢m n<m) (Fill ⊢n₁ ⊢m₁ n<m₁)
    = ⟦Δ∙n⟧-≡⁺ Δ m (⟦<⟧ n<m) (⟦<⟧ n<m₁) refl refl
  ⟦⟧σ-param {σ = Skip} (Skip ⊢n) (Skip ⊢n₁) = refl


⟦_⟧ΔRG : S.Ctx → RGraph
⟦ Δ ⟧ΔRG = record
  { ObjHSet = ⟦Δ⟧-HSet Δ
  ; eqHProp = λ _ _ → ⊤-HProp
  }


SizesRG : RGraph
SizesRG = record
  { ObjHSet = HLevel⁺ Size Size-IsSet
  ; eqHProp = λ _ _ → ⊤-HProp
  }


⟦_⟧nRG : ∀ {Δ} (n : S.Size Δ) → ⟦ Δ ⟧ΔRG RG.⇒ SizesRG
⟦ n ⟧nRG = record
  { fobj = ⟦ n ⟧n .fobj
  }


⟦_⟧σRG : ∀ {Δ Ω σ} → σ ∶ Δ ⇒ᵤ Ω → ⟦ Δ ⟧ΔRG RG.⇒ ⟦ Ω ⟧ΔRG
⟦ σ ⟧σRG = record
  { fobj = ⟦ σ ⟧σ .fobj
  }
