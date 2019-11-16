{-# OPTIONS --without-K #-} --TODO
module Model.Size where

open import Relation.Binary using (Rel ; Preorder ; IsPreorder)

import Data.Nat as ℕ
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.Construct.On as On

open import Model.RGraph as RG using (RGraph)
open import Source.Size as S using (Δ ; Ω)
open import Source.Size.Substitution.Universe using (⟨_⟩ ; Sub⊢ᵤ)
open import Util.HoTT.HLevel
open import Util.Induction.WellFounded as WFInd using (Acc ; acc ; WellFounded)
open import Util.Prelude
open import Util.Relation.Binary.PropositionalEquality as ≡ using (cong₂-dep)

import Source.Size.Substitution.Canonical as SC
import Source.Size.Substitution.Universe as S

open S.Ctx
open S.Size
open S.Sub
open S.Sub⊢ᵤ
open S.Var
open S._<_ hiding (<-trans)


infix 4 _<_ _≤_


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


  n<m→Sn≤m : ∀ {n} → nat n < m → nat (suc n) ≤ m
  n<m→Sn≤m (nat (ℕ.s≤s n≤m)) = ≤-nat⁺ (ℕ.s≤s n≤m)
  n<m→Sn≤m nat<∞ = <→≤ nat<∞
  n<m→Sn≤m nat<⋆ = <→≤ nat<⋆


  Sn≤m→n<m : ∀ {n} → nat (suc n) ≤ m → nat n < m
  Sn≤m→n<m ≤-refl = nat (ℕ.s≤s ℕ.≤-refl)
  Sn≤m→n<m (<→≤ (nat Sn<m)) = nat (ℕ.<-trans (ℕ.s≤s ℕ.≤-refl) Sn<m)
  Sn≤m→n<m (<→≤ nat<∞) = nat<∞
  Sn≤m→n<m (<→≤ nat<⋆) = nat<⋆


  <-irrefl : ¬ (n < n)
  <-irrefl (nat n<n) = ℕ.<-irrefl refl n<n


  ≤-antisym : n ≤ m → m ≤ n → n ≡ m
  ≤-antisym ≤-refl m≤n = refl
  ≤-antisym (<→≤ n<m) m≤n = ⊥-elim (<-irrefl (<→≤→< n<m m≤n))


  <-IsProp : (p q : n < m) → p ≡ q
  <-IsProp (nat p) (nat q) = cong nat (ℕ.<-irrelevant p q)
  <-IsProp nat<∞ nat<∞ = refl
  <-IsProp nat<⋆ nat<⋆ = refl
  <-IsProp ∞<⋆ ∞<⋆ = refl


  ≤-IsProp : (p q : n ≤ m) → p ≡ q
  ≤-IsProp ≤-refl (reflexive p) = cong reflexive (Size-IsSet _ _)
  ≤-IsProp ≤-refl (<→≤ n<n) = ⊥-elim (<-irrefl n<n)
  ≤-IsProp (<→≤ n<n) ≤-refl = ⊥-elim (<-irrefl n<n)
  ≤-IsProp (<→≤ n<m) (<→≤ n<m₁) = cong <→≤ (<-IsProp _ _)


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


Size< : Size → Set
Size< n = ∃[ m ] (m < n)


abstract
  Size<-≡⁺ : (m k : Size< n) → proj₁ m ≡ proj₁ k → m ≡ k
  Size<-≡⁺ (m , _) (k , _) refl = cong (m ,_) (<-IsProp _ _)


Size<-IsSet : ∀ {n} → IsSet (Size< n)
Size<-IsSet = Σ-IsSet Size-IsSet λ _ → IsOfHLevel-suc 1 <-IsProp


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


  n<ssucn : n < ∞ → n < ssuc n
  n<ssucn nat<∞ = nat (ℕ.s≤s ℕ.≤-refl)


mutual
  ⟦_⟧Δ′ : S.Ctx → Set
  ⟦ [] ⟧Δ′ = ⊤
  ⟦ Δ ∙ n ⟧Δ′ = Σ[ δ ∈ ⟦ Δ ⟧Δ′ ] (Size< (⟦ n ⟧n′ δ))


  ⟦_⟧x′ : S.Var Δ → ⟦ Δ ⟧Δ′ → Size
  ⟦ zero ⟧x′ (δ , n , _) = n
  ⟦ suc x ⟧x′ (δ , _ , _) = ⟦ x ⟧x′ δ


  ⟦_⟧n′ : S.Size Δ → ⟦ Δ ⟧Δ′ → Size
  ⟦ var x ⟧n′ = ⟦ x ⟧x′
  ⟦ ∞ ⟧n′ _ = ∞
  ⟦ ⋆ ⟧n′ _ = ⋆
  ⟦ zero ⟧n′ _ = szero
  ⟦ suc n ⟧n′ = ssuc ∘ ⟦ n ⟧n′


abstract
  ⟦Δ⟧-IsSet : ∀ Δ → IsSet ⟦ Δ ⟧Δ′
  ⟦Δ⟧-IsSet [] = ⊤-IsSet
  ⟦Δ⟧-IsSet (Δ ∙ n) = Σ-IsSet (⟦Δ⟧-IsSet Δ) λ _ → Size<-IsSet


⟦Δ⟧-HSet : S.Ctx → HSet 0ℓ
⟦Δ⟧-HSet Δ = HLevel⁺ _ (⟦Δ⟧-IsSet Δ)


abstract
  ⟦Δ∙n⟧-≡⁺ : ∀ Δ (n : S.Size Δ) {δ δ′ : ⟦ Δ ⟧Δ′} {m m′ : Size}
    → (m<n : m < ⟦ n ⟧n′ δ)
    → (m′<n : m′ < ⟦ n ⟧n′ δ′)
    → δ ≡ δ′
    → m ≡ m′
    → (δ , m , m<n) ≡ (δ′ , m′ , m′<n)
  ⟦Δ∙n⟧-≡⁺  Δ n {δ} _ _ refl eq₂
    = cong (δ ,_) (Size<-≡⁺ _ _ eq₂)


abstract
  ⟦wk⟧ : ∀ (n m : S.Size Δ) {δ} → ⟦ S.wk {n = n} m ⟧n′ δ ≡ ⟦ m ⟧n′ (proj₁ δ)
  ⟦wk⟧ n (var x) = refl
  ⟦wk⟧ n ∞ = refl
  ⟦wk⟧ n ⋆ = refl
  ⟦wk⟧ n zero = refl
  ⟦wk⟧ n (suc m) = cong ssuc (⟦wk⟧ n m)


  ⟦<⟧ₓ : ∀ (x : S.Var Δ) {δ} → ⟦ x ⟧x′ δ < ⟦ S.bound x ⟧n′ δ
  ⟦<⟧ₓ (zero {n = n}) {δ , m , m<n}
    = subst (m <_) (sym (⟦wk⟧ _ n)) m<n
  ⟦<⟧ₓ (suc x) {δ , m , m<n}
    = subst (⟦ x ⟧x′ δ <_) (sym (⟦wk⟧ _ (S.bound x))) (⟦<⟧ₓ x)


  ⟦<⟧ : ∀ {n m : S.Size Δ} {δ} → n S.< m → ⟦ n ⟧n′ δ < ⟦ m ⟧n′ δ
  ⟦<⟧ (var {x = x} _ refl) = ⟦<⟧ₓ x
  ⟦<⟧ (<suc n n<∞) = n<ssucn (⟦<⟧ n<∞)
  ⟦<⟧ zero<∞ = nat<∞
  ⟦<⟧ (suc<∞ n n<∞) = ssuc-resp-< (⟦<⟧ n<∞)
  ⟦<⟧ ∞<⋆ = ∞<⋆
  ⟦<⟧ (S.<-trans n<m m<o) = <-trans (⟦<⟧ n<m) (⟦<⟧ m<o)


mutual
  ⟦_⟧σ′ : ∀ {σ} → σ ∶ Δ ⇒ᵤ Ω → ⟦ Δ ⟧Δ′ → ⟦ Ω ⟧Δ′
  ⟦ Id ⟧σ′ δ = δ
  ⟦ comp σ τ ⟧σ′ δ = ⟦ τ ⟧σ′ (⟦ σ ⟧σ′ δ)
  ⟦ Wk ⟧σ′ (δ , m) = δ
  ⟦ Lift {n = n} σ refl ⟧σ′ (δ , m , m<n)
    = ⟦ σ ⟧σ′ δ , m , subst (m <_) (⟦sub⟧ σ n) m<n
  ⟦ Fill {n = n} n<m ⟧σ′ δ = δ , ⟦ n ⟧n′ δ , ⟦<⟧ n<m
  ⟦ Skip ⟧σ′ ((δ , m , m<n) , k , k<m) = δ , k , <-trans k<m m<n


  abstract
    ⟦subV′⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (x : S.Var Ω) {δ}
      → ⟦ S.subV′ σ x ⟧n′ δ ≡ ⟦ x ⟧x′ (⟦ ⊢σ ⟧σ′ δ)
    ⟦subV′⟧ Id x = refl
    ⟦subV′⟧ (comp {σ = σ} {τ = τ} ⊢σ ⊢τ) x
      = trans (⟦sub′⟧ ⊢σ (S.subV′ τ x)) (⟦subV′⟧ ⊢τ x)
    ⟦subV′⟧ Wk x = refl
    ⟦subV′⟧ (Lift ⊢σ refl) zero {δ , m} = refl
    ⟦subV′⟧ (Lift {σ = σ} {n = n} ⊢σ refl) (suc x) {δ , m}
      rewrite ⟦wk⟧ (S.sub σ n) (S.subV′ σ x) {δ , m}
      = ⟦subV′⟧ ⊢σ x
    ⟦subV′⟧ (Fill n<m) zero = refl
    ⟦subV′⟧ (Fill n<m) (suc x) = refl
    ⟦subV′⟧ Skip zero = refl
    ⟦subV′⟧ Skip (suc x) = refl


    ⟦sub′⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (n : S.Size Ω) {δ}
      → ⟦ S.sub′ σ n ⟧n′ δ ≡ ⟦ n ⟧n′ (⟦ ⊢σ ⟧σ′ δ)
    ⟦sub′⟧ σ (var x) = ⟦subV′⟧ σ x
    ⟦sub′⟧ σ ∞ = refl
    ⟦sub′⟧ σ ⋆ = refl
    ⟦sub′⟧ σ zero = refl
    ⟦sub′⟧ σ (suc n) = cong ssuc (⟦sub′⟧ σ n)


    ⟦sub⟧ :  ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (n : S.Size Ω) {δ}
      → ⟦ S.sub σ n ⟧n′ δ ≡ ⟦ n ⟧n′ (⟦ ⊢σ ⟧σ′ δ)
    ⟦sub⟧ {σ = σ} ⊢σ n {δ}
      = trans (cong (λ k → ⟦ k ⟧n′ δ) (sym (S.sub′≡sub σ n))) (⟦sub′⟧ ⊢σ n)


abstract
  ⟦subV⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (x : S.Var Ω) {δ}
    → ⟦ S.subV σ x ⟧n′ δ ≡ ⟦ x ⟧x′ (⟦ ⊢σ ⟧σ′ δ)
  ⟦subV⟧ {σ = σ} ⊢σ x {δ}
    = trans (cong (λ k → ⟦ k ⟧n′ δ) (sym (S.subV′≡subV σ x))) (⟦subV′⟧ ⊢σ x)


  ⟦⟧σ-param : ∀ {σ} (p q : σ ∶ Δ ⇒ᵤ Ω) {δ}
    → ⟦ p ⟧σ′ δ ≡ ⟦ q ⟧σ′ δ
  ⟦⟧σ-param Id Id = refl
  ⟦⟧σ-param (comp p p′) (comp q q′)
    = trans (⟦⟧σ-param p′ q′) (cong (⟦ q′ ⟧σ′) (⟦⟧σ-param p q))
  ⟦⟧σ-param Wk Wk = refl
  ⟦⟧σ-param {Ω = Ω ∙ m} (Lift p refl) (Lift q m≡n[σ]₁)
    rewrite S.Size-IsSet m≡n[σ]₁ refl
    = ⟦Δ∙n⟧-≡⁺ Ω m _ _ (⟦⟧σ-param p q) refl
  ⟦⟧σ-param {Δ = Δ} {σ = Fill {m = m} n} (Fill n<m) (Fill n<m₁)
    = ⟦Δ∙n⟧-≡⁺ Δ m (⟦<⟧ n<m) (⟦<⟧ n<m₁) refl refl
  ⟦⟧σ-param Skip Skip = refl


⟦_⟧Δ : S.Ctx → RGraph
⟦ Δ ⟧Δ = record
  { ObjHSet = ⟦Δ⟧-HSet Δ
  ; eqHProp = λ _ _ → ⊤-HProp
  }


Sizes : RGraph
Sizes = record
  { ObjHSet = HLevel⁺ Size Size-IsSet
  ; eqHProp = λ _ _ → ⊤-HProp
  }


⟦_⟧n : ∀ {Δ} (n : S.Size Δ) → ⟦ Δ ⟧Δ RG.⇒ Sizes
⟦ n ⟧n = record
  { fobj = ⟦ n ⟧n′
  }


⟦_⟧σ : ∀ {Δ Ω σ} → σ ∶ Δ ⇒ᵤ Ω → ⟦ Δ ⟧Δ RG.⇒ ⟦ Ω ⟧Δ
⟦ σ ⟧σ = record
  { fobj = ⟦ σ ⟧σ′
  }
