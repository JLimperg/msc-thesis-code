{-# OPTIONS --without-K #-}
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

import Source.Size.Substitution.Canonical as SC
import Source.Size.Substitution.Universe as S

open S.Ctx
open S.Size
open S.Sub
open S.Sub⊢ᵤ
open S.Var
open S._<_ hiding (<-trans)


infix 4 _<_ _≤_


private
  variable
    i j k : ℕ


{-
This is an encoding of the set of ordinals

  ℕ ∪ { ω + i | i ∈ ℕ }

i.e. of the ordinals below ω*2.
-}
data Size : Set where
  zero+ : (i : ℕ) → Size
  ∞+ : (i : ℕ) → Size


variable
  n m o : Size


nat : ℕ → Size
nat = zero+


abstract
  zero+-inj : zero+ i ≡ zero+ j → i ≡ j
  zero+-inj refl = refl


  zero+-≡-canon : (p : zero+ i ≡ zero+ j) → p ≡ cong zero+ (zero+-inj p)
  zero+-≡-canon refl = refl


  ∞+-inj : ∞+ i ≡ ∞+ j → i ≡ j
  ∞+-inj refl = refl


  ∞+-≡-canon : (p : ∞+ i ≡ ∞+ j) → p ≡ cong ∞+ (∞+-inj p)
  ∞+-≡-canon refl = refl


  Size-IsSet : IsSet Size
  Size-IsSet {zero+ i} {zero+ j} p refl
    = trans (zero+-≡-canon p) (cong (cong zero+) (ℕ.≡-irrelevant _ _))
  Size-IsSet {∞+ i} {∞+ j} p refl
    = trans (∞+-≡-canon p) (cong (cong ∞+) (ℕ.≡-irrelevant _ _))


data _<_ : (n m : Size) → Set where
  zero+ : (i<j : i ℕ.< j) → zero+ i < zero+ j
  ∞+ : (i<j : i ℕ.< j) → ∞+ i < ∞+ j
  zero<∞ : zero+ i < ∞+ j


data _≤_ (n m : Size) : Set where
  reflexive : n ≡ m → n ≤ m
  <→≤ : n < m → n ≤ m


pattern ≤-refl = reflexive refl


abstract
  <-trans : n < m → m < o → n < o
  <-trans (zero+ i<j) (zero+ j<k) = zero+ (ℕ.<-trans i<j j<k)
  <-trans (zero+ i<j) zero<∞ = zero<∞
  <-trans (∞+ i<j) (∞+ j<k) = ∞+ (ℕ.<-trans i<j j<k)
  <-trans zero<∞ (∞+ i<j) = zero<∞


  ≤→<→< : n ≤ m → m < o → n < o
  ≤→<→< ≤-refl m<o = m<o
  ≤→<→< (<→≤ n<m) m<o = <-trans n<m m<o


  <→≤→< : n < m → m ≤ o → n < o
  <→≤→< n<m ≤-refl = n<m
  <→≤→< n<m (<→≤ m<o) = <-trans n<m m<o


  ≤-trans : n ≤ m → m ≤ o → n ≤ o
  ≤-trans n≤m ≤-refl = n≤m
  ≤-trans n≤m (<→≤ m<o) = <→≤ (≤→<→< n≤m m<o)


⟦zero⟧ ⟦∞⟧ : Size
⟦zero⟧ = zero+ 0
⟦∞⟧ = ∞+ 0


⟦suc⟧ : Size → Size
⟦suc⟧ (zero+ i) = zero+ (suc i)
⟦suc⟧ (∞+ i) = ∞+ (suc i)


abstract
  ⟦zero⟧<⟦suc⟧ : ⟦zero⟧ < ⟦suc⟧ n
  ⟦zero⟧<⟦suc⟧ {zero+ i} = zero+ (ℕ.s≤s ℕ.z≤n)
  ⟦zero⟧<⟦suc⟧ {∞+ i} = zero<∞


  ⟦zero⟧<⟦∞⟧ : ⟦zero⟧ < ⟦∞⟧
  ⟦zero⟧<⟦∞⟧ = zero<∞


  ⟦suc⟧<⟦suc⟧ : n < m → ⟦suc⟧ n < ⟦suc⟧ m
  ⟦suc⟧<⟦suc⟧ (zero+ i<j) = zero+ (ℕ.s≤s i<j)
  ⟦suc⟧<⟦suc⟧ (∞+ i<j) = ∞+ (ℕ.s≤s i<j)
  ⟦suc⟧<⟦suc⟧ zero<∞ = zero<∞


  ⟦suc⟧<⟦∞⟧ : n < ⟦∞⟧ → ⟦suc⟧ n < ⟦∞⟧
  ⟦suc⟧<⟦∞⟧ zero<∞ = zero<∞


  <⟦suc⟧ : n < ⟦suc⟧ n
  <⟦suc⟧ {zero+ i} = zero+ (ℕ.s≤s ℕ.≤-refl)
  <⟦suc⟧ {∞+ i} = ∞+ (ℕ.s≤s ℕ.≤-refl)


Size< : Size → Set
Size< n = ∃[ m ] (m < n)


mutual
  ⟦_⟧Δ′ : S.Ctx → Set
  ⟦ [] ⟧Δ′ = ⊤
  ⟦ Δ ∙ n ⟧Δ′ = Σ[ δ ∈ ⟦ Δ ⟧Δ′ ] (Size< (⟦ n ⟧n′ δ))


  ⟦_⟧x′ : S.Var Δ → ⟦ Δ ⟧Δ′ → Size
  ⟦ zero ⟧x′ (δ , n , _) = n
  ⟦ suc x ⟧x′ (δ , _ , _) = ⟦ x ⟧x′ δ


  ⟦_⟧n′ : S.Size Δ → ⟦ Δ ⟧Δ′ → Size
  ⟦ var x ⟧n′ = ⟦ x ⟧x′
  ⟦ ∞ ⟧n′ _ = ⟦∞⟧
  ⟦ zero ⟧n′ _ = ⟦zero⟧
  ⟦ suc n ⟧n′ = ⟦suc⟧ ∘ ⟦ n ⟧n′


abstract
  ⟦wk⟧ : ∀ (n m : S.Size Δ) {δ} → ⟦ S.wk {n = n} m ⟧n′ δ ≡ ⟦ m ⟧n′ (proj₁ δ)
  ⟦wk⟧ n (var x) = refl
  ⟦wk⟧ n ∞ = refl
  ⟦wk⟧ n zero = refl
  ⟦wk⟧ n (suc m) = cong ⟦suc⟧ (⟦wk⟧ n m)


  ⟦<⟧ₓ : ∀ (x : S.Var Δ) {δ}
    → ⟦ x ⟧x′ δ < ⟦ S.bound x ⟧n′ δ
  ⟦<⟧ₓ {Δ ∙ n} zero {δ , m , m<n} = subst (m <_) (sym (⟦wk⟧ n n)) m<n
  ⟦<⟧ₓ {Δ ∙ n} (suc x) {δ , m , m<n}
    = subst (⟦ x ⟧x′ δ <_) (sym (⟦wk⟧ n (S.bound x))) (⟦<⟧ₓ x)


  ⟦<⟧ : ∀ {n m : S.Size Δ} {δ}
    → n S.< m
    → ⟦ n ⟧n′ δ < ⟦ m ⟧n′ δ
  ⟦<⟧ (var {x = x} refl) = ⟦<⟧ₓ x
  ⟦<⟧ zero<suc = ⟦zero⟧<⟦suc⟧
  ⟦<⟧ zero<∞ = ⟦zero⟧<⟦∞⟧
  ⟦<⟧ (suc<suc n<m) = ⟦suc⟧<⟦suc⟧ (⟦<⟧ n<m)
  ⟦<⟧ (suc<∞ n<m) = ⟦suc⟧<⟦∞⟧ (⟦<⟧ n<m)
  ⟦<⟧ (S.<-trans n<m m<o) = <-trans (⟦<⟧ n<m) (⟦<⟧ m<o)
  ⟦<⟧ <suc = <⟦suc⟧


  <-irrefl : ¬ n < n
  <-irrefl {zero+ i} (zero+ i<i) = ℕ.<⇒≢ i<i refl
  <-irrefl {∞+ i} (∞+ i<i) = ℕ.<⇒≢ i<i refl


  ≤-antisym : n ≤ m → m ≤ n → n ≡ m
  ≤-antisym ≤-refl m≤n = refl
  ≤-antisym (<→≤ n<m) m≤n = ⊥-elim (<-irrefl (<→≤→< n<m m≤n))


  <-IsProp : IsProp (n < m)
  <-IsProp (zero+ i<j) (zero+ i<j₁) = cong zero+ (ℕ.<-irrelevant _ _)
  <-IsProp (∞+ i<j) (∞+ i<j₁) = cong ∞+ (ℕ.<-irrelevant _ _)
  <-IsProp zero<∞ zero<∞ = refl


  ≤-IsProp : IsProp (n ≤ m)
  ≤-IsProp (reflexive p) (reflexive q) = cong reflexive (Size-IsSet _ _)
  ≤-IsProp ≤-refl (<→≤ q) = ⊥-elim (<-irrefl q)
  ≤-IsProp (<→≤ p) ≤-refl = ⊥-elim (<-irrefl p)
  ≤-IsProp (<→≤ p) (<→≤ q) = cong <→≤ (<-IsProp p q)


  Size<-≡⁺ : (m k : Size< n) → proj₁ m ≡ proj₁ k → m ≡ k
  Size<-≡⁺ (m , _) (k , _) refl = cong (m ,_) (<-IsProp _ _)


  Size<-IsSet : ∀ {n} → IsSet (Size< n)
  Size<-IsSet = Σ-IsSet Size-IsSet λ _ → IsOfHLevel-suc 1 <-IsProp


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


  zero+-<ℕ-acc→<-acc : Acc ℕ._<_ i → Acc _<_ (zero+ i)
  zero+-<ℕ-acc→<-acc (acc rs) = acc λ where
    (zero+ i) (zero+ i<j) → zero+-<ℕ-acc→<-acc (rs i i<j)


  zero+-acc : Acc _<_ (zero+ i)
  zero+-acc = zero+-<ℕ-acc→<-acc (ℕ.<-wellFounded _)


  ∞+-<ℕ-acc→<-acc : Acc ℕ._<_ i → Acc _<_ (∞+ i)
  ∞+-<ℕ-acc→<-acc (acc rs) = acc λ where
    (∞+ i) (∞+ i<j) → ∞+-<ℕ-acc→<-acc (rs i i<j)
    (zero+ i) zero<∞ → zero+-acc


  ∞+-acc : Acc _<_ (∞+ i)
  ∞+-acc = ∞+-<ℕ-acc→<-acc (ℕ.<-wellFounded _)


  <-wf : WellFounded _<_
  <-wf m = acc λ where
    _ (zero+ i<j) → zero+-acc
    _ (∞+ i<j) → ∞+-acc
    _ zero<∞ → zero+-acc


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


mutual
  ⟦_⟧σ′ : ∀ {σ} → σ ∶ Δ ⇒ᵤ Ω → ⟦ Δ ⟧Δ′ → ⟦ Ω ⟧Δ′
  ⟦ Id ⟧σ′ δ = δ
  ⟦ comp σ τ ⟧σ′ δ = ⟦ τ ⟧σ′ (⟦ σ ⟧σ′ δ)
  ⟦ Wk ⟧σ′ (δ , m) = δ
  ⟦ Lift {n = n} σ refl ⟧σ′ (δ , m , m<n)
    = ⟦ σ ⟧σ′ δ , m , subst (m <_) (⟦sub⟧ σ n) m<n
  ⟦ Sing {n = n} n<m ⟧σ′ δ = δ , ⟦ n ⟧n′ δ , ⟦<⟧ n<m
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
    ⟦subV′⟧ (Sing n<m) zero = refl
    ⟦subV′⟧ (Sing n<m) (suc x) = refl
    ⟦subV′⟧ Skip zero = refl
    ⟦subV′⟧ Skip (suc x) = refl


    ⟦sub′⟧ : ∀ {σ} (⊢σ : σ ∶ Δ ⇒ᵤ Ω) (n : S.Size Ω) {δ}
      → ⟦ S.sub′ σ n ⟧n′ δ ≡ ⟦ n ⟧n′ (⟦ ⊢σ ⟧σ′ δ)
    ⟦sub′⟧ σ (var x) = ⟦subV′⟧ σ x
    ⟦sub′⟧ σ ∞ = refl
    ⟦sub′⟧ σ zero = refl
    ⟦sub′⟧ σ (suc n) = cong ⟦suc⟧ (⟦sub′⟧ σ n)


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
  ⟦⟧σ-param {Δ = Δ} {σ = Sing {m = m} n} (Sing n<m) (Sing n<m₁)
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


data _≤′_ : (n m : Size) → Set where
  zero+ : (i≤j : i ℕ.≤ j) → zero+ i ≤′ zero+ j
  ∞+ : (i≤j : i ℕ.≤ j) → ∞+ i ≤′ ∞+ j
  zero<∞ : zero+ i ≤′ ∞+ j


abstract
  ≤→≤′ : n ≤ m → n ≤′ m
  ≤→≤′ {zero+ i} ≤-refl = zero+ ℕ.≤-refl
  ≤→≤′ {∞+ i} ≤-refl = ∞+ ℕ.≤-refl
  ≤→≤′ (<→≤ (zero+ i<j)) = zero+ (ℕ.<⇒≤ i<j)
  ≤→≤′ (<→≤ (∞+ i<j)) = ∞+ (ℕ.<⇒≤ i<j)
  ≤→≤′ (<→≤ zero<∞) = zero<∞


  ≤′→≤ : n ≤′ m → n ≤ m
  ≤′→≤ (zero+ i≤j) with ℕ.≤⇒≤′ i≤j
  ... | ℕ.≤′-refl = ≤-refl
  ... | ℕ.≤′-step i≤′j = <→≤ (zero+ (ℕ.s≤s (ℕ.≤′⇒≤ i≤′j)))
  ≤′→≤ (∞+ i≤j) with ℕ.≤⇒≤′ i≤j
  ... | ℕ.≤′-refl = ≤-refl
  ... | ℕ.≤′-step i≤′j = <→≤ (∞+ (ℕ.s≤s (ℕ.≤′⇒≤ i≤′j)))
  ≤′→≤ zero<∞ = <→≤ zero<∞


  0≤n : ⟦zero⟧ ≤ n
  0≤n {zero+ zero} = ≤-refl
  0≤n {zero+ (suc i)} = <→≤ (zero+ (ℕ.s≤s ℕ.z≤n))
  0≤n {∞+ i} = <→≤ zero<∞


  n<m→Sn≤m : n < m → ⟦suc⟧ n ≤ m
  n<m→Sn≤m (zero+ (ℕ.s≤s i≤j)) = ≤′→≤ (zero+ (ℕ.s≤s i≤j))
  n<m→Sn≤m (∞+ (ℕ.s≤s i≤j)) = ≤′→≤ (∞+ (ℕ.s≤s i≤j))
  n<m→Sn≤m zero<∞ = <→≤ zero<∞


  Sn≤m→n<m : ⟦suc⟧ n ≤ m → n < m
  Sn≤m→n<m ≤-refl = <⟦suc⟧
  Sn≤m→n<m (<→≤ Sn<m) = <-trans <⟦suc⟧ Sn<m
