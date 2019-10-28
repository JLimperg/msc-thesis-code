{-# OPTIONS --without-K --safe #-}
module Source.Size.Substitution.Canonical where

open import Source.Size
open import Util.Prelude


infix  0 Sub⊢
infixl 5 _>>_


data Sub (Δ : Ctx) : (Ω : Ctx) → Set where
  [] : Sub Δ []
  Snoc : (σ : Sub Δ Ω) (n : Size Δ) → Sub Δ (Ω ∙ m)


variable
  σ τ σ′ τ′ ι ι′ : Sub Δ Ω


subV : Sub Δ Ω → Var Ω → Size Δ
subV (Snoc σ n) zero = n
subV (Snoc σ n) (suc x) = subV σ x


sub : Sub Δ Ω → Size Ω → Size Δ
sub σ (var x) = subV σ x
sub σ ∞ = ∞
sub σ ⋆ = ⋆
sub σ zero = zero
sub σ (suc n) = suc (sub σ n)


data Sub⊢ Δ : ∀ Ω (σ : Sub Δ Ω) → Set where
  [] : Sub⊢ Δ [] []
  Snoc : (⊢σ : Sub⊢ Δ Ω σ) (n<m : n < sub σ m) → Sub⊢ Δ (Ω ∙ m) (Snoc σ n)


syntax Sub⊢ Δ Ω σ = σ ∶ Δ ⇒ Ω


abstract
  sub-Snoc : ∀ (σ : Sub Δ Ω) n o
    → sub (Snoc {m = m} σ n) (wk o) ≡ sub σ o
  sub-Snoc σ n (var x) = refl
  sub-Snoc σ n ∞ = refl
  sub-Snoc σ n ⋆ = refl
  sub-Snoc σ n zero = refl
  sub-Snoc σ n (suc o) = cong suc (sub-Snoc σ n o)


  mutual
    subV-resp-< : σ ∶ Δ ⇒ Ω → var x < n → subV σ x < sub σ n
    subV-resp-< {x = zero} (Snoc {σ = σ} {n} {m} ⊢σ n<m) (var _ refl)
      = subst (n <_) (sym (sub-Snoc σ n m)) n<m
    subV-resp-< {x = suc x} (Snoc {σ = σ} {n} {m} ⊢σ n<m) (var _ refl)
      = subst (subV σ x <_) (sym (sub-Snoc σ n (bound x)))
          (subV-resp-< ⊢σ (var _ refl))
    subV-resp-< ⊢σ (<suc .(var _) x<n) = <suc _ (sub-resp-< ⊢σ x<n)
    subV-resp-< ⊢σ (<-trans x<m m<n)
      = <-trans (subV-resp-< ⊢σ x<m) (sub-resp-< ⊢σ m<n)


    sub-resp-< : σ ∶ Δ ⇒ Ω → n < m → sub σ n < sub σ m
    sub-resp-< ⊢σ (var b b≡bx) = subV-resp-< ⊢σ (var b b≡bx)
    sub-resp-< ⊢σ (<suc n n<∞) = <suc _ (sub-resp-< ⊢σ n<∞)
    sub-resp-< ⊢σ zero<∞ = zero<∞
    sub-resp-< ⊢σ (suc<∞ n n<∞) = suc<∞ _ (sub-resp-< ⊢σ n<∞)
    sub-resp-< ⊢σ ∞<⋆ = ∞<⋆
    sub-resp-< ⊢σ (<-trans n<m m<o)
      = <-trans (sub-resp-< ⊢σ n<m) (sub-resp-< ⊢σ m<o)


Weaken : Sub Δ Ω → Sub (Δ ∙ n) Ω
Weaken [] = []
Weaken (Snoc σ m) = Snoc (Weaken σ) (wk m)


abstract
  subV-Weaken : ∀ (σ : Sub Δ Ω) x → subV (Weaken {n = o} σ) x ≡ wk (subV σ x)
  subV-Weaken (Snoc σ n) zero = refl
  subV-Weaken (Snoc σ n) (suc x) = subV-Weaken σ x


  sub-Weaken : ∀ (σ : Sub Δ Ω) n → sub (Weaken {n = o} σ) n ≡ wk (sub σ n)
  sub-Weaken σ (var x) = subV-Weaken σ x
  sub-Weaken σ ∞ = refl
  sub-Weaken σ ⋆ = refl
  sub-Weaken σ zero = refl
  sub-Weaken σ (suc n) = cong suc (sub-Weaken σ n)


  Weaken⊢ : σ ∶ Δ ⇒ Ω → Weaken σ ∶ Δ ∙ n ⇒ Ω
  Weaken⊢ [] = []
  Weaken⊢ (Snoc {σ = σ} {n} {m} ⊢σ n<m)
    = Snoc (Weaken⊢ ⊢σ)
        (subst (wk n <_) (sym (sub-Weaken σ m)) (wk-resp-< n<m))


Keep : (σ : Sub Δ Ω) → Sub (Δ ∙ m) (Ω ∙ n)
Keep σ = Snoc (Weaken σ) (var zero)


abstract
  Keep⊢ : σ ∶ Δ ⇒ Ω → m ≡ sub σ n → Keep σ ∶ Δ ∙ m ⇒ Ω ∙ n
  Keep⊢ {Δ} {σ = σ} {n = n} ⊢σ refl
    = Snoc (Weaken⊢ ⊢σ)
        (var (sub (Weaken σ) n) (sub-Weaken σ n))


mutual
  Id : Sub Δ Δ
  Id {[]} = []
  Id {Δ ∙ n} = Keep Id


  abstract
    subV-Id : ∀ x → subV (Id {Δ}) x ≡ var x
    subV-Id zero = refl
    subV-Id (suc x) = trans (subV-Weaken Id x) (cong wk (subV-Id x))


    sub-Id : ∀ n → σ ≡ Id → sub σ n ≡ n
    sub-Id (var x) refl  = subV-Id x
    sub-Id ∞ _ = refl
    sub-Id ⋆ _ = refl
    sub-Id zero _ = refl
    sub-Id (suc n) p = cong suc (sub-Id n p)


abstract
  Id⊢ : Id ∶ Δ ⇒ Δ
  Id⊢ {[]} = []
  Id⊢ {Δ ∙ n} = Keep⊢ Id⊢ (sym (sub-Id _ refl))


Wk : Sub (Δ ∙ n) Δ
Wk = Weaken Id


abstract
  sub-Wk : ∀ n → sub (Wk {Δ} {o}) n ≡ wk n
  sub-Wk n = trans (sub-Weaken Id n) (cong wk (sub-Id _ refl))


  Wk⊢ : Wk ∶ Δ ∙ n ⇒ Δ
  Wk⊢ = Weaken⊢ Id⊢


Fill : Size Δ → Sub Δ (Δ ∙ m)
Fill n = Snoc Id n


abstract
  Fill⊢ : n < m → Fill n ∶ Δ ⇒ Δ ∙ m
  Fill⊢ {n = n} n<m
    = Snoc Id⊢ (subst (n <_) (sym (sub-Id _ refl)) n<m)


_>>_ : Sub Δ Δ′ → Sub Δ′ Δ″ → Sub Δ Δ″
σ >> [] = []
σ >> Snoc τ n = Snoc (σ >> τ) (sub σ n)


abstract
  subV->> : ∀ (σ : Sub Δ Δ′) (τ : Sub Δ′ Δ″) x
    → subV (σ >> τ) x ≡ sub σ (subV τ x)
  subV->> σ (Snoc τ n) zero = refl
  subV->> σ (Snoc τ n) (suc x) = subV->> σ τ x


  sub->> : ∀ n → ι ≡ σ >> τ
    → sub ι n ≡ sub σ (sub τ n)
  sub->> {σ = σ} {τ} (var x) refl = subV->> σ τ x
  sub->> ∞ _ = refl
  sub->> ⋆ _ = refl
  sub->> zero _ = refl
  sub->> {σ = σ} {τ} (suc n) p = cong suc (sub->> n p)


  sub->>′ : σ >> τ ≡ σ′ >> τ′ → sub σ (sub τ n) ≡ sub σ′ (sub τ′ n)
  sub->>′ {σ = σ} {τ = τ} {σ′ = σ′} {τ′} {n} eq
    = trans (sym (sub->> n refl))
        (trans (cong (λ σ → sub σ n) eq) (sub->> n refl))


  >>⊢ : σ ∶ Δ ⇒ Δ′ → τ ∶ Δ′ ⇒ Δ″ → σ >> τ ∶ Δ ⇒ Δ″
  >>⊢ ⊢σ [] = []
  >>⊢ {σ = σ} ⊢σ (Snoc {σ = τ} {n} {m} ⊢τ n<m)
    = Snoc (>>⊢ ⊢σ ⊢τ)
        (subst (sub σ n <_) (sym (sub->> m refl)) (sub-resp-< ⊢σ n<m))


Skip : Sub (Δ ∙ n ∙ v0) (Δ ∙ n)
Skip = Snoc (Weaken Wk) (var zero)


abstract
  Skip⊢ : Skip ∶ Δ ∙ n ∙ v0 ⇒ Δ ∙ n
  Skip⊢ {n = n}
    = Snoc (Weaken⊢ Wk⊢)
        (<-trans (var v1 refl)
          (var (sub (Weaken Wk) n) (trans (sub-Weaken Wk n) (cong wk (sub-Wk n)))))


  Weaken>> : Weaken σ >> τ ≡ Weaken {n = n} (σ >> τ)
  Weaken>> {τ = []} = refl
  Weaken>> {σ = σ} {τ = Snoc τ n} = cong₂ Snoc Weaken>>  (sub-Weaken σ n)


  Snoc>>Weaken : Snoc {m = m} σ n >> Weaken τ ≡ σ >> τ
  Snoc>>Weaken {τ = []} = refl
  Snoc>>Weaken {σ = σ} {n = n} {τ = Snoc τ k}
    = cong₂ Snoc Snoc>>Weaken (sub-Snoc σ n k)


  id-l : Id >> σ ≡ σ
  id-l {σ = []} = refl
  id-l {σ = Snoc σ n} = cong₂ Snoc id-l (sub-Id n refl)


  id-r : {σ : Sub Δ Ω} → σ >> Id ≡ σ
  id-r {σ = []} = refl
  id-r {σ = Snoc σ n} = cong₂ Snoc (trans Snoc>>Weaken id-r) refl


  >>-assoc : σ >> (τ >> ι) ≡ σ >> τ >> ι
  >>-assoc {ι = []} = refl
  >>-assoc {σ = σ} {τ = τ} {ι = Snoc ι n}
    = cong₂ Snoc >>-assoc (sym (sub->> n refl))


  Wk>> : Wk >> σ ≡ Weaken {n = n} σ
  Wk>> = trans Weaken>> (cong Weaken id-l)


  Snoc>>Wk : Snoc {m = m} σ n >> Wk ≡ σ
  Snoc>>Wk = trans Snoc>>Weaken id-r


  Keep>>Weaken : Keep {m = m} {n} σ >> Weaken τ ≡ Weaken (σ >> τ)
  Keep>>Weaken = trans Snoc>>Weaken Weaken>>


  Keep>>Wk : Keep {m = m} {n} σ >> Wk ≡ Wk >> σ
  Keep>>Wk = trans Keep>>Weaken (trans (sym Wk>>) (cong (Wk >>_) id-r))


  Fill>>Weaken : Fill {m = m} n >> Weaken σ ≡ σ
  Fill>>Weaken = trans Snoc>>Weaken id-l


  Fill>>Wk : Fill {m = m} n >> Wk ≡ Id
  Fill>>Wk = trans Snoc>>Weaken id-r


  Fill>>Keep : ∀ n → Fill (sub σ n) >> Keep {m = m} {o} σ ≡ σ >> Fill n
  Fill>>Keep n = cong₂ Snoc (trans Fill>>Weaken (sym id-r)) refl


  Keep>>Keep : Keep {m = m} {n} σ >> Keep {n = o} τ ≡ Keep (σ >> τ)
  Keep>>Keep = cong₂ Snoc Keep>>Weaken refl


  Skip>>Weaken : Skip {n = n} >> Weaken σ ≡ Weaken (Weaken σ)
  Skip>>Weaken = trans Snoc>>Weaken (trans Weaken>> (cong Weaken Wk>>))


  Skip>>Keep : Skip >> Keep {m = m} {n} σ ≡ Keep (Keep σ) >> Skip
  Skip>>Keep
    = cong₂ Snoc
        (trans Skip>>Weaken
          (sym (trans Keep>>Weaken (cong Weaken (trans Snoc>>Weaken id-r)))))
      refl


  Keep-Id : Keep {m = m} Id ≡ Id
  Keep-Id = refl


  KeepFill>>Wk>>Wk : Keep {m = o} {m} (Fill n) >> (Wk >> Wk) ≡ Wk
  KeepFill>>Wk>>Wk {n = n} {m} = let open ≡-Reasoning in
    begin
      Keep (Fill n) >> (Wk >> Wk)
    ≡⟨ cong (Keep (Fill n) >>_) Wk>> ⟩
      Keep (Fill n) >> (Weaken Wk)
    ≡⟨ Keep>>Weaken ⟩
      Weaken (Fill n >> Weaken Id)
    ≡⟨ cong Weaken Fill>>Weaken ⟩
      Wk
    ∎


  KeepFill>>Skip
    : Keep {m = m} (Fill {m = m} n) >> Skip ≡ Fill {m = o} (var zero) >> Keep Wk
  KeepFill>>Skip {n = n} = cong₂ Snoc go refl
    where
      go : Keep (Fill n) >> Weaken Wk ≡ Fill (var zero) >> Weaken Wk
      go = let open ≡-Reasoning in
        begin
          Keep (Fill n) >> Weaken Wk
        ≡⟨ Keep>>Weaken ⟩
          Weaken (Fill n >> Weaken Id)
        ≡⟨ cong Weaken Fill>>Wk ⟩
          Wk
        ≡⟨ sym Fill>>Weaken ⟩
          Fill (var zero) >> Weaken Wk
        ∎


  KeepKeep>>Skip : Keep (Keep {m = m} {n} σ) >> Skip ≡ Skip >> Keep σ
  KeepKeep>>Skip
    = cong₂ Snoc (trans Keep>>Weaken
        (sym (trans Skip>>Weaken (cong Weaken (sym Snoc>>Wk))))) refl
