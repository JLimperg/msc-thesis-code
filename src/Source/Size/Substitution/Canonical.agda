{-# OPTIONS --without-K --safe #-}
module Source.Size.Substitution.Canonical where

open import Source.Size
open import Util.Prelude


infixl 5 _>>_


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


abstract
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


abstract
  Snoc-≡⁺ : σ ≡ τ → n ≡ m → {n<o : n < sub σ o} {m<o : m < sub τ o}
    → Snoc {m = o} σ n n<o ≡ Snoc τ m m<o
  Snoc-≡⁺ {σ = σ} {n = n} refl refl = cong (Snoc σ n) (<-IsProp _ _)


  sub-Snoc : ∀ (σ : Sub Δ Ω) n (n<m : n < sub σ m) o
    → sub (Snoc {m = m} σ n n<m) (wk o) ≡ sub σ o
  sub-Snoc σ n n<m (var x) = refl
  sub-Snoc σ n n<m ∞ = refl
  sub-Snoc σ n n<m ⋆ = refl
  sub-Snoc σ n n<m zero = refl
  sub-Snoc σ n n<m (suc o o<∞) = suc-≡⁺ (sub-Snoc σ n n<m o)


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


  abstract
    subV-Weaken : ∀ (σ : Sub Δ Ω) x → subV (Weaken {n = o} σ) x ≡ wk (subV σ x)
    subV-Weaken (Snoc σ n n<m) zero = refl
    subV-Weaken (Snoc σ n n<m) (suc x) = subV-Weaken σ x


    sub-Weaken : ∀ (σ : Sub Δ Ω) n → sub (Weaken {n = o} σ) n ≡ wk (sub σ n)
    sub-Weaken σ (var x) = subV-Weaken σ x
    sub-Weaken σ ∞ = refl
    sub-Weaken σ ⋆ = refl
    sub-Weaken σ zero = refl
    sub-Weaken σ (suc n x) = suc-≡⁺ (sub-Weaken σ n)


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


  abstract
    subV-Id : ∀ x → subV (Id {Δ}) x ≡ var x
    subV-Id zero = refl
    subV-Id (suc x) = trans (subV-Weaken Id x) (cong wk (subV-Id x))


    sub-Id : ∀ n → σ ≡ Id → sub σ n ≡ n
    sub-Id (var x) refl  = subV-Id x
    sub-Id ∞ _ = refl
    sub-Id ⋆ _ = refl
    sub-Id zero _ = refl
    sub-Id (suc n x) p = suc-≡⁺ (sub-Id n p)


Wk : Sub (Δ ∙ n) Δ
Wk = Weaken Id


abstract
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


  abstract
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
    sub->> {σ = σ} {τ} (suc n x) p = suc-≡⁺ (sub->> n p)


Skip : Sub (Δ ∙ n ∙ var zero) (Δ ∙ n)
Skip {Δ} {n} = Snoc (Weaken Wk) (var zero)
  (var (bound zero) refl
    (<→≤ (var (bound (suc zero)) refl
      (reflexive (sym (trans (sub-Weaken Wk n) (cong wk (sub-Wk n))))))))


Weaken>> : Weaken σ >> τ ≡ Weaken {n = n} (σ >> τ)
Weaken>> {τ = []} = refl
Weaken>> {σ = σ} {τ = Snoc τ n n<m} = Snoc-≡⁺ Weaken>> (sub-Weaken σ n)


abstract
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


  Keep′Keep′>>Skip : Keep′ (Keep′ {n = n} σ) >> Skip ≡ Skip >> Keep′ σ
  Keep′Keep′>>Skip = Snoc-≡⁺
    (trans Keep>>Weaken (sym (trans Skip>>Weaken (cong Weaken (sym Snoc>>Wk)))))
    refl


  sub->>′ : σ >> τ ≡ σ′ >> τ′ → sub σ (sub τ n) ≡ sub σ′ (sub τ′ n)
  sub->>′ {σ = σ} {τ = τ} {σ′ = σ′} {τ′} {n} eq
    = trans (sym (sub->> n refl))
        (trans (cong (λ σ → sub σ n) eq) (sub->> n refl))
