{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Semisimplicial.Truncated where

open import 2LTT.Semisimplicial.Face public

-- Semisimplicial types of level n for n : ℕᵉ, following Section 3 of
-- "Extending Homotopy Type Theory with Strict Equality" (2016) paper.
-- SSTᵉ, Map, restrict, restrict-⊙ are SST, SK, SK→, α there.

-- By UIP, transports to a common endpoint agree
tr-coh : {i j k : Level} {M : UUᵉ i} (P : M → UUᵉ j) {H : UUᵉ k} {s : H → M}
          (τ : (h : H) → P (s h)) {h h' : H} → _=ᵉ_ {k} {H} h h'
          → {y : M} (p : _=ᵉ_ {i} {M} (s h) y) (q : _=ᵉ_ {i} {M} (s h') y)
          → _=ᵉ_ {j} {P y} (exo-tr {i} {j} {M} P p (τ h)) (exo-tr {i} {j} {M} P q (τ h'))
tr-coh {i} {j} {k} {M} P τ reflᵉ p q = exo-ap-tr {i} {j} {M} {P} (UIPᵉ {i} p q)

module _ (i : Level) where

  mutual
    -- The exo-type of semisimplicial types of level n
    SSTᵉ : ℕᵉ → UUᵉ (lsuc i)
    SSTᵉ zeroᵉ     = ⊤ᵉ {lsuc i}
    SSTᵉ (succᵉ n) = Σᵉ {lsuc i} {lsuc i} (SSTᵉ n) (λ X → Map n X (succᵉ n) → UU i)

    -- Maps from the n-skeleton of the simplex with v vertices into X
    Map : (n : ℕᵉ) → SSTᵉ n → ℕᵉ → UUᵉ i
    Map zeroᵉ     X        v = ⊤ᵉ {i}
    Map (succᵉ n) (X ,ᵉ A) v =
      Σᵉ {i} {i} (Map n X v) (λ σ → (f : Face v (succᵉ n)) → (A (restrict n X σ f)))

    -- The contravariant action of faces on Map n X
    restrict : (n : ℕᵉ) (X : SSTᵉ n) {v w : ℕᵉ} → Map n X v → Face v w → Map n X w
    restrict zeroᵉ     X        σ        f = starᵉ
    restrict (succᵉ n) (X ,ᵉ A) (σ ,ᵉ τ) f =
      restrict n X σ f ,ᵉ
      (λ g → exo-tr {i} {i} {Map n X (succᵉ n)} (λ s → (A s)) (restrict-⊙ n X σ f g) (τ (f ⊙ g)))

    -- restrict preserves composition
    restrict-⊙ : (n : ℕᵉ) (X : SSTᵉ n) {v w u : ℕᵉ}
                  (σ : Map n X v) (f : Face v w) (g : Face w u)
                  → _=ᵉ_ {i} {Map n X u} (restrict n X σ (f ⊙ g)) (restrict n X (restrict n X σ f) g)
    restrict-⊙ zeroᵉ X σ f g = reflᵉ
    restrict-⊙ (succᵉ n) (X ,ᵉ A) {v} {w} {u} (σ ,ᵉ τ) f g =
      dep-pair-=ᵉ {i} {i} {Map n X u} {λ x → (h : Face u (succᵉ n)) → (A (restrict n X x h))} _ _
        ((restrict-⊙ n X σ f g) ,ᵉ
        (funextᵉ {lzero} {i} {Face u (succᵉ n)} {λ h → (A (restrict n X (restrict n X (restrict n X σ f) g) h))} λ h →
          exo-concat {i}
            (exo-tr-pi {i} {lzero} {i} {Map n X u} (restrict-⊙ n X σ f g) {Face u (succᵉ n)}
                       (λ x y → (A (restrict n X x y))))
            (exo-concat {i}
              (exo-tr-ap {i} {i} {Map n X u} {Map n X (succᵉ n)} {f = λ x → restrict n X x h} {P = λ s → (A s)}
                         (restrict-⊙ n X σ f g))
              (exo-concat {i}
                (exo-tr-concat {i} {i} {Map n X (succᵉ n)} {λ s → (A s)}
                  (restrict-⊙ n X σ (f ⊙ g) h)
                  (exo-ap {i} {i} {Map n X u} {Map n X (succᵉ n)} (λ x → restrict n X x h) (restrict-⊙ n X σ f g)))
                (exo-concat {i}
                  (tr-coh {i} {i} {lzero} {Map n X (succᵉ n)} (λ s → (A s))
                    {Face v (succᵉ n)} {λ k → restrict n X σ k} τ (⊙-assoc f g h)
                    (exo-concat {i} (restrict-⊙ n X σ (f ⊙ g) h)
                                (exo-ap {i} {i} {Map n X u} {Map n X (succᵉ n)} (λ x → restrict n X x h) (restrict-⊙ n X σ f g)))
                    (exo-concat {i} (restrict-⊙ n X σ f (g ⊙ h)) (restrict-⊙ n X (restrict n X σ f) g h)))
                  (exo-inv {i}
                    (exo-tr-concat {i} {i} {Map n X (succᵉ n)} {λ s → (A s)}
                      (restrict-⊙ n X σ f (g ⊙ h)) (restrict-⊙ n X (restrict n X σ f) g h))))))))

  -- restrict also preserves identities
  restrict-id : (n : ℕᵉ) (X : SSTᵉ n) {v : ℕᵉ} (σ : Map n X v)
                → _=ᵉ_ {i} {Map n X v} (restrict n X σ (idF v)) σ
  restrict-id zeroᵉ X σ = reflᵉ
  restrict-id (succᵉ n) (X ,ᵉ A) {v} (σ ,ᵉ τ) =
    dep-pair-=ᵉ {i} {i} {Map n X v} {λ x → (h : Face v (succᵉ n)) → (A (restrict n X x h))} _ _
      ((restrict-id n X σ) ,ᵉ
      (funextᵉ {lzero} {i} {Face v (succᵉ n)} {λ h → (A (restrict n X σ h))} λ h →
        exo-concat {i}
          (exo-tr-pi {i} {lzero} {i} {Map n X v} (restrict-id n X σ) {Face v (succᵉ n)}
                     (λ x y → (A (restrict n X x y))))
          (exo-concat {i}
            (exo-tr-ap {i} {i} {Map n X v} {Map n X (succᵉ n)} {f = λ x → restrict n X x h} {P = λ s → (A s)}
                       (restrict-id n X σ))
            (exo-concat {i}
              (exo-tr-concat {i} {i} {Map n X (succᵉ n)} {λ s → (A s)}
                (restrict-⊙ n X σ (idF v) h)
                (exo-ap {i} {i} {Map n X v} {Map n X (succᵉ n)} (λ x → restrict n X x h) (restrict-id n X σ)))
              (tr-coh {i} {i} {lzero} {Map n X (succᵉ n)} (λ s → (A s))
                {Face v (succᵉ n)} {λ k → restrict n X σ k} τ (⊙-idl h)
                (exo-concat {i} (restrict-⊙ n X σ (idF v) h)
                            (exo-ap {i} {i} {Map n X v} {Map n X (succᵉ n)} (λ x → restrict n X x h) (restrict-id n X σ)))
                reflᵉ)))))

  -- The boundary of an (n+1)-vertex simplex in an SST of level n
  Boundaryᵉ : (n : ℕᵉ) → SSTᵉ n → UUᵉ i
  Boundaryᵉ n X = Map n X (succᵉ n)

  -- Truncation: forget the top level
  truncᵉ : (n : ℕᵉ) → SSTᵉ (succᵉ n) → SSTᵉ n
  truncᵉ n = pr1ᵉ
