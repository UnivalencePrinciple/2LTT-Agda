{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Semisimplicial.Untruncated where

open import 2LTT.Semisimplicial.Fibrancy public

-- The homotopy limit of the tower of truncations, assuming ℕᵉ is cofibrant.
-- It corresponds to SS in Section 3 of "Extending Homotopy Type Theory with
-- Strict Equality" (2016) paper.
-- Under axiom (A2) the strict limit SSTᵉ∞ is fibrant, and it is equivalent to
-- the homotopy limit (SST∞-to-holim-is-equiv).

-- The strict limit of a tower
Tower-limᵉ : {l : Level} (A : ℕᵉ → UUᵉ l) (p : (n : ℕᵉ) → A (succᵉ n) → A n) → UUᵉ l
Tower-limᵉ {l} A p =
  Σᵉ {l} {l} ((n : ℕᵉ) → A n) (λ X → (n : ℕᵉ) → _=ᵉ_ {l} {A n} (p n (X (succᵉ n))) (X n))

-- Axiom (A2) of "Two-Level Type Theory and Applications" paper: towers of
-- fibrations over a fibrant base have fibrant limits
Fibrant-Tower-Limits : (l : Level) → UUᵉ (lsuc l)
Fibrant-Tower-Limits l = (A : ℕᵉ → UUᵉ l) (p : (n : ℕᵉ) → A (succᵉ n) → A n)
                          → isFibrant {l} (A zeroᵉ) → ((n : ℕᵉ) → isFibration {l} {l} (p n))
                          → isFibrant {l} (Tower-limᵉ {l} A p)

-- The fibre of the first projection over a is B a
fibre-pr1ᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (a : A)
              → _≅_ {i ⊔ j} {j} (Σᵉ {i ⊔ j} {i} (Σᵉ {i} {j} A B) (λ w → _=ᵉ_ {i} {A} (pr1ᵉ w) a)) (B a)
fibre-pr1ᵉ {i} {j} {A} {B} a = to ,ᵉ from ,ᵉ from-to ,ᵉ (λ b → reflᵉ)
  where
  Fib : UUᵉ (i ⊔ j)
  Fib = Σᵉ {i ⊔ j} {i} (Σᵉ {i} {j} A B) (λ w → _=ᵉ_ {i} {A} (pr1ᵉ w) a)

  to : Fib → B a
  to ((a' ,ᵉ b) ,ᵉ p) = exo-tr {i} {j} {A} B p b

  from : B a → Fib
  from x = (a ,ᵉ x) ,ᵉ reflᵉ

  from-to : (w : Fib) → _=ᵉ_ {i ⊔ j} {Fib} (from (to w)) w
  from-to ((a' ,ᵉ b) ,ᵉ p) =
    dep-pair-=ᵉ {i ⊔ j} {i} {Σᵉ {i} {j} A B} {λ w → _=ᵉ_ {i} {A} (pr1ᵉ w) a} _ _
      (dep-pair-=ᵉ {i} {j} {A} {B} _ _
        (exo-inv {i} p ,ᵉ
         exo-concat {j} (exo-tr-concat {i} {j} {A} {B} p (exo-inv {i} p))
                        (exo-tr-right-law {i} {j} {A} B p)) ,ᵉ
       UIPᵉ {i} _ _)

-- Paths out of a point form a contractible type
based-path-contr : {l : Level} {A : UU l} (a : A) → is-contr {l} (Σ {l} {l} A (λ x → Id {l} a x))
based-path-contr a = (a , refl) , λ {(a' , refl) → refl}

-- Fillers of a triangle of paths form a contractible type
filler-contr : {l : Level} {A : UU l} {a b d : A} (p : Id {l} a b) (u : Id {l} a d)
                → is-contr {l} (Σ {l} {l} (Id {l} b d) (λ h → Id {l} (_·_ {l} p h) u))
filler-contr refl refl = (refl , refl) , (λ {(p , refl) → refl})

-- Path lifting along a first projection: an element x1 over xn is moved
-- over y along paths h and pr2 z
lift-step : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ {l} {l'} A F) (xn : A)
            (h : Id {l} (pr1 x1) xn) (z : Σ {l} {l} A (λ y → Id {l} y xn))
            → Σ {l'} {l ⊔ l'} (F (pr1 z)) (λ f → Id {l ⊔ l'} {Σ {l} {l'} A F} (pr1 z , f) x1)
lift-step x1 _ refl (_ , refl) = pr2 x1 , refl

lift-step-coh : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ {l} {l'} A F) (xn : A)
                (h : Id {l} (pr1 x1) xn) (z : Σ {l} {l} A (λ y → Id {l} y xn))
                → Id {l} (_·_ {l} (ap {l ⊔ l'} {l} {Σ {l} {l'} A F} {A} pr1
                                      (pr2 (lift-step {l} {l'} {A} {F} x1 xn h z))) h)
                         (pr2 z)
lift-step-coh x1 _ refl (_ , refl) = refl

-- On strict data, lifting does nothing
lift-step-strict : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ {l} {l'} A F) (xn : A)
                    (e : _=ᵉ_ {l} {A} (pr1 x1) xn) (z : Σ {l} {l} A (λ y → Id {l} y xn))
                    → _=ᵉ_ {l} {Σ {l} {l} A (λ y → Id {l} y xn)} z (xn , refl)
                    → _=ᵉ_ {l ⊔ l'} {Σ {l ⊔ l'} {l ⊔ l'} (Σ {l} {l'} A F) (λ w → Id {l ⊔ l'} w x1)}
                        ((pr1 z , pr1 (lift-step {l} {l'} {A} {F} x1 xn (map-=ᵉ {l} {A} e) z)) ,
                         pr2 (lift-step {l} {l'} {A} {F} x1 xn (map-=ᵉ {l} {A} e) z))
                        (x1 , refl)
lift-step-strict x1 xn reflᵉ z reflᵉ = reflᵉ

module _ (i : Level) where

  -- The exo-type of untruncated semisimplicial types: the strict limit of the
  -- tower of truncations
  SSTᵉ∞ : UUᵉ (lsuc i)
  SSTᵉ∞ = Tower-limᵉ {lsuc i} (SSTᵉ i) (truncᵉ i)

  -- Truncation is a fibration
  truncᵉ-is-fibration : (n : ℕᵉ) → isFibration {lsuc i} {lsuc i} (truncᵉ i n)
  truncᵉ-is-fibration n X =
    isFibrant-iso {lsuc i}
      (≅-sym {lsuc i} {lsuc i}
        (fibre-pr1ᵉ {lsuc i} {lsuc i} {SSTᵉ i n} {λ Y → Map i n Y (succᵉ n) → UU i} X))
      (families-are-fibrant i (Map-is-fibrant i n X (succᵉ n)))

  -- Under (A2), untruncated semisimplicial types form an inner type
  module _ (A2 : Fibrant-Tower-Limits (lsuc i)) where

    SSTᵉ∞-is-fibrant : isFibrant {lsuc i} SSTᵉ∞
    SSTᵉ∞-is-fibrant = A2 (SSTᵉ i) (truncᵉ i) (isFibrant-⊤ᵉ {lsuc i}) truncᵉ-is-fibration

    SST∞ : UU (lsuc i)
    SST∞ = fibrant-match SSTᵉ∞-is-fibrant

    SST∞-≅ : _≅_ {lsuc i} {lsuc i} SSTᵉ∞ (SST∞)
    SST∞-≅ = fibrant-witness SSTᵉ∞-is-fibrant

module _ (i : Level) (ℕᵉ-is-cofibrant : isCofibrant {lzero} ℕᵉ (lsuc i)) where

  -- The type of coherences of a sequence at level n
  Coh : ((n : ℕᵉ) → SST i n) → ℕᵉ → UU (lsuc i)
  Coh X n = Id {lsuc i} {SST i n} (trunc i n (X (succᵉ n))) (X n)

  -- Sequences of inner types form a fibrant exo-type
  Seq-is-fibrant : (Y : ℕᵉ → UU (lsuc i)) → isFibrant {lsuc i} (Πᵉ {lzero} {lsuc i} ℕᵉ (λ n → (Y n)))
  Seq-is-fibrant Y = Π-fibrant-witness (ℕᵉ-is-cofibrant Y)

  -- The inner type of sequences of semisimplicial types of level n
  SST-Seq : UU (lsuc i)
  SST-Seq = fibrant-match (Seq-is-fibrant (SST i))

  SST-Seq-≅ : _≅_ {lsuc i} {lsuc i} (SST-Seq) (Πᵉ {lzero} {lsuc i} ℕᵉ (λ n → (SST i n)))
  SST-Seq-≅ = ≅-sym {lsuc i} {lsuc i} (fibrant-witness (Seq-is-fibrant (SST i)))

  _at_ : SST-Seq → (n : ℕᵉ) → SST i n
  s at n = pr1ᵉ SST-Seq-≅ (s) n

  -- The inner type of coherences for a sequence
  SST-Coh : SST-Seq → UU (lsuc i)
  SST-Coh s = fibrant-match (Seq-is-fibrant (Coh (λ n → s at n)))

  SST-Coh-≅ : (s : SST-Seq)
                → _≅_ {lsuc i} {lsuc i} ((SST-Coh s)) (Πᵉ {lzero} {lsuc i} ℕᵉ (λ n → (Coh (λ m → s at m) n)))
  SST-Coh-≅ s = ≅-sym {lsuc i} {lsuc i} (fibrant-witness (Seq-is-fibrant (Coh (λ n → s at n))))

  -- The homotopy limit, an inner type
  SST-holim : UU (lsuc i)
  SST-holim = Σ {lsuc i} {lsuc i} SST-Seq SST-Coh

  -- Projections and their coherence
  proj-holim : (n : ℕᵉ) → SST-holim → SST i n
  proj-holim n x = pr1 x at n

  proj-holim-coh : (n : ℕᵉ) (x : SST-holim)
                   → Id {lsuc i} {SST i n} (trunc i n (proj-holim (succᵉ n) x)) (proj-holim n x)
  proj-holim-coh n (s , hs) = pr1ᵉ (SST-Coh-≅ s) (hs) n

  -- Elements of SST-holim are exactly the homotopy coherent sequences
  Holimᵉ : UUᵉ (lsuc i)
  Holimᵉ = Σᵉ {lsuc i} {lsuc i} ((n : ℕᵉ) → (SST i n)) (λ X → (n : ℕᵉ) → (Coh X n))

  holim-≅ : _≅_ {lsuc i} {lsuc i} (SST-holim) Holimᵉ
  holim-≅ = ≅-trans {lsuc i} {lsuc i} {lsuc i} (≅-sym {lsuc i} {lsuc i}
            (exo-Σᵉ-equiv {lsuc i} {lsuc i} {SST-Seq} {SST-Coh}))
            (Σᵉ-iso-cong {lsuc i} {lsuc i} {SST-Seq} {(n : ℕᵉ) → SST i n} {SST-Coh} {λ X → (n : ℕᵉ) → Coh X n}
                          (pr1ᵉ SST-Seq-≅) {pr2ᵉ SST-Seq-≅}
                          (λ s → pr1ᵉ (SST-Coh-≅ s))
                          {λ s → pr2ᵉ (SST-Coh-≅ s)})

  to-holim : Holimᵉ → SST-holim
  to-holim = pr1ᵉ (pr2ᵉ holim-≅)

  -- Universal property: maps into SST-holim are exactly the cones over the tower
  Coneᵉ : {j : Level} → UUᵉ j → UUᵉ (lsuc i ⊔ j)
  Coneᵉ {j} Z = Σᵉ {lsuc i ⊔ j} {lsuc i ⊔ j} ((n : ℕᵉ) → Z → (SST i n))
                    (λ f → (n : ℕᵉ) (z : Z) → (Id {lsuc i} {SST i n} (trunc i n (f (succᵉ n) z)) (f n z)))

  holim-UP : {j : Level} (Z : UUᵉ j) → _≅_ {lsuc i ⊔ j} {lsuc i ⊔ j} (Z → SST-holim) (Coneᵉ Z)
  holim-UP {j} Z =
    ≅-trans {lsuc i ⊔ j} {lsuc i ⊔ j} {lsuc i ⊔ j}
      (Πᵉ-iso-cong' {j} {lsuc i} {Z} {Z} {λ _ → SST-holim} {λ _ → Holimᵉ} (≅-refl {j} {Z}) (λ b → holim-≅))
      (≅-trans {lsuc i ⊔ j} {lsuc i ⊔ j} {lsuc i ⊔ j}
        (Πᵉ-Σᵉ-distr {j} {lsuc i} {lsuc i} {Z} {λ _ → (n : ℕᵉ) → SST i n} {λ _ X → (n : ℕᵉ) → Coh X n})
        swap)
    where
    swap : _≅_ {lsuc i ⊔ j} {lsuc i ⊔ j}
             (Σᵉ {lsuc i ⊔ j} {lsuc i ⊔ j} ((z : Z) → (n : ℕᵉ) → SST i n) (λ f → (z : Z) → (n : ℕᵉ) → Coh (f z) n))
             (Coneᵉ Z)
    swap = (λ (f ,ᵉ h) → (λ n z → f z n) ,ᵉ (λ n z → h z n)) ,ᵉ
           (λ (f ,ᵉ h) → (λ z n → f n z) ,ᵉ (λ z n → h n z)) ,ᵉ
           (λ _ → reflᵉ) ,ᵉ
           (λ _ → reflᵉ)

  -- A cone of inner maps gives an inner map into SST-holim
  SST-holim-intro : {j : Level} {Z : UU j}
                    (f : (n : ℕᵉ) → Z → SST i n)
                    (h : (n : ℕᵉ) (z : Z) → Id {lsuc i} {SST i n} (trunc i n (f (succᵉ n) z)) (f n z))
                    → Z → SST-holim
  SST-holim-intro f h z = to-holim ((λ n → (f n z)) ,ᵉ (λ n → (h n z)))

  -- Its projections are the given maps
  proj-holim-intro : {j : Level} {Z : UU j}
                      (f : (n : ℕᵉ) → Z → SST i n)
                      (h : (n : ℕᵉ) (z : Z) → Id {lsuc i} {SST i n} (trunc i n (f (succᵉ n) z)) (f n z))
                      (n : ℕᵉ) (z : Z)
                      → _=ᵉ_ {lsuc i} {SST i n} ((proj-holim n (SST-holim-intro f h z))) ((f n z))
  proj-holim-intro f h n z =
    exo-ap {lsuc i} {lsuc i} {(m : ℕᵉ) → SST i m} {SST i n} (λ Y → Y n)
           (pr2ᵉ (pr2ᵉ (pr2ᵉ SST-Seq-≅)) (λ m → (f m z)))

  -- The strict limit maps into SST-holim
  strict-Holimᵉ : (X : (n : ℕᵉ) → (SST i n))
                  → ((n : ℕᵉ) → _=ᵉ_ {lsuc i} {SST i n} ((trunc i n (X (succᵉ n)))) (X n)) → Holimᵉ
  strict-Holimᵉ X e = X ,ᵉ (λ n → (map-=ᵉ {lsuc i} {SST i n} (e n)))

  strict-to-Holimᵉ : SSTᵉ∞ i → Holimᵉ
  strict-to-Holimᵉ (X ,ᵉ e) =
    strict-Holimᵉ (λ n → pr1ᵉ (SST-≅ i n) (X n))
                  (λ n → exo-ap {lsuc i} {lsuc i} {SSTᵉ i n} {SST i n} (pr1ᵉ (SST-≅ i n)) (e n))

  strict-to-holim : SSTᵉ∞ i → SST-holim
  strict-to-holim x = to-holim (strict-to-Holimᵉ x)

  -- Under (A2), this is an inner map SST∞ → SST-holim
  SST∞-to-holim : (A2 : Fibrant-Tower-Limits (lsuc i)) → SST∞ i A2 → SST-holim
  SST∞-to-holim A2 x = strict-to-holim (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (x))

  -- Two homotopy coherent sequences are identified in SST-holim once they are
  -- related by pointwise paths and fillers
  holim-Id-pt : (Y : (n : ℕᵉ) → SST i n) → ℕᵉ → UU (lsuc i)
  holim-Id-pt Y n = Σ {lsuc i} {lsuc i} (SST i n) (λ x → Id {lsuc i} {SST i n} (Y n) x)

  holim-Id-coh : (Y : (n : ℕᵉ) → SST i n) (k : (n : ℕᵉ) → Id {lsuc i} {SST i n} (trunc i n (Y (succᵉ n))) (Y n))
                  → ((n : ℕᵉ) → (holim-Id-pt Y n)) → ℕᵉ → UU (lsuc i)
  holim-Id-coh Y k w n =
    Σ {lsuc i} {lsuc i} (Id {lsuc i} {SST i n} (trunc i n (pr1 (w (succᵉ n)))) (pr1 (w n)))
      (λ h → Id {lsuc i}
                (_·_ {lsuc i} (ap {lsuc i} {lsuc i} {SST i (succᵉ n)} {SST i n} (trunc i n) (pr2 (w (succᵉ n)))) h)
                (_·_ {lsuc i} (k n) (pr2 (w n))))

  holim-Id : (Y : (n : ℕᵉ) → SST i n) (k : (n : ℕᵉ) → Id {lsuc i} {SST i n} (trunc i n (Y (succᵉ n))) (Y n))
              (w : (n : ℕᵉ) → (holim-Id-pt Y n)) (v : (n : ℕᵉ) → (holim-Id-coh Y k w n))
              → Id {lsuc i} {SST-holim}
                  (to-holim ((λ n → (Y n)) ,ᵉ (λ n → (k n))))
                  (to-holim ((λ n → (pr1 (w n))) ,ᵉ (λ n → (pr1 (v n)))))
  holim-Id Y k w v =
    contr-Σᵉ-const {lsuc i} {lsuc i} {lsuc i}
      {A = (n : ℕᵉ) → holim-Id-pt Y n}
      {B = λ w → (n : ℕᵉ) → holim-Id-coh Y k w n}
      {Z = SST-holim}
      (Seq-is-fibrant (holim-Id-pt Y))
      (λ w → Seq-is-fibrant (holim-Id-coh Y k w))
      (contr-preserve-witness (ℕᵉ-is-cofibrant (holim-Id-pt Y)) (λ n → based-path-contr {lsuc i} (Y n)))
      (λ w → contr-preserve-witness (ℕᵉ-is-cofibrant (holim-Id-coh Y k w))
              (λ n → filler-contr {lsuc i} (ap {lsuc i} {lsuc i} {SST i (succᵉ n)} {SST i n} (trunc i n) (pr2 (w (succᵉ n))))
                                      (_·_ {lsuc i} (k n) (pr2 (w n)))))
      (λ u → to-holim ((λ n → (pr1 (pr1ᵉ u n))) ,ᵉ (λ n → (pr1 (pr2ᵉ u n)))))
      ((λ n → (Y n , refl)) ,ᵉ (λ n → (k n , _⁻¹ {lsuc i} (right-unit {lsuc i} (k n)))))
      (w ,ᵉ v)

  -- The inverse of the comparison map, by lifting paths level by level
  lift-seq : (W : Holimᵉ) (n : ℕᵉ) → Σ {lsuc i} {lsuc i} (SST i n) (λ y → Id {lsuc i} {SST i n} y (pr1ᵉ W n))
  lift-seq W zeroᵉ = pr1ᵉ W zeroᵉ , refl
  lift-seq W (succᵉ n) = (pr1 (lift-seq W n) , pr1 r) , pr2 r
    where
    r = lift-step {lsuc i} {lsuc i} {SST i n} (pr1ᵉ W (succᵉ n)) (pr1ᵉ W n) (pr2ᵉ W n) (lift-seq W n)

  Holimᵉ-to-strict : Holimᵉ → SSTᵉ∞ i
  Holimᵉ-to-strict W = (λ n → pr1ᵉ (pr2ᵉ (SST-≅ i n)) ((pr1 (lift-seq W n)))) ,ᵉ (λ n → reflᵉ)

  -- It is a strict retraction
  lift-seq-strict : (x : SSTᵉ∞ i) (n : ℕᵉ)
                    → _=ᵉ_ {lsuc i}
                        {Σ {lsuc i} {lsuc i} (SST i n) (λ y → Id {lsuc i} {SST i n} y (pr1ᵉ (strict-to-Holimᵉ x) n))}
                        ((lift-seq (strict-to-Holimᵉ x) n))
                        ((pr1ᵉ (strict-to-Holimᵉ x) n , refl))
  lift-seq-strict x zeroᵉ = reflᵉ
  lift-seq-strict (X ,ᵉ e) (succᵉ n) =
    lift-step-strict {lsuc i} {lsuc i} {SST i n}
                    (pr1ᵉ (SST-≅ i (succᵉ n)) (X (succᵉ n))) (pr1ᵉ (SST-≅ i n) (X n))
                    (exo-ap {lsuc i} {lsuc i} {SSTᵉ i n} {SST i n} (pr1ᵉ (SST-≅ i n)) (e n))
                    ((lift-seq (strict-to-Holimᵉ (X ,ᵉ e)) n))
                    (lift-seq-strict (X ,ᵉ e) n)

  Holimᵉ-to-strict-retr : (x : SSTᵉ∞ i) → _=ᵉ_ {lsuc i} {SSTᵉ∞ i} (Holimᵉ-to-strict (strict-to-Holimᵉ x)) x
  Holimᵉ-to-strict-retr x =
    dep-pair-=ᵉ {lsuc i} {lsuc i} {(n : ℕᵉ) → SSTᵉ i n}
                {λ X → (n : ℕᵉ) → _=ᵉ_ {lsuc i} {SSTᵉ i n} (truncᵉ i n (X (succᵉ n))) (X n)} _ _
      (funextᵉ {lzero} {lsuc i} {ℕᵉ} {SSTᵉ i} (λ n → exo-concat {lsuc i}
                (exo-ap {lsuc i} {lsuc i}
                        {Σ {lsuc i} {lsuc i} (SST i n) (λ y → Id {lsuc i} {SST i n} y (pr1ᵉ (strict-to-Holimᵉ x) n))}
                        {SSTᵉ i n}
                        (λ t → pr1ᵉ (pr2ᵉ (SST-≅ i n)) ((pr1 t))) (lift-seq-strict x n))
                (pr1ᵉ (pr2ᵉ (pr2ᵉ (SST-≅ i n))) (pr1ᵉ x n))) ,ᵉ
      funextᵉ {lzero} {lsuc i} (λ n → UIPᵉ {lsuc i} _ _))

  -- It is a section up to identification
  strict-Holimᵉ-cong : (X X' : (n : ℕᵉ) → (SST i n)) → _=ᵉ_ {lsuc i} {(n : ℕᵉ) → SST i n} X X'
                        → (e : (n : ℕᵉ) → _=ᵉ_ {lsuc i} {SST i n} ((trunc i n (X (succᵉ n)))) (X n))
                          (e' : (n : ℕᵉ) → _=ᵉ_ {lsuc i} {SST i n} ((trunc i n (X' (succᵉ n)))) (X' n))
                        → _=ᵉ_ {lsuc i} {Holimᵉ} (strict-Holimᵉ X e) (strict-Holimᵉ X' e')
  strict-Holimᵉ-cong X .X reflᵉ e e' =
    exo-ap {lsuc i} {lsuc i} {(n : ℕᵉ) → _=ᵉ_ {lsuc i} {SST i n} (trunc i n (X (succᵉ n))) (X n)} {Holimᵉ}
           (strict-Holimᵉ X) (funextᵉ {lzero} {lsuc i} (λ n → UIPᵉ {lsuc i} (e n) (e' n)))

  Holimᵉ-to-strict-sec : (W : Holimᵉ)
                         → Id {lsuc i} {SST-holim} (strict-to-holim (Holimᵉ-to-strict W)) (to-holim W)
  Holimᵉ-to-strict-sec W =
    _·_ {lsuc i} {SST-holim}
      (=ᵉ-to-Id {lsuc i} {SST-holim}
        (exo-ap {lsuc i} {lsuc i} {Holimᵉ} {SST-holim} to-holim
              (strict-Holimᵉ-cong _ _
                (funextᵉ {lzero} {lsuc i} (λ n → pr2ᵉ (pr2ᵉ (pr2ᵉ (SST-≅ i n))) ((pr1 (lift-seq W n)))))
                _ (λ n → reflᵉ))))
      (holim-Id (λ n → pr1 (lift-seq W n)) (λ n → refl)
                (λ n → (pr1ᵉ W n , pr2 (lift-seq W n)))
                (λ n → (pr2ᵉ W n ,
                    lift-step-coh {lsuc i} {lsuc i} {SST i n} (pr1ᵉ W (succᵉ n)) (pr1ᵉ W n) (pr2ᵉ W n) (lift-seq W n))))

  -- Under (A2), the strict limit is the homotopy limit
  SST∞-to-holim-is-equiv : (A2 : Fibrant-Tower-Limits (lsuc i))
                           → isEquiv {lsuc i} {lsuc i} {SST∞ i A2} {SST-holim} (SST∞-to-holim A2)
  SST∞-to-holim-is-equiv A2 =
    invertibles-are-equiv {lsuc i} {lsuc i} {SST∞ i A2} {SST-holim} (SST∞-to-holim A2)
      ((λ y → pr1ᵉ (SST∞-≅ i A2) (Holimᵉ-to-strict (pr1ᵉ holim-≅ (y)))) ,
      (λ x → =ᵉ-to-Id {lsuc i} {SST∞ i A2}
          (exo-concat {lsuc i}
            (exo-ap {lsuc i} {lsuc i} {Holimᵉ} {SST∞ i A2} (λ W → pr1ᵉ (SST∞-≅ i A2) (Holimᵉ-to-strict W))
                    (pr2ᵉ (pr2ᵉ (pr2ᵉ holim-≅)) (strict-to-Holimᵉ (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (x)))))
            (exo-concat {lsuc i}
              (exo-ap {lsuc i} {lsuc i} {SSTᵉ∞ i} {SST∞ i A2} (pr1ᵉ (SST∞-≅ i A2))
                      (Holimᵉ-to-strict-retr (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (x))))
              (pr2ᵉ (pr2ᵉ (pr2ᵉ (SST∞-≅ i A2))) (x))))) ,
      (λ y → _·_ {lsuc i} {SST-holim}
               (=ᵉ-to-Id {lsuc i} {SST-holim}
                 (exo-ap {lsuc i} {lsuc i} {SSTᵉ∞ i} {SST-holim} strict-to-holim
                         (pr1ᵉ (pr2ᵉ (pr2ᵉ (SST∞-≅ i A2))) (Holimᵉ-to-strict (pr1ᵉ holim-≅ (y))))))
               (_·_ {lsuc i} {SST-holim}
                 (Holimᵉ-to-strict-sec (pr1ᵉ holim-≅ (y)))
                 (=ᵉ-to-Id {lsuc i} {SST-holim} (pr1ᵉ (pr2ᵉ (pr2ᵉ holim-≅)) (y))))))
