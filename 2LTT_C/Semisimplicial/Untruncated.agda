{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Semisimplicial.Untruncated where

open import 2LTT_C.Semisimplicial.Fibrancy public
open import 2LTT_C.Coercion.Fibrant_Functions public

-- The homotopy limit of the tower of truncations, assuming ℕᵉ is cofibrant.
-- It corresponds to SS in Section 3 of "Extending Homotopy Type Theory with
-- Strict Equality" (2016) paper.
-- Under axiom (A2) the strict limit SSTᵉ∞ is fibrant, and it is equivalent to
-- the homotopy limit (SST∞-to-holim-is-equiv).

-- The strict limit of a tower
Tower-limᵉ : {l : Level} (A : ℕᵉ → UUᵉ l) (p : (n : ℕᵉ) → A (succᵉ n) → A n) → UUᵉ l
Tower-limᵉ A p = Σᵉ ((n : ℕᵉ) → A n) (λ X → (n : ℕᵉ) → p n (X (succᵉ n)) =ᵉ X n)

-- Axiom (A2) of "Two-Level Type Theory and Applications" paper: towers of
-- fibrations over a fibrant base have fibrant limits
Fibrant-Tower-Limits : (l : Level) → UUᵉ (lsuc l)
Fibrant-Tower-Limits l = (A : ℕᵉ → UUᵉ l) (p : (n : ℕᵉ) → A (succᵉ n) → A n)
                          → isFibrant (A zeroᵉ) → ((n : ℕᵉ) → isFibration (p n))
                          → isFibrant (Tower-limᵉ A p)

-- The fibre of the first projection over a is B a
fibre-pr1ᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} (a : A)
              → Σᵉ (Σᵉ A B) (λ w → pr1ᵉ w =ᵉ a) ≅ B a
fibre-pr1ᵉ {B = B} a =
  (λ {((a' ,ᵉ b) ,ᵉ p) → exo-tr B p b}) ,ᵉ
  (λ x → ((a ,ᵉ x)) ,ᵉ reflᵉ) ,ᵉ
  (λ {((a' ,ᵉ b) ,ᵉ p) →
    dep-pair-=ᵉ _ _
      (dep-pair-=ᵉ _ _
        (exo-inv p ,ᵉ exo-concat (exo-tr-concat p (exo-inv p)) (exo-tr-right-law B p)) ,ᵉ UIPᵉ _ _)}) ,ᵉ
  (λ b → reflᵉ)

-- Paths out of a point form a contractible type
based-path-contr : {l : Level} {A : UU l} (a : A) → is-contr (Σ A (λ x → Id a x))
based-path-contr a = (a , refl) , λ {(a' , refl) → refl}

-- Fillers of a triangle of paths form a contractible type
filler-contr : {l : Level} {A : UU l} {a b d : A} (p : Id a b) (u : Id a d)
                → is-contr (Σ (Id b d) (λ h → Id (p · h) u))
filler-contr refl refl = (refl , refl) , (λ {(p , refl) → refl})

-- Path lifting along a first projection: an element x1 over xn is moved
-- over y along paths h and pr2 z
lift-step : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ A F) (xn : A)
            (h : Id (pr1 x1) xn) (z : Σ A (λ y → Id y xn))
            → Σ (F (pr1 z)) (λ f → Id {A = Σ A F} (pr1 z , f) x1)
lift-step x1 _ refl (_ , refl) = pr2 x1 , refl

lift-step-coh : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ A F) (xn : A)
                (h : Id (pr1 x1) xn) (z : Σ A (λ y → Id y xn))
                → Id (ap pr1 (pr2 (lift-step x1 xn h z)) · h) (pr2 z)
lift-step-coh x1 _ refl (_ , refl) = refl

-- On strict data, lifting does nothing
lift-step-strict : {l l' : Level} {A : UU l} {F : A → UU l'} (x1 : Σ A F) (xn : C A)
                    (e : c (pr1 x1) =ᵉ xn) (z : C (Σ A (λ y → Id y (ic xn))))
                    → z =ᵉ c (ic xn , refl)
                    → c {A = Σ (Σ A F) (λ w → Id w x1)}
                        ((pr1 (ic z) , pr1 (lift-step x1 (ic xn) (map-=ᵉ {u = pr1 x1} {v = ic xn} e) (ic z))) ,
                        pr2 (lift-step x1 (ic xn) (map-=ᵉ {u = pr1 x1} {v = ic xn} e) (ic z)))
                      =ᵉ c (x1 , refl)
lift-step-strict x1 xn reflᵉ z reflᵉ = reflᵉ

module _ (i : Level) where

  -- The exo-type of untruncated semisimplicial types: the strict limit of the
  -- tower of truncations
  SSTᵉ∞ : UUᵉ (lsuc i)
  SSTᵉ∞ = Tower-limᵉ (SSTᵉ i) (truncᵉ i)

  -- Truncation is a fibration
  truncᵉ-is-fibration : (n : ℕᵉ) → isFibration (truncᵉ i n)
  truncᵉ-is-fibration n =
    λ X → isFibrant-iso (≅-sym (fibre-pr1ᵉ X))
      (families-are-fibrant i (Map-is-fibrant i n X (succᵉ n)))

  -- Under (A2), untruncated semisimplicial types form an inner type
  module _ (A2 : Fibrant-Tower-Limits (lsuc i)) where

    SSTᵉ∞-is-fibrant : isFibrant SSTᵉ∞
    SSTᵉ∞-is-fibrant = A2 (SSTᵉ i) (truncᵉ i) isFibrant-⊤ᵉ truncᵉ-is-fibration

    SST∞ : UU (lsuc i)
    SST∞ = fibrant-match SSTᵉ∞-is-fibrant

    SST∞-≅ : SSTᵉ∞ ≅ C SST∞
    SST∞-≅ = fibrant-witness SSTᵉ∞-is-fibrant

module _ (i : Level) (ℕᵉ-is-cofibrant : isCofibrant ℕᵉ (lsuc i)) where

  -- Sequences of inner types form a fibrant exo-type
  Seq-is-fibrant : (Y : ℕᵉ → UU (lsuc i)) → isFibrant (Πᵉ ℕᵉ (λ n → C (Y n)))
  Seq-is-fibrant Y = (ℕᵉ-is-cofibrant Y).Π-fibrant-witness

  -- The inner type of sequences of semisimplicial types of level n
  SST-Seq : UU (lsuc i)
  SST-Seq = fibrant-match (Seq-is-fibrant (SST i))

  SST-Seq-≅ : C SST-Seq ≅ Πᵉ ℕᵉ (λ n → C (SST i n))
  SST-Seq-≅ = ≅-sym (fibrant-witness (Seq-is-fibrant (SST i)))

  _at_ : SST-Seq → (n : ℕᵉ) → SST i n
  s at n = ic (pr1ᵉ SST-Seq-≅ (c s) n)

  -- The inner type of coherences for a sequence
  SST-Coh : SST-Seq → UU (lsuc i)
  SST-Coh s =
    fibrant-match (Seq-is-fibrant (λ n → Id (trunc i n (s at (succᵉ n))) (s at n)))

  SST-Coh-≅ : (s : SST-Seq)
                → C (SST-Coh s) ≅ Πᵉ ℕᵉ (λ n → C (Id (trunc i n (s at (succᵉ n))) (s at n)))
  SST-Coh-≅ s =
    ≅-sym (fibrant-witness (Seq-is-fibrant (λ n → Id (trunc i n (s at (succᵉ n))) (s at n))))

  -- The homotopy limit, an inner type
  SST-holim : UU (lsuc i)
  SST-holim = Σ SST-Seq SST-Coh

  -- Projections and their coherence
  proj-holim : (n : ℕᵉ) → SST-holim → SST i n
  proj-holim n x = pr1 x at n

  proj-holim-coh : (n : ℕᵉ) (x : SST-holim) → Id (trunc i n (proj-holim (succᵉ n) x)) (proj-holim n x)
  proj-holim-coh n (s , hs) = ic (pr1ᵉ (SST-Coh-≅ s) (c hs) n)

  -- Elements of SST-holim are exactly the homotopy coherent sequences
  Holimᵉ : UUᵉ (lsuc i)
  Holimᵉ = Σᵉ ((n : ℕᵉ) → C (SST i n))
              (λ X → (n : ℕᵉ) → C (Id (trunc i n (ic (X (succᵉ n)))) (ic (X n))))

  holim-≅ : C SST-holim ≅ Holimᵉ
  holim-≅ = ≅-trans (≅-sym exo-Σᵉ-equiv)
            (Σᵉ-iso-cong (pr1ᵉ SST-Seq-≅) {pr2ᵉ SST-Seq-≅}
                          (λ {(c s) → pr1ᵉ (SST-Coh-≅ s)})
                          {λ {(c s) → pr2ᵉ (SST-Coh-≅ s)}})

  to-holim : Holimᵉ → C SST-holim
  to-holim = pr1ᵉ (pr2ᵉ holim-≅)

  -- Universal property: maps into SST-holim are exactly the cones over the tower
  Coneᵉ : {j : Level} → UUᵉ j → UUᵉ (lsuc i ⊔ j)
  Coneᵉ Z = Σᵉ ((n : ℕᵉ) → Z → C (SST i n))
                (λ f → (n : ℕᵉ) (z : Z) → C (Id (trunc i n (ic (f (succᵉ n) z))) (ic (f n z))))

  holim-UP : {j : Level} (Z : UUᵉ j) → (Z → C SST-holim) ≅ Coneᵉ Z
  holim-UP Z =
    ≅-trans (Πᵉ-iso-cong' ≅-refl (λ b → holim-≅))
            (≅-trans Πᵉ-Σᵉ-distr
                    ((λ (f ,ᵉ h) → (λ n z → f z n) ,ᵉ (λ n z → h z n)) ,ᵉ
                    (λ (f ,ᵉ h) → (λ z n → f n z) ,ᵉ (λ z n → h n z)) ,ᵉ
                    (λ _ → reflᵉ) ,ᵉ
                    (λ _ → reflᵉ)))

  -- A cone of inner maps gives an inner map into SST-holim
  SST-holim-intro : {j : Level} {Z : UU j}
                    (f : (n : ℕᵉ) → Z → SST i n)
                    (h : (n : ℕᵉ) (z : Z) → Id (trunc i n (f (succᵉ n) z)) (f n z))
                    → Z → SST-holim
  SST-holim-intro f h z = ic (to-holim ((λ n → c (f n z)) ,ᵉ (λ n → c (h n z))))

  -- Its projections are the given maps
  proj-holim-intro : {j : Level} {Z : UU j}
                      (f : (n : ℕᵉ) → Z → SST i n)
                      (h : (n : ℕᵉ) (z : Z) → Id (trunc i n (f (succᵉ n) z)) (f n z))
                      (n : ℕᵉ) (z : Z) → c (proj-holim n (SST-holim-intro f h z)) =ᵉ c (f n z)
  proj-holim-intro f h n z = exo-ap (λ Y → Y n) (pr2ᵉ (pr2ᵉ (pr2ᵉ SST-Seq-≅)) (λ m → c (f m z)))

  -- The strict limit maps into SST-holim
  strict-Holimᵉ : (X : (n : ℕᵉ) → C (SST i n))
                  → ((n : ℕᵉ) → c (trunc i n (ic (X (succᵉ n)))) =ᵉ X n) → Holimᵉ
  strict-Holimᵉ X e = X ,ᵉ (λ n → c (map-=ᵉ (e n)))

  strict-to-Holimᵉ : SSTᵉ∞ i → Holimᵉ
  strict-to-Holimᵉ (X ,ᵉ e) =
    strict-Holimᵉ (λ n → pr1ᵉ (SST-≅ i n) (X n)) (λ n → exo-ap (pr1ᵉ (SST-≅ i n)) (e n))

  strict-to-holim : SSTᵉ∞ i → C SST-holim
  strict-to-holim x = to-holim (strict-to-Holimᵉ x)

  -- Under (A2), this is an inner map SST∞ → SST-holim
  SST∞-to-holim : (A2 : Fibrant-Tower-Limits (lsuc i)) → SST∞ i A2 → SST-holim
  SST∞-to-holim A2 x = ic (strict-to-holim (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (c x)))

  -- Two homotopy coherent sequences are identified in SST-holim once they are
  -- related by pointwise paths and fillers
  holim-Id-pt : (Y : (n : ℕᵉ) → SST i n) → ℕᵉ → UU (lsuc i)
  holim-Id-pt Y n = Σ (SST i n) (λ x → Id (Y n) x)

  holim-Id-coh : (Y : (n : ℕᵉ) → SST i n) (k : (n : ℕᵉ) → Id (trunc i n (Y (succᵉ n))) (Y n))
                  → ((n : ℕᵉ) → C (holim-Id-pt Y n)) → ℕᵉ → UU (lsuc i)
  holim-Id-coh Y k w n =
    Σ (Id (trunc i n (pr1 (ic (w (succᵉ n))))) (pr1 (ic (w n))))
      (λ h → Id (ap (trunc i n) (pr2 (ic (w (succᵉ n)))) · h) (k n · pr2 (ic (w n))))

  holim-Id : (Y : (n : ℕᵉ) → SST i n) (k : (n : ℕᵉ) → Id (trunc i n (Y (succᵉ n))) (Y n))
              (w : (n : ℕᵉ) → C (holim-Id-pt Y n)) (v : (n : ℕᵉ) → C (holim-Id-coh Y k w n))
              → Id (ic (to-holim ((λ n → c (Y n)) ,ᵉ (λ n → c (k n)))))
                  (ic (to-holim ((λ n → c (pr1 (ic (w n)))) ,ᵉ (λ n → c (pr1 (ic (v n)))))))
  holim-Id Y k w v =
    contr-Σᵉ-const
      {B = λ w → Πᵉ ℕᵉ (λ n → C (holim-Id-coh Y k w n))}
      (Seq-is-fibrant (holim-Id-pt Y))
      (λ w → Seq-is-fibrant (holim-Id-coh Y k w))
      (contr-preserve-witness (ℕᵉ-is-cofibrant (holim-Id-pt Y)) (λ n → based-path-contr (Y n)))
      (λ w → contr-preserve-witness (ℕᵉ-is-cofibrant (holim-Id-coh Y k w))
              (λ n → filler-contr (ap (trunc i n) (pr2 (ic (w (succᵉ n))))) (k n · pr2 (ic (w n)))))
      (λ u → to-holim ((λ n → c (pr1 (ic (pr1ᵉ u n)))) ,ᵉ (λ n → c (pr1 (ic (pr2ᵉ u n))))))
      ((λ n → c (Y n , refl)) ,ᵉ (λ n → c (k n , (right-unit (k n)) ⁻¹)))
      (w ,ᵉ v)

  -- The inverse of the comparison map, by lifting paths level by level
  lift-seq : (W : Holimᵉ) (n : ℕᵉ) → Σ (SST i n) (λ y → Id y (ic (pr1ᵉ W n)))
  lift-seq W zeroᵉ = ic (pr1ᵉ W zeroᵉ) , refl
  lift-seq W (succᵉ n) = (pr1 (lift-seq W n) , pr1 r) , pr2 r
    where
    r = lift-step (ic (pr1ᵉ W (succᵉ n))) (ic (pr1ᵉ W n)) (ic (pr2ᵉ W n)) (lift-seq W n)

  Holimᵉ-to-strict : Holimᵉ → SSTᵉ∞ i
  Holimᵉ-to-strict W = (λ n → pr1ᵉ (pr2ᵉ (SST-≅ i n)) (c (pr1 (lift-seq W n)))) ,ᵉ (λ n → reflᵉ)

  -- It is a strict retraction
  lift-seq-strict : (x : SSTᵉ∞ i) (n : ℕᵉ)
                    → c (lift-seq (strict-to-Holimᵉ x) n) =ᵉ c (ic (pr1ᵉ (strict-to-Holimᵉ x) n) , refl)
  lift-seq-strict x zeroᵉ = reflᵉ
  lift-seq-strict (X ,ᵉ e) (succᵉ n) =
    lift-step-strict (ic (pr1ᵉ (SST-≅ i (succᵉ n)) (X (succᵉ n)))) (pr1ᵉ (SST-≅ i n) (X n))
                    (exo-ap (pr1ᵉ (SST-≅ i n)) (e n))
                    (c (lift-seq (strict-to-Holimᵉ (X ,ᵉ e)) n))
                    (lift-seq-strict (X ,ᵉ e) n)

  Holimᵉ-to-strict-retr : (x : SSTᵉ∞ i) → Holimᵉ-to-strict (strict-to-Holimᵉ x) =ᵉ x
  Holimᵉ-to-strict-retr x =
    dep-pair-=ᵉ _ _
      (funextᵉ (λ n → exo-concat
                (exo-ap (λ t → pr1ᵉ (pr2ᵉ (SST-≅ i n)) (c (pr1 (ic t)))) (lift-seq-strict x n))
                (pr1ᵉ (pr2ᵉ (pr2ᵉ (SST-≅ i n))) (pr1ᵉ x n))) ,ᵉ
      funextᵉ (λ n → UIPᵉ _ _))

  -- It is a section up to identification
  strict-Holimᵉ-cong : (X X' : (n : ℕᵉ) → C (SST i n)) → X =ᵉ X'
                        → (e : (n : ℕᵉ) → c (trunc i n (ic (X (succᵉ n)))) =ᵉ X n)
                          (e' : (n : ℕᵉ) → c (trunc i n (ic (X' (succᵉ n)))) =ᵉ X' n)
                        → strict-Holimᵉ X e =ᵉ strict-Holimᵉ X' e'
  strict-Holimᵉ-cong X .X reflᵉ e e' = exo-ap (strict-Holimᵉ X) (funextᵉ (λ n → UIPᵉ (e n) (e' n)))

  Holimᵉ-to-strict-sec : (W : Holimᵉ) → Id (ic (strict-to-holim (Holimᵉ-to-strict W))) (ic (to-holim W))
  Holimᵉ-to-strict-sec W =
    cic-eq (exo-ap to-holim
              (strict-Holimᵉ-cong _ _
                (funextᵉ (λ n → pr2ᵉ (pr2ᵉ (pr2ᵉ (SST-≅ i n))) (c (pr1 (lift-seq W n)))))
                _ (λ n → reflᵉ)))
    · holim-Id (λ n → pr1 (lift-seq W n)) (λ n → refl)
                (λ n → c (ic (pr1ᵉ W n) , pr2 (lift-seq W n)))
                (λ n → c (ic (pr2ᵉ W n) ,
                    lift-step-coh (ic (pr1ᵉ W (succᵉ n))) (ic (pr1ᵉ W n)) (ic (pr2ᵉ W n)) (lift-seq W n)))

  -- Under (A2), the strict limit is the homotopy limit
  SST∞-to-holim-is-equiv : (A2 : Fibrant-Tower-Limits (lsuc i)) → isEquiv (SST∞-to-holim A2)
  SST∞-to-holim-is-equiv A2 =
    invertibles-are-equiv (SST∞-to-holim A2)
      ((λ y → ic (pr1ᵉ (SST∞-≅ i A2) (Holimᵉ-to-strict (pr1ᵉ holim-≅ (c y))))) ,
      (λ x → cic-eq
          (exo-concat
            (exo-ap (λ W → pr1ᵉ (SST∞-≅ i A2) (Holimᵉ-to-strict W))
                    (pr2ᵉ (pr2ᵉ (pr2ᵉ holim-≅)) (strict-to-Holimᵉ (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (c x)))))
            (exo-concat
              (exo-ap (pr1ᵉ (SST∞-≅ i A2)) (Holimᵉ-to-strict-retr (pr1ᵉ (pr2ᵉ (SST∞-≅ i A2)) (c x))))
              (pr2ᵉ (pr2ᵉ (pr2ᵉ (SST∞-≅ i A2))) (c x))))) ,
      (λ y → cic-eq (exo-ap strict-to-holim
                        (pr1ᵉ (pr2ᵉ (pr2ᵉ (SST∞-≅ i A2))) (Holimᵉ-to-strict (pr1ᵉ holim-≅ (c y)))))
              · (Holimᵉ-to-strict-sec (pr1ᵉ holim-≅ (c y))
              · cic-eq (pr1ᵉ (pr2ᵉ (pr2ᵉ holim-≅)) (c y)))))
