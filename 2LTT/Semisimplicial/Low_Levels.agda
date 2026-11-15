{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Semisimplicial.Low_Levels where

open import 2LTT.Semisimplicial.Fibrancy public

-- Checks: SSTᵉ n at levels 1, 2, 3 gives points, edges and triangle boundaries.

-- Vertices of an edge
e0 e1 : Face twoᵉ oneᵉ
e0 = skip (take done)
e1 = take (skip done)

-- Vertices of a triangle
t0 t1 t2 : Face threeᵉ oneᵉ
t0 = skip (skip (take done))
t1 = skip (take (skip done))
t2 = take (skip (skip done))

-- Edges of the triangle
t01 t02 t12 : Face threeᵉ twoᵉ
t01 = skip (take (take done))
t02 = take (skip (take done))
t12 = take (take (skip done))

-- The endpoints of each edge are given by composition
_ : (t01 ⊙ e0 =ᵉ t0) ×ᵉ (t01 ⊙ e1 =ᵉ t1)
_ = reflᵉ ,ᵉ reflᵉ

_ : (t02 ⊙ e0 =ᵉ t0) ×ᵉ (t02 ⊙ e1 =ᵉ t2)
_ = reflᵉ ,ᵉ reflᵉ

_ : (t12 ⊙ e0 =ᵉ t1) ×ᵉ (t12 ⊙ e1 =ᵉ t2)
_ = reflᵉ ,ᵉ reflᵉ

module _ (i : Level) where

  -- Level 1: a type of points

  level-1 : SSTᵉ i oneᵉ ≅ (UU i)
  level-1 = (λ x → ((pr2ᵉ x) starᵉ)) ,ᵉ (λ x → starᵉ ,ᵉ (λ y → x)) ,ᵉ
            (λ a → reflᵉ) ,ᵉ (λ b → reflᵉ)

  -- Level 2: points and edges

  edge-boundary : {A : UU i} → A → A → (f : Face twoᵉ oneᵉ) → A
  edge-boundary x y (skip (take done)) = x
  edge-boundary x y (take (skip done)) = y

  fwd2 : SSTᵉ i twoᵉ → (Σ (UU i) (λ A → A → A → UU i))
  fwd2 ((t ,ᵉ A0) ,ᵉ A1) = (A0 starᵉ , (λ x y → A1 (starᵉ ,ᵉ edge-boundary x y)))

  bwd2 : (Σ (UU i) (λ A → A → A → UU i)) → SSTᵉ i twoᵉ
  bwd2 (B0 , B1) = (starᵉ ,ᵉ (λ _ → B0)) ,ᵉ (λ s → B1 ((pr2ᵉ s e0)) ((pr2ᵉ s e1)))

  from-endpoints : {A0 : ⊤ᵉ → UU i} → Map i oneᵉ (starᵉ ,ᵉ A0) twoᵉ
                                    → Map i oneᵉ (starᵉ ,ᵉ A0) twoᵉ
  from-endpoints (t ,ᵉ τ) = starᵉ ,ᵉ edge-boundary ((τ e0)) ((τ e1))

  from-endpoints-id : {A0 : ⊤ᵉ → UU i} (s : Map i oneᵉ (starᵉ ,ᵉ A0) twoᵉ)
                      → from-endpoints s =ᵉ s
  from-endpoints-id (t ,ᵉ τ) =
    dep-pair-=ᵉ _ _ (reflᵉ ,ᵉ (funextᵉ λ {(skip (take done)) → reflᵉ
                                        ; (take (skip done)) → reflᵉ}))

  bwd-fwd : (X : SSTᵉ i twoᵉ) → bwd2 (fwd2 X) =ᵉ X
  bwd-fwd ((t ,ᵉ A0) ,ᵉ A1) = exo-ap (λ h → (starᵉ ,ᵉ A0) ,ᵉ (λ s → A1 (h s))) (funextᵉ from-endpoints-id)

  level-2 : SSTᵉ i twoᵉ ≅ (Σ (UU i) (λ A → A → A → UU i))
  level-2 = fwd2 ,ᵉ (bwd2 ,ᵉ bwd-fwd ,ᵉ (λ b → reflᵉ))

  -- Level 3: the boundary of a triangle is three vertices and three edges

  triangle-boundary : (A0 : ⊤ᵉ → UU i) (A1 : Map i oneᵉ (starᵉ ,ᵉ A0) twoᵉ → UU i)
    → Boundaryᵉ i twoᵉ ((starᵉ ,ᵉ A0) ,ᵉ A1)
      =ᵉ Σᵉ (Σᵉ (⊤ᵉ {i}) (λ _ → Face threeᵉ oneᵉ → (A0 starᵉ)))
            (λ τ → (f : Face threeᵉ twoᵉ) → (A1 (starᵉ ,ᵉ (λ g → pr2ᵉ τ (f ⊙ g)))))
  triangle-boundary A0 A1 = reflᵉ
