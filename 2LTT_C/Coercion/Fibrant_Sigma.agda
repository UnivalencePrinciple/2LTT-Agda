{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Sigma where


open import 2LTT_C.Coercion.Fibrant_Conversion public

--Fibrancy is preserved under Σᵉ
isFibrant-Σ : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Σᵉ A B)
isFibrant-Σ {i} {j} {A = A} {B = B} (isfibrant fr P) Q =
  isfibrant (Σ fr (λ x → frB (g (c x)))) (≅-trans iso-1 iso-2)
  where
  f : A → C fr
  f = pr1ᵉ P

  g : C fr → A
  g = pr1ᵉ (pr2ᵉ P)

  gf : (a : A) → (g (f a)) =ᵉ a
  gf = (pr1ᵉ (pr2ᵉ (pr2ᵉ P)))

  frB : (a : A) → UU j
  frB a = isFibrant.fibrant-match (Q a)

  iso-1 : (Σᵉ A B) ≅ Σᵉ (C fr) (λ x → C (frB (g x)))
  iso-1 = Σᵉ-iso-cong' {i} {j} P
                            (exo-tr (λ u → ((a : A) → _≅_ {j} {j} (B a) (C (frB (u a)))))
                                    (exo-inv (funextᵉ gf))
                                    (λ a → (isFibrant.fibrant-witness (Q a))) )

  iso-2 : Σᵉ (C fr) (λ x → C (frB (g x))) ≅ C (Σ fr (λ x → frB (g (c x))))
  iso-2 = exo-Σᵉ-equiv
  
------------------------------------------------------------------------------------------------------------------------
--Fibrancy is preserved under ×ᵉ
isFibrant-× : {i j : Level}{A : UUᵉ i}{B : UUᵉ j}
              → isFibrant {i} A → isFibrant {j} B
              → isFibrant {i ⊔ j} (A ×ᵉ B)
isFibrant-× {i} {j} {A = A} {B = B} (isfibrant RA wA) (isfibrant RB wB)
  = isfibrant (RA × RB) (fA×B ,ᵉ gA×B ,ᵉ gfA×B ,ᵉ fgA×B)
  where
  fA : A → C RA
  fA = pr1ᵉ wA

  gA : C RA → A
  gA = pr1ᵉ (pr2ᵉ wA)

  gfA : (a : A) → (gA (fA a)) =ᵉ a
  gfA = (pr1ᵉ (pr2ᵉ (pr2ᵉ wA)))

  fgA : (x : RA) → (fA (gA (c x))) =ᵉ c x
  fgA x = (pr2ᵉ (pr2ᵉ (pr2ᵉ wA))) (c x)

  fB : B → C RB
  fB = pr1ᵉ wB

  gB : C RB → B
  gB = pr1ᵉ (pr2ᵉ wB)

  gfB : (a : B) → (gB (fB a)) =ᵉ a
  gfB = (pr1ᵉ (pr2ᵉ (pr2ᵉ wB)))

  fgB : (x : RB) → (fB (gB (c x))) =ᵉ (c x)
  fgB x = (pr2ᵉ (pr2ᵉ (pr2ᵉ wB))) (c x)

  fA×B : A ×ᵉ B → C (RA × RB)
  fA×B (a ,ᵉ b) = c (ic (fA a) , ic (fB b))

  gA×B : C (RA × RB) → A ×ᵉ B
  gA×B (c (x , y)) = gA (c x) ,ᵉ gB (c y)

  gfA×B : (w : _) → gA×B (fA×B w) =ᵉ w
  gfA×B (a ,ᵉ b) = pair-=ᵉ _ _ (gfA a ,ᵉ gfB b)

  fgA×B : (w : _) → fA×B (gA×B w) =ᵉ w
  fgA×B (c (x , y)) = pair-=ᵉ' _ _ (fgA x ,ᵉ fgB y)
