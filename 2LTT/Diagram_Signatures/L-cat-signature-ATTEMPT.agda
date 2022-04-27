{-# OPTIONS --without-K --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.L-cat-signature where

open import 2LTT.Diagram_Signatures.Definition public

L-cat-Obj : UUᵉ lzero
L-cat-Obj = ℕᵉ< fourᵉ


L-cat-O : L-cat-Obj
L-cat-O = inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))

L-cat-A : L-cat-Obj
L-cat-A = inlᵉ (inlᵉ (inrᵉ starᵉ))

L-cat-I : L-cat-Obj
L-cat-I = inlᵉ (inrᵉ starᵉ)

L-cat-T : L-cat-Obj
L-cat-T = inrᵉ starᵉ

L-cat-Hom : L-cat-Obj → L-cat-Obj → UUᵉ lzero
L-cat-Hom (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) = ℕᵉ< oneᵉ
L-cat-Hom (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) y = ℕᵉ< zeroᵉ

L-cat-Hom (inlᵉ (inlᵉ (inrᵉ starᵉ))) (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) = ℕᵉ< twoᵉ
L-cat-Hom (inlᵉ (inlᵉ (inrᵉ starᵉ))) (inlᵉ (inlᵉ (inrᵉ starᵉ))) = ℕᵉ< oneᵉ
L-cat-Hom (inlᵉ (inlᵉ (inrᵉ starᵉ))) y = ℕᵉ< zeroᵉ

L-cat-Hom (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) = ℕᵉ< oneᵉ
L-cat-Hom (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inlᵉ (inrᵉ starᵉ))) = ℕᵉ< oneᵉ
L-cat-Hom (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) = ℕᵉ< oneᵉ
L-cat-Hom (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) = ℕᵉ< zeroᵉ

L-cat-Hom (inrᵉ starᵉ) (inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))) = ℕᵉ< threeᵉ
L-cat-Hom (inrᵉ starᵉ) (inlᵉ (inlᵉ (inrᵉ starᵉ))) = ℕᵉ< threeᵉ
L-cat-Hom (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) = ℕᵉ< zeroᵉ
L-cat-Hom (inrᵉ starᵉ) (inrᵉ starᵉ) = ℕᵉ< oneᵉ


L-cat-Comp : {a b c : L-cat-Obj} → L-cat-Hom b c → L-cat-Hom a b → L-cat-Hom a c
L-cat-Comp {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = g
L-cat-Comp {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = f
L-cat-Comp {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = g
L-cat-Comp {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inrᵉ starᵉ))} g f = g
L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = f

L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inlᵉ (inrᵉ starᵉ)) f = (inrᵉ starᵉ)
L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inrᵉ starᵉ) f = (inrᵉ starᵉ)

L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inrᵉ starᵉ))} g f = f
L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = g
L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inlᵉ (inrᵉ starᵉ))} g f = g
L-cat-Comp {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inrᵉ starᵉ)} g f = g
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = f

L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inlᵉ (inrᵉ starᵉ)))
                                                                                     = (inlᵉ (inlᵉ (inrᵉ starᵉ)))
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) = (inlᵉ (inrᵉ starᵉ))
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) = (inlᵉ (inrᵉ starᵉ))
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inrᵉ starᵉ) (inlᵉ (inlᵉ (inrᵉ starᵉ))) = (inrᵉ starᵉ)
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) = (inlᵉ (inlᵉ (inrᵉ starᵉ)))
L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} (inrᵉ starᵉ) (inrᵉ starᵉ) = (inrᵉ starᵉ)

L-cat-Comp {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} {inlᵉ (inlᵉ (inrᵉ starᵉ))} g f = f
L-cat-Comp {inrᵉ starᵉ} {inrᵉ starᵉ} {inlᵉ (inlᵉ (inlᵉ (inrᵉ starᵉ)))} g f = g
L-cat-Comp {inrᵉ starᵉ} {inrᵉ starᵉ} {inlᵉ (inlᵉ (inrᵉ starᵉ))} g f = g
L-cat-Comp {inrᵉ starᵉ} {inrᵉ starᵉ} {inrᵉ starᵉ} g f = g
