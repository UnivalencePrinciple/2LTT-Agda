{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Pi where


open import 2LTT_C.Coercion.Fibrant_Conversion public


--Fibrancy is preserved under Πᵉ
isFibrant-Π : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Πᵉ A B)
isFibrant-Π {i} {j} {A = A} {B = B} (isfibrant fr P) Q =
  isfibrant (Π fr (λ x → (frB (g (c x))))) (≅-trans iso-1 iso-2)
  where
    g : C fr → A
    g = pr1ᵉ (pr2ᵉ P)

    frB : (a : A) → UU j
    frB a = isFibrant.fibrant-match (Q a)

    iso-1 : (Πᵉ A B) ≅ Πᵉ (C fr) (λ x → C (frB (g x)))
    iso-1 = Πᵉ-iso-cong' (≅-sym {i} P) (λ b → (isFibrant.fibrant-witness (Q (g b))))

    iso-2 : Πᵉ (C fr) (λ x → C (frB (g x))) ≅ C (Π fr (λ x → (frB (g (c x)))))
    iso-2 = exo-Πᵉ-equiv
