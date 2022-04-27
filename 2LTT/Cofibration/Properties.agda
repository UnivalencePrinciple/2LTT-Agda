{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Cofibration.Properties where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Cofibration.isCofibrant public

----Cofibrancy preserved under exo-isomorphisms.
isCofibrant-iso : {i k : Level}{A B : UUᵉ i}
              → A ≅ B → isCofibrant {i} A k
              → isCofibrant {i} B k
isCofibrant-iso {i} {k} {A} {B} (f , g , gf , fg) P Y
  = iscofibrant-at
       (isfibrant frA
                  (F' , G' , GF' , FG'))
       λ K → ctrA (λ a → K (f a))
  where
  frA : UU (i ⊔ k)
  frA = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a))))

  ctrA :  Πᵉ A (λ a → is-contr (Y (f a))) → (Fib-is-contr {i ⊔ k} (Πᵉ A (Y ∘ᵉ f))
                                                                   {isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))})
  ctrA = isCofibrant-at.contr-preserve-witness (P (λ a → Y (f a)))

  F : Πᵉ A (Y ∘ᵉ f) → frA
  F = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))

  G : frA → Πᵉ A (Y ∘ᵉ f)
  G = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a))))))

  GF : (T : Πᵉ A (Y ∘ᵉ f)) → G (F (T)) =ᵉ T
  GF = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))))

  FG : (T : frA) → F (G (T)) =ᵉ T
  FG = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))))

  F' : Πᵉ B Y → frA
  F' T = F (λ a → T (f a))

  G' : frA → Πᵉ B Y
  G' T = λ x → exo-tr Y (fg x) (G T (g x))

  GF' : (T : Πᵉ B Y) → G' (F' (T)) =ᵉ T
  GF' T = funextᵉ (λ b →  exo-concat (exo-tr-elim {i} {k} {p = (fg b)}
                                        (happlyᵉ (GF (λ a → T (f a))) (g b)))
                                        (exo-apd {i} {k} T (fg b)))

  FG' : (T : frA) → F' (G' T) =ᵉ T
  FG' T = exo-concat (exo-ap {i ⊔ k} {i ⊔ k} {_} {_} F {λ a →  exo-tr {i} {k} Y (fg (f a)) (G T (g (f a)))}
                              (funextᵉ {i} {k} (λ a → exo-concat
                                                        (exo-ap-tr (UIPᵉ (fg (f a)) (exo-ap {i} {i} f (gf a))))
                                                        ((exo-concat (exo-inv (exo-tr-ap (gf a)))
                                                                      (exo-apd {i} {k} (G T) (gf a)))))))
                      (FG T)

----------------------------------------------------------------------------------------------------------------
