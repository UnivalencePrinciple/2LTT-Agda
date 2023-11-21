{-# OPTIONS --without-K --exact-split  --two-level #-}

module 2LTT_C.Cofibration.Properties where


open import 2LTT_C.Cofibration.isCofibrant public

----Cofibrancy preserved under exo-isomorphisms.
isCofibrant-iso : {i k : Level}{A B : UUᵉ i}
              → A ≅ B → isCofibrant {i} A k
              → isCofibrant {i} B k
isCofibrant-iso {i} {k} {A} {B} (f ,ᵉ g ,ᵉ gf ,ᵉ fg) P Y
  = iscofibrant-at
       (isfibrant frA
                  (F' ,ᵉ G' ,ᵉ GF' ,ᵉ FG'))
       λ K → ctrA (λ a → K (f a))
  where
  frA : UU (i ⊔ k)
  frA = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a))))

  ctrA :  ((a : A) → is-contr (Y (f a))) → (Fib-is-contr {i ⊔ k} (Πᵉ A (λ a → C (Y (f a))))
                                                                   {isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))})
  ctrA = isCofibrant-at.contr-preserve-witness (P (λ a → Y (f a)))

  F : (Πᵉ A (λ a → C (Y (f a)))) → C frA
  F = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))

  G : C frA → (Πᵉ A (λ a → C (Y (f a))))
  G = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a))))))

  GF : (T : (Πᵉ A (λ a → C (Y (f a))))) → G (F (T)) =ᵉ T
  GF = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))))

  FG : (T : C frA) → F (G (T)) =ᵉ T
  FG = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P (λ a → Y (f a)))))))

  F' : Πᵉ B (λ b → C (Y b)) → C frA
  F' T = F (λ a → T (f a))

  G' : C frA → Πᵉ B (λ b → C (Y b))
  G' T = λ x → exo-tr (λ b → C (Y b)) (fg x) (G T (g x))

  GF' : (T : Πᵉ B (λ b → C (Y b))) → G' (F' (T)) =ᵉ T
  GF' T = funextᵉ (λ b →  exo-concat (exo-tr-elim {i} {k} {p = (fg b)}
                                        (happlyᵉ (GF (λ a → T (f a))) (g b)))
                                        (exo-apd {i} {k} T (fg b)))

  FG' : (T : C frA) → F' (G' T) =ᵉ T
  FG' T = exo-concat (exo-ap {i ⊔ k} {i ⊔ k} {_} {_} F {λ a →  exo-tr {i} {k} (λ b → C (Y b)) (fg (f a)) (G T (g (f a)))}
                              (funextᵉ {i} {k} (λ a → exo-concat
                                                        (exo-ap-tr (UIPᵉ (fg (f a)) (exo-ap {i} {i} f (gf a))))
                                                        ((exo-concat (exo-inv (exo-tr-ap (gf a)))
                                                                      (exo-apd {i} {k} (G T) (gf a)))))))
                      (FG T)

----------------------------------------------------------------------------------------------------------------
