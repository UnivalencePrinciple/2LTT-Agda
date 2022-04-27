{-# OPTIONS --without-K --two-level  --cumulativity #-}


module 2LTT.Diagram_Signatures.Exo-functor where

open import 2LTT.Diagram_Signatures.Exo-category public
open import 2LTT.Exotypes.Pi public


--Definition of an exo-functor
Exo-Functor : {i j i' j' : Level} (C : Exo-cat i j) (D : Exo-cat i' j')  → UUᵉ (i ⊔ j ⊔ i' ⊔ j')
Exo-Functor {i} {j} {i'} {j'} C D = Σᵉ {i ⊔ i'} (Objᵉ C → Objᵉ D)
                                   (λ F0 → Σᵉ {i ⊔ j ⊔ j'} ({a b : Objᵉ C} → (C [ a , b ] → D [ (F0 a) , (F0 b) ]))
                                   (λ F1 → ({a : Objᵉ C} →  _=ᵉ_ {j'} (F1 (Id-Exo-cat C a)) (Id-Exo-cat D (F0 a)))
                                                     ×ᵉ
                                            ({a b c : Objᵉ C} {g : C [ b , c ]} {f : C [ a , b ]}
                                                        → _=ᵉ_ {j'} (F1 (g ○⟨ C ⟩ f)) ((F1 g) ○⟨ D ⟩ (F1 f)))))


--Definition of an exo-natural transformation
Exo-Nat-Trans : {i j i' j' : Level}(C : Exo-cat i j) (D : Exo-cat i' j') (F G : Exo-Functor C D) → UUᵉ (i ⊔ j ⊔ i' ⊔ j')
Exo-Nat-Trans {i} {j} {i'} {j'} C D F G = Σᵉ (Πᵉ (Objᵉ C) (λ a → D [ F0 a , G0 a ]))
                                         (λ α → {a b : Objᵉ C} {f : C [ a , b ]} → _=ᵉ_ {j'} ((G1 f) ○⟨ D ⟩ (α a)) ((α b) ○⟨ D ⟩ (F1 f)))
  where
  F0 = pr1ᵉ F
  G0 = pr1ᵉ G

  F1 = pr1ᵉ (pr2ᵉ F)
  G1 = pr1ᵉ (pr2ᵉ G)
