{-# OPTIONS --without-K --exact-split --two-level  --type-in-type #-}


module 2LTT_C.Diagram_Signatures.Exo-functor where

open import 2LTT_C.Diagram_Signatures.Exo-category public
open import 2LTT_C.Exotypes.Pi public


module _
  {i j i' j' : Level}
  (C : Exo-cat i j)
  (D : Exo-cat i' j') where

--Definition of an exo-functor
  Exo-Functor : UUᵉ (i ⊔ j ⊔ i' ⊔ j')
  Exo-Functor = Σᵉ {i ⊔ i'} (Objᵉ C → Objᵉ D)
                (λ F0 → Σᵉ {i ⊔ j ⊔ j'} ({a b : Objᵉ C} → (C [ a , b ] → D [ (F0 a) , (F0 b) ]))
                (λ F1 → ({a : Objᵉ C} → _=ᵉ_ {j'} (F1 (Id-Exo-cat C a)) (Id-Exo-cat D (F0 a)))
                                  ×ᵉ
                ({a b c : Objᵉ C} {g : C [ b , c ]} {f : C [ a , b ]} →
                   _=ᵉ_ {j'} (F1 (g ○⟨ C ⟩ f)) ((F1 g) ○⟨ D ⟩ (F1 f)))))

  Obj-map : (Exo-Functor) → (Objᵉ C → Objᵉ D)
  Obj-map F = pr1ᵉ F


  Arrow-map : (F : Exo-Functor) → ({a b : Objᵉ C} → (C [ a , b ] → D [ (Obj-map F a) , (Obj-map F b) ]))
  Arrow-map F = pr1ᵉ (pr2ᵉ F)

  Functor-id-rule : (F : Exo-Functor) →
                    ({a : Objᵉ C} →
                    _=ᵉ_ {j'} ((Arrow-map F) (Id-Exo-cat C a)) (Id-Exo-cat D ((Obj-map F) a)))
  Functor-id-rule F = pr1ᵉ (pr2ᵉ (pr2ᵉ F))

  Functor-comp-rule :  (F : Exo-Functor) →
                       ({a b c : Objᵉ C} {g : C [ b , c ]} {f : C [ a , b ]} →
                       _=ᵉ_ {j'} (Arrow-map F (g ○⟨ C ⟩ f)) ((Arrow-map F g) ○⟨ D ⟩ (Arrow-map F f)))
  Functor-comp-rule F = pr2ᵉ (pr2ᵉ (pr2ᵉ F))

--Definition of an exo-natural transformation
  Exo-Nat-Trans : (F G : Exo-Functor) → UUᵉ (i ⊔ j ⊔ i' ⊔ j')
  Exo-Nat-Trans F G = Σᵉ (Πᵉ (Objᵉ C) (λ a → D [ Obj-map F a , Obj-map G a ]))
                         (λ α → {a b : Objᵉ C} {f : C [ a , b ]} →
                           _=ᵉ_ {j'} ((Arrow-map G f) ○⟨ D ⟩ (α a)) ((α b) ○⟨ D ⟩ (Arrow-map F f)))
   
