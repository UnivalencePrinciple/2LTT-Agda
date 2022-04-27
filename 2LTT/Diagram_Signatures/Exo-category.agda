{-# OPTIONS --without-K --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.Exo-category where

open import 2LTT.Primitive public
open import 2LTT.Exotypes.Exo_Equality public
open import 2LTT.Exotypes.Sigma public
open import 2LTT.Exotypes.Functions public 

--NOTE!! I learned the following usage of modules from Egbert's library https://unimath.github.io/agda-unimath/

module _
  {i j : Level} {A : UUᵉ i} (hom : A → A → UUᵉ j)
  where
  
  assoc-comp : UUᵉ (i ⊔ j)
  assoc-comp = Σᵉ {i ⊔ j} {i ⊔ j} ({a b c : A} → hom b c → hom a b → hom a c)
                  (λ μ → {a b c d : A} (h : hom c d) (g : hom b c) (f : hom a b)
                          → _=ᵉ_ {j} (μ h (μ g f)) (μ (μ h g) f))

  unital-comp : assoc-comp → UUᵉ (i ⊔ j)
  unital-comp μ = Σᵉ {i ⊔ j} {i ⊔ j} ((a : A) → (hom a a))
                     (λ e → ({a b : A} (f : hom a b) →  _=ᵉ_ {j} (pr1ᵉ μ (e b) f) f) ×ᵉ
                              ({a b : A} (f : hom a b) →  _=ᵉ_ {j} (pr1ᵉ μ f (e a)) f))
                              
--Definition of an exo-category
Exo-cat : (i j : Level) → UUᵉ (lsuc i ⊔ lsuc j)
Exo-cat i j = Σᵉ {lsuc i} {lsuc i ⊔ lsuc j} (UUᵉ i)
                (λ A → Σᵉ {i ⊔ lsuc j} {i ⊔ j} (A → A → UUᵉ j)
                        (λ hom → Σᵉ {i ⊔ j} {i ⊔ j} (assoc-comp {i} {j} hom) (unital-comp hom)))


Objᵉ  : {i j : Level} (C : Exo-cat i j) → UUᵉ i
Objᵉ C = pr1ᵉ C
  
_[_,_] : {i j : Level} (C : Exo-cat i j) (a b : Objᵉ C) → UUᵉ j
C [ a , b ] = pr1ᵉ (pr2ᵉ C) a b

comp-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b c : Objᵉ C} (g : C [ b , c ]) (f : C [ a , b ]) → C [ a , c ]
comp-Exo-cat C = pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ C)))

infixl 15 comp-Exo-cat
syntax comp-Exo-cat C g f = g ○⟨ C ⟩ f

assoc-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b c d : Objᵉ C} (h : C [ c , d ]) (g : C [ b , c ]) (f : C [ a , b ])
                     → h ○⟨ C ⟩ (g ○⟨ C ⟩ f) =ᵉ (h ○⟨ C ⟩ g) ○⟨ C ⟩ f
assoc-rule-Exo-cat C h g f = pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ C))) h g f

Id-Exo-cat : {i j : Level} (C : Exo-cat i j) (a : Objᵉ C) → C [ a , a ]
Id-Exo-cat C = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ C)))

left-unit-comp-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b : Objᵉ C} (f : C [ a , b ])
                            → (Id-Exo-cat C b) ○⟨ C ⟩ f =ᵉ f
left-unit-comp-rule-Exo-cat C = pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ C))))

right-unit-comp-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b : Objᵉ C} (f : C [ a , b ])
                            → f ○⟨ C ⟩ (Id-Exo-cat C a) =ᵉ f
right-unit-comp-rule-Exo-cat C = pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ C))))

--Any exo-universe gives rise to an exo-category
ExoUniv-is-Exo-cat : (i : Level) → Exo-cat (lsuc i) i
pr1ᵉ (ExoUniv-is-Exo-cat i) = UUᵉ i
pr1ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i)) = λ A B → (A → B)
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i)))) g f = g ∘ᵉ f
pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i)))) h g f = reflᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i)))) a = idᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i))))) f = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ExoUniv-is-Exo-cat i))))) f = reflᵉ

--Definition of Opposite Categories
_ᵒᵖ : {i j : Level} → (Exo-cat i j) → (Exo-cat i j)
pr1ᵉ (C ᵒᵖ) = Objᵉ C
pr1ᵉ (pr2ᵉ (C ᵒᵖ)) a b = C [ b , a ]
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (C ᵒᵖ)))) g f = f ○⟨ C ⟩ g
pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ (C ᵒᵖ)))) h g f = exo-inv (assoc-rule-Exo-cat C f g h)
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (C ᵒᵖ)))) a = Id-Exo-cat C a
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (C ᵒᵖ))))) = right-unit-comp-rule-Exo-cat C
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (C ᵒᵖ))))) = left-unit-comp-rule-Exo-cat C

