{-# OPTIONS --without-K --exact-split  --two-level #-}

module 2LTT_C.Diagram_Signatures.Exo-category where

open import 2LTT_C.Primitive public
open import 2LTT_C.Exotypes.Exo_Equality public
open import 2LTT_C.Exotypes.Sigma public
open import 2LTT_C.Exotypes.Functions public


record Exo-cat (i j : Level) : UUᵉ (lsuc i ⊔ lsuc j) where
  constructor is-exo-cat
  field 
    Object : UUᵉ i
    Hom : (a b : Object) → UUᵉ j
    Comp : {a b c : Object} → Hom b c → Hom a b → Hom a c
    Assoc : {a b c d : Object} (h : Hom c d) (g : Hom b c) (f : Hom a b)
            → _=ᵉ_ {j} (Comp h (Comp g f)) (Comp (Comp h g) f)    
    Id-hom : (a : Object) → Hom a a
    Id-left-coh : {a b : Object} (f : Hom a b) → _=ᵉ_ {j} (Comp (Id-hom b) f) f
    Id-right-coh : {a b : Object} (f : Hom a b) → _=ᵉ_ {j} (Comp f (Id-hom a)) f
    

Objᵉ  : {i j : Level} (C : Exo-cat i j) → UUᵉ i
Objᵉ C = Exo-cat.Object C

_[_,_] : {i j : Level} (C : Exo-cat i j) (a b : Objᵉ C) → UUᵉ j
C [ a , b ] = Exo-cat.Hom C a b


comp-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b c : Objᵉ C} (g : C [ b , c ]) (f : C [ a , b ]) → C [ a , c ]
comp-Exo-cat C = Exo-cat.Comp C

{-# INLINE comp-Exo-cat #-}


infixl 15 comp-Exo-cat
syntax comp-Exo-cat C g f = g ○⟨ C ⟩ f

assoc-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b c d : Objᵉ C} (h : C [ c , d ]) (g : C [ b , c ]) (f : C [ a , b ])
                     → h ○⟨ C ⟩ (g ○⟨ C ⟩ f) =ᵉ (h ○⟨ C ⟩ g) ○⟨ C ⟩ f
assoc-rule-Exo-cat C h g f = Exo-cat.Assoc C h g f

Id-Exo-cat : {i j : Level} (C : Exo-cat i j) (a : Objᵉ C) → C [ a , a ]
Id-Exo-cat C = Exo-cat.Id-hom C

left-unit-comp-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b : Objᵉ C} (f : C [ a , b ])
                            → (Id-Exo-cat C b) ○⟨ C ⟩ f =ᵉ f
left-unit-comp-rule-Exo-cat C = Exo-cat.Id-left-coh C

right-unit-comp-rule-Exo-cat : {i j : Level} (C : Exo-cat i j) {a b : Objᵉ C} (f : C [ a , b ])
                            → f ○⟨ C ⟩ (Id-Exo-cat C a) =ᵉ f
right-unit-comp-rule-Exo-cat C = Exo-cat.Id-right-coh C


--Any exo-universe gives rise to an exo-category
ExoUniv-is-Exo-cat : (i : Level) → Exo-cat (lsuc i) i
Exo-cat.Object (ExoUniv-is-Exo-cat i) = UUᵉ i
Exo-cat.Hom (ExoUniv-is-Exo-cat i) = λ A B → (A → B)
Exo-cat.Comp (ExoUniv-is-Exo-cat i) = λ g f → g ∘ᵉ f
Exo-cat.Assoc (ExoUniv-is-Exo-cat i) = λ h g f → reflᵉ 
Exo-cat.Id-hom (ExoUniv-is-Exo-cat i) = λ a → idᵉ
Exo-cat.Id-left-coh (ExoUniv-is-Exo-cat i) = λ f → reflᵉ
Exo-cat.Id-right-coh (ExoUniv-is-Exo-cat i) = λ f → reflᵉ


--Definition of Opposite Categories
_ᵒᵖ : {i j : Level} → (Exo-cat i j) → (Exo-cat i j)
Exo-cat.Object (C ᵒᵖ) = Objᵉ C
Exo-cat.Hom (C ᵒᵖ) a b = C [ b , a ]
Exo-cat.Comp (C ᵒᵖ) g f = f ○⟨ C ⟩ g
Exo-cat.Assoc (C ᵒᵖ) h g f = exo-inv (assoc-rule-Exo-cat C f g h)
Exo-cat.Id-hom (C ᵒᵖ) a = Id-Exo-cat C a
Exo-cat.Id-left-coh (C ᵒᵖ) = right-unit-comp-rule-Exo-cat C
Exo-cat.Id-right-coh (C ᵒᵖ) = left-unit-comp-rule-Exo-cat C

