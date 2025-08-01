{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Cofibration.isCofibrant where

open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Type_Hierarchy public
open import 2LTT.Coercion.Fibrant_Equivalences public


--For f : A → B , being fibration 
isFibration : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}(f : A → B) → UUᵉ (lsuc i ⊔ lsuc j)
isFibration {i} {j} {A} {B} f = (b : B) → isFibrant {i ⊔ j} (Σᵉ A (λ a → f a =ᵉ b))

--For exo-type B, being cofibrant at Y : B → UU j
record isCofibrant-at {i : Level} (B : UUᵉ i) (j : Level) (Y : B → UU j) : UUᵉ (lsuc (i ⊔ j)) where
    eta-equality
    constructor iscofibrant-at
    field 
      Π-fibrant-witness : isFibrant (Πᵉ B Y)
      contr-preserve-witness : Πᵉ B (λ b → is-contr (Y b)) → (Fib-is-contr {i ⊔ j} (Πᵉ B Y) {Π-fibrant-witness})

open isCofibrant-at public

isCofibrant : {i : Level}(B : UUᵉ i)(j : Level) → UUᵉ (lsuc (i ⊔ j))
isCofibrant {i} B j = (Y : B → UU j) → isCofibrant-at {i} B j Y
