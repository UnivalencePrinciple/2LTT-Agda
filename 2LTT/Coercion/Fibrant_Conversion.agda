{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Conversion where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public

----------
--FIBRANT CONVERSION
record isFibrant {i : Level}(B : UUᵉ i) : UUᵉ (lsuc i) where
  constructor isfibrant
  field
    fibrant-match : UU i
    fibrant-witness : B ≅ fibrant-match

open isFibrant public
    
fibrant-conversion : {i : Level} → (B : UUᵉ i) → (isFibrant B) → UU i
fibrant-conversion B (isfibrant fibrant-match fibrant-witness) = fibrant-match

----------------------------------------
-----------POSTULATES about "coercion"

postulate
   T1-type : {i : Level} {A B : UU i} → C A =ᵉ C B → A =ᵉ B
   T2-⊤ : ⊤ᵉ =ᵉ C ⊤
   T2-Σ : {i j : Level}{A : UU i}{B : A → UU j} → C (Σ A B) =ᵉ Σᵉ (C A) (λ x → C (B x))
   T2-Π : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) =ᵉ Πᵉ (C A) (λ x → C (B x))
   T2-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} {x : C {i ⊔ j} (Π A B)} → map-Πᵉ x =ᵉ  exo-tr idᵉ (T2-Π {i} {j}) x
   T3 : {i : Level} {A : UUᵉ i} {B : UU i} → A ≅ C B → Σᵉ (UU i) (λ D → A =ᵉ C D)

exo-eq-fibrant-match : {i : Level} {B : UUᵉ i} → isFibrant {i} B →  Σᵉ (UU i) (λ D → B =ᵉ C D)
exo-eq-fibrant-match {i} {B} (isfibrant fm fw) = T3 {i} {B} {fm} (fw)

T1-term : {i : Level} {A : UU i} {a b : A} → c a =ᵉ c b → a =ᵉ b
T1-term reflᵉ = reflᵉ

T2-× :  {i j : Level}{A : UU i}{B : UU j} → C (A × B) =ᵉ (C A) ×ᵉ (C B)
T2-× {i} {j} {A} {B} = T2-Σ {i} {j} {A} {(λ _ → B)}




