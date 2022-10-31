{-# OPTIONS --without-K --two-level #-}

module 2LTT.Exotypes.List where

open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Primitive

data Listᵉ {l1 : Level}(A : UUᵉ l1) : UUᵉ l1  where
  nilᵉ : Listᵉ A
  consᵉ : A → Listᵉ A → Listᵉ A

ind-Listᵉ : {l1 l2 : Level}(A : UUᵉ l1) (Y : Listᵉ {l1} A → UUᵉ l2) →
                           Y (nilᵉ) → ((a : A) (l : Listᵉ A) → Y (l) → Y (consᵉ a l)) → ((l : (Listᵉ A)) → Y l)
ind-Listᵉ A Y c f nilᵉ = c
ind-Listᵉ A Y c f (consᵉ a l) = f a l (ind-Listᵉ A Y c f l)

list-appendᵉ : {i : Level} {A : UUᵉ i} → Listᵉ A → Listᵉ A → Listᵉ A
list-appendᵉ nilᵉ l'  =  l'
list-appendᵉ (consᵉ a l) l' =  consᵉ a (list-appendᵉ l l')
{-# INLINE list-appendᵉ #-}

list-appendᵉ-right : {i : Level} {A : UUᵉ i} → (l : Listᵉ A) → list-appendᵉ l nilᵉ =ᵉ l
list-appendᵉ-right nilᵉ = reflᵉ
list-appendᵉ-right (consᵉ x l) = exo-ap (consᵉ x) (list-appendᵉ-right l)

list-deleteᵉ : {i : Level} {A : UUᵉ i} → Listᵉ A → Listᵉ A
list-deleteᵉ nilᵉ = nilᵉ
list-deleteᵉ (consᵉ x nilᵉ) = nilᵉ
list-deleteᵉ (consᵉ x (consᵉ x₁ l)) = consᵉ x (list-deleteᵉ (consᵉ x₁ l))

embed-to-Listᵉ : {i : Level} (A : UUᵉ i) → A → Listᵉ A
embed-to-Listᵉ A a = consᵉ a nilᵉ

