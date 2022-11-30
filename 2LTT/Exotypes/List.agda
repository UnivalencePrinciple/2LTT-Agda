{-# OPTIONS --without-K --two-level #-}

module 2LTT.Exotypes.List where

open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Primitive

data Listᵉ {l1 : Level}(A : UUᵉ l1) : UUᵉ l1  where
  []ᵉ : Listᵉ A
  _::ᵉ_ : A → Listᵉ A → Listᵉ A

infixr 5 _::ᵉ_

ind-Listᵉ : {l1 l2 : Level}(A : UUᵉ l1) (Y : Listᵉ {l1} A → UUᵉ l2) →
                           Y ([]ᵉ) → ((a : A) (l : Listᵉ A) → Y (l) → Y (a ::ᵉ l)) → ((l : (Listᵉ A)) → Y l)
ind-Listᵉ A Y c f []ᵉ = c
ind-Listᵉ A Y c f (a ::ᵉ l) = f a l (ind-Listᵉ A Y c f l)

list-appendᵉ : {i : Level} {A : UUᵉ i} → Listᵉ A → Listᵉ A → Listᵉ A
list-appendᵉ []ᵉ l'  =  l'
list-appendᵉ (a ::ᵉ l) l' = a ::ᵉ (list-appendᵉ l l')
{-# INLINE list-appendᵉ #-}

list-appendᵉ-right : {i : Level} {A : UUᵉ i} → (l : Listᵉ A) → list-appendᵉ l []ᵉ =ᵉ l
list-appendᵉ-right []ᵉ = reflᵉ
list-appendᵉ-right (x ::ᵉ l) = exo-ap (λ l → x ::ᵉ l) (list-appendᵉ-right l)

embed-to-Listᵉ : {i : Level} (A : UUᵉ i) → A → Listᵉ A
embed-to-Listᵉ A a = a ::ᵉ []ᵉ

