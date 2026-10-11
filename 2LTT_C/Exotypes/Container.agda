{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Exotypes.Container where

open import 2LTT_C.Primitive
open import 2LTT_C.Exotypes.Naturals
open import 2LTT_C.Exotypes.Finite
open import 2LTT_C.Exotypes.Sigma
open import 2LTT_C.Exotypes.Coproduct
open import 2LTT_C.Exotypes.Functions
open import 2LTT_C.Exotypes.Exo_Equality
open import 2LTT_C.Exotypes.Empty
open import 2LTT_C.Exotypes.Unit
open import 2LTT_C.Exotypes.List

--Containers, equivalently polynomial functors in one variable
record Containerᵉ (i j : Level) : UUᵉ (lsuc (i ⊔ j)) where
  constructor _◁_
  field
    Shape : UUᵉ i
    Pos   : Shape → UUᵉ j

open Containerᵉ public

infix 5 _◁_

--The extension of a container
⟦_⟧ᵉ : {i j k : Level} → Containerᵉ i j → UUᵉ k → UUᵉ (i ⊔ j ⊔ k)
⟦ S ◁ P ⟧ᵉ A = Σᵉ S (λ s → P s → A)

⟦_⟧ᵉ-map : {i j k l : Level} (F : Containerᵉ i j) {A : UUᵉ k} {B : UUᵉ l}
           → (A → B) → ⟦ F ⟧ᵉ A → ⟦ F ⟧ᵉ B
⟦ F ⟧ᵉ-map f (s ,ᵉ h) = s ,ᵉ (λ p → f (h p))

--A container is finitary if each position fiber is exo-finite.
isFinitary : {i j : Level} → Containerᵉ i j → UUᵉ (i ⊔ j)
isFinitary {i} {j} (S ◁ P) = (s : S) → Σᵉ {lzero} {j} ℕᵉ (λ n → _≅_ {lzero} {j} (ℕᵉ< n) (P s))

--An exo-type is countable if it is exo-finite or isomorphic to ℕᵉ.
isCountable : {i : Level} → UUᵉ i → UUᵉ i
isCountable S = (Σᵉ ℕᵉ (λ n → ℕᵉ< n ≅ S)) +ᵉ (ℕᵉ ≅ S)

------------------------------------------------------------------------------

--List container
List-Containerᵉ : Containerᵉ lzero lzero
List-Containerᵉ = ℕᵉ ◁ ℕᵉ<

List-Containerᵉ-isFinitary : isFinitary List-Containerᵉ
List-Containerᵉ-isFinitary n = n ,ᵉ ≅-refl

List-Containerᵉ-isCountable : isCountable (Shape List-Containerᵉ)
List-Containerᵉ-isCountable = inrᵉ ≅-refl

--maps
List-Containerᵉ-to-Listᵉ' : {i : Level} {A : UUᵉ i} (n : ℕᵉ) → (ℕᵉ< n → A) → Listᵉ A
List-Containerᵉ-to-Listᵉ' zeroᵉ h = []ᵉ
List-Containerᵉ-to-Listᵉ' (succᵉ n) h = h (inrᵉ starᵉ) ::ᵉ List-Containerᵉ-to-Listᵉ' n (λ x → h (inlᵉ x))

List-Containerᵉ-to-Listᵉ : {i : Level} {A : UUᵉ i} → ⟦ List-Containerᵉ ⟧ᵉ A → Listᵉ A
List-Containerᵉ-to-Listᵉ (n ,ᵉ h) = List-Containerᵉ-to-Listᵉ' n h

cons-List-Containerᵉ : {i : Level} {A : UUᵉ i} → A → ⟦ List-Containerᵉ ⟧ᵉ A → ⟦ List-Containerᵉ ⟧ᵉ A
cons-List-Containerᵉ a (n ,ᵉ h) = succᵉ n ,ᵉ (λ { (inlᵉ x) → h x ; (inrᵉ starᵉ) → a})

Listᵉ-to-List-Containerᵉ : {i : Level} {A : UUᵉ i} → Listᵉ A → ⟦ List-Containerᵉ ⟧ᵉ A
Listᵉ-to-List-Containerᵉ []ᵉ = zeroᵉ ,ᵉ ex-falsoᵉ
Listᵉ-to-List-Containerᵉ (a ::ᵉ l) = cons-List-Containerᵉ a (Listᵉ-to-List-Containerᵉ l)

--isomorphisms
List-Containerᵉ-to-Listᵉ-is-sec : {i : Level} {A : UUᵉ i} (l : Listᵉ A) →
                                 List-Containerᵉ-to-Listᵉ (Listᵉ-to-List-Containerᵉ l) =ᵉ l
List-Containerᵉ-to-Listᵉ-is-sec []ᵉ = reflᵉ
List-Containerᵉ-to-Listᵉ-is-sec (a ::ᵉ l) = exo-ap (a ::ᵉ_) (List-Containerᵉ-to-Listᵉ-is-sec l)

List-Containerᵉ-to-Listᵉ-is-retr' : {i : Level} {A : UUᵉ i} (n : ℕᵉ) (h : ℕᵉ< n → A) →
                                   Listᵉ-to-List-Containerᵉ (List-Containerᵉ-to-Listᵉ' n h) =ᵉ (n ,ᵉ h)
List-Containerᵉ-to-Listᵉ-is-retr' {i} zeroᵉ h = exo-ap {i} {i} (_,ᵉ_ {lzero} {i} zeroᵉ) (funextᵉ {lzero} {i} (λ ()))
List-Containerᵉ-to-Listᵉ-is-retr' {i} (succᵉ n) h =
  exo-concat {i} (exo-ap {i} {i} (cons-List-Containerᵉ {i} (h (inrᵉ starᵉ))) (List-Containerᵉ-to-Listᵉ-is-retr' {i} n (λ x → h (inlᵉ x))))
                  (exo-ap {i} {i} (_,ᵉ_ {lzero} {i} (succᵉ n)) (funextᵉ {lzero} {i} (λ { (inlᵉ x) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ})))

List-Containerᵉ-to-Listᵉ-is-retr : {i : Level} {A : UUᵉ i} (t : ⟦ List-Containerᵉ ⟧ᵉ A) →
                                  Listᵉ-to-List-Containerᵉ (List-Containerᵉ-to-Listᵉ t) =ᵉ t
List-Containerᵉ-to-Listᵉ-is-retr (n ,ᵉ h) = List-Containerᵉ-to-Listᵉ-is-retr' n h

List-Containerᵉ≅Listᵉ : {i : Level} {A : UUᵉ i} → ⟦ List-Containerᵉ ⟧ᵉ A ≅ Listᵉ A
List-Containerᵉ≅Listᵉ = List-Containerᵉ-to-Listᵉ ,ᵉ
                        (Listᵉ-to-List-Containerᵉ ,ᵉ
                         (List-Containerᵉ-to-Listᵉ-is-retr ,ᵉ List-Containerᵉ-to-Listᵉ-is-sec))
