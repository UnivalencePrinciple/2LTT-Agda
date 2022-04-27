{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Types.Pi where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Types.Functions
open import 2LTT.Exotypes.Functions
open import 2LTT.Types.Sigma


--------------------------------------------------------
--Type formers of dependent functions for types

Π : {i j : Level} (A : UU i) (P : A → UU j) → UU (i ⊔ j)
Π A P = (x : A) → P x

Π-intro : {i j : Level} (A : UU i) (P : A → UU j) (e : (a : A) → P a) → Π A P
Π-intro A P e = λ x → e x

Π-elim : {i j : Level} {A : UU i} {P : A → UU j} {a : A} → Π A P → P a
Π-elim {a = a} f = f a

Π-β-rule : {i j : Level} {A : UU i} {P : A → UU j} → (f : Π A P)
            → (a : A) → (λ x → f x) a =ᵉ f a
Π-β-rule f a = reflᵉ

Π-η-rule : {i j : Level} {A : UU i} {P : A → UU j} → (f : Π A P) → f =ᵉ (λ x → f x)
Π-η-rule f = reflᵉ

Π-form-cong1 : {i j : Level}{A : UU i}{P Q : A → UU j}
             → (P =ᵉ Q)
             → Π A P =ᵉ Π A Q
Π-form-cong1 reflᵉ = reflᵉ

Π-form-cong2 : {i j : Level}{A B : UU i}{P : A → UU j}{Q : B → UU j}
             → (w : _=ᵉ_ {lsuc i} A B) → (p : (a : A) → P a =ᵉ Q (embed w a))
             → Π A P =ᵉ Π B Q
Π-form-cong2 {i} {j} reflᵉ p = Π-form-cong1 {i} {j} (funextᵉ p)

Π-intro-cong : {i j : Level}{A : UU i}{P : A → UU j}
                → (e f : (a : A) → P a) → e =ᵉ f
                → (λ a → e a) =ᵉ (λ a → f a)
Π-intro-cong e .e reflᵉ = reflᵉ


Π-elim-cong : {i j : Level}{A : UU i}{P : A → UU j}{e e' : Π A P}{a a' : A}
                → (p : _=ᵉ_ {i} a a') → (q : e =ᵉ e')
                → exo-tr P (p) (e a) =ᵉ e' a'
Π-elim-cong reflᵉ reflᵉ = reflᵉ

