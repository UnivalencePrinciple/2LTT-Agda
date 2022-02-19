{-# OPTIONS --without-K --two-level #-}

module 2LTT.Types.Pi where

open import 2LTT.Primitive 
open import 2LTT.Types.Exo_Equality
open import 2LTT.Types.Functions
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
            → (a : A) → (λ x → f x) a =ₛ f a
Π-β-rule f a = reflₛ

Π-η-rule : {i j : Level} {A : UU i} {P : A → UU j} → (f : Π A P) → f =ₛ (λ x → f x)
Π-η-rule f = reflₛ

Π-form-cong1 : {i j : Level}{A : UU i}{P Q : A → UU j}
             → (P =ₛ Q)
             → Π A P =ₛ Π A Q
Π-form-cong1 reflₛ = reflₛ

Π-form-cong2 : {i j : Level}{A B : UU i}{P : A → UU j}{Q : B → UU j}
             → (w : A =ₛ B) → (p : (a : A) → P a =ₛ Q (exo-tr (λ x → x) w a))
             → Π A P =ₛ Π B Q
Π-form-cong2 reflₛ p = Π-form-cong1 (funextₛ p)

Π-intro-cong : {i j : Level}{A : UU i}{P : A → UU j}
                → (e f : (a : A) → P a) → e =ₛ f
                → (λ a → e a) =ₛ (λ a → f a)
Π-intro-cong e .e reflₛ = reflₛ

Π-elim-cong : {i j : Level}{A : UU i}{P : A → UU j}{e e' : Π A P}{a a' : A}
                → (p : a =ₛ a') → (q : e =ₛ e')
                → exo-tr P (p) (e a) =ₛ e' a'
Π-elim-cong reflₛ reflₛ = reflₛ


