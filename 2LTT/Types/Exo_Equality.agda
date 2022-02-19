{-# OPTIONS --without-K --two-level  #-}

module 2LTT.Types.Exo_Equality where


open import 2LTT.Primitive
open import 2LTT.Exotypes.Exo_Equality


infix 4 _=ₛ_ 
--Notation:
-- a =ₛ b means a b are terms of types and they are exo-equal
--NOTE THAT in order to prevent any possible confusion,
--we take the constructor of x =ₛᵉ x as reflₛᵉ while the constructor of x =ₛ x as reflₛ .

--exo(strict)equality for types
data _=ₛ_ {i : Level}{A : UU i} (x : A) : A → UUᵉ i where
  reflₛ : x =ₛ x

--Uniqueness of Identity Proof for =ₛ
UIP : {i : Level} {A : UU i} {x y : A} {p q : x =ₛ y} → p =ₛᵉ q
UIP {p = reflₛ} {q = reflₛ} = reflₛᵉ

exo-inv : {i : Level} {A : UU i}{x y : A} → x =ₛ y → y =ₛ x
exo-inv  reflₛ =  reflₛ

exo-concat : {i : Level} {A : UU i}{x y z : A} → x =ₛ y → y =ₛ z → x =ₛ z
exo-concat  reflₛ  reflₛ = reflₛ

exo-left-inv : {i : Level} {A : UU i} {x y : A} → (p : x =ₛ y) → exo-concat (exo-inv p) p =ₛᵉ reflₛ
exo-left-inv reflₛ = reflₛᵉ

exo-right-inv : {i : Level} {A : UU i} {x y : A} → (p : x =ₛ y) → exo-concat p (exo-inv p) =ₛᵉ reflₛ
exo-right-inv reflₛ = reflₛᵉ

exo-left-unit : {i : Level} {A : UU i} {x y : A} → (p : x =ₛ y) → exo-concat reflₛ p =ₛᵉ p
exo-left-unit reflₛ = reflₛᵉ

exo-right-unit : {i : Level} {A : UU i} {x y : A} → (p : x =ₛ y) → exo-concat p reflₛ =ₛᵉ p
exo-right-unit reflₛ = reflₛᵉ

exo-tr : {i j : Level} {A : UU i} (P : A → UU j) {x y : A} → x =ₛ y → P x → P y
exo-tr P  reflₛ p = p

exo-tr-left-law : {i j : Level} {A : UU i} {P : A → UU j} {x : A}{p : x =ₛ x}{z : P x}
                   → exo-tr P (exo-concat (exo-inv p) p) z =ₛ z
exo-tr-left-law {p = reflₛ} = reflₛ

exo-tr-right-law : {i j : Level} {A : UU i} {P : A → UU j} {x : A}{p : x =ₛ x}{z : P x}
                   → exo-tr P (exo-concat p (exo-inv p)) z =ₛ z
exo-tr-right-law {p = reflₛ} = reflₛ 

exo-tr-concat : {i j : Level} {A : UU i} {P : A → UU j} {x y z : A}
                  {e₁ : x =ₛ y} {e₂ : y =ₛ z} {p : P x}
                → exo-tr P e₂ (exo-tr P e₁ p) =ₛ exo-tr P (exo-concat e₁ e₂) p
exo-tr-concat {e₁ = reflₛ} {e₂ =  reflₛ } = reflₛ

exo-tr-pi : {i j k : Level}{A : UU i}{a a' : A}{e : a =ₛ a'}
                {B : UU j} {C : A → B → UU k}{f : (y : B) → C a y} {y : B}
                 → exo-tr (λ x → (y : B) → C x y) e f y =ₛ exo-tr (λ x → C x y) e (f y)
exo-tr-pi {e =  reflₛ} = reflₛ

exo-ap : {i j : Level}{A : UU i} {B : UU j} → (f : A → B) {x₁ x₂ : A} → x₁ =ₛ x₂ → f x₁ =ₛ f x₂
exo-ap f  reflₛ = reflₛ

exo-ap2 : {i j : Level}{A : UU i} {B : A → UU j} {C : UU j} (f : (x : A) → B x → C)
      → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
      → (p : x₁ =ₛ x₂) (q : exo-tr B p y₁ =ₛ y₂)
      → f x₁ y₁ =ₛ f x₂ y₂
exo-ap2 f  reflₛ reflₛ =  reflₛ


exo-apd : {i j : Level} {A : UU i} {P : A → UU j} (f : (a : A) → P a) {x y : A} (p : x =ₛ y)
            → exo-tr P p (f x) =ₛ f y
exo-apd f reflₛ = reflₛ

exo-tr-ap : {i j : Level} {A B : UU i}{f : A → B} {P : B → UU j} {x₁ x₂ : A} (e : x₁ =ₛ x₂) {p : P (f x₁)}
               → exo-tr (λ x → P (f x)) e p =ₛ exo-tr P (exo-ap f e) p
exo-tr-ap reflₛ =  reflₛ

exo-ap-tr : {i j : Level} {A : UU i} {P : A → UU j} {x y : A} {e₁ e₂ : x =ₛ y} {p : P x}
               → e₁ =ₛᵉ e₂ → exo-tr P e₁ p =ₛ exo-tr P e₂ p
exo-ap-tr  reflₛᵉ = reflₛ

ap-transport : {i j : Level} {A : UU i} {P Q : A → UU j} {x y : A} (p : x =ₛ y) (f : (x : A) → P x → Q x) (z : P x)
                → f y (exo-tr P p z) =ₛ exo-tr Q p (f x z)
ap-transport reflₛ f z = reflₛ

