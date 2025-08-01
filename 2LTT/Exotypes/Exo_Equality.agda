{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT.Exotypes.Exo_Equality where


open import 2LTT.Primitive


infix 4 _=ᵉ_ 
--Except for HoTT style, we have a strict equality. It's kind a judgmental equality. We call it exo-equality.
--Notation:
-- a =ᵉ b means a b are terms of exo-types and they are exo-equal

--exo(strict)equality for exotypes
data _=ᵉ_ {i : Level}{A : UUᵉ i} (x : A) : A → UUᵉ i where
  reflᵉ : x =ᵉ x


--Uniqueness of Identity Proof for =ᵉ
UIPᵉ : {i : Level} {A : UUᵉ i} {x y : A} (p q : x =ᵉ y) → p =ᵉ q
UIPᵉ reflᵉ reflᵉ = reflᵉ


--Basic Properties of =ᵉ
exo-inv  : {i : Level} {A : UUᵉ i}{x y : A} → x =ᵉ y → y =ᵉ x
exo-inv reflᵉ =  reflᵉ

exo-concat : {i : Level} {A : UUᵉ i}{x y z : A} → x =ᵉ y → y =ᵉ z → x =ᵉ z
exo-concat reflᵉ  reflᵉ = reflᵉ

exo-left-inv : {i : Level} {A : UUᵉ i} {x y : A} → (p : x =ᵉ y) → exo-concat (exo-inv p) p =ᵉ reflᵉ
exo-left-inv reflᵉ = reflᵉ

exo-right-inv : {i : Level} {A : UUᵉ i} {x y : A} → (p : x =ᵉ y) → exo-concat p (exo-inv p) =ᵉ reflᵉ
exo-right-inv reflᵉ = reflᵉ

exo-left-unit : {i : Level} {A : UUᵉ i} {x y : A} → (p : x =ᵉ y) → exo-concat reflᵉ p =ᵉ p
exo-left-unit reflᵉ = reflᵉ

exo-right-unit : {i : Level} {A : UUᵉ i} {x y : A} → (p : x =ᵉ y) → exo-concat p reflᵉ =ᵉ p
exo-right-unit reflᵉ = reflᵉ

exo-tr : {i j : Level} {A : UUᵉ i} (P : A → UUᵉ j) {x y : A} → x =ᵉ y → P x → P y
exo-tr P  reflᵉ p = p

exo-tr-elim : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {x y : A} {p : x =ᵉ y}{z z' : P x}
                 → (z =ᵉ z') → exo-tr P p z =ᵉ exo-tr P p z'
exo-tr-elim reflᵉ = reflᵉ

exo-tr-left-law : {i j : Level} {A : UUᵉ i} (P : A → UUᵉ j) {x y : A} (p : x =ᵉ y) {z : P y}
                   → exo-tr P (exo-concat (exo-inv p) p) z =ᵉ z
exo-tr-left-law P reflᵉ = reflᵉ

exo-tr-right-law : {i j : Level} {A : UUᵉ i} (P : A → UUᵉ j) {x y : A}(p : x =ᵉ y) {z : P x}
                   → exo-tr P (exo-concat p (exo-inv p)) z =ᵉ z
exo-tr-right-law P reflᵉ = reflᵉ 

exo-tr-concat : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {x y z : A}
                  (e₁ : x =ᵉ y) (e₂ : y =ᵉ z) {p : P x}
                → exo-tr P e₂ (exo-tr P e₁ p) =ᵉ exo-tr P (exo-concat e₁ e₂) p
exo-tr-concat reflᵉ reflᵉ = reflᵉ
{-# INLINE exo-tr-concat #-}


exo-tr-pi : {i j k : Level}{A : UUᵉ i}{a a' : A}(e : a =ᵉ a')
                {B : UUᵉ j} (C : A → B → UUᵉ k) {f : (y : B) → C a y} {y : B}
                 → exo-tr (λ x → (y : B) → C x y) e f y =ᵉ exo-tr (λ x → C x y) e (f y)
exo-tr-pi reflᵉ C = reflᵉ

exo-ap : {i j : Level}{A : UUᵉ i} {B : UUᵉ j} → (f : A → B) {x₁ x₂ : A} → x₁ =ᵉ x₂ → f x₁ =ᵉ f x₂
exo-ap f  reflᵉ = reflᵉ

exo-ap2 : {i j : Level}{A : UUᵉ i} {B : A → UUᵉ j} {C : UUᵉ j} (f : (x : A) → B x → C)
      → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
      → (p : x₁ =ᵉ x₂) (q : exo-tr B p y₁ =ᵉ y₂)
      → f x₁ y₁ =ᵉ f x₂ y₂
exo-ap2 f reflᵉ reflᵉ =  reflᵉ


exo-apd : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} (f : (a : A) → P a) {x y : A} (p : x =ᵉ y)
            → exo-tr P p (f x) =ᵉ f y
exo-apd f reflᵉ = reflᵉ

exo-tr-ap : {i j : Level} {A B : UUᵉ i} {f : A → B} {P : B → UUᵉ j} {x₁ x₂ : A} (e : x₁ =ᵉ x₂) {p : P (f x₁)}
               → exo-tr (λ x → P (f x)) e p =ᵉ exo-tr P (exo-ap f e) p
exo-tr-ap reflᵉ =  reflᵉ

exo-ap-tr : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {x y : A} {e₁ e₂ : x =ᵉ y} {p : P x}
               → e₁ =ᵉ e₂ → exo-tr P e₁ p =ᵉ exo-tr P e₂ p
exo-ap-tr reflᵉ = reflᵉ

exo-ap-transport : {i j : Level} {A : UUᵉ i} {P Q : A → UUᵉ j} {x y : A} (p : x =ᵉ y) (f : (x : A) → P x → Q x) (z : P x)
                → f y (exo-tr P p z) =ᵉ exo-tr Q p (f x z)
exo-ap-transport reflᵉ f z = reflᵉ

exo-tr-fam-ap : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {x y : A} {p : x =ᵉ y} {f g : P x → P x}{z : P x}
                 → (f =ᵉ g) → exo-tr P p (f z) =ᵉ exo-tr P p (g z)
exo-tr-fam-ap reflᵉ = reflᵉ
