{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Coercion.Fibrant_Type_Hierarchy where


open import 2LTT_C.Coercion.Fibrant_Pi public
open import 2LTT_C.Coercion.Fibrant_Sigma public

--is-contr for Fibrant Types
Fib-is-contr : {i : Level} (A : UUᵉ i) {W : isFibrant A} → UU i
Fib-is-contr {i} A {W} = is-contr FA
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

--is-prop for Fibrant Types
Fib-is-prop : {i : Level} (A : UUᵉ i) {W : isFibrant A} → UU i
Fib-is-prop {i} A {W} = is-prop FA
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

--is-set for Fibrant Types
Fib-is-set : {i : Level} (A : UUᵉ i) {W : isFibrant A} → UU i
Fib-is-set {i} A {W} = is-set FA
  where
  FA : UU i
  FA = isFibrant.fibrant-match W


--PROPERTIES OF FIB-IS-CONTR
--If B is a family of contractible fibrant exo-types over a fibrant exo-type A, then Πᵉ A B is contractible.
Fib-Π-type-contr : {i j : Level} {A : UUᵉ i} {W : isFibrant {i} A} {B : A → UUᵉ j} {V : (a : A) → isFibrant {j} (B a)}
                   → ((a : A) → Fib-is-contr {j} (B a) {V a}) → Fib-is-contr {i ⊔ j} (Πᵉ A B) {isFibrant-Π W V}
Fib-Π-type-contr {i} {j} {A} {W} {B} {V} F = Π-type-contr Pointwise-cont
 where
 Type : UU (i ⊔ j)
 Type = isFibrant.fibrant-match (isFibrant-Π W V)

 FA : UU i
 FA = isFibrant.fibrant-match W

 g : C FA → A
 g = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))

 FB : (a : A) → UU j
 FB a = isFibrant.fibrant-match (V a)

 Pointwise-cont : (x : FA) → is-contr (FB (g (c x)))
 Pointwise-cont x = F (g (c x))
------------------------------------------------------------------------------------------------------------------------

--Contractibility is preserved under exo-isomorphism.    
is-contr-iso : {i : Level} {A B : UU i}
               → C A ≅ C B
               → is-contr A
               → is-contr B
is-contr-iso {i} {A} {B} (f ,ᵉ g ,ᵉ lh ,ᵉ rh) (a , P) =
  ic (f (c a)) , λ x → (=ᵉ-to-Id (rh (c x))) ⁻¹ · ap (λ u → ic (f (c u))) (P (ic (g (c x))))

-------------------------------------------------------------------------------------------------------

--If two fibrant exo-type are exo-isomorphic, then one is contractible iff the other is.
Fib-iso-contr : {i : Level} {A B : UUᵉ i} {W : isFibrant {i} A} {V : isFibrant {i} B}
                → A ≅ B → Fib-is-contr {i} A {W} → Fib-is-contr {i} B {V}
Fib-iso-contr {i} {A} {B} {W} {V} (F ,ᵉ G ,ᵉ GF ,ᵉ FG) P = is-contr-iso (F' ,ᵉ G' ,ᵉ GF' ,ᵉ FG') P
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

  fA : A → C FA
  fA = pr1ᵉ (isFibrant.fibrant-witness W)

  gA : C FA → A
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))

  gfA : (a : A) → gA (fA a) =ᵉ a
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness W)))

  fgA : (x : FA) → fA (gA (c x)) =ᵉ c x
  fgA x = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))) (c x)

  FB : UU i
  FB = isFibrant.fibrant-match V

  fB : B → C FB
  fB = pr1ᵉ (isFibrant.fibrant-witness V)

  gB : C FB → B
  gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness V))

  gfB : (b : B) → gB (fB b) =ᵉ b
  gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness V)))

  fgB : (x : FB) → fB (gB (c x)) =ᵉ c x
  fgB x = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness V))) (c x)

  F' : C FA → C FB
  F' a = fB (F (gA a))

  G' : C FB → C FA
  G' b = fA (G (gB b))

  GF' : (x : C FA) → (G' (F' x)) =ᵉ x
  GF' x = exo-concat (exo-ap (fA ∘ᵉ G) (gfB (F (gA x))))
                (exo-concat (exo-ap fA (GF (gA x))) (fgA (ic x)))

  FG' : (y : C FB) → (F' (G' y)) =ᵉ y
  FG' y = exo-concat (exo-ap (fB ∘ᵉ F) (gfA (G (gB y))))
                 (exo-concat (exo-ap fB (FG (gB y))) (fgB (ic y)))
-------------------------------------------------------------------------------------------------------------

--If two fibrant exo-types A and B are contractible, so is A × B.
Fib-×ᵉ-contr : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} {W : isFibrant {i} A} {V : isFibrant {j} B}
              → Fib-is-contr {i} A {W} → Fib-is-contr {j} B {V}
              → Fib-is-contr {i ⊔ j} (A ×ᵉ B) {isFibrant-× W V}
Fib-×ᵉ-contr {i} {j} {A} {B} {W} {V} P Q = ×-contr-is-contr P Q
-------------------------------------------------------------------------------------------------------------

