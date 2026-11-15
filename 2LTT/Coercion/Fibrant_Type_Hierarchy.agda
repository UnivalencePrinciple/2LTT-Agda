{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Type_Hierarchy where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Pi public
open import 2LTT.Coercion.Fibrant_Sigma public

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

 g : FA → A
 g = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))

 FB : (a : A) → UU j
 FB a = isFibrant.fibrant-match (V a)

 Pointwise-cont : (x : FA) → is-contr (FB (g x))
 Pointwise-cont x = F (g x)
------------------------------------------------------------------------------------------------------------------------

--Contractibility is preserved under exo-isomorphism.
is-contr-iso : {i : Level} {A B : UU i}
               → A ≅ B
               → is-contr A
               → is-contr B
is-contr-iso {i} (f ,ᵉ g ,ᵉ lh ,ᵉ rh) (a , P) = f a , λ b → (=ᵉ-to-Id (exo-inv (rh b)) · ap f (P (g b)))
-------------------------------------------------------------------------------------------------------

--If two fibrant exo-type are exo-isomorphic, then one is contractible iff the other is.
Fib-iso-contr : {i : Level} {A B : UUᵉ i} {W : isFibrant {i} A} {V : isFibrant {i} B}
                → A ≅ B → Fib-is-contr {i} A {W} → Fib-is-contr {i} B {V}
Fib-iso-contr {i} {A} {B} {W} {V} (F ,ᵉ G ,ᵉ GF ,ᵉ FG) P = is-contr-iso (F' ,ᵉ G' ,ᵉ GF' ,ᵉ FG') P
  where
  FA : UU i
  FA = isFibrant.fibrant-match W

  fA : A → FA
  fA = pr1ᵉ (isFibrant.fibrant-witness W)

  gA : FA → A
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))

  gfA : (a : A) → gA (fA a) =ᵉ a
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness W)))

  fgA : (x : FA) → fA (gA x) =ᵉ x
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness W)))

  FB : UU i
  FB = isFibrant.fibrant-match V

  fB : B → FB
  fB = pr1ᵉ (isFibrant.fibrant-witness V)

  gB : FB → B
  gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness V))

  gfB : (b : B) → gB (fB b) =ᵉ b
  gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness V)))

  fgB : (x : FB) → fB (gB x) =ᵉ x
  fgB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness V)))

  F' : FA → FB
  F' = fB ∘ᵉ (F ∘ᵉ gA)

  G' : FB → FA
  G' = fA ∘ᵉ (G ∘ᵉ gB)

  GF' : (a : FA) → G' (F' a) =ᵉ a
  GF' a = exo-concat (exo-ap (fA ∘ᵉ G) (gfB (F (gA a))))
                      (exo-concat (exo-ap fA (GF (gA a))) (fgA a))

  FG' : (b : FB) → F' (G' b) =ᵉ b
  FG' b = exo-concat (exo-ap (fB ∘ᵉ F) (gfA (G (gB b))))
                      (exo-concat (exo-ap fB (FG (gB b))) (fgB b))
-------------------------------------------------------------------------------------------------------------

--If two fibrant exo-types A and B are contractible, so is A × B.
Fib-×ᵉ-contr : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} {W : isFibrant {i} A} {V : isFibrant {j} B}
              → Fib-is-contr {i} A {W} → Fib-is-contr {j} B {V}
              → Fib-is-contr {i ⊔ j} (A ×ᵉ B) {isFibrant-× W V}
Fib-×ᵉ-contr {i} {j} {A} {B} {W} {V} P Q = ×-contr-is-contr P Q
-------------------------------------------------------------------------------------------------------------

module _ {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {Z : UU l3}
         (FA : isFibrant {l1} A) (FB : (a : A) → isFibrant {l2} (B a))
         (cA : is-contr {l1} (fibrant-match FA)) (cB : (a : A) → is-contr {l2} (fibrant-match (FB a)))
         (F : Σᵉ {l1} {l2} A B → Z) where
  private
    MA : UU l1
    MA = fibrant-match FA

    MB : A → UU l2
    MB a = fibrant-match (FB a)

    fa : A → MA
    fa = pr1ᵉ (fibrant-witness FA)

    ga : MA → A
    ga = pr1ᵉ (pr2ᵉ (fibrant-witness FA))

    lha : (a : A) → _=ᵉ_ {l1} {A} (ga (fa a)) a
    lha = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness FA)))

    fb : (a : A) → B a → MB a
    fb a = pr1ᵉ (fibrant-witness (FB a))

    gb : (a : A) → MB a → B a
    gb a = pr1ᵉ (pr2ᵉ (fibrant-witness (FB a)))

    lhb : (a : A) (b : B a) → _=ᵉ_ {l2} {B a} (gb a (fb a b)) b
    lhb a = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (FB a))))

    T : UU (l1 ⊔ l2)
    T = Σ {l1} {l2} MA (λ x → MB (ga x))

    cT : is-contr {l1 ⊔ l2} T
    cT = Σ-is-contr {l1} {l2} {MA} {λ x → MB (ga x)} cA (λ x → cB (ga x))

    G : T → Z
    G (x , y) = F (ga x ,ᵉ gb (ga x) y)

    pt : Σᵉ {l1} {l2} A B → T
    pt (a ,ᵉ b) = fa a , fb (ga (fa a)) (exo-tr {l1} {l2} {A} B (exo-inv {l1} {A} (lha a)) b)

    tr-F : {a' a : A} (p : _=ᵉ_ {l1} {A} a' a) (b : B a)
           → _=ᵉ_ {l3} {Z} (F (a' ,ᵉ exo-tr {l1} {l2} {A} B (exo-inv {l1} {A} p) b)) (F (a ,ᵉ b))
    tr-F reflᵉ b = reflᵉ

    G-pt : (u : Σᵉ {l1} {l2} A B) → _=ᵉ_ {l3} {Z} (G (pt u)) (F u)
    G-pt (a ,ᵉ b) =
      exo-concat {l3} {Z}
        (exo-ap {l2} {l3} {B (ga (fa a))} {Z} (λ t → F (ga (fa a) ,ᵉ t))
                (lhb (ga (fa a)) (exo-tr {l1} {l2} {A} B (exo-inv {l1} {A} (lha a)) b)))
        (tr-F (lha a) b)

  contr-Σᵉ-const : (u u' : Σᵉ {l1} {l2} A B) → Id {l3} {Z} (F u) (F u')
  contr-Σᵉ-const u u' =
    _·_ {l3} {Z} (_⁻¹ {l3} {Z} (=ᵉ-to-Id {l3} {Z} (G-pt u)))
      (_·_ {l3} {Z}
        (ap {l1 ⊔ l2} {l3} {T} {Z} G
            (_·_ {l1 ⊔ l2} {T} (centrality {l1 ⊔ l2} T cT (pt u))
                               (_⁻¹ {l1 ⊔ l2} {T} (centrality {l1 ⊔ l2} T cT (pt u')))))
        (=ᵉ-to-Id {l3} {Z} (G-pt u')))
-------------------------------------------------------------------------------------------------------------
