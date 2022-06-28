{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Equivalences where

open import 2LTT.Exotypes public
open import 2LTT.Types public
open import 2LTT.Coercion.C public
open import 2LTT.Coercion.Fibrant_Conversion public
open import 2LTT.Coercion.Fibrant_Id_Type public
open import 2LTT.Coercion.Fibrant_Sigma public


--Tranfering a map between fibrant exo-types to a map between types
Fib-map : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
          (P : isFibrant {i} A) (Q : isFibrant {j} B) → (F : A → B) 
          → isFibrant.fibrant-match P → isFibrant.fibrant-match Q
Fib-map {i} {j} {A} {B} P Q F = fB ∘ᵉ (F ∘ᵉ gA)
   where
   gA : isFibrant.fibrant-match P → A
   gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))
   
   fB : B → isFibrant.fibrant-match Q
   fB = pr1ᵉ (isFibrant.fibrant-witness Q)

--Composition of maps between exo-types
Fib-∘-map : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k}
            (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C)
            → (G : B → C) → (F : A → B)
            → isFibrant.fibrant-match P → isFibrant.fibrant-match R
Fib-∘-map P Q R G F = Fib-map P R (G ∘ᵉ F)

--Second definition for this
Fib-comp-htpy : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k}
                (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C)
                → (G : B → C) → (F : A → B)
                → ((Fib-map Q R G) ∘ (Fib-map P Q F)) ~ (Fib-map P R (G ∘ᵉ F))
Fib-comp-htpy {i} {j} {k} {A} {B} {C} P Q R G F T = =ᵉ-to-Id (exo-ap {k} {k} fC (exo-ap G (gfB (F (gA T)))))
 where
   gA : isFibrant.fibrant-match P → A
   gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))

   gB : isFibrant.fibrant-match Q → B
   gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q))  
   
   fB : B → isFibrant.fibrant-match Q
   fB = pr1ᵉ (isFibrant.fibrant-witness Q)

   gfB : (x : B) → gB (fB x) =ᵉ x
   gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q)))

   fC : C → isFibrant.fibrant-match R
   fC = pr1ᵉ (isFibrant.fibrant-witness R)

------------------------------------------------------------------------------------
--Being equivalence of functions between fibrant exo-types
Fib-isEquiv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
              (P : isFibrant {i} A) (Q : isFibrant {j} B)
              → (F : A → B) → UU (i ⊔ j)
Fib-isEquiv P Q F = isEquiv (Fib-map P Q F)


--Inverse of an fib-equivalence
Fib-inv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
          (P : isFibrant {i} A) (Q : isFibrant {j} B)
          → (F : A → B) → (Fib-isEquiv P Q F)
          → isFibrant.fibrant-match Q → isFibrant.fibrant-match P
Fib-inv {i} {j} {A} {B} P Q F W = pr1 (equivs-are-invertible _ W)

--Coherence Laws for fib-equivalences
Fib-right-htpy : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                (P : isFibrant {i} A) (Q : isFibrant {j} B) (F : A → B) (W : Fib-isEquiv P Q F)
                → (Fib-inv {i} P Q F W) ∘ (Fib-map P Q F) ~ id
Fib-right-htpy {i} {j} {A} {B} P Q F W = pr1 (pr2 (equivs-are-invertible _ W))


Fib-left-htpy : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                (P : isFibrant {i} A) (Q : isFibrant {j} B) (F : A → B) (W : Fib-isEquiv P Q F)
                → (Fib-map P Q F) ∘ (Fib-inv {i} P Q F W) ~ id
Fib-left-htpy {i} {j} {A} {B} P Q F W = pr2 (pr2 (equivs-are-invertible _ W))

Fib-inv-isEquiv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                  (P : isFibrant {i} A) (Q : isFibrant {j} B) (F : A → B) (W : Fib-isEquiv P Q F)
                  → isEquiv (Fib-inv P Q F W)
Fib-inv-isEquiv {i} {j} {A} {B} P Q F W = invertibles-are-equiv _ (Fib-map P Q F ,
                                                                   Fib-left-htpy P Q F W ,
                                                                   Fib-right-htpy P Q F W)

--If a map between two fibrant exo-type is isomorphic, then it's fib-isequiv.
Iso-to-Fib-isEquiv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                     (P : isFibrant {i} A) (Q : isFibrant {j} B)
                     (F : A → B) → is-exo-iso F
                     → Fib-isEquiv P Q F
Iso-to-Fib-isEquiv {i} {j} {A} {B} P Q F W
  = invertibles-are-equiv {i} {j} _ (Fib-map Q P G ,
                                    (λ x → =ᵉ-to-Id (exo-concat (exo-ap {j} {i} (fA ∘ᵉ G) (gfB (F (gA x))))
                                                                  (exo-concat
                                                                   (exo-ap fA (GF (gA x)))
                                                                   (fgA x)))) ,
                                    (λ x → =ᵉ-to-Id (exo-concat (exo-ap {i} {j} (fB ∘ᵉ F) (gfA (G (gB x))))
                                                                  (exo-concat
                                                                   (exo-ap fB (FG (gB x)))
                                                                   (fgB x)))))
  where
  G : B → A
  G = pr1ᵉ W

  GF : (a : A) → G (F a) =ᵉ a
  GF = pr1ᵉ (pr2ᵉ W)

  FG : (b : B) → F (G b) =ᵉ b
  FG = pr2ᵉ (pr2ᵉ W)

  fA : A → isFibrant.fibrant-match P
  fA = pr1ᵉ (isFibrant.fibrant-witness P)

  gA : isFibrant.fibrant-match P → A
  gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))

  gfA : (x : A) → gA (fA x) =ᵉ x
  gfA = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

  fgA : (x : isFibrant.fibrant-match P) → fA (gA x) =ᵉ x
  fgA = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

  gB : isFibrant.fibrant-match Q → B
  gB = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q))

  fB : B → isFibrant.fibrant-match Q
  fB = pr1ᵉ (isFibrant.fibrant-witness Q)

  gfB : (x : B) → gB (fB x) =ᵉ x
  gfB = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q)))

  fgB : (x : isFibrant.fibrant-match Q) → fB (gB x) =ᵉ x
  fgB = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q)))


---The fib-map version of Π-functoriality
Fib-Π-functor : {i j : Level}{A : UUᵉ i}{P Q : A → UU j} {F : (a : A) → P a → Q a}
                → (W : isFibrant (Πᵉ A P)) → (U : isFibrant (Πᵉ A Q))
                → isFibrant.fibrant-match W → isFibrant.fibrant-match U
Fib-Π-functor {i} {j} {A} {P} {Q} {F} W U = fQ ∘ᵉ ((Πᵉ-functor {i} {j} idᵉ F) ∘ᵉ gP)
  where
  gP : isFibrant.fibrant-match W → (Πᵉ A P)
  gP = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness W))
   
  fQ : (Πᵉ A Q) → isFibrant.fibrant-match U
  fQ = pr1ᵉ (isFibrant.fibrant-witness U)




--If two maps are Fib-is-equiv, then so is their "product".
Fib-×-isEquiv :  {i j k l : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k} {D : UUᵉ l}
                 (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C) (S : isFibrant {l} D)
                 → (F : A → B) → (G : C → D)
                 → Fib-isEquiv P Q F
                 → Fib-isEquiv R S G
                 → Fib-isEquiv (isFibrant-× P R) (isFibrant-× Q S) (×ᵉ-of-maps F G)
Fib-×-isEquiv {i} {j} {k} {l} {A} {B} {C} {D} P Q R S F G W U
  = invertibles-are-equiv _
     ((λ {(x , y) → (inv-F x , inv-G y)}) ,
     (λ {(x , y) → pair⁼ _ _ (left-htp-F x , left-htp-G y)}) ,
     λ {(x , y) → pair⁼ _ _ (right-htp-F x , right-htp-G y)})
  where
  inv-F : isFibrant.fibrant-match Q → isFibrant.fibrant-match P
  inv-F = pr1 (equivs-are-invertible _ W)

  left-htp-F : (x : _ ) → Id (inv-F ((Fib-map P Q F) x)) x
  left-htp-F = pr1 (pr2 (equivs-are-invertible _ W))

  right-htp-F : (x : _ ) → Id ((Fib-map P Q F)(inv-F x)) x
  right-htp-F = pr2 (pr2 (equivs-are-invertible _ W))

  inv-G : isFibrant.fibrant-match S → isFibrant.fibrant-match R
  inv-G = pr1 (equivs-are-invertible _ U)

  left-htp-G : (y : _ ) → Id (inv-G ((Fib-map R S G) y)) y
  left-htp-G = pr1 (pr2 (equivs-are-invertible _ U))

  right-htp-G : (y : _ ) → Id ((Fib-map R S G)(inv-G y)) y
  right-htp-G = pr2 (pr2 (equivs-are-invertible _ U))




--If two maps between exo-types are homotopic wrt =ᵉ , one is Fib-isEquiv iff the other is.
Fib-htpy-to-isEquiv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                      (P : isFibrant {i} A) (Q : isFibrant {j} B)
                      → (F G : A → B)
                      → ((a : A) → F a =ᵉ G a)
                      → Fib-isEquiv P Q F
                      → Fib-isEquiv P Q G
Fib-htpy-to-isEquiv {i} {j} {A} {B} P Q F G Htpy W = htpy-equiv {i} {j} (Fib-map P Q F)
                                                     (Fib-map P Q G)
                                                     (λ x → =ᵉ-to-Id (exo-ap fB (Htpy (gA x))))
                                                     W
  where
   gA : isFibrant.fibrant-match P → A
   gA = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))
   
   fB : B → isFibrant.fibrant-match Q
   fB = pr1ᵉ (isFibrant.fibrant-witness Q)

--The composition of Fib-isEquiv maps is Fib-isEquiv
Fib-comp-isEquiv : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k}
                   (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C)
                   → (F : A → B) → (G : B → C)
                   → (Fib-isEquiv P Q F)
                   → (Fib-isEquiv Q R G)
                   → (Fib-isEquiv P R (G ∘ᵉ F))
Fib-comp-isEquiv {i} {j} {k} {A} {B} {C} P Q R F G U V
  = htpy-equiv {i} {k} ((Fib-map Q R G) ∘ (Fib-map P Q F))
                       (Fib-map P R (G ∘ᵉ F))
                       (Fib-comp-htpy {i} {j} {k} {A} {B} {C} P Q R G F)
                       (∘-is-equiv {i} {j} {k} (Fib-map P Q F) (Fib-map Q R G) U V)

-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------
--2-out-of-3-property for fibrant exo-types
--It says that if f and g are two composable maps, then if 2 of f, g, f∘ g are equivalent, so is the third.
Fib-First-2-out-of-3-rule : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k}
                            (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C)
                            → (F : A → B) → (G : B → C)
                            → (Fib-isEquiv P Q F)
                            → (Fib-isEquiv P R (G ∘ᵉ F))                            
                            → (Fib-isEquiv Q R G)
Fib-First-2-out-of-3-rule {i} {j} {k} {A} {B} {C} P Q R F G W U
  = htpy-equiv {j} {k} ((Fib-map P R (G ∘ᵉ F)) ∘ (Fib-inv P Q F W))
                        (Fib-map Q R G)
                        (λ x → ((Fib-comp-htpy {i} {j} {k} {A} {B} {C} P Q R G F) ((Fib-inv P Q F W) x)) ⁻¹
                                 · ap (Fib-map Q R G) (Fib-left-htpy {i} {j} {A} {B} P Q F W x))
                        (∘-is-equiv {j} {i} {k} (Fib-inv P Q F W) (Fib-map P R (G ∘ᵉ F)) (Fib-inv-isEquiv P Q F W) U)



Fib-Second-2-out-of-3-rule : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k}
                             (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C)
                            → (F : A → B) → (G : B → C)
                            → (Fib-isEquiv Q R G)
                            → (Fib-isEquiv P R (G ∘ᵉ F))                            
                            → (Fib-isEquiv P Q F)
Fib-Second-2-out-of-3-rule {i} {j} {k} {A} {B} {C} P Q R F G W U
  = htpy-equiv {i} {j} ((Fib-inv Q R G W) ∘ (Fib-map P R (G ∘ᵉ F)))
                        (Fib-map P Q F)
                        (λ x → ap (Fib-inv Q R G W) (((Fib-comp-htpy {i} {j} {k} {A} {B} {C} P Q R G F) x) ⁻¹)
                                · (Fib-right-htpy {j} {k} {B} {C} Q R G W  (Fib-map P Q F x)))
                        (∘-is-equiv {i} {k} {j} (Fib-map P R (G ∘ᵉ F)) (Fib-inv Q R G W) U (Fib-inv-isEquiv Q R G W))


---------------------------------------------------------------------------
--Commutative Squares
--Suppose we have commutative diagram
-- A --g→ B
-- |       |
-- f       f'
-- ↓       ↓ 
-- A'--g'→ B'
Fib-Com-Square : {i j k l : Level} {A : UUᵉ i} {A' : UUᵉ j} {B : UUᵉ k} {B' : UUᵉ l}
                 (g : A → B) (f : A → A') (f' : B → B') (g' : A' → B')
                  → UUᵉ (i ⊔ l)
Fib-Com-Square {i} {j} {k} {l} {A} g f f' g' = (a : A) → _=ᵉ_ {l} (f' (g a)) (g' (f a))



--In this case, if three of them are equivalent, then so is the fourth.
Fib-First-3-out-of-4-rule : {i j k l : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k} {D : UUᵉ l}
                          (P : isFibrant {i} A) (Q : isFibrant {j} B) (R : isFibrant {k} C) (S : isFibrant {l} D)
                          → (h-top : A → B) → (v-left : A → C) → (v-right : B → D) → (h-bot : C → D)
                          → Fib-Com-Square h-top v-left v-right h-bot
                          → (Fib-isEquiv P Q h-top) → (Fib-isEquiv Q S v-right) → (Fib-isEquiv R S h-bot)
                          → (Fib-isEquiv P R v-left)
Fib-First-3-out-of-4-rule  {i} {j} {k} {l} {A} {B} {C} {D} P Q R S h-top v-left v-right h-bot FCS W U V
  = Fib-Second-2-out-of-3-rule {i} {k} {l} {A} {C} {D} P R S v-left h-bot
                               V
                               (Fib-htpy-to-isEquiv {i} {l} {A} {D} P S (v-right ∘ᵉ h-top) (h-bot ∘ᵉ v-left) FCS
                               (Fib-comp-isEquiv {i} {j} {l} {A} {B} {D} P Q S h-top v-right W U))

