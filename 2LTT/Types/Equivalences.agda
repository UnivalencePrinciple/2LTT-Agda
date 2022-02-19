{-# OPTIONS --without-K --two-level #-}

module 2LTT.Types.Equivalences where

open import 2LTT.Types.Functions
open import 2LTT.Types.Id_Type
open import 2LTT.Types.Pi
open import 2LTT.Primitive
open import 2LTT.Types.Sigma
open import 2LTT.Types.Type_Hierarchy
open import 2LTT.Types.Unit
open import 2LTT.Types.Retraction
open import 2LTT.Types.Coproduct


----------------------------------------------------------
--There are various definitions of being equivalence. We'll use the definiton used in "Univalence Principle(2021)" paper :
isEquiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
isEquiv f = Π _ (λ b → is-contr (Σ _ (λ a → Id (f a) b)))


infixr 30 _≃_
_≃_ : {i j : Level} → (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → isEquiv f)

id-is-equiv : {i : Level} {A : UU i} → isEquiv (id {i} {A})
id-is-equiv {i} {A} = λ b → path-type-is-contr b

--This type is a proposition.
is-prop-isEquiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B)
                  → is-prop (isEquiv f)
is-prop-isEquiv {i} {j} {A} f = Π-type-prop λ b → is-prop-contr {i ⊔ j} (Σ A (λ a → Id (f a) b))

-----------------------------------------
----Different characterization
-----------------------------------------
--Source: Introduction to Univalent Foundations of Mathematics with Agda by
--Martín Hötzel Escardó

isInvertible : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
isInvertible f = Σ (_ → _) (λ g → ((g ∘ f) ~ id) × ((f ∘ g) ~ id)) 


fiber : {i j : Level}{A : UU i}{B : UU j} (f : A → B) → B → UU (i ⊔ j)
fiber f b =  Σ _ (λ a → Id (f a) b)

fiber-point : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{b : B}
             → fiber f b → A
fiber-point (a , p) = a

fiber-identification : {i j : Level}{A : UU i}{B : UU j}{f : A → B}{b : B} → (w : fiber f b) → Id (f (fiber-point w)) b
fiber-identification (a , p) = p

inv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f) → (B → A)
inv f P = λ b → fiber-point (center (fiber f b) (P b))

inv-is-section :  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f)
                  → (f ∘ (inv f P)) ~ id
inv-is-section f P b = fiber-identification (center (fiber f b) (P b))

inv-central : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f)
             → (b : B) (t : Σ A (λ a → Id (f a) b))
             → Id t ((inv f P b) , inv-is-section f P b)
inv-central f P b t = centrality (fiber f b) (P b) t

inv-is-retraction : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f)
                    → ((inv f P) ∘ f) ~ id
inv-is-retraction f P a = let p = inv-central f P (f a) (a , refl)
                          in (ap fiber-point p) ⁻¹

equivs-are-invertible : {i j : Level} {A : UU i} {B : UU j} (f : A → B)
                        → isEquiv f → isInvertible f
equivs-are-invertible f P = inv f P , (inv-is-retraction f P) , (inv-is-section f P)

invertibles-are-equiv : {k j : Level} {A : UU k} {B : UU j} (f : A → B)
                        → isInvertible f → isEquiv f
invertibles-are-equiv {k} {j} {A} {B} f (g , η , ε) b = iii
 where
  i : (b' : B) → (Id (f (g b')) b) ◃ (Id b' b)
  i  b' = r , s , tr-is-section (λ _ → Id _ b) (ε b')
   where
    s : Id (f (g b')) b → Id b' b
    s = tr (λ c → Id c b) (ε b')

    r : Id b' b → Id (f (g b')) b
    r = tr (λ c → Id c b) ((ε b') ⁻¹)

  ii : (fiber f b) ◃ (path-type b)
  ii = (Σ A (λ a → Id (f a) b)) ◃⟨ Σ-reindexing-retract g (f , η) ⟩
        ((Σ B (λ b' → Id (f (g b')) b)) ◃⟨ Σ-retract i ⟩
        ((Σ B (λ b' → Id b' b) ◂)))
  iii : is-contr (fiber f b)
  iii = retract-of-singleton ii (path-type-is-contr {j} {B} b)
-------------------------------------------

inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f) → isEquiv (inv f P)
inv-is-equiv f P = invertibles-are-equiv
                      (inv f P)
                      (f , inv-is-section f P , inv-is-retraction f P)

inversion-involute :  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv f) → Id (inv (inv f P) (inv-is-equiv f P)) f
inversion-involute f P = refl


∘-is-invertible : {i j k : Level} {A : UU i}{B : UU j}{C : UU k}
                  {f : A → B}{f' : B → C}
                  → isInvertible f' → isInvertible f → isInvertible (f' ∘ f)
∘-is-invertible {i} {j} {k} {A} {B} {C} {f} {f'} (g' , g'f' , f'g') (g , gf , fg) = g ∘ g' , η , ε
  where
    η = λ a → g (g' (f' (f a))) ≡⟨ ap g (g'f' (f a)) ⟩
              (g (f a)          ≡⟨ gf a ⟩
               (a ▮ ))

    ε = λ c → f' (f (g (g' c))) ≡⟨ ap f' (fg (g' c)) ⟩
              (f' (g' c)          ≡⟨ f'g' c ⟩
               (c ▮ ))

∘-is-equiv :  {i j k : Level} {A : UU i}{B : UU j}{C : UU k}
                  (f : A → B) (g : B → C)
                  → isEquiv g → isEquiv f → isEquiv (g ∘ f)
∘-is-equiv  {i} {j} {k} {A} {B} {C} f g r s =
                          invertibles-are-equiv (g ∘ f)
                                                (∘-is-invertible
                                                    (equivs-are-invertible g r)
                                                    (equivs-are-invertible f s))




--------------------------------------------------------------------------
-- ≃ is an equivalence relation
≃-refl : {i : Level} (A : UU i) → A ≃ A
≃-refl A = id , λ a → (a , refl) , λ {(a' , refl) → refl}

-----------------------------------------------------------------------
--UNIVALENCE AXIOM

idtoeqv : {i : Level} {A B : UU i}
          → Id A B → A ≃ B
idtoeqv {A = A} {B = .A} refl = (≃-refl A)

postulate
  UNIVALENCE : {i : Level} {A B : UU i} → isEquiv (idtoeqv {i} {A} {B})

ua : {i : Level} {A B : UU i}
      → A ≃ B → Id A B
ua = inv idtoeqv UNIVALENCE
-----------------------------------------------------------------------

≃-sym : {i : Level} {A B : UU i} → A ≃ B → B ≃ A
≃-sym P = idtoeqv ((ua P) ⁻¹)

≃-trans : {i : Level} {A B C : UU i} → A ≃ B → B ≃ C → A ≃ C
≃-trans P Q = idtoeqv (ua P · ua Q)


---Characterization of Some Identity Types
--Product
isEquiv-inv-pair⁼ : {i j : Level} {A : UU i} {B : UU j} (u v : A × B)
            → isEquiv (inv-pair⁼ u v)
isEquiv-inv-pair⁼ u v p = (pair⁼ u v p , htpy-inv-pair⁼-pair⁼ u v p) , λ {(refl , refl) → refl}

×-Id-char : {i j : Level} {A : UU i} {B : UU j} (u v : A × B)
            → Id u v ≃ pair-Id u v
×-Id-char u v = inv-pair⁼ u v , isEquiv-inv-pair⁼ u v

×-Id-rule : {i j : Level} {A : UU i} {B : UU j} (u v : A × B)
            → Id (Id u v) (pair-Id u v)
×-Id-rule u v = ua (×-Id-char u v)

--Sigma-Types
isEquiv-inv-dep-pair⁼ : {i j : Level} {A : UU i} {B : A → UU j} (u v : Σ A B)
            → isEquiv (inv-dep-pair⁼ u v)
isEquiv-inv-dep-pair⁼ u v p = (dep-pair⁼ u v p , htpy-inv-dep-pair⁼-dep-pair⁼ u v p) ,  λ {(refl , refl) → refl}

Σ-Id-char : {i j : Level} {A : UU i} {B : A → UU j} (u v : Σ A B)
            → Id u v ≃ dep-pair-Id u v
Σ-Id-char u v = inv-dep-pair⁼ u v , isEquiv-inv-dep-pair⁼ u v

Σ-Id-rule : {i j : Level} {A : UU i} {B : A → UU j} (u v : Σ A B)
            → Id (Id u v) (dep-pair-Id u v)
Σ-Id-rule u v  = ua (Σ-Id-char u v)

--Pi-Types
Π-Id-char : {i j : Level} {A : UU i} {B : A → UU j} (f g : Π A B)
            → Id f g ≃ (f ~ g)
Π-Id-char f g = happly , FUNEXT

Π-Id-rule : {i j : Level} {A : UU i} {B : A → UU j} (f g : Π A B)
            → Id (Id f g) (f ~ g)
Π-Id-rule f g = ua (Π-Id-char f g)


-------extra
const-from-contr-is-equiv : {i : Level}{A : UU i}{f : A → ⊤} → is-contr A → isEquiv f
const-from-contr-is-equiv (a , P) = λ {star
                                        → (a , refl) ,
                                           λ {(a' , p)
                                           → dep-pair⁼ (a' , p) (a , refl)
                                            (P a' , all-elements-equal-is-prop
                                                    (is-prop-is-contr (Id star star) (refl , (λ {refl → refl})))
                                                    (tr (λ v → star ≡ star) (P a') p) refl)}}



is-contr-cong : {i : Level} {A B : UU i}
                → A ≃ B
                → is-contr A
                → is-contr B
is-contr-cong (f , P) (a , Q) = f a , λ b → (ap f ((Q (pr1 (pr1 (P b)))) ⁻¹) · pr2 (pr1 (P b)) ) ⁻¹

--------------------------------------------------------------
Π-Σ-expansion : {i j k : Level} {A : UU i} {B : A → UU j} {Y : Σ A B → UU k}
               → (Π (Σ A B) Y) → (Π A (λ a → Π (B a) λ b → Y (a , b)))
Π-Σ-expansion = (λ g → λ a → λ b → g (a , b)) 
                
Π-Σ-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : A → UU j} {Y : Σ A B → UU k}
                          → isEquiv (Π-Σ-expansion {i} {j} {k} {A} {B} {Y})
Π-Σ-expansion-is-equiv = invertibles-are-equiv (λ g → λ a → λ b → g (a , b))
                             ((λ f → λ {(a , b) → f a b}) , (λ x → refl) , (λ x → refl))


--------------------------------------------------------------------------------
Π-×-expansion : {i j k : Level} {A : UU i} {B : UU j} {Y : A × B → UU k}
               → (Π (A × B) Y) → (Π A (λ a → Π B λ b → Y (a , b)))
Π-×-expansion = (λ g → λ a → λ b → g (a , b)) 
                
Π-×-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : UU j} {Y : A × B → UU k}
                          → isEquiv (Π-×-expansion {i} {j} {k} {A} {B} {Y})
Π-×-expansion-is-equiv = invertibles-are-equiv (λ g → λ a → λ b → g (a , b))
                             ((λ f → λ {(a , b) → f a b}) , (λ x → refl) , (λ x → refl))

-------------------------------------------------------------
Π-+-expansion : {i j k : Level} {A : UU i} {B : UU j} {Y : A + B → UU k}
               → (Π (A + B) Y) → (Π A (λ a → Y (inl a))) × (Π B (λ b → Y (inr b)))
Π-+-expansion t = (λ x → t (inl x)) , (λ x → t (inr x))

Π-+-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : UU j} {Y : A + B → UU k}
                          → isEquiv (Π-+-expansion {i} {j} {k} {A} {B} {Y})
Π-+-expansion-is-equiv = invertibles-are-equiv (λ t →  (λ x → t (inl x)) , (λ x → t (inr x)))
                            ((λ {(u , v) (inl x) → u x ; (u , v) (inr x) → v x}) ,
                            (λ x → funext λ {(inl x) → refl ; (inr x) → refl} ) ,
                            λ {(u , v) → pair⁼ _ _ (refl , refl)})



------------------------------------------------------------------------------
×-of-maps : {i j i' j' : Level} {A : UU i} {A' : UU i'} {B : UU j} {B' : UU j'}
            → (f : A → B) (f' : A' → B')
            → (A × A' → B × B')
×-of-maps f f' (a , a') = (f a , f' a')

×-of-maps-is-equiv : {i j i' j' : Level} {A : UU i} {A' : UU i'} {B : UU j} {B' : UU j'}{f : A → B}{f' : A' → B'}
                     → isEquiv f → isEquiv f' → isEquiv (×-of-maps f f')
×-of-maps-is-equiv {f = f} {f' = f'} P Q = let (g , gf , fg) = equivs-are-invertible f P ;
                                                (g' , g'f' , f'g') = equivs-are-invertible f' Q
                                            in invertibles-are-equiv (×-of-maps f f')
                                               (×-of-maps g g' ,
                                               (λ {(a , a') → pair⁼ _ _ (gf a , g'f' a')}) ,
                                               (λ {(b , b') → pair⁼ _ _ (fg b , f'g' b')}))

--------------------------------------------------------------------------
--Homotopic Maps & Equivalences
htpy-equiv : {i j : Level} {A : UU i} {B : UU j}
             (f g : A → B)
             → f ~ g
             → isEquiv f
             → isEquiv g
htpy-equiv f g H P = let (f' , (f'f , ff')) = equivs-are-invertible f P
                     in  invertibles-are-equiv g ((λ x → f' x) ,
                                              (λ x → (ap f' (H x) ⁻¹) · f'f x) ,
                                              (λ x → (H (f' x) ⁻¹) · ff' x))

-------------------------------------------------------------------------------------------
--2-out-of-3-property
--It says that if f and g are two composable maps, then if 2 of f, g, f∘ g are equivalent, so is the third.
First-2-out-of-3-rule : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                        (f : A → B) (g : B → C)
                        → isEquiv f
                        → isEquiv (g ∘ f)
                        → isEquiv g
First-2-out-of-3-rule f g P Q = let (f' , (f'f , ff')) = equivs-are-invertible f P
                                in htpy-equiv ((g ∘ f) ∘ f') g
                                              (λ x → ap g (ff' x))
                                              (∘-is-equiv f' (g ∘ f) Q (inv-is-equiv f P))

Second-2-out-of-3-rule : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                        (f : A → B) (g : B → C)
                        → isEquiv g
                        → isEquiv (g ∘ f)
                        → isEquiv f
Second-2-out-of-3-rule f g P Q = let (g' , (g'g , gg')) = equivs-are-invertible g P
                                in htpy-equiv (g' ∘ (g ∘ f)) f
                                              (λ x → g'g (f x))
                                              (∘-is-equiv (g ∘ f) g' (inv-is-equiv g P) Q)

---------------------------------------------------------------------------
--Commutative Squares
--Suppose we have commutative diagram
-- A --g→ B
-- |       |
-- f       f'
-- ↓       ↓ 
-- A'--g'→ B'
Com-Square : {i j k l : Level} {A : UU i} {A' : UU j} {B : UU k} {B' : UU l}
             (f : A → A') (f' : B → B') (g : A → B) (g' : A' → B')
             → UU (i ⊔ l)
Com-Square f f' g g' = (a : _) → Id (f' (g a)) (g' (f a)) 

--In this case, if three of them are equivalent, then so is the fourth.
First-3-out-of-4-rule : {i j k l : Level} {A : UU i} {A' : UU j} {B : UU k} {B' : UU l}
                        (f : A → A') (f' : B → B') (g : A → B) (g' : A' → B')
                        → Com-Square f f' g g'
                        → (isEquiv f') → (isEquiv g) → (isEquiv g')
                        → isEquiv f
First-3-out-of-4-rule f f' g g' CS Pf' Pg Pg' = Second-2-out-of-3-rule
                                                      f
                                                      g'
                                                      Pg'
                                                      (htpy-equiv
                                                         (f' ∘ g)
                                                         (g' ∘ f)
                                                         (CS)
                                                         (∘-is-equiv g f' Pf' Pg))                       
