{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

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

inv-is-section :  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv {i} {j} f)
                  → (f ∘ (inv f P)) ~ id
inv-is-section {i} {j} f P b = fiber-identification (center {i ⊔ j} (fiber f b) (P b))

inv-central : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv {i} {j} f)
             → (b : B) (t : Σ A (λ a → Id {j} (f a) b))
             → Id {i ⊔ j} t ((inv f P b) , inv-is-section f P b)
inv-central {i} {j} f P b t = centrality {i ⊔ j} (fiber f b) (P b) t

inv-is-retraction : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv {i} {j} f)
                    → ((inv f P) ∘ f) ~ id
inv-is-retraction {i} {j} f P a = let p = inv-central {i} {j} f P (f a) (a , refl)
                          in (ap {i ⊔ j} {i} fiber-point p) ⁻¹

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
  ii = _◃⟨_⟩_ (Σ {k} {j} A (λ a → Id {j} (f a) b)) (Σ-reindexing-retract {k} {j} {j} g (f , η))
        (_◃⟨_⟩_ {j} {j} {j} (Σ {j} {j} B (λ b' → Id {j} (f (g b')) b)) (Σ-retract {j} {j} {j} i)
        ((Σ {j} {j} B (λ b' → Id {j} b' b) ◂)))
  iii : is-contr (fiber f b)
  iii = retract-of-singleton ii (path-type-is-contr {j} {B} b)
-------------------------------------------

inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv {i} {j} f) → isEquiv {j} {i} (inv f P)
inv-is-equiv {i} {j} f P = invertibles-are-equiv {j} {i}
                      (inv f P)
                      (f , inv-is-section f P , inv-is-retraction f P)


≃-sym : {i j : Level} {A : UU i} {B : UU j} → A ≃ B → B ≃ A
≃-sym P = inv (pr1 P) (pr2 P) , inv-is-equiv (pr1 P) (pr2 P)


inversion-involute :  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (P : isEquiv {i} {j} f)
                             → Id {i ⊔ j} (inv {j} {i} (inv f P) (inv-is-equiv f P)) f
inversion-involute f P = refl


∘-is-invertible : {i j k : Level} {A : UU i}{B : UU j}{C : UU k}
                  {f : A → B}{f' : B → C}
                  → isInvertible f → isInvertible f' → isInvertible (f' ∘ f)
∘-is-invertible {i} {j} {k} {A} {B} {C} {f} {f'} (g , gf , fg) (g' , g'f' , f'g') = g ∘ g' , η , ε
  where
    η = λ a → _≡⟨_⟩_ {i} (g (g' (f' (f a)))) (ap g (g'f' (f a)))
                (_≡⟨_⟩_ {i} (g (f a)) (gf a)
                (a ▮ ))

    ε = λ c → _≡⟨_⟩_ {k} (f' (f (g (g' c)))) (ap f' (fg (g' c)))
              (_≡⟨_⟩_ {k} (f' (g' c)) (f'g' c)
              (c ▮ ))

∘-is-equiv :  {i j k : Level} {A : UU i}{B : UU j}{C : UU k}
                  (f : A → B) (g : B → C)
                  → isEquiv f → isEquiv g → isEquiv (g ∘ f)
∘-is-equiv  {i} {j} {k} {A} {B} {C} f g r s =
                          invertibles-are-equiv {i} {k} (g ∘ f)
                                                (∘-is-invertible
                                                    (equivs-are-invertible {i} {j} f r)
                                                    (equivs-are-invertible {j} {k} g s))

≃-trans : {i j k : Level} {A : UU i}{B : UU j}{C : UU k} → A ≃ B → B ≃ C → A ≃ C
≃-trans P Q = (pr1 Q) ∘ (pr1 P) , ∘-is-equiv (pr1 P) (pr1 Q) (pr2 P) (pr2 Q)

-------------------------------------------------------------------------
--Property of coherently invertible map
nat-htpy-of-invertible : {i j : Level} {A : UU i} {B : UU j} (f : A → B)
                         → ((g , gf , fg) : isInvertible {i} {j} f)
                         → Σ {j} {i ⊔ j} (f ∘ g ~ id) (λ G → ((a : A) → Id {j} (ap {i} {j} f (gf a)) (G (f a))))
nat-htpy-of-invertible {i} {j} {A} {B} f (g , gf , fg) = G , T
  where
  G : f ∘ g ~ id
  G b = (fg (f (g b))) ⁻¹ · ((ap f (gf (g b))) · (fg b))

  p1 : (a : A) → Id (gf (g (f a))) (ap {j} {i} g (ap {i} {j}f (gf a)))
  p1 a = (nat-trans-htpy-to-id {i} {A} (g ∘ f) a gf) · (ap-comp {i} {j} {i} g f (gf a)) ⁻¹

  p2 : (a : A) → Id ((ap {i} {j} f (gf (g (f a)))) · fg (f a))  (fg (f (g (f a))) · ap f (gf a))
  p2 a = ap {i} {j} (λ q → (ap f q) · (fg (f a))) (p1 a) ·
         (ap (λ q → q · (fg (f a))) (ap-comp {j} {i} {j} f g (ap f (gf a))) ·
          ((nat-trans-htpy {j} {j} {B} {B} {f ∘ g} {id} {f (g (f a))} {f a} fg (ap {i} {j} f (gf a))) ⁻¹ ·
            ap {j} {j} (λ q → fg (f (g (f a))) · q) (ap-id (ap f (gf a)))))

  T : (a : A) → Id (ap f (gf a)) (G (f a))
  T a = (left-unit (ap {i} {j} f (gf a))) ⁻¹ ·
          (ap (λ p → p · (ap {i} {j} f (gf a))) (left-inv (fg (f (g (f a))))) ⁻¹ ·
             (assoc ((fg (f (g (f a)))) ⁻¹) (fg (f (g (f a)))) (ap f (gf a)) ·
               (ap {j} {j} (λ q → (((fg (f (g (f a)))) ⁻¹) · q)) (p2 a) ⁻¹)))


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
Π-Id-char {i} {j} f g = happly {i} {j} , FUNEXT {i} {j}

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



is-contr-cong : {i j : Level} {A : UU i} {B : UU j}
                → A ≃ B
                → is-contr A
                → is-contr B
is-contr-cong (f , P) (a , Q) = f a , λ b → (ap f ((Q (pr1 (pr1 (P b)))) ⁻¹) · pr2 (pr1 (P b)) ) ⁻¹

---------------------------------------------------------------------------------------------------------------------------
ap-isEquiv : {i j : Level} {A : UU i} {B : UU j}
             → (W : A ≃ B)
             → (x y : A) → isEquiv (ap (pr1 W) {x} {y})
ap-isEquiv {i} {j} {A} {B} W x y = invertibles-are-equiv (ap {i} {j} f) ((λ p → (gf x ⁻¹) · ((ap {j} {i} g p) · (gf y))) ,
                                                 (λ q → F q) ,
                                                 (λ q → G q))
  where
  f = pr1 W
  g = pr1 (equivs-are-invertible f (pr2 W))
  gf = pr1 (pr2 (equivs-are-invertible f (pr2 W)))
  fg = pr2 (pr2 (equivs-are-invertible f (pr2 W)))

  F : (q : Id {i} x y) → Id ((gf x ⁻¹) · (ap {j} {i} g (ap f q) · gf y)) (id q)
  F refl = left-inv (gf x)

  G : (q : Id {j} (f x) (f y)) → Id (ap f ((gf x ⁻¹) · (ap {j} {i} g q · gf y))) (id q)
  G q = path1 · (path2 · (path3 · (path4 · path5)))
    where
    path = (ap f ((gf x ⁻¹) · (ap {j} {i} g q · gf y)))
    path1 : Id path
               ((fg (f x) ⁻¹ · fg (f x)) · ((ap f ((gf x ⁻¹) · (ap {j} {i} g q · gf y))) · (fg (f y) ⁻¹ · fg (f y))))
    path1 = (left-unit (ap {i} {j} f ((gf x ⁻¹) · (ap {j} {i} g q · gf y)))) ⁻¹ ·
           ((ap {j} {j} (λ s → s · (ap {i} {j} f ((gf x ⁻¹) · (ap {j} {i} g q · gf y)))) (left-inv (fg (f x)))) ⁻¹ ·
           ((ap {j} {j} (λ s → ((fg (f x) ⁻¹) · fg (f x)) · s) (right-unit (ap {i} {j} f ((gf x ⁻¹) · (ap {j} {i} g q · gf y))))) ⁻¹ ·
           ((ap {j} {j} (λ s → ((fg (f x) ⁻¹) · fg (f x)) · ( (ap f ((gf x ⁻¹) · (ap {j} {i} g q · gf y))) · s)) (left-inv (fg (f y)))) ⁻¹)))

    path2 : Id ((fg (f x) ⁻¹ · fg (f x)) · (path · (fg (f y) ⁻¹ · fg (f y))))
               (fg (f x) ⁻¹ · (ap {i} {j} f (ap {j} {i} g path) · (fg (f y))))
    path2 = assoc (fg (f x) ⁻¹) (fg (f x)) _ · (ap {j} {j} (λ s → fg (f x) ⁻¹ · s) ((assoc (fg (f x)) path _) ⁻¹) ·
            (ap (λ s → fg (f x) ⁻¹ · s) ((assoc (fg (f x) · path) (fg (f y) ⁻¹) (fg (f y))) ⁻¹) ·
            ((ap {j} {j} (λ s → fg (f x) ⁻¹ · (((fg (f x) · s) · (fg (f y) ⁻¹)) · (fg (f y)))) (ap-id path) ⁻¹)
            · (ap {j} {j} (λ s → fg (f x) ⁻¹ · (s · fg (f y))) (nat-trans-htpy2 {j} {j} {B} {B} {f ∘ g} {id} fg path) ·
             ap {j} {j} (λ s → fg (f x) ⁻¹ · (s · fg (f y))) (ap-comp f g path) ⁻¹ ))))

    path3 : Id (fg (f x) ⁻¹ · (ap {i} {j} f (ap {j} {i} g path) · (fg (f y))))
               (fg (f x) ⁻¹ · (ap {i} {j} f ((((gf x) · (gf x) ⁻¹) · (ap g q)) · ((gf y) · (gf y) ⁻¹)) · (fg (f y))))
    path3 =  ap {i} {j} (λ s → fg (f x) ⁻¹ · ((ap {i} {j} f s) · fg (f y))) (ap-comp g f _)  ·
             (ap {i} {j} (λ s → fg (f x) ⁻¹ · ((ap {i} {j} f s) · fg (f y)))
                                      ((nat-trans-htpy2 {i} {i} {A} {A} {g ∘ f} {id} gf ((gf x ⁻¹) · (ap {j} {i} g q · gf y))) ⁻¹) ·
             (ap {i} {j} (λ s → fg (f x) ⁻¹ · ((ap {i} {j} f ((gf x · s) · (gf y ⁻¹))) · fg (f y))) (ap-id _)  ·
             (ap {i} {j} (λ s → (fg (f x) ⁻¹) · (ap {i} {j} f (((gf x) · s) · (gf y ⁻¹)) · (fg (f y))))
                           ((assoc (gf x ⁻¹) (ap {j} {i} g q) (gf y)) ⁻¹) ·
             (ap {i} {j} (λ s → (fg (f x) ⁻¹) · (ap {i} {j} f (s · (gf y ⁻¹)) · (fg (f y))))
                           ((assoc (gf x) (gf x ⁻¹ · ap {j} {i} g q) (gf y)) ⁻¹) ·
             (ap {i} {j} (λ s → (fg (f x) ⁻¹) · (ap f ((s · gf y) · (gf y ⁻¹)) · (fg (f y))))
                           ((assoc (gf x) (gf x ⁻¹) (ap g q)) ⁻¹) ·
             (ap {i} {j} (λ s → (fg (f x) ⁻¹) · ((ap {i} {j} f s) · (fg (f y))))
                           (assoc ((gf x · gf x ⁻¹) · ap {j} {i} g q) (gf y) (gf y ⁻¹))))))))

    path4 : Id (fg (f x) ⁻¹ · (ap {i} {j} f ((((gf x) · (gf x) ⁻¹) · (ap g q)) · ((gf y) · (gf y) ⁻¹)) · (fg (f y))))
               (fg (f x) ⁻¹ · (ap {i} {j} f (ap g q) · (fg (f y))))
    path4 = ap {i} {j} (λ s → (fg (f x) ⁻¹) · ((ap {i} {j} f ((((gf x) · (gf x) ⁻¹) · (ap {j} {i} g q)) · s)) · (fg (f y))))
                                                                                                          (right-inv (gf y)) ·
            (ap {i} {j} (λ s → (fg (f x) ⁻¹) · ((ap {i} {j} f s) · (fg (f y)))) (right-unit ((gf x · gf x ⁻¹) · ap g q)) ·
            (ap {i} {j} (λ s → (fg (f x) ⁻¹) · ((ap {i} {j} f (s · ap {j} {i} g q)) · (fg (f y)))) (right-inv {i} (gf x)) ·
            ap {i} {j} (λ s → (fg (f x) ⁻¹) · ((ap {i} {j} f s) · (fg (f y)))) (left-unit {i} (ap {j} {i} g q))))

    path5 : Id (fg (f x) ⁻¹ · (ap {i} {j} f (ap g q) · (fg (f y)))) q
    path5 = ap {j} {j} (λ s → (fg (f x) ⁻¹) · (s · (fg (f y)))) (ap-comp f g q) ·
           ((ap {j} {j} (λ s → (fg (f x) ⁻¹ · (ap {j} {j} (f ∘ g) q · s))) (double-inv {j} (fg (f y)) ⁻¹) ·
            (assoc (fg (f x) ⁻¹) (ap {j} {j} (f ∘ g) q) ((fg (f y) ⁻¹) ⁻¹) ⁻¹)) ·
            (nat-trans-htpy2 {j} {j} {B} {B} {id} {f ∘ g} {f x} {f y} (λ x → (fg x ⁻¹)) q · ap-id {j} q))


----------------------------------------------------------------------------------------------------------------------------------
is-truncation-cong : {i j : Level} {A : UU i} {B : UU j}
                     → _≃_ {i} {j} A B
                     → (t : 𝕋)
                     → is-type {j} t B
                     → is-type {i} t A
is-truncation-cong {i} {j} W neg-two-𝕋 P = is-contr-cong {j} {i} (≃-sym W) P
is-truncation-cong {i} {j} W (succ-𝕋 t) P = λ a a' → is-truncation-cong {i} {j} {Id {i} (a) (a')} {Id {j} (f a) (f a')}
                                                                         (ap {i} {j} f , ap-isEquiv W a a') t (P (f a) (f a'))
  where
  f = pr1 W
  g = pr1 (equivs-are-invertible f (pr2 W))
  gf = pr1 (pr2 (equivs-are-invertible f (pr2 W)))
  fg = pr2 (pr2 (equivs-are-invertible f (pr2 W)))

--------------------------------------------------------------
Π-Σ-expansion : {i j k : Level} {A : UU i} {B : A → UU j} {Y : Σ {i} {j} A B → UU k}
               → (Π (Σ A B) Y) → (Π A (λ a → Π (B a) λ b → Y (a , b)))
Π-Σ-expansion = (λ g → λ a → λ b → g (a , b))
{-# INLINE Π-Σ-expansion #-}

Π-Σ-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : A → UU j} {Y : Σ {i} {j} A B → UU k}
                          → isEquiv {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (Π-Σ-expansion {i} {j} {k} {A} {B} {Y})
Π-Σ-expansion-is-equiv = invertibles-are-equiv (λ g → λ a → λ b → g (a , b))
                             ((λ f → λ {(a , b) → f a b}) , (λ x → refl) , (λ x → refl))


--------------------------------------------------------------------------------
Π-×-expansion : {i j k : Level} {A : UU i} {B : UU j} {Y : _×_ {i} {j} A B → UU k}
               → (Π (A × B) Y) → (Π A (λ a → Π B λ b → Y (a , b)))
Π-×-expansion = (λ g → λ a → λ b → g (a , b))

Π-×-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : UU j} {Y : _×_ {i} {j} A B → UU k}
                          → isEquiv {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (Π-×-expansion {i} {j} {k} {A} {B} {Y})
Π-×-expansion-is-equiv = invertibles-are-equiv (λ g → λ a → λ b → g (a , b))
                             ((λ f → λ {(a , b) → f a b}) , (λ x → refl) , (λ x → refl))

-------------------------------------------------------------
Π-+-expansion : {i j k : Level} {A : UU i} {B : UU j} {Y : _+_ {i} {j} A B → UU k}
               → (Π (A + B) Y) → (Π A (λ a → Y (inl a))) × (Π B (λ b → Y (inr b)))
Π-+-expansion t = (λ x → t (inl x)) , (λ x → t (inr x))

Π-+-expansion-is-equiv :  {i j k : Level} {A : UU i} {B : UU j} {Y : A + B → UU k}
                          → isEquiv {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (Π-+-expansion {i} {j} {k} {A} {B} {Y})
Π-+-expansion-is-equiv {i} {j} {k} = invertibles-are-equiv {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} (λ t →  (λ x → t (inl x)) , (λ x → t (inr x)))
                            ((λ {(u , v) (inl x) → u x ; (u , v) (inr x) → v x}) ,
                            (λ x → funext {i ⊔ j} {k} λ {(inl x) → refl ; (inr x) → refl} ) ,
                            λ {(u , v) → pair⁼ _ _ (refl , refl)})



------------------------------------------------------------------------------
×-of-maps : {i j i' j' : Level} {A : UU i} {A' : UU i'} {B : UU j} {B' : UU j'}
            → (f : A → B) (f' : A' → B')
            → (A × A' → B × B')
×-of-maps f f' (a , a') = (f a , f' a')

×-of-maps-is-equiv : {i j i' j' : Level} {A : UU i} {A' : UU i'} {B : UU j} {B' : UU j'}{f : A → B}{f' : A' → B'}
                     → isEquiv {i} {j} f → isEquiv {i'} {j'} f' → isEquiv {i ⊔ i'} {j ⊔ j'} (×-of-maps f f')
×-of-maps-is-equiv {i} {j} {i'} {j'} {f = f} {f' = f'} P Q = let (g , gf , fg) = equivs-are-invertible {i} {j} f P
                                                                 (g' , g'f' , f'g') = equivs-are-invertible {i'} {j'} f' Q
                                                             in invertibles-are-equiv {i ⊔ i'} {j ⊔ j'} (×-of-maps f f')
                                                                 (×-of-maps g g' ,
                                                                 (λ {(a , a') → pair⁼ _ _ (gf a , g'f' a')}) ,
                                                                 (λ {(b , b') → pair⁼ _ _ (fg b , f'g' b')}))

--------------------------------------------------------------------------
--Homotopic Maps & Equivalences
htpy-equiv : {i j : Level} {A : UU i} {B : UU j}
             (f g : A → B)
             → f ~ g
             → isEquiv {i} {j} f
             → isEquiv {i} {j} g
htpy-equiv {i} {j} f g H P = let (f' , (f'f , ff')) = equivs-are-invertible {i} {j} f P
                     in  invertibles-are-equiv {i} {j} g ((λ x → f' x) ,
                                              (λ x → (ap f' (H x) ⁻¹) · f'f x) ,
                                              (λ x → (H (f' x) ⁻¹) · ff' x))

-------------------------------------------------------------------------------------------
--2-out-of-3-property
--It says that if f and g are two composable maps, then if 2 of f, g, f∘ g are equivalent, so is the third.
First-2-out-of-3-rule : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                        (f : A → B) (g : B → C)
                        → isEquiv {i} {j} f
                        → isEquiv {i} {k} (g ∘ f)
                        → isEquiv {j} {k} g
First-2-out-of-3-rule {i} {j} {k} f g P Q = let (f' , (f'f , ff')) = equivs-are-invertible {i} {j} f P
                                            in htpy-equiv {j} {k} ((g ∘ f) ∘ f') g
                                              (λ x → ap g (ff' x))
                                              (∘-is-equiv f' (g ∘ f) (inv-is-equiv {i} {j} f P) Q)

Second-2-out-of-3-rule : {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
                        (f : A → B) (g : B → C)
                        → isEquiv {j} {k} g
                        → isEquiv {i} {k} (g ∘ f)
                        → isEquiv {i} {j} f
Second-2-out-of-3-rule {i} {j} {k} f g P Q = let (g' , (g'g , gg')) = equivs-are-invertible {j} {k} g P
                                             in htpy-equiv {i} {j} (g' ∘ (g ∘ f)) f
                                                (λ x → g'g (f x))
                                                (∘-is-equiv (g ∘ f) g' Q (inv-is-equiv {j} {k} g P))

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
Com-Square {i} {j} {k} {l} f f' g g' = (a : _) → Id {l} (f' (g a)) (g' (f a))

--In this case, if three of them are equivalent, then so is the fourth.
First-3-out-of-4-rule : {i j k l : Level} {A : UU i} {A' : UU j} {B : UU k} {B' : UU l}
                        (f : A → A') (f' : B → B') (g : A → B) (g' : A' → B')
                        → Com-Square {i} {j} {k} {l} f f' g g'
                        → (isEquiv {k} {l} f') → (isEquiv {i} {k} g) → (isEquiv {j} {l} g')
                        → isEquiv {i} {j} f
First-3-out-of-4-rule  {i} {j} {k} {l} f f' g g' CS Pf' Pg Pg' = Second-2-out-of-3-rule  {i} {j} {l}
                                                                    f
                                                                    g'
                                                                    Pg'
                                                                    (htpy-equiv {i} {l}
                                                                       (f' ∘ g)
                                                                       (g' ∘ f)
                                                                        (CS)
                                                                    (∘-is-equiv g f' Pg Pf'))
