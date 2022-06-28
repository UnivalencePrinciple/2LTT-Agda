{-# OPTIONS --without-K --exact-split --two-level  --cumulativity #-}

module 2LTT.Types.Id_Type where

open import Agda.Builtin.Equality public

open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Types.Functions
open import 2LTT.Types.Sigma
open import 2LTT.Types.Pi
open import 2LTT.Primitive

--identity type for (fibrant) types
Id : {i : Level} {A : UU i} → A → A → UU i
Id {i} {A} = _≡_ {i} {A}

--exo-equality for types implies the identity type. The converse is not valid!
=ᵉ-to-Id : {i : Level} {A : UU i} {a b : A} → a =ᵉ b → Id a b
=ᵉ-to-Id reflᵉ = refl


--induction principle for the identity type
ind-Id : {i j : Level} {A : UU i} (D : (x y : A) → Id {i} x y → UU j)
         → ((x : A) → D x x refl) → ((x y : A) → (p : Id {i} x y) → D x y p )
ind-Id D f x .x refl = f x

--In keeping with Martin-Löf own notation we call this 𝕁
𝕁 =  ind-Id

infix 20 _·_
-- notation for concatenation · is "\ cdot" 
_·_ : {i : Level} {A : UU i} {x y z : A} → Id x y → Id y z → Id x z
refl · q = q

_≡⟨_⟩_ : {i : Level} {A : UU i} (x : A) {y z : A} → Id x y → Id y z → Id x z
x ≡⟨ p ⟩ q = p · q

_▮ : {i : Level} {A : UU i} (x : A) → Id x x
x ▮ = refl

infixr 30 _⁻¹
_⁻¹ : {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
refl ⁻¹ = refl

double-inv : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id ((p ⁻¹) ⁻¹) p
double-inv refl = refl

--properties of inverse path
left-inv : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id (p ⁻¹ · p) refl
left-inv refl = refl

right-inv : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id (p · p ⁻¹) refl
right-inv refl = refl

left-unit : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id (refl · p) p
left-unit refl = refl

right-unit : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id (p · refl) p
right-unit refl = refl

idempotency : {i : Level} {A : UU i} {x y : A} → (p : Id x y) → Id ((p ⁻¹) ⁻¹) p
idempotency refl = refl

--associativity
assoc : {i : Level} {A : UU i} {x y z w : A} (p : Id {i} x y) (q : Id {i} y z) (r : Id {i} z w)
        → Id ((p · q) · r) (p · (q · r))
assoc refl q r = refl

--Horizontal composition and Whiskering

infixr 30 _◾ᵣ_ _◾ₗ_ _⋆_
--right whiskering
_◾ᵣ_ : {i : Level} {A : UU i} {a b c : A} {p q : Id {i} a b}
       (α : Id  p q) (r : Id b c) → Id (p · r) (q · r)
α ◾ᵣ refl = (right-unit _) · (α · (right-unit _) ⁻¹)

--left whiskering
_◾ₗ_ : {i : Level} {A : UU i} {a b c : A} {r s : Id {i} b c}
       (q : Id a b) (β : Id r s) → Id (q · r) (q · s)
refl ◾ₗ β = (left-unit _) · (β · (left-unit _) ⁻¹)

--horizontal composition
_⋆_ : {i : Level} {A : UU i} {a b c : A} {p q : Id {i} a b} {r s : Id {i} b c}
      (α : Id p q) (β : Id r s) → Id (p · r) (q · s)
α ⋆ β = (α ◾ᵣ _) · (_ ◾ₗ β)

--Functions are functors
ap : {i j : Level} {A : UU i} {B : UU j}
     (f : A → B) {x y : A} (p : Id {i} x y) → Id {j} (f x) (f y)
ap f refl = refl

ap-concat : {i j : Level} {A : UU i} {B : UU j}
            (f : A → B) {x y z : A} (p : Id {i} x y) (q : Id {i} y z)
            → Id {j} (ap {i} {j} f (p · q)) (ap {i} {j} f p · ap {i} {j} f q)
ap-concat f refl refl = refl

ap-inverse : {i j : Level} {A : UU i} {B : UU j}
            (f : A → B) {x y : A} (p : Id {i} x y)
            → Id {j} (ap {i} {j} f (p ⁻¹)) ((ap {i} {j} f p) ⁻¹)
ap-inverse f refl = refl

ap-comp :  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
           (g : B → C) (f : A → B) {x y : A} (p : Id {i} x y)
           → Id {k} (ap {j} {k} g (ap {i} {j} f p)) (ap {i} {k} (g ∘ f) p)
ap-comp g f refl = refl

ap-id : {i : Level} {A : UU i} {x y : A} (p : Id {i} x y)
        → Id (ap (id) p) p
ap-id refl = refl
{-# INLINE ap-id #-}

--Type Families are fibrations
tr : {i j : Level} {A : UU i} (P : A → UU j) {x y : A} (p : Id x y) → P x → P y
tr P refl b = b

tr-is-retraction : {i j : Level} {A : UU i} (P : A → UU j) {a a' : A} (p : Id {i} a a') → (z : P a') → Id (tr P p (tr P (p ⁻¹) z)) z  
tr-is-retraction P refl z = refl

tr-is-section : {i j : Level} {A : UU i} (P : A → UU j) {a a' : A} (p : Id {i} a a') → (z : P a) → Id (tr P (p ⁻¹) (tr P p z)) z  
tr-is-section P refl z = refl

tr-cong : {i j : Level} {A : UU i} {P : A → UU j} {x y : A} {p q : Id {i} x y} {b : P x}
          → Id p q → Id (tr P p b) (tr P q b)
tr-cong refl = refl

--path lifting property
lift : {i j : Level} {A : UU i} {P : A → UU j} {y : A} (u : Σ {i} {j} A P) (p : Id {i} (pr1 u) y)
       → Id u (y , tr P p (pr2 u))
lift u refl = refl


apd : {i j : Level} {A : UU i} {P : A → UU j} (f : (x : A) → P x) {x y : A}
      (p : Id {i} x y) → Id {j} (tr {i} {j} P p (f x)) (f y)
apd f refl = refl


tr-concat : {i j : Level} {A : UU i} {P : A → UU j} {x y z : A} {u : P x} (p : Id {i} x y) (q : Id {i} y z)
            → Id {j} (tr {i} {j} P q (tr {i} {j} P p u)) (tr {i} {j} P (p · q) u)
tr-concat refl refl = refl

tr-comp-fam : {i j : Level} {A : UU i} {P Q : A → UU j}
              {f : (x : A) → (P x → Q x)} {x y : A} (p : Id {i} x y) (u : P x)
              → Id {j} (tr Q p (f x u)) (f y (tr P p u))
tr-comp-fam refl u = refl

tr-ap : {i j : Level} {A B : UU i} {f : A → B} {P : B → UU j} {x₁ x₂ : A} (e : Id {i} x₁ x₂) {p : P (f x₁)}
               → Id (tr (λ x → P (f x)) e p)  (tr {i} {j} P (ap f e) p)
tr-ap refl = refl


tr-fam-ap : {i j : Level} {A : UU i} {P : A → UU j} {x y : A} {p : Id {i} x y} {f g : P x → P x}{z : P x}
            → (Id f g) → Id (tr P p (f z)) (tr P p (g z))
tr-fam-ap refl = refl

--Homotopies and Equivalences

_~_ : ∀ {i j} {A : UU i} {P : A → UU j} (f g : Π A P) → UU (i ⊔ j)
_~_ {i} {j} {A} {B} f g = (x : A) → Id {j} (f x) (g x)


id-htpy : {i j : Level} {A : UU i} {P : A → UU j} (f : Π {i} {j} A P)
          → f ~ f
id-htpy f a = refl

sym-htpy : {i j : Level} {A : UU i} {P : A → UU j} (f g : Π {i} {j} A P)
           → f ~ g → g ~ f
sym-htpy f g H a = (H a) ⁻¹

trns-htpy : {i j : Level} {A : UU i} {P : A → UU j} (f g h : Π {i} {j} A P)
            → f ~ g → g ~ h → f ~ h
trns-htpy f g h H1 H2 a = (H1 a) · (H2 a)

nat-trans-htpy : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} {x y : A} 
                 (H : _~_ {i} {j} f g) (p : Id {i} x y) → Id ((H x) · (ap g p)) ((ap f p) · (H y))
nat-trans-htpy H refl = right-unit (H _)

nat-trans-htpy2 : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} {x y : A} 
                 (H : _~_ {i} {j} f g) (p : Id {i} x y) → Id (((H x) · (ap g p)) · (H y) ⁻¹) (ap f p)
nat-trans-htpy2 {i} {j} {f = f} {x = x} {y = y} H p = ap {j} {j} (λ s → s · (H y ⁻¹)) (nat-trans-htpy H p)
                                                  · (assoc (ap {i} {j} f p) (H y) (H y ⁻¹)
                                                  · (ap (λ s → (ap f p) · s) (right-inv (H y))
                                                  · right-unit (ap {i} {j} f p)) )

nat-trans-htpy-to-id : {i : Level} {A : UU i} (f : A → A) (x : A)
                 (H : _~_ {i} {i} f id) → Id (H (f x)) (ap f (H x))
nat-trans-htpy-to-id {i} {A} f x H = ((((right-unit (H (f x)) ⁻¹ ) ·
                                     ap (λ q → (H (f x)) · q) (right-inv (H x) ⁻¹)) ·
                                     ap {i} (λ q → H (f x) · q) (ap (λ q → q · (H x ⁻¹)) (ap-id {i} {A} {f x} {x} (H x))) ⁻¹) ·
                                     assoc (H (f x)) (ap (λ z → id z) (H x)) (H x ⁻¹) ⁻¹) ·
                                               (nat-trans-htpy {i} {i} H (H x) ◾ᵣ ((H x) ⁻¹) ·
                                     (assoc (ap {i} {i} f (H x)) (H x) (H x ⁻¹) ·
                                     (ap {i} {i} (λ q → (ap {i} {i} f (H x)) · q) (right-inv (H x)) ·
                                     right-unit (ap f (H x)))))

-----------------------------------------
--IDENTITY TYPES FOR CARTESIAN PRODUCTS
pair-Id : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
              → UU (i ⊔ j)
pair-Id x y = Id (pr1 x) (pr1 y) × Id (pr2 x) (pr2 y)

pair⁼ : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
                    → (pair-Id x y) → Id x y 
pair⁼ (a , b) (.(pr1 (a , b)) , .(pr2 (a , b))) (refl , refl) = refl

inv-pair⁼ : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
                    → Id x y → (pair-Id x y)
inv-pair⁼ x .x refl = refl , refl

htpy-inv-pair⁼-pair⁼ : {i j : Level} {A : UU i} {B : UU j} (x y : A × B)
                      → (b : pair-Id x y) → Id (inv-pair⁼ x y (pair⁼ x y b)) b
htpy-inv-pair⁼-pair⁼ (a , b) (.(pr1 (a , b)) , .(pr2 (a , b))) (refl , refl) = refl

htpy-pair⁼-inv-pair⁼ : {i j : Level} {A : UU i} {B : UU j} (x y : _×_ {i} {j} A B)
                      → (p : Id x y) → Id (pair⁼ x y (inv-pair⁼ x y p)) p
htpy-pair⁼-inv-pair⁼  (a , b) (.(pr1 (a , b)) , .(pr2 (a , b))) refl = refl

--IDENTITY TYPES FOR Σ-TYPES
dep-pair-Id : {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
              → UU (i ⊔ j)
dep-pair-Id {i} {j} {A} {B} w w' = Σ {i} {j} (Id {i} (pr1 w) (pr1 w')) (λ p → Id {j} {B (pr1 w')} (tr B p (pr2 w)) (pr2 w'))

dep-pair⁼ :  {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
             → (dep-pair-Id w w') → Id w w'
dep-pair⁼ (a , b) (.a , .b) (refl , refl) = refl


inv-dep-pair⁼ : {i j : Level} {A : UU i} {B : A → UU j} (w w' : Σ A B)
                    → Id w w' → (dep-pair-Id w w')
inv-dep-pair⁼ (a , b) (.a , .b) refl = refl , refl

htpy-inv-dep-pair⁼-dep-pair⁼ : {i j : Level} {A : UU i} {B : A → UU j} (x y : Σ A B)
                      → (b : dep-pair-Id x y) → Id (inv-dep-pair⁼ x y (dep-pair⁼ x y b)) b
htpy-inv-dep-pair⁼-dep-pair⁼ (a , b) (.a , .b) (refl , refl) = refl

htpy-dep-pair⁼-inv-dep-pair⁼ : {i j : Level} {A : UU i} {B : A → UU j} (x y : Σ {i} {j} A B)
                      → (p : Id x y) → Id (dep-pair⁼ x y (inv-dep-pair⁼ x y p)) p
htpy-dep-pair⁼-inv-dep-pair⁼  (a , b) (.a , .b) refl = refl

--Function extensionality
happly : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
       → Id f g → (f ~ g) 
happly refl x = refl

--We have not defined isEquiv or is-contr. So we are using their expansions because we want that funext is inverse of happly.
postulate
 FUNEXT : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
         → (Π {i ⊔ j} {i ⊔ j} (_~_ {i} {j} f g) (λ H → let T = (Σ {i ⊔ j} {i ⊔ j} (Id {i ⊔ j} f g)
                                                                    (λ p → Id (happly p) H))
                                                         in Σ T (λ a → ((x : T) →  Id {i ⊔ j} x a)))) 

funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
       → (f ~ g) → Id f g 
funext H = pr1 (pr1 (FUNEXT H))


