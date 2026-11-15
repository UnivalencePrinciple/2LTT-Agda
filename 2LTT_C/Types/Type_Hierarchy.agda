{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Type_Hierarchy where

open import 2LTT_C.Types.Functions
open import 2LTT_C.Types.Id_Type
open import 2LTT_C.Types.Sigma
open import 2LTT_C.Types.Pi
open import 2LTT_C.Primitive
open import 2LTT_C.Types.Unit
open import 2LTT_C.Types.Empty

--Stratification of Types
data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 = succ-𝕋 neg-two-𝕋

zero-𝕋 = succ-𝕋 neg-one-𝕋

one-𝕋 = succ-𝕋 zero-𝕋

is-contr : {i : Level} (A : UU i) → UU i
is-contr {i} A = Σ A (λ a → ((x : A) →  Id {i} x a))

center : {i : Level} (A : UU i) → is-contr A → A
center A (a , p) = a

centrality : {i : Level} (A : UU i) (P : is-contr {i} A) (x : A) → Id x (center A P)
centrality A (a , p) x = p x

path-type : {i : Level} {A : UU i} (b : A) → UU i
path-type b = Σ _ (λ a → Id a b)

path-type-is-contr : {i : Level} {A : UU i} (b : A)
                     → is-contr (path-type b)
path-type-is-contr b = (b , refl) , (λ {(a , refl) → refl})

is-type : {i : Level} (t : 𝕋) → (A : UU i) → UU i
is-type neg-two-𝕋 A = is-contr A
is-type {i} (succ-𝕋 t) A = (a' : A) → (a : A) → is-type {i} t (Id a' a)

is-prop : {i : Level} (A : UU i) → UU i
is-prop A = is-type neg-one-𝕋 A

is-set : {i : Level} (A : UU i) → UU i
is-set A = is-type zero-𝕋 A

is-prop-is-contr : {i : Level}(A : UU i) → is-contr A → is-prop A
is-prop-is-contr A (a , P) = λ x → λ y → ((P x · (P y) ⁻¹) , λ {refl → right-inv (P x) ⁻¹})

type-hrchy : {i : Level}(A : UU i) → (n : 𝕋) → is-type n A → is-type (succ-𝕋 n) A
type-hrchy A neg-two-𝕋 W = is-prop-is-contr A W
type-hrchy A (succ-𝕋 n) W = λ a → λ b → type-hrchy (Id a b) n (W a b)

--is-prop means all elements is equal. (The idea is by Egbert Rijke's book.)
all-elements-equal : {i : Level} → UU i → UU i
all-elements-equal {i} A = (x y : A) → (Id {i} x y)

is-proof-irrelevant : {i : Level} → UU i → UU i
is-proof-irrelevant A = A → is-contr A

all-elements-equal-is-prop : {i : Level} {A : UU i} → is-prop A → all-elements-equal A
all-elements-equal-is-prop H = λ x → λ y → pr1 (H x y)

is-proof-irrelevant-all-elements-equal : {i : Level}{A : UU i} → all-elements-equal A → is-proof-irrelevant A
is-proof-irrelevant-all-elements-equal H = λ a → (a , (λ x → H x a))

is-prop-is-proof-irrelevant : {i : Level}{A : UU i} → is-proof-irrelevant A → is-prop A
is-prop-is-proof-irrelevant H = λ x → λ y → (((pr2 (H x)) x · (pr2 (H x) y) ⁻¹ ) , (λ {refl → (right-inv (pr2 (H x) x)) ⁻¹}))

is-prop-all-elements-equal : {i : Level} {A : UU i} → all-elements-equal A → is-prop A
is-prop-all-elements-equal = is-prop-is-proof-irrelevant ∘ is-proof-irrelevant-all-elements-equal
-------------------------

is-set-is-prop : {i : Level}(A : UU i) → is-prop A → is-set A
is-set-is-prop A = type-hrchy A neg-one-𝕋

is-set-is-contr : {i : Level}(A : UU i) → is-contr A → is-set A
is-set-is-contr {i} A = (is-set-is-prop {i} A) ∘ (is-prop-is-contr A)

is-set-to-all-paths-equal : {i : Level} (A : UU i) → is-set A → (a b : A) → (p q : Id a b) → Id p q
is-set-to-all-paths-equal A W a b p q = all-elements-equal-is-prop (W a b) p q

Π-type-contr : {i j : Level} {A : UU i} {B : A → UU j} →
              ((a : A) → is-contr (B a)) → is-contr (Π A B)
Π-type-contr F = ((λ a → pr1 (F a))) , λ f → funext λ a → (pr2 (F a)) (f a)

Π-type-prop : {i j : Level} {A : UU i} {B : A → UU j} →
              ((a : A) → is-prop (B a)) → is-prop (Π A B)
Π-type-prop F = is-prop-all-elements-equal (λ f → λ g →  funext (λ x → pr1 ((F x) (f x) (g x))) )

is-prop-contr :  {i : Level}(A : UU i) → is-prop (is-contr A)
is-prop-contr {i} A = is-prop-all-elements-equal λ {(a , p) → λ {(a' , p')
                                                 → dep-pair⁼ {i} {i} {A = A} {B = λ a → (Π A (λ x → Id {i} x a))} (a , p) (a' , p')
                                                   (p' a ,
                                                   all-elements-equal-is-prop {i}
                                                    (Π-type-prop λ a'' → (is-set-is-contr {i} A (a , p)) a'' a')
                                                    (tr (λ a₁ → Π A (λ x → Id x a₁)) (p' a) p) p')}}
                                                   --Here, we've applied exactly the same method in the proof of Lemma 3.11.4 in HoTT Book


×-contr-is-contr : {i j : Level} {A : UU i} {B : UU j}
                   → is-contr A → is-contr B
                  → is-contr (A × B)
×-contr-is-contr (a , P) (b , Q) = (a , b) , λ {(a' , b') → pair⁼ (a' , b') (a , b) ((P a') , Q b')}

Σ-is-contr : {l l' : Level} {A : UU l} {B : A → UU l'}
              → is-contr A → ((a : A) → is-contr (B a)) → is-contr (Σ A B)
Σ-is-contr (a , ha) cB =
  (a , (center _ (cB a))) , λ {(a' , b') → dep-pair⁼ _ _ ((ha a') , (centrality _ (cB a) (tr _ (ha a') b')))}



Π-over-⊥-is-contr : {i : Level} {Y : ⊥ → UU i} → is-contr (Π ⊥ Y)
Π-over-⊥-is-contr = ind-⊥ , (λ x → funext (λ x₁ → ex-falso x₁))
