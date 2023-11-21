{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Coproduct where

open import 2LTT_C.Primitive


---------------------------------------------------
--Type formers of coproducts for types
data _+_ {l1 l2 : Level}(A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → A + B
  inr : B → A + B


--induction principle for coproducts
ind-+ : {i j k : Level} {A : UU i} {B : UU j} (C : _+_ {i} {j} A B → UU k)
              → ((x : A) → C (inl x)) → ((y : B) → C (inr y))
              → (t : A + B) → C t
ind-+ C f g (inl x) = f x
ind-+ C f g (inr x) = g x

inr-fmly : {i j k : Level} {A : UU i} {B : UU j} (C : A + B → UU k)
           → (B → UU k)
inr-fmly C = λ b → C (inr b)

inl-fmly : {i j k : Level} {A : UU i} {B : UU j} (C : A + B → UU k)
           → (A → UU k)
inl-fmly C = λ a → C (inl a)

--------------------------------------------------------

