# 2LTT-Agda

This library is an experiment about some new features of Agda that allows us work with two level type theory. We are mainly formalizing the content of the [Univalence Principle](https://arxiv.org/abs/2102.06275) (UP) paper, but the second chapter of the paper is about two level type theory ([2LTT](https://arxiv.org/abs/1705.03307)), and the rest of the paper makes use of it. Thus, the library also contains the basics of 2LTT.

---
The flag `--two-level` enables a new sort called `SSet`. This provides two distinct universes for us. One stands for the universe of types (like in HoTT), the other stands for the universe of types with strict equalities. In 2LTT, these are called the universe of inner types and the universe of outer types, respectively. In UP, these are called the universe of of types and the exo-universe of exo-types, respectively. We are using the second version. According to Voevodsky’s approach in his [Homotopy Type System](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf) (HTS), types are regarded as fibrant types, but exo-types are not necessarily fibrant. The following [Agda code](https://github.com/UnivalencePrinciple/2LTT-Agda/blob/main/2LTT/Primitive.agda) formalizes these two (polymophic) universes. 

```agda
{-# OPTIONS --two-level #-}

open import Agda.Primitive public

--exo-universe of exotypes
UUᵉ : (i : Level) → SSet (lsuc i)
UUᵉ i = SSet i

--universe of types
UU : (i : Level) → Set (lsuc i)
UU i = Set i
```
---
In the folders `Types` and `Exotypes`, we defined the basic type and exo-type formers. 

In the folder `Type`, we also defined equivalences of types and proved some functoriality properties. In the file `Retraction`, we took the formulas from Martin Escardo's [notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/). Also, we defined the type hierarchy for future needs. In the folder `Exotype`, we defined isomorphism of exo-types which is the analogue of equivalence for types. Whenever it is needed, we make distinction between them using the superscript `-ᵉ`.

---
As for the relation between types and exo-types, while 2LTT assumes ”one can convert a type into an exo-type” via an additional conversion operation,
the other work UP assumes directly that every type is an exo-type, but not vice-versa. To formalize this principle, Agda has another new flag, which
is `--cumulativity`. This enables the subtyping rule `Set i ≤ SSet i` for any level `i`. Thanks to the flag we can take types as arguments for the oper-
ations/formations which are originally defined for exo-types. The following Agda codes illustrate this idea. If we take an exo-type `Aᵉ` , a type `A`, two families of exo-types `Bᵉ : Aᵉ → Uᵉ` and `C : A → Uᵉ` , and two families of types `B : A → U` and `Cᵉ : Aᵉ → U`, each one gives a suitable sigma type or sigma exo-type. Note that even with the cumulativity, we cannot evaluate a type former at exo-types.

```agda
{-# OPTIONS --without-K --two-level --cumulativity #-}

--Type former of dependent pairs for exotypes
record Σᵉ {i j : Level} (A : UUᵉ i) (B : A → UUᵉ j) : UUᵉ (i ⊔ j) where
  constructor _,ᵉ_
  field
    pr1ᵉ : A
    pr2ᵉ : B pr1ᵉ
    
--Type former of dependent pairs for types
record Σ {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  constructor _,_
  field
    pr1 : A
    pr2 : B pr1

module _
  {i : Level}
  {Aᵉ : UUᵉ i} {Bᵉ : Aᵉ → UUᵉ i} {A : UU i} {B : A → UU i} {Cᵉ : Aᵉ → UU i} {C : A  → UUᵉ i}
  where

--These two are usual.
Type-1 = Σᵉ Aᵉ Bᵉ
Type-2 = Σ A B
--These three are valid only when --cumulativity assumed.
Type-3 = Σᵉ A B
Type-4 = Σᵉ A C
Type-5 = Σᵉ Aᵉ Cᵉ
--This is by no means valid.
!!!Type-6 = Σ Aᵉ Bᵉ
```
---
In the folder `Coercion`, we formalized the relation between types and exo-types. The file `C` contains the proof of Lemma 2.11 in 2LTT paper. We defined type conversion `C` and term conversion `c`, but there is no need to use in the formalization because `--cumulativity` does this job invisibly. However, the flag causes other results that we don't want to get. For example, using a lifting operation `L : U → Uᵉ` as `L(A) = A`, one can show that
`L(A + B)` and `L(A) +ᵉ L(B)` are exo-isomorphic, which is not assumed in both 2LTT and UP. The related issues are [#5948](https://github.com/agda/agda/issues/5948) and [#5761](https://github.com/agda/agda/issues/5761). Although Axiom A6 in 2LTT paper discusses the possibility of taking such isomorphisms, the most problematic case would be the exo-isomorphism between [exo-equality](https://github.com/UnivalencePrinciple/2LTT-Agda/blob/main/2LTT/Exotypes/Exo_Equality.agda) and [identity type](https://github.com/UnivalencePrinciple/2LTT-Agda/blob/main/2LTT/Types/Id_Type.agda) because this would break the complete motivation for 2LTT. Currently, Agda does not allow such a thing thanks to an update about type checking. 

The file `Fibrant_Conversion` formalizes another notion. We say an exo-type is fibrant if it is exo-isomorphic to a type. We proved many useful properties about fibrant exo-types. Especially, the file `Fibrant_Equivalences` is quite useful for the rest of the library. We say two fibrant exo-types are equivalent, if so are their fibrant matches. Moreover, we showed that exo-unit type is fibrant and that `Σᵉ` and `Πᵉ` preserve being a fibrant exo-type. 

---
In the folder `Cofibration` we formalized cofibrant exo-types and some of their properties. An exo-type `A` is cofibrant if for any families of types `B : A → U` we have `Πᵉ A B` is fibrant, and when `B(a)` is contractible for each `a : A`, so is `Πᵉ A B`. We showed that all fibrant types are cofibrant, 
exo-unit is cofibrant, and that if `A` and `B` are cofibrant so are `A +ᵉ B` and `A ×ᵉ B`. Also we showed that if `A` is cofibrant and `B : A → Uᵉ`
is such that each `B(a)` is cofibrant, then `Σᵉ A B` is cofibrant.

---
In the folder `Sharpness`, we formalized sharp exo-types and some of their properties. An exo-type `A` is sharp if it is cofibrant and has a fibrant replacement which is a type `RA` such that there is a map `n : A → RA` and for any families `Y` of types over `RA`, the precomposition map `Π RA Y  → Πᵉ A (Y∘ᵉn)` is a fibrant equivalence. We also formalized Lemma 2.3 in UP.

---
In the folder `Diagram_Signatures`, we've started to formalize Chapter 4 of UP. It's in progress, but we have basic definitions and examples.

---
For questions and suggestions, please write to euskuplu@usc.edu
