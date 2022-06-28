{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Coercion.dd where

open import Agda.Builtin.Equality public
open import Agda.Primitive public
--exo-universe of exotypes
UUᵉ : (i : Level) → SSet (lsuc i)
UUᵉ i = SSet i

--universe of types
UU : (i : Level) → Set (lsuc i)
UU i = Set i

--coercion
c : {i : Level} → UU i → UUᵉ i
c A = A

--exo(strict)equality
data _=ᵉ_ {i : Level} {A : UUᵉ i } (x : A) : A → UUᵉ i where
  reflᵉ : x =ᵉ x

--Id type
Id : {i : Level} {A : UU i} → A → A → UU i
Id {i} {A} = _≡_ {i} {A}

--map from exo-equality to id type
map-≡ : {i : Level} {A : UU i} {u v : A} → u =ᵉ v → (Id u v)
map-≡ reflᵉ = refl

--For the inverse, this works. Here we used "c (Id u v)"
imap-≡1 : {i : Level} {A : UU i} {u v : A} → c (Id u v) → u =ᵉ v
imap-≡1 refl = reflᵉ

--this does not work
imap-≡2 : {i : Level} {A : UU i} {u v : A} → (Id u v) → u =ᵉ v
imap-≡2 p = {!!}
--the error:
--Cannot eliminate fibrant type Id u v
--unless target type is also fibrant
--when checking that the pattern refl has type Id u v

----------------------------------------

--Naturals
data ℕ : UU lzero where
  zero : ℕ
  succ : ℕ → ℕ

--Exo-naturals
data ℕᵉ : UUᵉ lzero where
  zeroᵉ : ℕᵉ
  succᵉ : ℕᵉ → ℕᵉ

--I expect this is a valid map, and it works.
ℕᵉ-to-cℕ : ℕᵉ → c ℕ
ℕᵉ-to-cℕ zeroᵉ = zero
ℕᵉ-to-cℕ (succᵉ n) = succ (ℕᵉ-to-cℕ n)

--The following does not work, which is good.
ℕ-to-ℕᵉ : ℕ → ℕᵉ
ℕ-to-ℕᵉ n = {!n!}
--I'm taking the following error.
--Cannot eliminate fibrant type ℕ unless target type is also fibrant
--when checking that the expression ? has type ℕᵉ

--However, the following works. This is not someting we expected.
cℕ-to-ℕᵉ : c ℕ → ℕᵉ
cℕ-to-ℕᵉ zero = zeroᵉ
cℕ-to-ℕᵉ (succ n) = succᵉ (cℕ-to-ℕᵉ n)
