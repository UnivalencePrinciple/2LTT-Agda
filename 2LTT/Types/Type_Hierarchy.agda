{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Types.Type_Hierarchy where

open import 2LTT.Types.Functions
open import 2LTT.Types.Id_Type
open import 2LTT.Types.Sigma
open import 2LTT.Types.Pi
open import 2LTT.Primitive
open import 2LTT.Types.Unit
open import 2LTT.Types.Empty

--Stratification of Types
data ๐ : UU lzero where
  neg-two-๐ : ๐
  succ-๐ : ๐ โ ๐

neg-one-๐ = succ-๐ neg-two-๐

zero-๐ = succ-๐ neg-one-๐

one-๐ = succ-๐ zero-๐

is-contr : {i : Level} (A : UU i) โ UU i
is-contr {i} A = ฮฃ A (ฮป a โ ((x : A) โ  Id {i} x a))

center : {i : Level} (A : UU i) โ is-contr A โ A
center A (a , p) = a

centrality : {i : Level} (A : UU i) (P : is-contr {i} A) (x : A) โ Id x (center A P)
centrality A (a , p) x = p x

path-type : {i : Level} {A : UU i} (b : A) โ UU i
path-type b = ฮฃ _ (ฮป a โ Id a b)

path-type-is-contr : {i : Level} {A : UU i} (b : A)
                     โ is-contr (path-type b)
path-type-is-contr b = (b , refl) , (ฮป {(a , refl) โ refl})

is-type : {i : Level} (t : ๐) โ (A : UU i) โ UU i
is-type neg-two-๐ A = is-contr A
is-type {i} (succ-๐ t) A = (a' : A) โ (a : A) โ is-type {i} t (Id a' a)

is-prop : {i : Level} (A : UU i) โ UU i
is-prop A = is-type neg-one-๐ A

is-set : {i : Level} (A : UU i) โ UU i
is-set A = is-type zero-๐ A

is-prop-is-contr : {i : Level}(A : UU i) โ is-contr A โ is-prop A
is-prop-is-contr A (a , P) = ฮป x โ ฮป y โ ((P x ยท (P y) โปยน) , ฮป {refl โ right-inv (P x) โปยน})

type-hrchy : {i : Level}(A : UU i) โ (n : ๐) โ is-type n A โ is-type (succ-๐ n) A
type-hrchy A neg-two-๐ W = is-prop-is-contr A W
type-hrchy A (succ-๐ n) W = ฮป a โ ฮป b โ type-hrchy (Id a b) n (W a b)

--is-prop means all elements is equal. (The idea is by Egbert Rijke's book.)
all-elements-equal : {i : Level} โ UU i โ UU i
all-elements-equal {i} A = (x y : A) โ (Id {i} x y)

is-proof-irrelevant : {i : Level} โ UU i โ UU i
is-proof-irrelevant A = A โ is-contr A

all-elements-equal-is-prop : {i : Level} {A : UU i} โ is-prop A โ all-elements-equal A
all-elements-equal-is-prop H = ฮป x โ ฮป y โ pr1 (H x y)

is-proof-irrelevant-all-elements-equal : {i : Level}{A : UU i} โ all-elements-equal A โ is-proof-irrelevant A
is-proof-irrelevant-all-elements-equal H = ฮป a โ (a , (ฮป x โ H x a))

is-prop-is-proof-irrelevant : {i : Level}{A : UU i} โ is-proof-irrelevant A โ is-prop A
is-prop-is-proof-irrelevant H = ฮป x โ ฮป y โ (((pr2 (H x)) x ยท (pr2 (H x) y) โปยน ) , (ฮป {refl โ (right-inv (pr2 (H x) x)) โปยน}))

is-prop-all-elements-equal : {i : Level} {A : UU i} โ all-elements-equal A โ is-prop A
is-prop-all-elements-equal = is-prop-is-proof-irrelevant โ is-proof-irrelevant-all-elements-equal
-------------------------

is-set-is-prop : {i : Level}(A : UU i) โ is-prop A โ is-set A
is-set-is-prop A = type-hrchy A neg-one-๐

is-set-is-contr : {i : Level}(A : UU i) โ is-contr A โ is-set A
is-set-is-contr {i} A = (is-set-is-prop {i} A) โ (is-prop-is-contr A)

is-set-to-all-paths-equal : {i : Level} (A : UU i) โ is-set A โ (a b : A) โ (p q : Id a b) โ Id p q
is-set-to-all-paths-equal A W a b p q = all-elements-equal-is-prop (W a b) p q

ฮ?-type-contr : {i j : Level} {A : UU i} {B : A โ UU j} โ
              ((a : A) โ is-contr (B a)) โ is-contr (ฮ? A B)
ฮ?-type-contr F = ((ฮป a โ pr1 (F a))) , ฮป f โ funext ฮป a โ (pr2 (F a)) (f a) 

ฮ?-type-prop : {i j : Level} {A : UU i} {B : A โ UU j} โ
              ((a : A) โ is-prop (B a)) โ is-prop (ฮ? A B)
ฮ?-type-prop F = is-prop-all-elements-equal (ฮป f โ ฮป g โ  funext (ฮป x โ pr1 ((F x) (f x) (g x))) )

is-prop-contr :  {i : Level}(A : UU i) โ is-prop (is-contr A) 
is-prop-contr {i} A = is-prop-all-elements-equal ฮป {(a , p) โ ฮป {(a' , p')
                                                 โ dep-pairโผ {i} {i} {A = A} {B = ฮป a โ (ฮ? A (ฮป x โ Id {i} x a))} (a , p) (a' , p') 
                                                   (p' a ,  
                                                   all-elements-equal-is-prop {i} 
                                                    (ฮ?-type-prop ฮป a'' โ (is-set-is-contr {i} A (a , p)) a'' a')
                                                    (tr (ฮป aโ โ ฮ? A (ฮป x โ Id x aโ)) (p' a) p) p')}}
                                                   --Here, we've applied exactly the same method in the proof of Lemma 3.11.4 in HoTT Book


ร-contr-is-contr : {i j : Level} {A : UU i} {B : UU j}
                   โ is-contr A โ is-contr B
                  โ is-contr (A ร B)
ร-contr-is-contr (a , P) (b , Q) = (a , b) , ฮป {(a' , b') โ pairโผ (a' , b') (a , b) ((P a') , Q b')}



ฮ?-over-โฅ-is-contr : {i : Level} {Y : โฅ โ UU i} โ is-contr (ฮ? โฅ Y)
ฮ?-over-โฅ-is-contr = ind-โฅ , (ฮป x โ funext (ฮป xโ โ ex-falso xโ))
