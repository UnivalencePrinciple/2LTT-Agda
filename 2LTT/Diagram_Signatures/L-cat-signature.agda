{-# OPTIONS --without-K --exact-split --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.L-cat-signature where

open import 2LTT.Diagram_Signatures.Definition public


--Objects for L-cat
data L-cat-Obj : UUᵉ lzero where
   O : L-cat-Obj
   A : L-cat-Obj
   I : L-cat-Obj
   T : L-cat-Obj

--Arrows for L-cat
data L-cat-Hom : L-cat-Obj → L-cat-Obj → UUᵉ lzero where
   dom : L-cat-Hom A O
   codom : L-cat-Hom A O
   id-arrow : L-cat-Hom I A
   id-arrow' : L-cat-Hom I O
   tri-0 : L-cat-Hom T A
   tri-1 : L-cat-Hom T A
   tri-2 : L-cat-Hom T A
   tri-0' : L-cat-Hom T O
   tri-1' : L-cat-Hom T O
   tri-2' : L-cat-Hom T O
   1-O : L-cat-Hom O O
   1-A : L-cat-Hom A A
   1-I : L-cat-Hom I I
   1-T : L-cat-Hom T T
  
--Id-Homs
Id-Hom-L-cat : (a : L-cat-Obj) → L-cat-Hom a a
Id-Hom-L-cat O = 1-O
Id-Hom-L-cat A = 1-A
Id-Hom-L-cat I = 1-I
Id-Hom-L-cat T = 1-T

------------------------------------
--Composition
L-cat-Comp : {a b c : L-cat-Obj}
             → L-cat-Hom b c → L-cat-Hom a b → L-cat-Hom a c
L-cat-Comp dom id-arrow = id-arrow'
L-cat-Comp dom tri-0 = tri-1'
L-cat-Comp dom tri-1 = tri-0'
L-cat-Comp dom tri-2 = tri-1'
L-cat-Comp dom 1-A = dom
L-cat-Comp codom id-arrow = id-arrow'
L-cat-Comp codom tri-0 = tri-0'
L-cat-Comp codom tri-1 = tri-2'
L-cat-Comp codom tri-2 = tri-2'
L-cat-Comp codom 1-A = codom
L-cat-Comp id-arrow 1-I = id-arrow
L-cat-Comp id-arrow' 1-I = id-arrow'
L-cat-Comp tri-0 1-T = tri-0
L-cat-Comp tri-1 1-T = tri-1
L-cat-Comp tri-2 1-T = tri-2
L-cat-Comp tri-0' 1-T = tri-0'
L-cat-Comp tri-1' 1-T = tri-1'
L-cat-Comp tri-2' 1-T = tri-2'
L-cat-Comp 1-O f = f
L-cat-Comp 1-A f = f
L-cat-Comp 1-I f = f
L-cat-Comp 1-T f = f

--Associativity
L-cat-Assoc : {a b c d : L-cat-Obj} (h : L-cat-Hom c d) (g : L-cat-Hom b c) (f : L-cat-Hom a b) →
              L-cat-Comp h (L-cat-Comp g f) =ᵉ L-cat-Comp (L-cat-Comp h g) f
L-cat-Assoc dom id-arrow 1-I = reflᵉ
L-cat-Assoc dom tri-0 1-T = reflᵉ
L-cat-Assoc dom tri-1 1-T = reflᵉ
L-cat-Assoc dom tri-2 1-T = reflᵉ
L-cat-Assoc dom 1-A f = reflᵉ
L-cat-Assoc codom id-arrow 1-I = reflᵉ
L-cat-Assoc codom tri-0 1-T = reflᵉ
L-cat-Assoc codom tri-1 1-T = reflᵉ
L-cat-Assoc codom tri-2 1-T = reflᵉ
L-cat-Assoc codom 1-A f = reflᵉ
L-cat-Assoc id-arrow 1-I f = reflᵉ
L-cat-Assoc id-arrow' 1-I f = reflᵉ
L-cat-Assoc tri-0 1-T f = reflᵉ
L-cat-Assoc tri-1 1-T f = reflᵉ
L-cat-Assoc tri-2 1-T f = reflᵉ
L-cat-Assoc tri-0' 1-T f = reflᵉ
L-cat-Assoc tri-1' 1-T f = reflᵉ
L-cat-Assoc tri-2' 1-T f = reflᵉ
L-cat-Assoc 1-O g f = reflᵉ
L-cat-Assoc 1-A g f = reflᵉ
L-cat-Assoc 1-I g f = reflᵉ
L-cat-Assoc 1-T g f = reflᵉ


---Left/Right Identity Rules
L-cat-Left-Id-rule : {a b : L-cat-Obj} (f : L-cat-Hom a b) → L-cat-Comp (Id-Hom-L-cat b) f =ᵉ f
L-cat-Left-Id-rule dom = reflᵉ
L-cat-Left-Id-rule codom = reflᵉ
L-cat-Left-Id-rule id-arrow = reflᵉ
L-cat-Left-Id-rule id-arrow' = reflᵉ
L-cat-Left-Id-rule tri-0 = reflᵉ
L-cat-Left-Id-rule tri-1 = reflᵉ
L-cat-Left-Id-rule tri-2 = reflᵉ
L-cat-Left-Id-rule tri-0' = reflᵉ
L-cat-Left-Id-rule tri-1' = reflᵉ
L-cat-Left-Id-rule tri-2' = reflᵉ
L-cat-Left-Id-rule 1-O = reflᵉ
L-cat-Left-Id-rule 1-A = reflᵉ
L-cat-Left-Id-rule 1-I = reflᵉ
L-cat-Left-Id-rule 1-T = reflᵉ


L-cat-Right-Id-rule : {a b : L-cat-Obj} (f : L-cat-Hom a b) → L-cat-Comp f (Id-Hom-L-cat a) =ᵉ f
L-cat-Right-Id-rule dom = reflᵉ
L-cat-Right-Id-rule codom = reflᵉ
L-cat-Right-Id-rule id-arrow = reflᵉ
L-cat-Right-Id-rule id-arrow' = reflᵉ
L-cat-Right-Id-rule tri-0 = reflᵉ
L-cat-Right-Id-rule tri-1 = reflᵉ
L-cat-Right-Id-rule tri-2 = reflᵉ
L-cat-Right-Id-rule tri-0' = reflᵉ
L-cat-Right-Id-rule tri-1' = reflᵉ
L-cat-Right-Id-rule tri-2' = reflᵉ
L-cat-Right-Id-rule 1-O = reflᵉ
L-cat-Right-Id-rule 1-A = reflᵉ
L-cat-Right-Id-rule 1-I = reflᵉ
L-cat-Right-Id-rule 1-T = reflᵉ


------------------------------------------------------------------
-----L-cat is an exo-category.
L-cat-is-Exo-cat : Exo-cat lzero lzero
Exo-cat.Object L-cat-is-Exo-cat = L-cat-Obj
Exo-cat.Hom L-cat-is-Exo-cat = L-cat-Hom
Exo-cat.Comp L-cat-is-Exo-cat = L-cat-Comp 
Exo-cat.Assoc L-cat-is-Exo-cat = L-cat-Assoc 
Exo-cat.Id-hom L-cat-is-Exo-cat = Id-Hom-L-cat
Exo-cat.Id-left-coh L-cat-is-Exo-cat = L-cat-Left-Id-rule
Exo-cat.Id-right-coh L-cat-is-Exo-cat = L-cat-Right-Id-rule


-------------------------------------------------------------------
---There is an exo-functor from L-cat to (ℕᵉ)ᵒᵖ
Exo-functor-L-cat-to-op-ℕᵉ-cat : Exo-Functor L-cat-is-Exo-cat op-ℕᵉ-cat
Exo-functor-L-cat-to-op-ℕᵉ-cat = obj-map ,ᵉ arrow-map ,ᵉ id-hom-rule ,ᵉ comp-hom-rule
  where
  obj-map : Objᵉ L-cat-is-Exo-cat → Objᵉ op-ℕᵉ-cat
  obj-map O = zeroᵉ
  obj-map A = oneᵉ
  obj-map I = twoᵉ
  obj-map T = twoᵉ

  arrow-map : {a b : Objᵉ L-cat-is-Exo-cat} → L-cat-is-Exo-cat [ a , b ] → op-ℕᵉ-cat [ obj-map a , obj-map b ]
  arrow-map dom = (oneᵉ ,ᵉ reflᵉ)
  arrow-map codom = (oneᵉ ,ᵉ reflᵉ)
  arrow-map id-arrow = (oneᵉ ,ᵉ reflᵉ)
  arrow-map id-arrow' = (twoᵉ ,ᵉ reflᵉ)
  arrow-map tri-0 = (oneᵉ ,ᵉ reflᵉ)
  arrow-map tri-1 = (oneᵉ ,ᵉ reflᵉ)
  arrow-map tri-2 = (oneᵉ ,ᵉ reflᵉ)
  arrow-map tri-0' = (twoᵉ ,ᵉ reflᵉ)
  arrow-map tri-1' = (twoᵉ ,ᵉ reflᵉ)
  arrow-map tri-2' = (twoᵉ ,ᵉ reflᵉ)
  arrow-map 1-O = (zeroᵉ ,ᵉ reflᵉ)
  arrow-map 1-A = (zeroᵉ ,ᵉ reflᵉ)
  arrow-map 1-I = (zeroᵉ ,ᵉ reflᵉ)
  arrow-map 1-T = (zeroᵉ ,ᵉ reflᵉ)

  id-hom-rule :  {a : Objᵉ L-cat-is-Exo-cat} → arrow-map (Id-Exo-cat L-cat-is-Exo-cat a) =ᵉ Id-Exo-cat op-ℕᵉ-cat (obj-map a)
  id-hom-rule {O} = reflᵉ
  id-hom-rule {A} = reflᵉ
  id-hom-rule {I} = reflᵉ
  id-hom-rule {T} = reflᵉ

  comp-hom-rule : {a b c : Objᵉ L-cat-is-Exo-cat} {g : L-cat-is-Exo-cat [ b , c ]} {f : L-cat-is-Exo-cat [ a , b ]}
                   → arrow-map {a} {c} (comp-Exo-cat {lzero} {lzero} L-cat-is-Exo-cat {a} {b} {c} g f)
                            =ᵉ comp-Exo-cat {lzero} {lzero} op-ℕᵉ-cat (arrow-map {b} {c} g) (arrow-map {a} {b} f)
  comp-hom-rule {g = dom} {f = id-arrow} = reflᵉ
  comp-hom-rule {g = dom} {f = tri-0} = reflᵉ
  comp-hom-rule {g = dom} {f = tri-1} = reflᵉ
  comp-hom-rule {g = dom} {f = tri-2} = reflᵉ
  comp-hom-rule {g = dom} {f = 1-A} = reflᵉ
  comp-hom-rule {g = codom} {f = id-arrow} = reflᵉ
  comp-hom-rule {g = codom} {f = tri-0} = reflᵉ
  comp-hom-rule {g = codom} {f = tri-1} = reflᵉ
  comp-hom-rule {g = codom} {f = tri-2} = reflᵉ
  comp-hom-rule {g = codom} {f = 1-A} = reflᵉ
  comp-hom-rule {g = id-arrow} {f = 1-I} = reflᵉ
  comp-hom-rule {g = id-arrow'} {f = 1-I} = reflᵉ
  comp-hom-rule {g = tri-0} {f = 1-T} = reflᵉ
  comp-hom-rule {g = tri-1} {f = 1-T} = reflᵉ
  comp-hom-rule {g = tri-2} {f = 1-T} = reflᵉ
  comp-hom-rule {g = tri-0'} {f = 1-T} = reflᵉ
  comp-hom-rule {g = tri-1'} {f = 1-T} = reflᵉ
  comp-hom-rule {g = tri-2'} {f = 1-T} = reflᵉ
  comp-hom-rule {g = 1-O} {f = dom} = reflᵉ
  comp-hom-rule {g = 1-O} {f = codom} = reflᵉ
  comp-hom-rule {g = 1-O} {f = id-arrow'} = reflᵉ
  comp-hom-rule {g = 1-O} {f = tri-0'} = reflᵉ
  comp-hom-rule {g = 1-O} {f = tri-1'} = reflᵉ
  comp-hom-rule {g = 1-O} {f = tri-2'} = reflᵉ
  comp-hom-rule {g = 1-O} {f = 1-O} = reflᵉ
  comp-hom-rule {g = 1-A} {f = id-arrow} = reflᵉ
  comp-hom-rule {g = 1-A} {f = tri-0} = reflᵉ
  comp-hom-rule {g = 1-A} {f = tri-1} = reflᵉ
  comp-hom-rule {g = 1-A} {f = tri-2} = reflᵉ
  comp-hom-rule {g = 1-A} {f = 1-A} = reflᵉ
  comp-hom-rule {g = 1-I} {f = 1-I} = reflᵉ
  comp-hom-rule {g = 1-T} {f = 1-T} = reflᵉ


-------------------------------------------
--L-cat is an inverse exo category
L-cat-is-Inv-Exo-cat : Inv-Exo-cat lzero lzero
L-cat-is-Inv-Exo-cat = L-cat-is-Exo-cat ,ᵉ Exo-functor-L-cat-to-op-ℕᵉ-cat

--L-cat is of height three
L-cat-has-height-three : has-height L-cat-is-Inv-Exo-cat threeᵉ
L-cat-has-height-three O = (twoᵉ ,ᵉ reflᵉ)
L-cat-has-height-three A = (oneᵉ ,ᵉ reflᵉ)
L-cat-has-height-three I = (zeroᵉ ,ᵉ reflᵉ)
L-cat-has-height-three T = (zeroᵉ ,ᵉ reflᵉ)

----------------------------
--Each L(n) is finite
L-cat-0-sorts : ℕᵉ< oneᵉ ≅ (L-cat-is-Inv-Exo-cat ⟅ zeroᵉ ⟆)
L-cat-0-sorts = (λ {(inrᵉ starᵉ) → (O ,ᵉ reflᵉ)}) ,ᵉ (λ x → inrᵉ starᵉ) ,ᵉ
                (λ {(inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ {(O ,ᵉ reflᵉ) → reflᵉ})


L-cat-1-sorts : ℕᵉ< oneᵉ ≅ (L-cat-is-Inv-Exo-cat ⟅ oneᵉ ⟆)
L-cat-1-sorts = (λ {(inrᵉ starᵉ) → (A ,ᵉ reflᵉ) }) ,ᵉ (λ x → inrᵉ starᵉ) ,ᵉ 
                (λ {(inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ {(A ,ᵉ reflᵉ) → reflᵉ})

L-cat-2-sorts : ℕᵉ< twoᵉ ≅ (L-cat-is-Inv-Exo-cat ⟅ twoᵉ ⟆)
L-cat-2-sorts = (λ { (inlᵉ (inrᵉ starᵉ)) → (I ,ᵉ reflᵉ) ;
                     (inrᵉ starᵉ) → (T ,ᵉ reflᵉ)}) ,ᵉ
                (λ { (I ,ᵉ reflᵉ) → (inlᵉ (inrᵉ starᵉ)) ;
                     (T ,ᵉ b) → (inrᵉ starᵉ)}) ,ᵉ
                (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ { (I ,ᵉ reflᵉ) → reflᵉ ; (T ,ᵉ reflᵉ) → reflᵉ})

L-cat-higher-sorts-are-empty : (n : ℕᵉ) → (threeᵉ ≤ᵉ n) → ⊥ᵉ ≅ (L-cat-is-Inv-Exo-cat ⟅ n ⟆)
L-cat-higher-sorts-are-empty (succᵉ (succᵉ (succᵉ n))) p = (λ {()}) ,ᵉ
                                                          (λ {(O ,ᵉ ()) ; (A ,ᵉ ()) ; (I ,ᵉ ()) ; (T ,ᵉ ())}) ,ᵉ
                                                          (λ {()}) ,ᵉ
                                                          (λ {(O ,ᵉ ()) ; (A ,ᵉ ()) ; (I ,ᵉ ()) ; (T ,ᵉ ())})

--------------------------------------------
--Each Fanout is finite
L-cat-A-Fanout : ℕᵉ< twoᵉ ≅ (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} oneᵉ (A ,ᵉ reflᵉ) zeroᵉ (zeroᵉ ,ᵉ reflᵉ))
L-cat-A-Fanout = (λ { (inlᵉ (inrᵉ starᵉ)) → (O ,ᵉ reflᵉ) ,ᵉ dom ;
                      (inrᵉ starᵉ) → (O ,ᵉ reflᵉ) ,ᵉ codom}) ,ᵉ
                 (λ { ((O ,ᵉ reflᵉ) ,ᵉ dom) → (inlᵉ (inrᵉ starᵉ)) ;
                      ((O ,ᵉ reflᵉ) ,ᵉ codom) → (inrᵉ starᵉ)}) ,ᵉ
                 (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ;
                      (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                 (λ { ((O ,ᵉ reflᵉ) ,ᵉ dom) → reflᵉ ;
                      ((O ,ᵉ reflᵉ) ,ᵉ codom) → reflᵉ})

L-cat-I-Fanout-O : ℕᵉ< oneᵉ ≅ (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} twoᵉ (I ,ᵉ reflᵉ) zeroᵉ (oneᵉ ,ᵉ reflᵉ))
L-cat-I-Fanout-O = (λ { (inrᵉ starᵉ) → (O ,ᵉ reflᵉ) ,ᵉ id-arrow'}) ,ᵉ
                   (λ { ((O ,ᵉ reflᵉ) ,ᵉ id-arrow') → inrᵉ starᵉ}) ,ᵉ
                   (λ { (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                   (λ { ((O ,ᵉ reflᵉ) ,ᵉ id-arrow') → reflᵉ})

L-cat-I-Fanout-A : ℕᵉ< oneᵉ ≅ (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} twoᵉ (I ,ᵉ reflᵉ) oneᵉ (zeroᵉ ,ᵉ reflᵉ))
L-cat-I-Fanout-A = (λ { (inrᵉ starᵉ) → (A ,ᵉ reflᵉ) ,ᵉ id-arrow}) ,ᵉ
                   (λ { ((A ,ᵉ reflᵉ) ,ᵉ id-arrow) → inrᵉ starᵉ}) ,ᵉ
                   (λ { (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                   (λ { ((A ,ᵉ reflᵉ) ,ᵉ id-arrow) → reflᵉ})

L-cat-T-Fanout-O : ℕᵉ< threeᵉ ≅ (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} twoᵉ (T ,ᵉ reflᵉ) zeroᵉ (oneᵉ ,ᵉ reflᵉ))
L-cat-T-Fanout-O = (λ { (inlᵉ (inlᵉ (inrᵉ starᵉ))) → ((O ,ᵉ reflᵉ) ,ᵉ tri-0') ;
                        (inlᵉ (inrᵉ starᵉ)) → ((O ,ᵉ reflᵉ) ,ᵉ tri-1') ;
                        (inrᵉ starᵉ) → ((O ,ᵉ reflᵉ) ,ᵉ tri-2')}) ,ᵉ
                   (λ { ((O ,ᵉ reflᵉ) ,ᵉ tri-0') → (inlᵉ (inlᵉ (inrᵉ starᵉ))) ;
                        ((O ,ᵉ reflᵉ) ,ᵉ tri-1') → (inlᵉ (inrᵉ starᵉ)) ;
                        ((O ,ᵉ reflᵉ) ,ᵉ tri-2') → (inrᵉ starᵉ)}) ,ᵉ
                   (λ { (inlᵉ (inlᵉ (inrᵉ starᵉ))) → reflᵉ ;
                        (inlᵉ (inrᵉ starᵉ)) → reflᵉ ;
                        (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                   (λ { ((O ,ᵉ reflᵉ) ,ᵉ tri-0') → reflᵉ ;
                        ((O ,ᵉ reflᵉ) ,ᵉ tri-1') → reflᵉ ;
                        ((O ,ᵉ reflᵉ) ,ᵉ tri-2') → reflᵉ})

L-cat-T-Fanout-A : ℕᵉ< threeᵉ ≅ (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} twoᵉ (T ,ᵉ reflᵉ) oneᵉ (zeroᵉ ,ᵉ reflᵉ))
L-cat-T-Fanout-A = (λ { (inlᵉ (inlᵉ (inrᵉ starᵉ))) → ((A ,ᵉ reflᵉ) ,ᵉ tri-0) ;
                        (inlᵉ (inrᵉ starᵉ)) → ((A ,ᵉ reflᵉ) ,ᵉ tri-1) ;
                        (inrᵉ starᵉ) → ((A ,ᵉ reflᵉ) ,ᵉ tri-2)}) ,ᵉ
                   (λ { ((A ,ᵉ reflᵉ) ,ᵉ tri-0) → (inlᵉ (inlᵉ (inrᵉ starᵉ))) ;
                        ((A ,ᵉ reflᵉ) ,ᵉ tri-1) → (inlᵉ (inrᵉ starᵉ)) ;
                        ((A ,ᵉ reflᵉ) ,ᵉ tri-2) → (inrᵉ starᵉ)}) ,ᵉ
                   (λ { (inlᵉ (inlᵉ (inrᵉ starᵉ))) → reflᵉ ;
                        (inlᵉ (inrᵉ starᵉ)) → reflᵉ ;
                        (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                   (λ { ((A ,ᵉ reflᵉ) ,ᵉ tri-0) → reflᵉ ;
                        ((A ,ᵉ reflᵉ) ,ᵉ tri-1) → reflᵉ ;
                        ((A ,ᵉ reflᵉ) ,ᵉ tri-2) → reflᵉ})


--------------------------------------------
--L-cat is a diagram signature of height three

L-cat-isDSig : DSig {lzero} {lzero} {lzero} {lzero} threeᵉ
L-cat-isDSig = L-cat-is-Inv-Exo-cat ,ᵉ
               is-dsig L-cat-has-height-three
                       proof-of-sharpness 
                       proof-of-cofibrancy

  where
   proof-of-sharpness : (n : ℕᵉ) → isSharp (L-cat-is-Inv-Exo-cat ⟅ n ⟆) lzero
   proof-of-sharpness zeroᵉ = isSharp-iso L-cat-0-sorts (Fin-is-sharp oneᵉ lzero) 
   proof-of-sharpness (succᵉ zeroᵉ) = isSharp-iso L-cat-1-sorts (Fin-is-sharp oneᵉ lzero) 
   proof-of-sharpness (succᵉ (succᵉ zeroᵉ)) = isSharp-iso L-cat-2-sorts (Fin-is-sharp twoᵉ lzero) 
   proof-of-sharpness (succᵉ (succᵉ (succᵉ n))) = isSharp-iso
                                                   (L-cat-higher-sorts-are-empty (succᵉ (succᵉ (succᵉ n))) (n ,ᵉ reflᵉ))
                                                   (is-⊥ᵉ-Sharp lzero)

   proof-of-cofibrancy : (n : ℕᵉ) (K : L-cat-is-Inv-Exo-cat ⟅ n ⟆) (m : ℕᵉ) (m<n : succᵉ m ≤ᵉ n) 
                          → isCofibrant (Fanout {lzero} {lzero} {L-cat-is-Inv-Exo-cat} n K m m<n) lzero
   proof-of-cofibrancy (succᵉ zeroᵉ) (A ,ᵉ reflᵉ) zeroᵉ p = isCofibrant-iso L-cat-A-Fanout (Fin-is-cofibrant twoᵉ lzero) 
   proof-of-cofibrancy (succᵉ (succᵉ zeroᵉ)) (I ,ᵉ reflᵉ) zeroᵉ p = isCofibrant-iso L-cat-I-Fanout-O (Fin-is-cofibrant oneᵉ lzero)
   proof-of-cofibrancy (succᵉ (succᵉ zeroᵉ)) (I ,ᵉ reflᵉ) (succᵉ zeroᵉ) p = isCofibrant-iso L-cat-I-Fanout-A (Fin-is-cofibrant oneᵉ lzero)
   proof-of-cofibrancy (succᵉ (succᵉ zeroᵉ)) (T ,ᵉ reflᵉ) zeroᵉ p = isCofibrant-iso L-cat-T-Fanout-O (Fin-is-cofibrant threeᵉ lzero) 
   proof-of-cofibrancy (succᵉ (succᵉ zeroᵉ)) (T ,ᵉ reflᵉ) (succᵉ zeroᵉ) p = isCofibrant-iso L-cat-T-Fanout-A (Fin-is-cofibrant threeᵉ lzero) 
   proof-of-cofibrancy (succᵉ (succᵉ (succᵉ n))) (O ,ᵉ ()) m p
   proof-of-cofibrancy (succᵉ (succᵉ (succᵉ n))) (A ,ᵉ ()) m p
   proof-of-cofibrancy (succᵉ (succᵉ (succᵉ n))) (I ,ᵉ ()) m p
   proof-of-cofibrancy (succᵉ (succᵉ (succᵉ n))) (T ,ᵉ ()) m p
