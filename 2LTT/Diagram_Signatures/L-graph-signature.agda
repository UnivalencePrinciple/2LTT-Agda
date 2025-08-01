{-# OPTIONS --without-K --exact-split --two-level  --cumulativity #-}

module 2LTT.Diagram_Signatures.L-graph-signature where

open import 2LTT.Diagram_Signatures.Reedy-fibration public

--Objects for L-graph
data L-graph-Obj : UUᵉ lzero where
   V : L-graph-Obj
   E : L-graph-Obj

--Arrows for L-graph
data L-graph-Hom : L-graph-Obj → L-graph-Obj → UUᵉ lzero where
   end1 : L-graph-Hom E V
   end2 : L-graph-Hom E V
   1-V : L-graph-Hom V V
   1-E : L-graph-Hom E E
  
--Id-Homs
Id-Hom-L-graph : (a : L-graph-Obj) → L-graph-Hom a a
Id-Hom-L-graph V = 1-V
Id-Hom-L-graph E = 1-E

--Composition
L-graph-Comp : {a b c : L-graph-Obj}
             → L-graph-Hom b c → L-graph-Hom a b → L-graph-Hom a c
L-graph-Comp end1 1-E = end1
L-graph-Comp end2 1-E = end2
L-graph-Comp 1-V end1 = end1
L-graph-Comp 1-V end2 = end2
L-graph-Comp 1-V 1-V = 1-V
L-graph-Comp 1-E 1-E = 1-E


--Associativity
L-graph-Assoc : {a b c d : L-graph-Obj} (h : L-graph-Hom c d) (g : L-graph-Hom b c) (f : L-graph-Hom a b) →
              L-graph-Comp h (L-graph-Comp g f) =ᵉ L-graph-Comp (L-graph-Comp h g) f
L-graph-Assoc end1 1-E 1-E = reflᵉ
L-graph-Assoc end2 1-E 1-E = reflᵉ
L-graph-Assoc 1-V end1 1-E = reflᵉ
L-graph-Assoc 1-V end2 1-E = reflᵉ
L-graph-Assoc 1-V 1-V end1 = reflᵉ
L-graph-Assoc 1-V 1-V end2 = reflᵉ
L-graph-Assoc 1-V 1-V 1-V = reflᵉ
L-graph-Assoc 1-E 1-E 1-E = reflᵉ

---Left/Right Identity Rules
L-graph-Left-Id-rule : {a b : L-graph-Obj} (f : L-graph-Hom a b) → L-graph-Comp (Id-Hom-L-graph b) f =ᵉ f
L-graph-Left-Id-rule end1 = reflᵉ
L-graph-Left-Id-rule end2 = reflᵉ
L-graph-Left-Id-rule 1-V = reflᵉ
L-graph-Left-Id-rule 1-E = reflᵉ


L-graph-Right-Id-rule : {a b : L-graph-Obj} (f : L-graph-Hom a b) → L-graph-Comp f (Id-Hom-L-graph a) =ᵉ f
L-graph-Right-Id-rule end1 = reflᵉ
L-graph-Right-Id-rule end2 = reflᵉ
L-graph-Right-Id-rule 1-V = reflᵉ
L-graph-Right-Id-rule 1-E = reflᵉ


------------------------------------------------------------------
-----L-graph is an exo-category.
L-graph-is-Exo-cat : Exo-cat lzero lzero
Exo-cat.Object L-graph-is-Exo-cat = L-graph-Obj
Exo-cat.Hom L-graph-is-Exo-cat = L-graph-Hom
Exo-cat.Comp L-graph-is-Exo-cat = L-graph-Comp
Exo-cat.Assoc L-graph-is-Exo-cat = L-graph-Assoc
Exo-cat.Id-hom L-graph-is-Exo-cat = Id-Hom-L-graph
Exo-cat.Id-left-coh L-graph-is-Exo-cat = L-graph-Left-Id-rule
Exo-cat.Id-right-coh L-graph-is-Exo-cat = L-graph-Right-Id-rule

-------------------------------------------------------------------
---There is an exo-functor from L-graph to (ℕᵉ)ᵒᵖ
Exo-functor-L-graph-to-op-ℕᵉ-cat : Exo-Functor L-graph-is-Exo-cat op-ℕᵉ-cat
Exo-functor-L-graph-to-op-ℕᵉ-cat = obj-map ,ᵉ arrow-map ,ᵉ id-hom-rule ,ᵉ comp-hom-rule
  where
  obj-map : Objᵉ L-graph-is-Exo-cat → Objᵉ op-ℕᵉ-cat
  obj-map V = zeroᵉ
  obj-map E = oneᵉ

  arrow-map : {a b : Objᵉ L-graph-is-Exo-cat} → L-graph-is-Exo-cat [ a , b ] → op-ℕᵉ-cat [ obj-map a , obj-map b ]
  arrow-map end1 = oneᵉ ,ᵉ reflᵉ
  arrow-map end2 = oneᵉ ,ᵉ reflᵉ
  arrow-map 1-V = zeroᵉ ,ᵉ reflᵉ
  arrow-map 1-E = zeroᵉ ,ᵉ reflᵉ
  
  id-hom-rule :  {a : Objᵉ L-graph-is-Exo-cat} → arrow-map (Id-Exo-cat L-graph-is-Exo-cat a) =ᵉ Id-Exo-cat op-ℕᵉ-cat (obj-map a)
  id-hom-rule {V} = reflᵉ
  id-hom-rule {E} = reflᵉ
  
  comp-hom-rule : {a b c : Objᵉ L-graph-is-Exo-cat} {g : L-graph-is-Exo-cat [ b , c ]} {f : L-graph-is-Exo-cat [ a , b ]}
                   → arrow-map {a} {c} (comp-Exo-cat {lzero} {lzero} L-graph-is-Exo-cat {a} {b} {c} g f)
                            =ᵉ comp-Exo-cat {lzero} {lzero} op-ℕᵉ-cat (arrow-map {b} {c} g) (arrow-map {a} {b} f)
  comp-hom-rule {g = end1} {f = 1-E} = reflᵉ
  comp-hom-rule {g = end2} {f = 1-E} = reflᵉ
  comp-hom-rule {g = 1-V} {f = end1} = reflᵉ
  comp-hom-rule {g = 1-V} {f = end2} = reflᵉ
  comp-hom-rule {g = 1-V} {f = 1-V} = reflᵉ
  comp-hom-rule {g = 1-E} {f = 1-E} = reflᵉ


-------------------------------------------
--L-graph is an inverse exo category
L-graph-is-Inv-Exo-cat : Inv-Exo-cat lzero lzero
L-graph-is-Inv-Exo-cat = L-graph-is-Exo-cat ,ᵉ Exo-functor-L-graph-to-op-ℕᵉ-cat

--L-graph is of height two
L-graph-has-height-two : has-height L-graph-is-Inv-Exo-cat twoᵉ
L-graph-has-height-two V = oneᵉ ,ᵉ reflᵉ
L-graph-has-height-two E = zeroᵉ ,ᵉ reflᵉ


----------------------------
--Each L(n) is finite
L-graph-0-sorts : ℕᵉ< oneᵉ ≅ (L-graph-is-Inv-Exo-cat ⟅ zeroᵉ ⟆)
L-graph-0-sorts = (λ {(inrᵉ starᵉ) → V ,ᵉ reflᵉ}) ,ᵉ
                (λ x → inrᵉ starᵉ) ,ᵉ
                (λ {(inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ {(V ,ᵉ reflᵉ) → reflᵉ})


L-graph-1-sorts : ℕᵉ< oneᵉ ≅ (L-graph-is-Inv-Exo-cat ⟅ oneᵉ ⟆)
L-graph-1-sorts = (λ {(inrᵉ starᵉ) → E ,ᵉ reflᵉ}) ,ᵉ
                (λ x → inrᵉ starᵉ) ,ᵉ
                (λ {(inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ {(E ,ᵉ reflᵉ) → reflᵉ})

L-graph-higher-sorts-are-empty : (n : ℕᵉ) → (twoᵉ ≤ᵉ n) → ⊥ᵉ ≅ (L-graph-is-Inv-Exo-cat ⟅ n ⟆)
L-graph-higher-sorts-are-empty (succᵉ (succᵉ n)) p =  (λ {()}) ,ᵉ
                                                   (λ {(V ,ᵉ ()) ; (E ,ᵉ ())}) ,ᵉ
                                                   (λ {()}) ,ᵉ
                                                   (λ {(V ,ᵉ ()) ; (E ,ᵉ ())})


--------------------------------------------
--Each Fanout is finite
L-graph-E-Fanout : ℕᵉ< twoᵉ ≅ (Fanout {lzero} {lzero} {L-graph-is-Inv-Exo-cat} oneᵉ (E ,ᵉ reflᵉ) zeroᵉ (zeroᵉ ,ᵉ reflᵉ))
L-graph-E-Fanout = (λ { (inlᵉ (inrᵉ starᵉ)) → (V ,ᵉ reflᵉ) ,ᵉ end1 ;
                      (inrᵉ starᵉ) → (V ,ᵉ reflᵉ) ,ᵉ end2}) ,ᵉ
                 (λ { ((V ,ᵉ reflᵉ) ,ᵉ end1) → (inlᵉ (inrᵉ starᵉ)) ;
                      ((V ,ᵉ reflᵉ) ,ᵉ end2) → (inrᵉ starᵉ)}) ,ᵉ
                 (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ;
                      (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                 (λ { ((V ,ᵉ reflᵉ) ,ᵉ end1) → reflᵉ ;
                      ((V ,ᵉ reflᵉ) ,ᵉ end2) → reflᵉ})


--------------------------------------------
--L-graph is a diagram signature of height two

L-graph-isDSig : DSig {lzero} {lzero} {lzero} {lzero} twoᵉ
L-graph-isDSig = L-graph-is-Inv-Exo-cat ,ᵉ
                 is-dsig L-graph-has-height-two
                         proof-of-sharpness 
                         proof-of-cofibrancy

  where
   proof-of-sharpness : (n : ℕᵉ) → isSharp (L-graph-is-Inv-Exo-cat ⟅ n ⟆) lzero
   proof-of-sharpness zeroᵉ = isSharp-iso L-graph-0-sorts (Fin-is-sharp oneᵉ lzero) 
   proof-of-sharpness (succᵉ zeroᵉ) = isSharp-iso L-graph-1-sorts (Fin-is-sharp oneᵉ lzero) 
   proof-of-sharpness (succᵉ (succᵉ n)) = isSharp-iso
                                                   (L-graph-higher-sorts-are-empty (succᵉ (succᵉ n)) (n ,ᵉ reflᵉ))
                                                   (is-⊥ᵉ-Sharp lzero)

   proof-of-cofibrancy : (n : ℕᵉ) (K : L-graph-is-Inv-Exo-cat ⟅ n ⟆) (m : ℕᵉ) (m<n : succᵉ m ≤ᵉ n) 
                          → isCofibrant (Fanout {lzero} {lzero} {L-graph-is-Inv-Exo-cat} n K m m<n) lzero
   proof-of-cofibrancy (succᵉ zeroᵉ) (E ,ᵉ reflᵉ) zeroᵉ p = isCofibrant-iso L-graph-E-Fanout (Fin-is-cofibrant twoᵉ lzero)
   proof-of-cofibrancy (succᵉ (succᵉ n)) (V ,ᵉ ())
   proof-of-cofibrancy (succᵉ (succᵉ n)) (E ,ᵉ ())

--------------------------
--Properties

--Example 4.11. For an exo-diagram M on the signature E ⇉ V for graphs, we have matching object at E is ≅ MV × MV
match-obj-E-≅-V×V : {M : Exo-Functor (iexo-cat L-graph-is-Inv-Exo-cat) (ExoUniv-is-Exo-cat lzero)}
                    → (matching-object {ℒ = L-graph-is-Inv-Exo-cat} {M} {oneᵉ} {K = (E ,ᵉ reflᵉ)})
                           ≅  ((pr1ᵉ M) V ×ᵉ (pr1ᵉ M) V)
match-obj-E-≅-V×V =
 (λ {(d ,ᵉ mp-d) → (d zeroᵉ (≤ᵉ-refl oneᵉ) ((V ,ᵉ reflᵉ) ,ᵉ end1)) ,ᵉ
                    (d zeroᵉ (≤ᵉ-refl oneᵉ) ((V ,ᵉ reflᵉ) ,ᵉ end2))}) ,ᵉ
 (λ {(u ,ᵉ v) → (λ {zeroᵉ → λ p → λ {((V ,ᵉ reflᵉ) ,ᵉ end1) → u ;
                                       ((V ,ᵉ reflᵉ) ,ᵉ end2) → v} ;
                    (succᵉ m) → λ {()}}) ,ᵉ
                 λ {zeroᵉ → λ {zeroᵉ → λ {()} ;
                               (succᵉ m2) → λ p → λ {()}} ;
                   (succᵉ m1) → λ {zeroᵉ → λ {()} ;
                                   (succᵉ m2) → λ p → λ {()}}}}) ,ᵉ
 (λ {(d ,ᵉ mp-d) → dep-pair-=ᵉ _ _
                    ((funextᵉ (λ {zeroᵉ → funextᵉ λ {(zeroᵉ ,ᵉ reflᵉ) →
                                             funextᵉ λ {((V ,ᵉ reflᵉ) ,ᵉ end1) → reflᵉ ;
                                                        ((V ,ᵉ reflᵉ) ,ᵉ end2) → reflᵉ}} ;
                                 (succᵉ x) → funextᵉ λ {()}})) ,ᵉ
                    (funextᵉ (λ {zeroᵉ → funextᵉ λ { zeroᵉ → funextᵉ {lsuc lzero} {lsuc lzero} λ {()} ;
                                                    (succᵉ x) → funextᵉ {lsuc lzero} λ p → funextᵉ λ {()}} ;
                                (succᵉ x) → funextᵉ {lsuc lzero} λ {zeroᵉ → funextᵉ {lsuc lzero} {lsuc lzero} λ {()} ;
                                                                    (succᵉ x) → funextᵉ {lsuc lzero} λ p → funextᵉ λ {()}}})))}) ,ᵉ
 (λ {(u ,ᵉ v) → reflᵉ})                   
