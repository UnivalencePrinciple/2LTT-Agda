{-# OPTIONS --without-K --two-level  #-}

module 2LTT.Exotypes.Functions where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Sigma

--EXO-UNIVERSE--

---------------------------------------------------------------------
--Functions in Exo-Universe
idᵉ : {i : Level}{A : UUᵉ i} → (A → A)
idᵉ {A} a = a

_∘ᵉ_ : {i j k : Level}
    → {A : UUᵉ i} {B : A → UUᵉ j} {C : (a : A) → B a → UUᵉ k}
    → ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ᵉ f) a = g (f a)

is-exo-iso : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} (f : A → B) → UUᵉ (i ⊔ j)
is-exo-iso {i} {j} {A} {B} f = Σᵉ (B → A) (λ g → ((a : A) → (g ∘ᵉ f) a =ᵉ a) ×ᵉ ((b : B) → (f ∘ᵉ g) b =ᵉ b))

_≅_ : {i j : Level}(A : UUᵉ i) (B : UUᵉ j) → UUᵉ (i ⊔ j)
A ≅ B = Σᵉ (A → B) (λ f → is-exo-iso f)

≅-refl : {i : Level} {A : UUᵉ i} → A ≅ A
≅-refl = idᵉ , (idᵉ , ((λ a → reflᵉ) , λ b → reflᵉ))

idtoiso : {i : Level} {A B : UUᵉ i} → A =ᵉ B → A ≅ B
idtoiso reflᵉ = ≅-refl

happlyᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} {f g : (x : A) → B x}
         → f =ᵉ g → (∀ x → f x =ᵉ g x)      
happlyᵉ reflᵉ x = reflᵉ

postulate
  funextᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} {f g : (x : A) → B x}
          → (∀ x → f x =ᵉ g x) → f =ᵉ g

=ᵉ-preserve-eqv : {i j : Level} (A A' : UUᵉ i) → (B : UUᵉ j)
                    → A =ᵉ A' → A ≅ B → A' ≅ B
=ᵉ-preserve-eqv A .A B reflᵉ W = W

≅-sym : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} → A ≅ B → B ≅ A
≅-sym (F , (G , (lh , rh))) = (G , (F , (rh , lh)))

≅-trans : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k} → A ≅ B → B ≅ C → A ≅ C
≅-trans {i} {j} {k} (F , (G , (lh , rh))) (F' , (G' , (lh' , rh')))
        = ((F' ∘ᵉ F) ,
            ((G ∘ᵉ G') ,
              ((λ a → exo-concat (exo-ap G (lh' (F a))) (lh a)) ,
                 (λ c → exo-concat (exo-ap F' (rh (G' c ))) (rh' c)))))

idtoincl : {i : Level} {A B : UUᵉ i} → A =ᵉ B → A → B
idtoincl reflᵉ a = a


--some congruence rules

Family-isoᵉ : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {f g : A → A}
             → (f =ᵉ g) → ((a : A) → P (f a) ≅ P (g a))
Family-isoᵉ reflᵉ a = ≅-refl


Σᵉ-functor : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (f0 : A → B ) → (f1 : (a : A) → P (a) →  Q (f0 a))
             → Σᵉ A P → Σᵉ B Q
Σᵉ-functor {i} {j} {A} {B} {P} {Q} f0 f1 = λ (a , p) → (f0 a , f1 a p)


Σᵉ-iso-cong : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
           → (f0 : A → B) → {is-exo-iso f0}
           → (f1 : (a : A) → P (a) → Q (f0 a)) → {(a : A) → is-exo-iso (f1 a)}
           → Σᵉ A P ≅ Σᵉ B Q
Σᵉ-iso-cong {i} {j} {A} {B} {P} {Q} f0 {(f0' , lh , rh)} f1 {G}
   = Σᵉ-functor f0 (λ (a : A) → (f1 a)) ,
     Σᵉ-functor f0' (λ (b : B) → (pr1ᵉ (G (f0' b))) ∘ᵉ (exo-tr Q (exo-inv (rh b)))) ,
      (λ {(a , p) → dep-pair-=ᵉ (f0' (f0 a) , pr1ᵉ (G (f0' (f0 a))) (exo-tr Q (exo-inv (rh (f0 a))) (f1 a p)))
                                         (a , p)
                                         (lh a ,
                                         exo-concat
                                           (exo-inv (exo-ap-transport (lh a) (λ u → pr1ᵉ (G u))
                                                                   (exo-tr Q (exo-inv (rh (f0 a))) (f1 a p))))
                                           (exo-concat
                                             (exo-ap (pr1ᵉ (G a)) (exo-tr-ap {_} {_} {_} {_} {_} {Q} {f0' (f0 a)} {a} (lh a)
                                                                              {exo-tr Q (exo-inv (rh (f0 a))) (f1 a p)}))
                                             (exo-concat
                                               (exo-ap (pr1ᵉ (G a)) (exo-tr-concat {i} {j} {B} {Q} {_}{_}{_} (exo-inv (rh (f0 a)))
                                                                                    (exo-ap f0 (lh a))))
                                               (exo-concat
                                                 (exo-ap (pr1ᵉ (G a)) (exo-ap-tr {i} {j} {B} {Q} {f0 a} {f0 a}
                                                                                  {exo-concat (exo-inv (rh (f0 a)))
                                                                                               (exo-ap f0 (lh a))}
                                                                                  {reflᵉ} {f1 a p} (UIPᵉ _ _)))
                                                 ((pr1ᵉ (pr2ᵉ (G a))) p)))))}) ,
     (λ {(b , q) → dep-pair-=ᵉ (f0 (f0' b) , f1 (f0' b) (pr1ᵉ (G (f0' b)) (exo-tr Q (exo-inv (rh b)) q)))
                                         (b , q)
                                         (rh b ,
                                          exo-concat
                                            (exo-tr-fam-ap {i} {j} {B} {Q} {f0 (f0' b)} {b} {rh b}
                                                        {(f1 (f0' b)) ∘ᵉ (pr1ᵉ (G (f0' b)))} {idᵉ}
                                                        {exo-tr Q (exo-inv (rh b)) q} (funextᵉ (λ x → (pr2ᵉ (pr2ᵉ (G (f0' b)))) x)))
                                            (exo-concat
                                              (exo-tr-concat {i} {j} {B} {Q} {_} {_} {_} (exo-inv (rh b)) (rh b))
                                              ((exo-ap-tr {i} {j} {B} {Q} {b} {b} {exo-concat (exo-inv (rh b))
                                                                                                   (rh b)}
                                                                                  {reflᵉ} {q} (UIPᵉ _ _)))))})
   

Σᵉ-iso-cong' : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
           → (W : A ≅ B)
           → (V : (a : A) → (P (a) ≅ Q ((pr1ᵉ W) a)))
           → Σᵉ A P ≅ Σᵉ B Q
Σᵉ-iso-cong' {i} {j} {A} {B} {P} {Q} W V
             = Σᵉ-iso-cong {i} {j} {A} {B} {P} {Q} (pr1ᵉ W) {pr2ᵉ W} (λ (a : A) → pr1ᵉ (V a)) {λ (a : A) → pr2ᵉ (V a)}

×ᵉ-iso-cong : {i j : Level}{A B : UUᵉ i}{P Q : UUᵉ j}
           → (W : A ≅ B)
           → (V : P ≅ Q)
           → (A ×ᵉ P) ≅ (B ×ᵉ Q)
×ᵉ-iso-cong {i} {j} {A} {B} {P} {Q} W V = Σᵉ-iso-cong' {i} {j} {A} {B} {λ _ → P} {λ _ → Q} W λ _ → V
            
