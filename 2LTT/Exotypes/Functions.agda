{-# OPTIONS --without-K --two-level #-}

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
is-exo-iso {i} {j} {A} {B} f = Σᵉ (B → A) (λ g → ((g ∘ᵉ f) =ₛᵉ idᵉ) ×ᵉ ((f ∘ᵉ g) =ₛᵉ idᵉ))

_≅_ : {i j : Level}(A : UUᵉ i) (B : UUᵉ j) → UUᵉ (i ⊔ j)
A ≅ B = Σᵉ (A → B) (λ f → is-exo-iso f)

≅-refl : {i : Level} {A : UUᵉ i} → A ≅ A
≅-refl = idᵉ , (idᵉ , (reflₛᵉ , reflₛᵉ))

idtoiso : {i : Level} {A B : UUᵉ i} → A =ₛᵉ B → A ≅ B
idtoiso reflₛᵉ = ≅-refl

happlyₛᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} {f g : (x : A) → B x}
         → f =ₛᵉ g → (∀ x → f x =ₛᵉ g x)      
happlyₛᵉ reflₛᵉ x = reflₛᵉ

postulate
  funextₛᵉ : {i j : Level} {A : UUᵉ i} {B : A → UUᵉ j} {f g : (x : A) → B x}
          → (∀ x → f x =ₛᵉ g x) → f =ₛᵉ g

≡ₛᵉ-preserve-eqv : {i j : Level} (A A' : UUᵉ i) → (B : UUᵉ j)
                    → A =ₛᵉ A' → A ≅ B → A' ≅ B
≡ₛᵉ-preserve-eqv A .A B reflₛᵉ W = W

≅-sym : {i j : Level} {A : UUᵉ i} {B : UUᵉ j} → A ≅ B → B ≅ A
≅-sym (F , (G , (lh , rh))) = (G , (F , (rh , lh)))

≅-trans : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {C : UUᵉ k} → A ≅ B → B ≅ C → A ≅ C
≅-trans {i} {j} {k} (F , (G , (lh , rh))) (F' , (G' , (lh' , rh')))
        = ((F' ∘ᵉ F) ,
            ((G ∘ᵉ G') ,
              (funextₛᵉ (λ a → exo-concatᵉ (exo-apᵉ G (happlyₛᵉ lh' (F a))) (happlyₛᵉ lh a)) ,
                 funextₛᵉ (λ c → exo-concatᵉ (exo-apᵉ F' (happlyₛᵉ rh (G' c ))) ((happlyₛᵉ rh' c))))))

idtoincl : {i : Level} {A B : UUᵉ i} → A =ₛᵉ B → A → B
idtoincl reflₛᵉ a = a


--some congruence rules

Family-isoᵉ : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {f g : A → A}
             → (f =ₛᵉ g) → ((a : A) → P (f a) ≅ P (g a))
Family-isoᵉ reflₛᵉ a = ≅-refl

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
     Σᵉ-functor f0' (λ (b : B) → (pr1ᵉ (G (f0' b))) ∘ᵉ (exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh b)))) ,
     funextₛᵉ (λ {(a , p) → dep-pair-=ₛᵉ (f0' (f0 a) , pr1ᵉ (G (f0' (f0 a))) (exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh (f0 a))) (f1 a p)))
                                         (a , p)
                                         (happlyₛᵉ lh a ,
                                         exo-concatᵉ
                                           (exo-invᵉ (ap-transportᵉ (happlyₛᵉ lh a) (λ u → pr1ᵉ (G u))
                                                                   (exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh (f0 a))) (f1 a p))))
                                           (exo-concatᵉ
                                             (exo-apᵉ (pr1ᵉ (G a)) (exo-tr-apᵉ {_} {_} {_} {_} {_} {Q} {f0' (f0 a)} {a} (happlyₛᵉ lh a)
                                                                              {exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh (f0 a))) (f1 a p)}))
                                             (exo-concatᵉ
                                               (exo-apᵉ (pr1ᵉ (G a)) (exo-tr-concatᵉ {i} {j} {B} {Q} {_}{_}{_} (exo-invᵉ (happlyₛᵉ rh (f0 a)))
                                                                                    (exo-apᵉ f0 (happlyₛᵉ lh a))))
                                               (exo-concatᵉ
                                                 (exo-apᵉ (pr1ᵉ (G a)) (exo-ap-trᵉ {i} {j} {B} {Q} {f0 a} {f0 a}
                                                                                  {exo-concatᵉ (exo-invᵉ (happlyₛᵉ rh (f0 a)))
                                                                                               (exo-apᵉ f0 (happlyₛᵉ lh a))}
                                                                                  {reflₛᵉ} {f1 a p} (UIPᵉ _ _)))
                                                 (happlyₛᵉ (pr1ᵉ (pr2ᵉ (G a))) p)))))}) ,
     funextₛᵉ (λ {(b , q) → dep-pair-=ₛᵉ (f0 (f0' b) , f1 (f0' b) (pr1ᵉ (G (f0' b)) (exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh b)) q)))
                                         (b , q)
                                         (happlyₛᵉ rh b ,
                                          exo-concatᵉ
                                            (tr-fam-apᵉ {i} {j} {B} {Q} {f0 (f0' b)} {b} {happlyₛᵉ rh b}
                                                        {(f1 (f0' b)) ∘ᵉ (pr1ᵉ (G (f0' b)))} {idᵉ}
                                                        {exo-trᵉ Q (exo-invᵉ (happlyₛᵉ rh b)) q} (pr2ᵉ (pr2ᵉ (G (f0' b)))))
                                            (exo-concatᵉ
                                              (exo-tr-concatᵉ {i} {j} {B} {Q} {_} {_} {_} (exo-invᵉ (happlyₛᵉ rh b)) (happlyₛᵉ rh b))
                                              ((exo-ap-trᵉ {i} {j} {B} {Q} {b} {b} {exo-concatᵉ (exo-invᵉ (happlyₛᵉ rh b))
                                                                                                   (happlyₛᵉ rh b)}
                                                                                  {reflₛᵉ} {q} (UIPᵉ _ _)))))})
   

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
            
