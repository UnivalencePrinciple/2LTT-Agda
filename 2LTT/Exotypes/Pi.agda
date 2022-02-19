{-# OPTIONS --without-K --two-level #-}

module 2LTT.Exotypes.Pi where

open import 2LTT.Primitive 
open import 2LTT.Exotypes.Exo_Equality
open import 2LTT.Exotypes.Functions
open import 2LTT.Exotypes.Sigma



--Type formers of dependent functions for exotypes
Πᵉ : {i j : Level} (A : UUᵉ i) (P : A → UUᵉ j) → UUᵉ (i ⊔ j)
Πᵉ A P = (x : A) → P x

Πᵉ-intro : {i j : Level} (A : UUᵉ i) (P : A → UUᵉ j) (e : (a : A) → P a) → Πᵉ A P
Πᵉ-intro A P e = λ x → e x

Πᵉ-elim : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {a : A} → Πᵉ A P → P a
Πᵉ-elim {a = a} f = f a

Πᵉ-β-rule : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} → (f : Πᵉ A P)
            → (a : A) → (λ x → f x) a =ₛᵉ f a
Πᵉ-β-rule f a = reflₛᵉ

Πᵉ-η-rule : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} → (f : Πᵉ A P) → f =ₛᵉ (λ x → f x)
Πᵉ-η-rule f = reflₛᵉ

Πᵉ-form-cong1 : {i j : Level}{A : UUᵉ i}{P Q : A → UUᵉ j}
             → (P =ₛᵉ Q)
             → Πᵉ A P =ₛᵉ Πᵉ A Q
Πᵉ-form-cong1 reflₛᵉ = reflₛᵉ

Πᵉ-form-cong2 : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (w : A =ₛᵉ B) → (p : (a : A) → P a =ₛᵉ Q (exo-trᵉ (λ x → x) w a))
             → Πᵉ A P =ₛᵉ Πᵉ B Q
Πᵉ-form-cong2 reflₛᵉ p = Πᵉ-form-cong1 (funextₛᵉ p)

Πᵉ-intro-cong : {i j : Level}{A : UUᵉ i}{P : A → UUᵉ j}
                → (e f : (a : A) → P a) → e =ₛᵉ f
                → (λ a → e a) =ₛᵉ (λ a → f a)
Πᵉ-intro-cong e .e reflₛᵉ = reflₛᵉ

Πᵉ-elim-cong : {i j : Level}{A : UUᵉ i}{P : A → UUᵉ j}{e e' : Πᵉ A P}{a a' : A}
                → (p : a =ₛᵉ a') → (q : e =ₛᵉ e')
                → exo-trᵉ P (p) (e a) =ₛᵉ e' a'
Πᵉ-elim-cong reflₛᵉ reflₛᵉ = reflₛᵉ

Πᵉ-×-expansion : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {Y : A ×ᵉ B → UUᵉ k}
               → (Πᵉ A (λ a → Πᵉ B λ b → Y (a , b))) ≅ (Πᵉ (A ×ᵉ B) Y)
Πᵉ-×-expansion = (λ f → λ {(a , b) → f a b}) ,
               (λ g → λ a → λ b → g (a , b)) ,
               funextₛᵉ (λ x → reflₛᵉ) , funextₛᵉ (λ x → reflₛᵉ)


Πᵉ-Σ-expansion : {i j k : Level} {A : UUᵉ i} {B : A → UUᵉ j} {Y : Σᵉ A B → UUᵉ k}
               → (Πᵉ A (λ a → Πᵉ (B a) λ b → Y (a , b))) ≅ (Πᵉ (Σᵉ A B) Y)
Πᵉ-Σ-expansion = (λ f → λ {(a , b) → f a b}) ,
               (λ g → λ a → λ b → g (a , b)) ,
               funextₛᵉ (λ x → reflₛᵉ) , funextₛᵉ (λ x → reflₛᵉ)

Πᵉ-functor : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (f0 : B → A ) → (f1 : (b : B) → P (f0 b) →  Q (b))
             → Πᵉ A P → Πᵉ B Q
Πᵉ-functor {i} {j} {A} {B} {P} {Q} f0 f1 = λ g → λ b → f1 _ (g (f0 b))
{-# INLINE Πᵉ-functor #-}

Πᵉ-iso-cong : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (f0 : B → A) → {is-exo-iso f0}
             → (f1 : (b : B) → P (f0 b) → Q (b)) → {(b : B) → is-exo-iso (f1 b)}
             → Πᵉ A P ≅ Πᵉ B Q
Πᵉ-iso-cong {i} {j} {A} {B} {P} {Q} f0 {(f0' , lh , rh)} f1 {G}
 = Πᵉ-functor f0 (λ (b : B) → (f1 b)) ,
   Πᵉ-functor f0' (λ (a : A) → (exo-trᵉ P ((happlyₛᵉ rh) a)) ∘ᵉ (pr1ᵉ (G (f0' a)))),
   funextₛᵉ (λ f → funextₛᵉ λ a → exo-concatᵉ
                                   (tr-fam-apᵉ {i} {j} {A} {P} {f0 (f0' a)} {a} {happlyₛᵉ rh a}
                                                       {(pr1ᵉ (G (f0' a))) ∘ᵉ (f1 (f0' a))} {idᵉ {j} {P (f0 (f0' a))}}
                                                       {f (f0 (f0' a))} (pr1ᵉ (pr2ᵉ (G (f0' a)))))
                                   (exo-apdᵉ {i} {j} {A} {P} (f) {f0 (f0' a)} {a} (happlyₛᵉ rh a))) ,
   funextₛᵉ (λ f → funextₛᵉ λ b → exo-concatᵉ
                                   (exo-apᵉ (f1 b)
                                   (exo-ap-trᵉ {i} {j} {A} {P} {f0 (f0' (f0 b))} {f0 b}
                                      {(happlyₛᵉ rh) (f0 b)} {exo-apᵉ f0 ((happlyₛᵉ lh) b)} 
                                       (UIPᵉ {i} {A} {f0 (f0' (f0 b))} {f0 b} ((happlyₛᵉ rh) (f0 b)) (exo-apᵉ f0 ((happlyₛᵉ lh) b)))))
                                   (exo-concatᵉ
                                    (exo-apᵉ (f1 b) (exo-invᵉ (exo-tr-apᵉ {i} {j} {B} {A} {f0} {P} {_} {_} _
                                                                        {(pr1ᵉ (G (f0' (f0 b))) (f (f0' (f0 b))))})))
                                    (exo-concatᵉ
                                      (ap-transportᵉ {i} {j} {B} {λ (x : B) → P (f0 x)} {Q} {f0' (f0 b)} {b}
                                                        (happlyₛᵉ lh b) (f1) (pr1ᵉ (G (f0' (f0 b))) (f (f0' (f0 b)))))
                                      (exo-concatᵉ
                                       (tr-fam-apᵉ {i} {j} {B} {Q} {f0' (f0 b)} {b} {happlyₛᵉ lh b}
                                                         {f1 (f0' (f0 b)) ∘ᵉ (pr1ᵉ (G (f0' (f0 b))))}
                                                         {idᵉ {j} {Q (f0' (f0 b))}} {f (f0' (f0 b))}
                                                         (pr2ᵉ (pr2ᵉ (G (f0' (f0 b))))))
                                       (exo-apdᵉ {i} {j} {B} {Q} (f) {f0' (f0 b)} {b} (happlyₛᵉ lh b))))))


Πᵉ-iso-cong' : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (W : B ≅ A) 
             → (f1 : (b : B) → P ((pr1ᵉ W) b) ≅ Q (b))
             → Πᵉ A P ≅ Πᵉ B Q
Πᵉ-iso-cong' W V
             = Πᵉ-iso-cong (pr1ᵉ W) {pr2ᵉ W} (λ (b : _) → pr1ᵉ (V b)) {λ (b : _) → pr2ᵉ (V b)}
