{-# OPTIONS --without-K --exact-split --two-level #-}

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
            → (a : A) → (λ x → f x) a =ᵉ f a
Πᵉ-β-rule f a = reflᵉ

Πᵉ-η-rule : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} → (f : Πᵉ A P) → f =ᵉ (λ x → f x)
Πᵉ-η-rule f = reflᵉ

Πᵉ-form-cong1 : {i j : Level}{A : UUᵉ i}{P Q : A → UUᵉ j}
             → (P =ᵉ Q)
             → Πᵉ A P =ᵉ Πᵉ A Q
Πᵉ-form-cong1 reflᵉ = reflᵉ

Πᵉ-cong : {i j : Level} {A : UUᵉ i} {P : A → UUᵉ j} {f g : Πᵉ A P}
          → f =ᵉ g → (a : A) → f a =ᵉ g a
Πᵉ-cong reflᵉ a = reflᵉ

Πᵉ-form-cong2 : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (w : A =ᵉ B) → (p : (a : A) → P a =ᵉ Q (exo-tr (λ x → x) w a))
             → Πᵉ A P =ᵉ Πᵉ B Q
Πᵉ-form-cong2 reflᵉ p = Πᵉ-form-cong1 (funextᵉ p)

Πᵉ-intro-cong : {i j : Level}{A : UUᵉ i}{P : A → UUᵉ j}
                → (e f : (a : A) → P a) → e =ᵉ f
                → (λ a → e a) =ᵉ (λ a → f a)
Πᵉ-intro-cong e .e reflᵉ = reflᵉ

Πᵉ-elim-cong : {i j : Level}{A : UUᵉ i}{P : A → UUᵉ j}{e e' : Πᵉ A P}{a a' : A}
                → (p : a =ᵉ a') → (q : e =ᵉ e')
                → exo-tr P (p) (e a) =ᵉ e' a'
Πᵉ-elim-cong reflᵉ reflᵉ = reflᵉ

Πᵉ-×-expansion : {i j k : Level} {A : UUᵉ i} {B : UUᵉ j} {Y : A ×ᵉ B → UUᵉ k}
               → (Πᵉ A (λ a → Πᵉ B λ b → Y (a ,ᵉ b))) ≅ (Πᵉ (A ×ᵉ B) Y)
Πᵉ-×-expansion = (λ f → λ {(a ,ᵉ b) → f a b}) ,ᵉ
               (λ g → λ a → λ b → g (a ,ᵉ b)) ,ᵉ
               (λ x → reflᵉ) ,ᵉ (λ x → reflᵉ)


Πᵉ-Σ-expansion : {i j k : Level} {A : UUᵉ i} {B : A → UUᵉ j} {Y : Σᵉ A B → UUᵉ k}
               → (Πᵉ A (λ a → Πᵉ (B a) λ b → Y (a ,ᵉ b))) ≅ (Πᵉ (Σᵉ A B) Y)
Πᵉ-Σ-expansion = (λ f → λ {(a ,ᵉ b) → f a b}) ,ᵉ
                 (λ g → λ a → λ b → g (a ,ᵉ b)) ,ᵉ
                 (λ x → reflᵉ) ,ᵉ (λ x → reflᵉ)

Πᵉ-functor : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (f0 : B → A ) → (f1 : (b : B) → P (f0 b) →  Q (b))
             → Πᵉ A P → Πᵉ B Q
Πᵉ-functor {i} {j} {A} {B} {P} {Q} f0 f1 = λ g → λ b → f1 _ (g (f0 b))
{-# INLINE Πᵉ-functor #-}

Πᵉ-iso-cong : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (f0 : B → A) → {is-exo-iso f0}
             → (f1 : (b : B) → P (f0 b) → Q (b)) → {(b : B) → is-exo-iso (f1 b)}
             → Πᵉ A P ≅ Πᵉ B Q
Πᵉ-iso-cong {i} {j} {A} {B} {P} {Q} f0 {(f0' ,ᵉ lh ,ᵉ rh)} f1 {G}
 = Πᵉ-functor f0 (λ (b : B) → (f1 b)) ,ᵉ
   Πᵉ-functor f0' (λ (a : A) → (exo-tr P (rh a)) ∘ᵉ (pr1ᵉ (G (f0' a)))),ᵉ
   (λ f → funextᵉ λ a → exo-concat
                                   (exo-tr-fam-ap {i} {j} {A} {P} {f0 (f0' a)} {a} {rh a}
                                                       {(pr1ᵉ (G (f0' a))) ∘ᵉ (f1 (f0' a))} {idᵉ {j} {P (f0 (f0' a))}}
                                                       {f (f0 (f0' a))} (funextᵉ (λ x → pr1ᵉ (pr2ᵉ (G (f0' a))) x)))
                                   (exo-apd {i} {j} {A} {P} (f) {f0 (f0' a)} {a} (rh a))) ,ᵉ
   (λ f → funextᵉ λ b → exo-concat
                                   (exo-ap (f1 b)
                                   (exo-ap-tr {i} {j} {A} {P} {f0 (f0' (f0 b))} {f0 b}
                                      {rh (f0 b)} {exo-ap f0 (lh b)} 
                                       (UIPᵉ {i} {A} {f0 (f0' (f0 b))} {f0 b} (rh (f0 b)) (exo-ap f0 (lh b)))))
                                   (exo-concat
                                    (exo-ap (f1 b) (exo-inv (exo-tr-ap {i} {j} {B} {A} {f0} {P} {_} {_} _
                                                                        {(pr1ᵉ (G (f0' (f0 b))) (f (f0' (f0 b))))})))
                                    (exo-concat
                                      (exo-ap-transport {i} {j} {B} {λ (x : B) → P (f0 x)} {Q} {f0' (f0 b)} {b}
                                                        (lh b) (f1) (pr1ᵉ (G (f0' (f0 b))) (f (f0' (f0 b)))))
                                      (exo-concat
                                       (exo-tr-fam-ap {i} {j} {B} {Q} {f0' (f0 b)} {b} {lh b}
                                                         {f1 (f0' (f0 b)) ∘ᵉ (pr1ᵉ (G (f0' (f0 b))))}
                                                         {idᵉ {j} {Q (f0' (f0 b))}} {f (f0' (f0 b))}
                                                         (funextᵉ (λ x → pr2ᵉ (pr2ᵉ (G (f0' (f0 b)))) x)))
                                       (exo-apd {i} {j} {B} {Q} (f) {f0' (f0 b)} {b} (lh b))))))


Πᵉ-iso-cong' : {i j : Level}{A B : UUᵉ i}{P : A → UUᵉ j}{Q : B → UUᵉ j}
             → (W : B ≅ A) 
             → (f1 : (b : B) → P ((pr1ᵉ W) b) ≅ Q (b))
             → Πᵉ A P ≅ Πᵉ B Q
Πᵉ-iso-cong' W V
             = Πᵉ-iso-cong (pr1ᵉ W) {pr2ᵉ W} (λ (b : _) → pr1ᵉ (V b)) {λ (b : _) → pr2ᵉ (V b)}


