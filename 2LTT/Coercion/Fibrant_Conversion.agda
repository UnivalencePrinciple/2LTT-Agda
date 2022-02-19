{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Coercion.Fibrant_Conversion where

open import 2LTT.Exotypes public
open import 2LTT.Types public


C : {i : Level} → (UU i) → (UUᵉ i)
C A = A

c : {i : Level}{A : UU i} → A → C A
c a = a


-----coprodᵉ
map-coprodᵉ : {i j : Level}{A : UU i} {B : UU j} → (C A) +ᵉ (C B) → C (A + B)
map-coprodᵉ (inlᵉ x) = inl x 
map-coprodᵉ (inrᵉ y) = inr y

-----exo-empty
map-⊥ᵉ : ⊥ᵉ → C ⊥
map-⊥ᵉ = ex-falsoᵉ

-----exo-nat
map-ℕᵉ : ℕᵉ → C ℕ
map-ℕᵉ zeroᵉ = zero
map-ℕᵉ (succᵉ x) = succ (map-ℕᵉ x)

-----exo-equality
map-=ₛᵉ : {i : Level} {A : UU i} {u v : A} → (c u) =ₛᵉ (c v) → C (Id u v)
map-=ₛᵉ reflₛᵉ = refl

-----exo-universe
map-UUᵉ : {i : Level} → C (UU i) → UUᵉ i
map-UUᵉ {i} A = A 

-----exo-unit
map-⊤ᵉ : ⊤ᵉ → C ⊤
map-⊤ᵉ starᵉ = star

inv-map-⊤ᵉ : C ⊤ → ⊤ᵉ
inv-map-⊤ᵉ star = starᵉ

is-map-⊤ᵉ-iso : is-exo-iso map-⊤ᵉ
is-map-⊤ᵉ-iso = inv-map-⊤ᵉ , (reflₛᵉ , reflₛᵉ)

exo-iso-⊤ᵉ : ⊤ᵉ ≅ C ⊤
exo-iso-⊤ᵉ = map-⊤ᵉ , is-map-⊤ᵉ-iso

-----exo sigma
map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → C {i ⊔ j} (Σ {i} {j} A B) → Σᵉ {i} {j} (C A) (λ x → C (B x))
map-Σᵉ (a , b) = (a , b)

inv-map-Σᵉ : {i j : Level}{A : UU i}{B : A → UU j} → Σᵉ (C A) (λ x → C (B x)) → C (Σ A B)
inv-map-Σᵉ (a , b) = (a , b)

is-map-Σᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Σᵉ {i} {j} {A} {B})
is-map-Σᵉ-iso = inv-map-Σᵉ , (reflₛᵉ , reflₛᵉ)

-----exo product
map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → C (A × B) → (C A) ×ᵉ (C B)
map-×ᵉ (a , b) = (a , b)

inv-map-×ᵉ : {i j : Level}{A : UU i}{B : UU j} → (C A) ×ᵉ (C B) → C (A × B)
inv-map-×ᵉ (a , b) = (a , b)


-----exo dependent function                                 
map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) → Πᵉ (C A) (λ x → C (B x))
map-Πᵉ f a = f a

inv-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} → Πᵉ (C A) (λ x → C (B x)) → C (Π A B)
inv-map-Πᵉ f = λ a → f a

is-map-Πᵉ-iso : {i j : Level}{A : UU i}{B : A → UU j} → is-exo-iso (map-Πᵉ {i} {j} {A} {B})
is-map-Πᵉ-iso = inv-map-Πᵉ , (reflₛᵉ , reflₛᵉ)

exo-Πᵉ-equiv : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) ≅ Πᵉ (C A) (λ x → C (B x))
exo-Πᵉ-equiv = map-Πᵉ , is-map-Πᵉ-iso


----------
--FIBRANT CONVERSION
record isFibrant {i : Level}(B : UUᵉ i) : UUᵉ (lsuc i) where
  constructor isfibrant
  field
    fibrant-match : UU i
    fibrant-witness : C fibrant-match ≅ B

    
fibrant-conversion : {i : Level} → (B : UUᵉ i) → (isFibrant B) → UU i
fibrant-conversion B (isfibrant fibrant-match fibrant-witness) = fibrant-match

exo-type-is-left-inverse-of-fibrant-conversion : {i : Level}(B : UUᵉ i) → (p : isFibrant {i} B)
                                               → (C (fibrant-conversion B p)) ≅ B
exo-type-is-left-inverse-of-fibrant-conversion {i} B (isfibrant fibrant-match fibrant-witness) = fibrant-witness

exo-type-is-right-inverse-of-fibrant-conversion : {i : Level}(A : UU i)
                                                → (fibrant-conversion {i} (c A) (isfibrant A (≅-refl))) ≃ A
exo-type-is-right-inverse-of-fibrant-conversion {i} A = id , id-is-equiv


----------------------------------------
-----------POSTULATES about "coercion"

postulate
   T1-type : {i : Level} {A B : UU i} → C A =ₛᵉ C B → A =ₛᵉ B
   T2-⊤ : C ⊤ =ₛᵉ ⊤ᵉ
   T2-Σ : {i j : Level}{A : UU i}{B : A → UU j} → C (Σ A B) =ₛᵉ Σᵉ (C A) (λ x → C (B x))
   T2-Π : {i j : Level} {A : UU i}{B : A → UU j} → C (Π A B) =ₛᵉ Πᵉ (C A) (λ x → C (B x))
   T2-map-Πᵉ : {i j : Level} {A : UU i}{B : A → UU j} {x : C {i ⊔ j} (Π A B)} → map-Πᵉ x =ₛᵉ  exo-trᵉ idᵉ (T2-Π {i} {j}) x
   T3 : {i : Level} {A : UUᵉ i} {B : UU i} → A ≅ C B → Σᵉ (UU i) (λ D → A =ₛᵉ C D)

exo-eq-fibrant-match : {i : Level} {B : UUᵉ i} → isFibrant {i} B →  Σᵉ (UU i) (λ D → B =ₛᵉ C D)
exo-eq-fibrant-match {i} {B} (isfibrant fm fw) = T3 {i} {B} {fm} (≅-sym fw)

T1-term : {i : Level} {A : UU i} {a b : A} → c a =ₛᵉ c b → a =ₛ b
T1-term reflₛᵉ = reflₛ

T2-× :  {i j : Level}{A : UU i}{B : UU j} → C (A × B) =ₛᵉ (C A) ×ᵉ (C B)
T2-× {i} {j} {A} {B} = T2-Σ {i} {j} {A} {(λ _ → B)}

isFibrant-⊤ᵉ : isFibrant ⊤ᵉ
isFibrant-⊤ᵉ = isfibrant ⊤ (idtoiso T2-⊤)

isFibrant-Σ : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Σᵉ A B)
isFibrant-Σ {i} {j} {A = A} {B = B} (isfibrant fr P) Q
                = isfibrant
                  (Σ {i} {j} fr (λ x →  fibrant-conversion (B ((pr1ᵉ P) (c x))) (Q ((pr1ᵉ P) (c x)))))
                  (≅-trans (idtoiso T2-Σ) ((Σᵉ-iso-cong' {i} {j} P
                                                                 λ a → (exo-type-is-left-inverse-of-fibrant-conversion {j}
                                                                          (B ((pr1ᵉ P) (c a))) (Q ((pr1ᵉ P) (c a)))))))
isFibrant-× : {i j : Level}{A : UUᵉ i}{B : UUᵉ j}
              → isFibrant {i} A → isFibrant {j} B
              → isFibrant {i ⊔ j} (A ×ᵉ B)
isFibrant-× {i} {j} {A = A} {B = B} P Q = isFibrant-Σ {i} {j} {A = A} {B = (λ _ → B)} P (λ _ → Q)


isFibrant-Π : {i j : Level}{A : UUᵉ i}{B : A → UUᵉ j}
              → isFibrant {i} A → ((a : A) → isFibrant {j} (B a))
              → isFibrant {i ⊔ j} (Πᵉ A B)
isFibrant-Π {i} {j} {A = A} {B = B} (isfibrant fr P) Q
                = isfibrant
                  (Π {i} {j} fr (λ x →  fibrant-conversion (B ((pr1ᵉ P) (c x))) (Q ((pr1ᵉ P) (c x)))))
                  (≅-trans {i ⊔ j} {i ⊔ j} {i ⊔ j}
                       (idtoiso T2-Π)
                       (≅-sym (Πᵉ-iso-cong' {i} {j} (P) λ x →
                                            ≅-sym (exo-type-is-left-inverse-of-fibrant-conversion {j}
                                                      (B ((pr1ᵉ P) (c x))) (Q ((pr1ᵉ P) (c x)))))))                  

isFibrant-iso : {i : Level}{A B : UUᵉ i}
              → A ≅ B → isFibrant {i} A
              → isFibrant {i} B
isFibrant-iso {i} {A} {B} I (isfibrant fr fw)
                  = isfibrant fr (≅-trans fw I)

=ₛᵉ-to-Id : {i : Level} {A : UU i} {a b : A} → a =ₛᵉ b → Id a b
=ₛᵉ-to-Id reflₛᵉ = refl
     
is-contr-iso : {i : Level} {A B : UU i}
               → C A ≅ C B
               → is-contr A
               → is-contr B
is-contr-iso {i} (f , g , lh , rh) (a , P) = f a , λ b → (=ₛᵉ-to-Id (exo-invᵉ (happlyₛᵉ {i} {i} rh b)) · ap f (P (g b)))

iso-to-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B)
               → is-exo-iso f → isEquiv f
iso-to-equiv {i} {j} f (g , gf , fg) = invertibles-are-equiv {i} {j} f (g , (λ x → =ₛᵉ-to-Id (happlyₛᵉ gf x)) ,
                                                            (λ x → =ₛᵉ-to-Id (happlyₛᵉ fg x)))



----------------------------------------------------------------------------------------------
function-transfer : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                    → (P : isFibrant {i} A) → (Q : isFibrant {j} B)
                    → (F : A → B) → (isFibrant.fibrant-match P → isFibrant.fibrant-match Q)
function-transfer {i} {j} {A} {B} P Q F = λ x → g' (F (f x)) 
  where
   A' : UU i
   A' = isFibrant.fibrant-match P

   f : A' → A
   f = pr1ᵉ (isFibrant.fibrant-witness P)

   B'  : UU j
   B' = isFibrant.fibrant-match Q

   g' : B → B'
   g' = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q))


function-transfer-isEquiv : {i j : Level} {A : UUᵉ i} {B : UUᵉ j}
                            → (P : isFibrant {i} A) → (Q : isFibrant {j} B)
                            → (F : A → B) → is-exo-iso F → isEquiv (function-transfer P Q F)
function-transfer-isEquiv {i} {j} {A} {B} P Q F W = invertibles-are-equiv {i} {j} _ ((λ y → f' (F' (g y))) ,
                                                                             (λ a → =ₛᵉ-to-Id
                                                                                 (exo-concatᵉ
                                                                                 (exo-apᵉ {j} {i} (f' ∘ᵉ F') (happlyₛᵉ gg' (F (f a))))
                                                                                   (exo-concatᵉ
                                                                                     (exo-apᵉ {i} {i} f' (happlyₛᵉ F'F (f a)))
                                                                                     (happlyₛᵉ f'f a)))) ,
                                                                             (λ b → =ₛᵉ-to-Id
                                                                                 (exo-concatᵉ
                                                                                 (exo-apᵉ {i} {j} (g' ∘ᵉ F) (happlyₛᵉ ff' (F' (g b))))
                                                                                   (exo-concatᵉ
                                                                                     (exo-apᵉ {j} {j} g' (happlyₛᵉ FF' (g b)))
                                                                                     (happlyₛᵉ g'g b)))))                            
 where
   A' : UU i
   A' = isFibrant.fibrant-match P

   f : A' → A
   f = pr1ᵉ (isFibrant.fibrant-witness P)

   f' : A → A'
   f' = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness P))

   f'f : f' ∘ᵉ f =ₛᵉ idᵉ
   f'f = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

   ff' : f ∘ᵉ f' =ₛᵉ idᵉ
   ff' = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness P)))

   B'  : UU j
   B' = isFibrant.fibrant-match Q

   g : B' → B
   g = pr1ᵉ (isFibrant.fibrant-witness Q)

   g' : B → B'
   g' = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q))

   g'g : g' ∘ᵉ g =ₛᵉ idᵉ
   g'g = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q)))

   gg' : g ∘ᵉ g' =ₛᵉ idᵉ
   gg' = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness Q)))

   F' : B → A
   F' = pr1ᵉ W

   F'F : F' ∘ᵉ F =ₛᵉ idᵉ
   F'F = pr1ᵉ (pr2ᵉ W)

   FF' : F ∘ᵉ F' =ₛᵉ idᵉ
   FF' = pr2ᵉ (pr2ᵉ W)
