{-# OPTIONS --without-K --exact-split --two-level --type-in-type #-}

module 2LTT_C.Sharpness.isSharp_equiv_definitions where

open import 2LTT_C.Sharpness.isSharp public

Precomp-isEquiv : {i j : Level} (B : UUᵉ i) → (isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) → (Y : RB → UU j) → UU (i ⊔ j)
Precomp-isEquiv {i} {j} B F RB r Y = Fib-isEquiv {i ⊔ j} {i ⊔ j} {C (Π RB Y)} {Πᵉ B (λ b → C (Y (r b)))}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (F (λ b → Y (r b))))
                                                           (precomp B RB r Y)

Has-Section-Precomp : {i j : Level} (B : UUᵉ i) → (isCofibrant {i} B j) →
                      (RB : UU i) → (r : B → RB) → (Y : RB → UU j) → UU (i ⊔ j)
Has-Section-Precomp {i} {j} B F RB r Y =  has-section {i ⊔ j} {i ⊔ j}
                                                      (Fib-map {i ⊔ j} {i ⊔ j} {C (Π RB Y)} {Πᵉ B  (λ b → C (Y (r b)))}
                                                      (isfibrant _ ≅-refl)
                                                      (isCofibrant-at.Π-fibrant-witness (F (λ b → Y (r b))))
                                                      (precomp B RB r Y))

Lemma-2-3--1->2 : {i j : Level} (B : UUᵉ i) →
                  (F : isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) →
                  ((Y : RB → UU j) → Precomp-isEquiv {i} {j} B F RB r Y) →
                  ((Y : RB → UU j) → Has-Section-Precomp {i} {j} B F RB r Y)
Lemma-2-3--1->2 B F RB r = λ P Y → (inv _ (P Y)) , inv-is-section _ (P Y)


Lemma-2-3--1->3 : {i j : Level} (B : UUᵉ i) →
                  (F : isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) →
                  ((Y : RB → UU j) → Precomp-isEquiv {i} {j} B F RB r Y) →
                  (Z : UU j) → Precomp-isEquiv {i} {j} B F RB r (λ _ → Z)
Lemma-2-3--1->3 B F RB r K =  λ Z → K (λ _ → Z)


Lemma-2-3--2->1 : {i j : Level} (B : UUᵉ i) →
                  (F : isCofibrant {i} B j) →
                  (RB : UU i) → (r : B → RB) →
                  ((Y : RB → UU j) → Has-Section-Precomp {i} {j} B F RB r Y ) →
                  ((Y : RB → UU j) → Precomp-isEquiv {i} {j} B F RB r Y)
Lemma-2-3--2->1 {i} {j} B F RB r P Y = invertibles-are-equiv _
                                       ((pr1 (P Y)) ,
                                       (λ T → auxiliary-map
                                                (pr1 (P Y) (Fib-map (isfibrant (Π RB Y) exo-Πᵉ-equiv)
                                                  (Π-fibrant-witness (F (λ a → Y (r a)))) (λ S b → S (c (r b))) T))
                                                T
                                                ((pr2 (P Y)) (ic (h λ x → c (T (r x)))))) , 
                                       pr2 (P Y))
  where
    FM = fibrant-match (Π-fibrant-witness (F (λ b → Y (r b))))

    h : Πᵉ B (λ b → C (Y (r b))) → C FM
    h = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (λ b → Y (r b)))))

    k : C FM → Πᵉ B (λ b → C (Y (r b)))
    k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ b → Y (r b))))))

    kh : (X : Πᵉ B (λ b → C (Y (r b)))) → k (h X) =ᵉ X
    kh = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ b → Y (r b)))))))

    auxiliary-map : (f g : Π RB Y) → Id (ic (h (λ x → c (f (r x))))) (ic (h (λ x → c (g (r x))))) → Id f g
    auxiliary-map f g X = funext (λ d → (pr1 (P (λ a → Id {j} (f a) (g a))))
                                        (ic (pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ a → Id {j} (f a) (g a)) (r x)))))
                                          λ b → c (=ᵉ-to-Id (happlyᵉ (exo-inv (kh (λ x → c (f (r x))))) b)
                                                   · (ap (λ x → ic ((k (c x)) b)) X
                                                   · =ᵉ-to-Id (happlyᵉ (kh (λ x → c (g (r x)))) b)))))
                                        d)
                                        
Lemma-2-3--3->2 : {i j : Level} (B : UUᵉ i) →
                  (F : isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) →
                  ((Z : UU j) → Precomp-isEquiv {i} {j} B F RB r (λ _ → Z)) →                   
                  ((Y : RB → UU j) → Has-Section-Precomp {i} {j} B F RB r Y)
Lemma-2-3--3->2 {i} {j} B F RB r P Y = sec-map , section-proof
  where    
    Z = Σ RB Y
    
    FM = fibrant-match (Π-fibrant-witness (F (λ x → Y (r x))))

    h : Πᵉ B (λ x → C (Y (r x))) → C FM
    h = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → Y (r x)))))

    k : C FM → Πᵉ B (λ x → C (Y (r x)))
    k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → Y (r x))))))

    hk : (X : C FM) → h (k X) =ᵉ X
    hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → Y (r x)))))))
    
    FM' = fibrant-match (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x))))

    h' : Πᵉ B (λ x → C ((λ _ → Z) (r x))) → C FM'
    h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x)))))

    k' : C FM' → Πᵉ B (λ x → C ((λ _ → Z) (r x)))
    k' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x))))))

    kh' : (X : Πᵉ B (λ x → C ((λ _ → Z) (r x)))) → k' (h' X) =ᵉ X
    kh' = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x)))))))

    σ = (inv _ (P Z))
    β = (Fib-map (isfibrant _ ≅-refl) (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x)))) (precomp B RB r (λ _ → Z)))

    βσ : (u : FM') → Id (β (σ u)) u
    βσ = Fib-left-htpy (isfibrant _ ≅-refl) (Π-fibrant-witness (F (λ x → (λ _ → Z) (r x)))) (precomp B RB r (λ _ → Z)) (P Z)

    FM'' = fibrant-match (Π-fibrant-witness (F (λ x → (λ _ → RB) (r x))))

    h'' : Πᵉ B (λ x → C ((λ _ → RB) (r x))) → C FM''
    h'' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ _ → RB) (r x)))))

    k'' : C FM'' → Πᵉ B (λ x → C ((λ _ → RB) (r x)))
    k'' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (λ x → (λ _ → RB) (r x))))))
    
    σ' = (inv _ (P RB))
    β' = (Fib-map (isfibrant _ ≅-refl) (Π-fibrant-witness (F (λ x → (λ _ → RB) (r x)))) (precomp B RB r (λ _ → RB)))

    σβ' : (u : (RB → RB)) → Id (σ' (β' u)) u
    σβ' = Fib-right-htpy (isfibrant _ ≅-refl) (Π-fibrant-witness (F (λ x → (λ _ → RB) (r x)))) (precomp B RB r (λ _ → RB)) (P RB)
    
    aux-map : (f : Πᵉ B (λ x → C (Y (r x)))) → (B → Z)
    aux-map f b = (r b) , ic (f b)

    aux-eq : (u : RB → Z) →
              ((precomp B RB r (λ _ → Z)) (c u)) =ᵉ (λ b → (k' (c (β u))) b)
    aux-eq u = exo-inv (kh' ((precomp B RB r (λ _ → Z)) (c u)))

    q : (f : Πᵉ B (λ x → C (Y (r x)))) → (b : B) →
        Id (pr1 ((σ (ic (h' (λ x → c ((aux-map f) x))))) (r b))) (r b)
    q f b = ap pr1 (=ᵉ-to-Id (happlyᵉ (aux-eq (σ (ic (h' (λ x → c ((aux-map f) x)))))) b)
                    · (ap (λ u → ic (k' (c (u (ic (h' λ x → c ((aux-map f) x))))) b)) (funext βσ)
                    · =ᵉ-to-Id (happlyᵉ (kh' λ x → c ((aux-map f) x)) b)))

    q' : (f : Πᵉ B  (λ x → C (Y (r x)))) →
        Id (ic (h'' (λ x → c ((pr1 ((σ (ic (h' (λ x → c ((aux-map f) x))))) (r x)))))))
           (ic (h'' (λ x → c (r x))))
    q' f = FUNEXT.FEP {i} {i} {B} {λ _ → RB} {F} (q f)

    p : (f : Πᵉ B (λ x → C (Y (r x)))) → Id (pr1 ∘ (σ (ic (h' (λ x → c ((aux-map f) x)))))) id 
    p f = ((σβ' (λ c' → pr1 ((σ (ic (h' (λ x → c ((aux-map f) x))))) c'))) ⁻¹) · ((ap σ' (q' f)) · σβ' id)

    sec-map : FM → Π RB Y
    sec-map x = λ d → tr Y (happly (p (k (c x))) d) (pr2 (σ (ic (h' λ s → c ((aux-map (k (c x))) s))) d))

    aux-eq2 : (x : FM) → (b : B) → Id (r b , sec-map x (r b)) (aux-map (k (c x)) b)
    aux-eq2 x b = (lift (σ (ic (h' λ s → c ((aux-map (k (c x))) s))) (r b)) (happly (p (k (c x))) (r b))) ⁻¹
                  · (=ᵉ-to-Id (happlyᵉ (aux-eq (σ (ic (h' λ s → c ((aux-map (k (c x))) s))))) b)
                  · (ap (λ u → ic (k' (c (u (ic (h' λ s → c ((aux-map (k (c x))) s))))) b)) (funext βσ)
                  · =ᵉ-to-Id (happlyᵉ (kh' λ s → c (aux-map (k (c x)) s)) b)))

    aux-eq3 : (x : FM) → (b : B) → Id (sec-map x (r b)) (ic ((k (c x)) b))
    aux-eq3 x b = (apd (sec-map x) (pr1 (inv-dep-pair⁼ _ _ (aux-eq2 x b)))) ⁻¹ · (pr2 (inv-dep-pair⁼ _ _ (aux-eq2 x b))) 

    fib-precomp = Fib-map {i ⊔ j} {i ⊔ j} {C (Π RB Y)} {Πᵉ B (λ x → C (Y (r x)))}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (F (λ x → Y (r x))))
                                                           (precomp B RB r Y)

    section-proof : (x : FM) → Id (fib-precomp (sec-map x)) x
    section-proof x =  FUNEXT.FEP {i ⊔ j} {i ⊔ j} {B} {λ x → Y (r x)} {F} (aux-eq3 x) · =ᵉ-to-Id (hk (c x))
