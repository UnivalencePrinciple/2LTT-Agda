{-# OPTIONS --without-K --exact-split --two-level --cumulativity --type-in-type #-}

module 2LTT.Sharpness.isSharp_equiv_definitions where

open import 2LTT.Sharpness.isSharp public

Precomp-isEquiv : {i j : Level} (B : UUᵉ i) → (isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) → (Y : RB → UU j) → UU (i ⊔ j)
Precomp-isEquiv {i} {j} B F RB r Y = Fib-isEquiv {i ⊔ j} {i ⊔ j} {Π RB Y} {Πᵉ B (Y ∘ᵉ r)}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (F (Y ∘ᵉ r)))
                                                           (precomp B RB r Y)

Has-Section-Precomp : {i j : Level} (B : UUᵉ i) → (isCofibrant {i} B j) →
                      (RB : UU i) → (r : B → RB) → (Y : RB → UU j) → UU (i ⊔ j)
Has-Section-Precomp {i} {j} B F RB r Y =  has-section {i ⊔ j} {i ⊔ j}
                                                           (Fib-map {i ⊔ j} {i ⊔ j} {Π RB Y} {Πᵉ B (Y ∘ᵉ r)}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (F (Y ∘ᵉ r)))
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
                                       (λ x → auxiliary-map
                                                (pr1 (P Y) (Fib-map (isfibrant (Π RB Y) ≅-refl)
                                                  (Π-fibrant-witness (F (Y ∘ᵉ r))) (λ T → T ∘ᵉ r) x))
                                                x
                                                ((pr2 (P Y)) (h (x ∘ᵉ r)))) , 
                                       pr2 (P Y))
  where
    FM = fibrant-match (Π-fibrant-witness (F (Y ∘ᵉ r)))

    h : Πᵉ B (Y ∘ᵉ r) → FM
    h = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r))))

    k : FM → Πᵉ B (Y ∘ᵉ r)
    k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r)))))

    kh : (X : Πᵉ B (Y ∘ᵉ r)) → k (h X) =ᵉ X
    kh = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r))))))

    auxiliary-map : (f g : Π RB Y) → Id (h (f ∘ᵉ r)) (h (g ∘ᵉ r)) → Id f g
    auxiliary-map f g X = funext (λ c → (pr1 (P (λ a → Id {j} (f a) (g a))))
                              (pr1ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ a → Id {j} (f a) (g a)) ∘ᵉ r))))
                              λ b → =ᵉ-to-Id (happlyᵉ (exo-inv (kh (f ∘ᵉ r))) b)
                                       · ((ap {i ⊔ j} {j} (λ u → (k u) b) X)
                                          · =ᵉ-to-Id (happlyᵉ (kh (g ∘ᵉ r)) b) ))
                              c)

Lemma-2-3--3->2 : {i j : Level} (B : UUᵉ i) →
                  (F : isCofibrant B j) →
                  (RB : UU i) → (r : B → RB) →
                  ((Z : UU j) → Precomp-isEquiv {i} {j} B F RB r (λ _ → Z)) →                   
                  ((Y : RB → UU j) → Has-Section-Precomp {i} {j} B F RB r Y)
Lemma-2-3--3->2 {i} {j} B F RB r P Y = sec-map , section-proof
  where    
    Z = Σ RB Y
    
    FM = fibrant-match (Π-fibrant-witness (F (Y ∘ᵉ r)))

    h : Πᵉ B (Y ∘ᵉ r) → FM
    h = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r))))

    k : FM → Πᵉ B (Y ∘ᵉ r)
    k = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r)))))

    hk : (X : FM) → h (k X) =ᵉ X
    hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F (Y ∘ᵉ r))))))
    
    FM' = fibrant-match (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r)))

    h' : Πᵉ B ((λ _ → Z) ∘ᵉ r) → FM'
    h' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r))))

    k' : FM' → Πᵉ B ((λ _ → Z) ∘ᵉ r)
    k' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r)))))

    kh' : (X : Πᵉ B ((λ _ → Z) ∘ᵉ r)) → k' (h' X) =ᵉ X
    kh' = pr1ᵉ (pr2ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r))))))

    σ = (inv _ (P Z))
    β = (Fib-map (isfibrant _ ≅-refl) (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r))) (precomp B RB r (λ _ → Z)))

    βσ : (u : FM') → Id (β (σ u)) u
    βσ = Fib-left-htpy (isfibrant _ ≅-refl) (Π-fibrant-witness (F ((λ _ → Z) ∘ᵉ r))) (precomp B RB r (λ _ → Z)) (P Z)

    FM'' = fibrant-match (Π-fibrant-witness (F ((λ _ → RB) ∘ᵉ r)))

    h'' : Πᵉ B ((λ _ → RB) ∘ᵉ r) → FM''
    h'' = pr1ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ _ → RB) ∘ᵉ r))))

    k'' : FM'' → Πᵉ B ((λ _ → RB) ∘ᵉ r)
    k'' = pr1ᵉ (pr2ᵉ (fibrant-witness (Π-fibrant-witness (F ((λ _ → RB) ∘ᵉ r)))))
    
    σ' = (inv _ (P RB))
    β' = (Fib-map (isfibrant _ ≅-refl) (Π-fibrant-witness (F ((λ _ → RB) ∘ᵉ r))) (precomp B RB r (λ _ → RB)))

    σβ' : (u : (RB → RB)) → Id (σ' (β' u)) u
    σβ' = Fib-right-htpy (isfibrant _ ≅-refl) (Π-fibrant-witness (F ((λ _ → RB) ∘ᵉ r))) (precomp B RB r (λ _ → RB)) (P RB)
    
    aux-map : (f : Πᵉ B (Y ∘ᵉ r)) → (B → Z)
    aux-map f b = (r b) , (f b)

    aux-eq : (u : RB → Z) →
              ((precomp B RB r (λ _ → Z)) u) =ᵉ ((k' ∘ᵉ β) u)
    aux-eq u = exo-inv (kh' ((precomp B RB r (λ _ → Z)) u))

    q : (f : Πᵉ B (Y ∘ᵉ r)) → (b : B) →
        Id (pr1 ((σ (h' (aux-map f))) (r b))) (r b)
    q f b = ap {i} {i} pr1
                   ((=ᵉ-to-Id (happlyᵉ (aux-eq (σ (h' (aux-map f)))) b)) ·
                    (ap {i} {i} (λ u → (k' (u (h' (aux-map f)))) b) (funext βσ) · =ᵉ-to-Id (happlyᵉ (kh' (aux-map f)) b)))

    q' : (f : Πᵉ B (Y ∘ᵉ r)) → Id (h'' ((pr1 ∘ (σ (h' (aux-map f)))) ∘ᵉ r)) (h'' r)
    q' f = FUNEXT.FEP {i} {i} {B} {λ _ → RB} {F} (q f)

    p : (f : Πᵉ B (Y ∘ᵉ r)) → Id (pr1 ∘ (σ (h' (aux-map f)))) id
    p f = ((σβ' (λ c' → pr1 ((σ (h' (aux-map f))) c'))) ⁻¹) · ((ap σ' (q' f)) · σβ' id)

    sec-map : FM → Π RB Y
    sec-map x = λ c → tr Y (happly (p (k x)) c) (pr2 (σ (h' (aux-map (k x))) c))

    aux-eq2 : (x : FM) → (b : B) → Id (r b , sec-map x (r b)) (aux-map (k x) b)
    aux-eq2 x b =  (lift {i} {j} {RB} {Y} {r b} (σ (h' (aux-map (k x))) (r b)) (happly (p (k x)) (r b))) ⁻¹ ·
                 ((=ᵉ-to-Id (happlyᵉ (aux-eq (σ (h' (aux-map (k x))))) b)) ·
                    (ap {i} {i} (λ u → (k' (u (h' (aux-map (k x))))) b) (funext βσ) · =ᵉ-to-Id (happlyᵉ (kh' (aux-map (k x))) b)))

    aux-eq3 : (x : FM) → (b : B) → Id (sec-map x (r b)) ((k x) b)
    aux-eq3 x b = (apd (sec-map x) (pr1 (inv-dep-pair⁼ _ _ (aux-eq2 x b)))) ⁻¹ · (pr2 (inv-dep-pair⁼ _ _ (aux-eq2 x b))) 

    fib-precomp = Fib-map {i ⊔ j} {i ⊔ j} {Π RB Y} {Πᵉ B (Y ∘ᵉ r)}
                                                           (isfibrant _ ≅-refl)
                                                           (isCofibrant-at.Π-fibrant-witness (F (Y ∘ᵉ r)))
                                                           (precomp B RB r Y)

    section-proof : (x : FM) → Id (fib-precomp (sec-map x)) x
    section-proof x =  FUNEXT.FEP {i ⊔ j} {i ⊔ j} {B} {Y ∘ᵉ r} {F} (aux-eq3 x) · (=ᵉ-to-Id (hk x))
