{-# OPTIONS --without-K --exact-split --two-level --cumulativity #-}

module 2LTT.Cofibration.Funext_for_cofibrant_types where

open import 2LTT.Cofibration.isCofibrant public

module FUNEXT {i j : Level}{A : UUᵉ i} {B : A → UU j} {P : isCofibrant {i} A j} where
  FM = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P B))

  α : FM → Πᵉ A B
  α = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B))))

  β : Πᵉ A B → FM
  β = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))

  βα : (X : FM) → (β ∘ᵉ α) X =ᵉ X
  βα = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))))

  αβ : (X : Πᵉ A B) → (α ∘ᵉ β) X =ᵉ X
  αβ = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))))

  FEP : {f g : Πᵉ A B} → ((x : A) → Id (f x) (g x)) → Id (β f) (β g)
  FEP {f} {g} T = p
    where
     Y : A → UU j
     Y x = Σ (B x) (λ y → Id y (f x))

     f' g' : Πᵉ A Y
     f' x = (f x , refl)
     g' x = (g x , (T x) ⁻¹)

     fibers-of-Y-is-contr : (x : A) → is-contr (Y x)
     fibers-of-Y-is-contr x = path-type-is-contr {j} {B x} (f x)

     WFEP = isCofibrant-at.contr-preserve-witness (P Y)

     Πtype = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P Y))
     
     α' : Πtype → Πᵉ A Y
     α' = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y))))

     β' : Πᵉ A Y → Πtype
     β' = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))

     βα' : (X : Πtype) → (β' ∘ᵉ α') X =ᵉ X
     βα' = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))))

     αβ' : (X : Πᵉ A Y) → (α' ∘ᵉ β') X =ᵉ X
     αβ' = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))))

     p' : Id (β' f') (β' g')
     p' = (pr2 (WFEP fibers-of-Y-is-contr) (β' f')) · ((pr2 (WFEP fibers-of-Y-is-contr) (β' g')) ⁻¹)

     p : Id (β f) (β g)
     p = =ᵉ-to-Id (exo-ap {i ⊔ j} {i ⊔ j} β (funextᵉ {i} {j} λ a →
                                               exo-inv (exo-ap {j} {j} pr1 (happlyᵉ (αβ' f') a))))
              · (ap (λ u → β (λ a → pr1 ((α' u) a))) p' ·
         =ᵉ-to-Id (exo-ap {i ⊔ j} {i ⊔ j} β (funextᵉ {i} {j} λ a → (exo-ap {j} {j} pr1 (happlyᵉ (αβ' g') a)))))

Fib-Π-functor-isEquiv : {i j : Level}{A : UUᵉ i}{P Q : A → UU j} {F : (a : A) → P a → Q a}
                       → (W : isCofibrant {i} A j)
                       → ((a : A) → isEquiv {j} {j} (F a))
                       → Fib-isEquiv (isCofibrant-at.Π-fibrant-witness (W P))
                                      (isCofibrant-at.Π-fibrant-witness (W Q)) (Πᵉ-functor {i} {j} idᵉ F)
Fib-Π-functor-isEquiv {i} {j} {A} {P} {Q} {F} W K
  = invertibles-are-equiv {i ⊔ j} {i ⊔ j} _ (fP ∘ᵉ ((Πᵉ-functor {i} {j} idᵉ G) ∘ᵉ gQ) ,
                            (λ T → =ᵉ-to-Id (exo-ap (fP ∘ᵉ (Πᵉ-functor {i} {j} idᵉ G)) (gfQ (((Πᵉ-functor {i} {j} idᵉ F) ∘ᵉ gP) T))) ·
                                    (htpP T  · =ᵉ-to-Id (fgP T))) ,
                            λ T → =ᵉ-to-Id (exo-ap (fQ ∘ᵉ (Πᵉ-functor {i} {j} idᵉ F)) (gfP (((Πᵉ-functor {i} {j} idᵉ G) ∘ᵉ gQ) T))) ·
                                    (htpQ T  · =ᵉ-to-Id (fgQ T)))
  where 
  fP : (Πᵉ A P) → isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W P))
  fP = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (W P)))
  
  gP : isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W P)) → (Πᵉ A P)
  gP = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (W P))))

  gfP : (T : _) → gP (fP T) =ᵉ T
  gfP = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W P)))))

  fgP : (T : _) → fP (gP T) =ᵉ T
  fgP = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W P)))))
     
  fQ : (Πᵉ A Q) → isFibrant.fibrant-match  (isCofibrant-at.Π-fibrant-witness (W Q))
  fQ = pr1ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))

  gQ : isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W Q)) → (Πᵉ A Q)
  gQ = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q))))

  gfQ : (T : (Πᵉ A Q)) → gQ  (fQ T) =ᵉ T
  gfQ = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))))

  fgQ : (T : _) → fQ (gQ T) =ᵉ T
  fgQ = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))))

  G : (a : A) → Q a → P a
  G a = pr1 (equivs-are-invertible _ (K a))

  GF : (a : A) → (G a) ∘ (F a) ~ id
  GF a = pr1 (pr2 (equivs-are-invertible _ (K a)))

  FG : (a : A) → (F a) ∘ (G a) ~ id
  FG a = pr2 (pr2 (equivs-are-invertible _ (K a)))

  htpP : (T : _) → Id (fP ((Πᵉ-functor {i} {j} idᵉ G) ((Πᵉ-functor {i} {j} idᵉ F) (gP T)))) (fP (gP T))
  htpP T = FUNEXT.FEP {i} {j} {A} {P} {W} {f = (Πᵉ-functor {i} {j} idᵉ G) ((Πᵉ-functor {i} {j} idᵉ F) (gP T))} {g = gP T}
                     λ a → (GF a) (gP T a)

  htpQ : (T : _) → Id (fQ ((Πᵉ-functor {i} {j} idᵉ F) ((Πᵉ-functor {i} {j} idᵉ G) (gQ T)))) (fQ (gQ T))
  htpQ T = FUNEXT.FEP {i} {j} {A} {Q} {W} {f = (Πᵉ-functor {i} {j} idᵉ F) ((Πᵉ-functor {i} {j} idᵉ G) (gQ T))} {g = gQ T}
                     λ a → (FG a) (gQ T a)


new-funext-to-cofib : {i j : Level} {A : UUᵉ i} →
                      (F : (Y : A → UU j) → isFibrant {i ⊔ j} (Πᵉ {i} {j} A Y)) →
                      ((Y : A → UU j) → ((f g : Πᵉ {i} {j} A Y) → (Πᵉ {i} {j} A (λ a → Id {j} (f a) (g a))) →
                      Id {i ⊔ j} (pr1ᵉ (isFibrant.fibrant-witness (F Y)) f) (pr1ᵉ (isFibrant.fibrant-witness (F Y)) g))) →
                      isCofibrant {i} A j
Π-fibrant-witness (new-funext-to-cofib F Q Y) = F Y
contr-preserve-witness (new-funext-to-cofib {A = A} F Q Y)
  = λ T → h (λ a → pr1 (T a)) , λ x → =ᵉ-to-Id (exo-inv (hk x)) · Q Y (k x) (λ a → pr1 (T a)) (λ a → pr2 (T a) (k x a))
    where
      FM = isFibrant.fibrant-match (F Y)

      k : FM → Πᵉ A Y
      k = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (F Y)))

      h : Πᵉ A Y → FM
      h = pr1ᵉ (isFibrant.fibrant-witness (F Y))

      hk : (X : FM) → (h ∘ᵉ k) X =ᵉ X
      hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (F Y))))
                      
