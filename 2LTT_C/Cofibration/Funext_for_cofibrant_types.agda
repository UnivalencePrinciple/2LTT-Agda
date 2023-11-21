{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Cofibration.Funext_for_cofibrant_types where

open import 2LTT_C.Cofibration.isCofibrant public

module FUNEXT {i j : Level}{A : UUᵉ i} {B : A → UU j} {P : isCofibrant {i} A j} where
  FM = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P B))

  α : C FM → Πᵉ A (λ a → C (B a))
  α = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B))))

  β : Πᵉ A (λ a → C (B a)) → C FM
  β = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))

  βα : (X : C FM) → (β ∘ᵉ α) X =ᵉ X
  βα = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))))

  αβ : (X : Πᵉ A (λ a → C (B a))) → (α ∘ᵉ β) X =ᵉ X
  αβ = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P B)))))

  FEP : {f g : Πᵉ A (λ a → C (B a))} → ((x : A) → Id (ic (f x)) (ic (g x))) → Id (ic (β f)) (ic (β g))
  FEP {f} {g} T = p
    where
     Y : A → UU j
     Y x = Σ (B x) (λ y → Id y (ic (f x)))

     f' g' : Πᵉ A (λ a → C (Y a))
     f' x = c (ic (f x) , refl)
     g' x = c (ic (g x) , (T x) ⁻¹)

     fibers-of-Y-is-contr : (x : A) → is-contr (Y x)
     fibers-of-Y-is-contr x = path-type-is-contr {j} {B x} (ic (f x))

     WFEP = isCofibrant-at.contr-preserve-witness (P Y)

     Πtype = isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (P Y))
     
     α' : C Πtype → Πᵉ A (λ a → C (Y a))
     α' = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y))))

     β' : Πᵉ A (λ a → C (Y a)) → C Πtype
     β' = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))

     βα' : (X : C Πtype) → (β' ∘ᵉ α') X =ᵉ X
     βα' = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))))

     αβ' : (X : Πᵉ A (λ a → C (Y a))) → (α' ∘ᵉ β') X =ᵉ X
     αβ' = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (P Y)))))

     p' : Id (ic (β' f')) (ic (β' g'))
     p' = (pr2 (WFEP fibers-of-Y-is-contr) (ic (β' f'))) · ((pr2 (WFEP fibers-of-Y-is-contr) (ic (β' g'))) ⁻¹)

     p : Id (ic (β f)) (ic (β g))
     p = cic-eq (exo-ap β (funextᵉ λ a → exo-inv (exo-ap (λ {(c x) → c (pr1 x)}) (happlyᵉ (αβ' f') a)))) ·
         (ap (λ u → ic (β λ a → c (pr1 (ic (((α' (c u)) a)))))) p' ·
         cic-eq (exo-ap β (funextᵉ λ a → (exo-ap (λ {(c x) → c (pr1 x)}) (happlyᵉ (αβ' g') a)))))

Fib-Π-functor-isEquiv : {i j : Level}{A : UUᵉ i}{P Q : A → UU j} {F : (a : A) → P a → Q a}
                       → (W : isCofibrant A j)
                       → ((a : A) → isEquiv (F a))
                       → Fib-isEquiv (isCofibrant-at.Π-fibrant-witness (W P))
                                      (isCofibrant-at.Π-fibrant-witness (W Q)) (Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x))))
Fib-Π-functor-isEquiv {i} {j} {A} {P} {Q} {F} W K
  = invertibles-are-equiv _
       ((λ x → ic (fP ((Πᵉ-functor idᵉ (λ a x → c (G a (ic x)))) (gQ (c x))))) ,
       (λ T → cic-eq (exo-ap (fP ∘ᵉ (Πᵉ-functor {i} {j} idᵉ (λ a x → c (G a (ic x)))))
                                          (gfQ (((Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x)))) ∘ᵉ gP) (c T)))) ·
               (htpP (c T) · cic-eq (fgP (c T)))) ,
       λ T → cic-eq (exo-ap (fQ ∘ᵉ (Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x)))))
                                          (gfP (((Πᵉ-functor {i} {j} idᵉ (λ a x → c (G a (ic x)))) ∘ᵉ gQ) (c T)))) ·
               (htpQ (c T) · cic-eq (fgQ (c T))))
  where 
  fP : (Πᵉ A (λ a → C (P a))) → C (isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W P)))
  fP = pr1ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (W P)))
  
  gP : C (isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W P))) → (Πᵉ A (λ a → C (P a)))
  gP = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (isCofibrant-at.Π-fibrant-witness (W P))))

  gfP : (T : _) → gP (fP T) =ᵉ T
  gfP = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W P)))))

  fgP : (T : _) → fP (gP T) =ᵉ T
  fgP = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W P)))))
     
  fQ : (Πᵉ A (λ a → C (Q a))) → C (isFibrant.fibrant-match  (isCofibrant-at.Π-fibrant-witness (W Q)))
  fQ = pr1ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))

  gQ : C (isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness (W Q))) → (Πᵉ A (λ a → C (Q a)))
  gQ = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q))))

  gfQ : (T : (Πᵉ A (λ a → C (Q a)))) → gQ  (fQ T) =ᵉ T
  gfQ = pr1ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))))

  fgQ : (T : _) → fQ (gQ T) =ᵉ T
  fgQ = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness  (isCofibrant-at.Π-fibrant-witness (W Q)))))

  G : (a : A) → Q a → P a
  G a = pr1 (equivs-are-invertible _ (K a))

  GF : (a : A) → (G a) ∘ (F a) ~ id
  GF a = pr1 (pr2 (equivs-are-invertible _ (K a)))

  FG : (a : A) → (F a) ∘ (G a) ~ id
  FG a = pr2 (pr2 (equivs-are-invertible _ (K a)))

  htpP : (T : _) →
     Id (ic (fP ((Πᵉ-functor {i} {j} idᵉ (λ a x → c (G a (ic x)))) ((Πᵉ-functor {i} {j} idᵉ  (λ a x → c (F a (ic x)))) (gP T)))))
         (ic (fP (gP T)))
  htpP T = FUNEXT.FEP {i} {j} {A} {P} {W}
     {f = (Πᵉ-functor {i} {j} idᵉ  (λ a x → c (G a (ic x)))) ((Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x)))) (gP T))}
     {g = gP T} (λ a → (GF a) (ic (gP T a)))

  htpQ : (T : _) →
     Id (ic (fQ ((Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x)))) ((Πᵉ-functor {i} {j} idᵉ (λ a x → c (G a (ic x)))) (gQ T)))))
         (ic (fQ (gQ T)))
  htpQ T = FUNEXT.FEP {i} {j} {A} {Q} {W}
     {f = (Πᵉ-functor {i} {j} idᵉ (λ a x → c (F a (ic x)))) ((Πᵉ-functor {i} {j} idᵉ (λ a x → c (G a (ic x)))) (gQ T))}
     {g = gQ T} (λ a → (FG a) (ic (gQ T a)))


new-funext-to-cofib : {i j : Level} {A : UUᵉ i} →
                      (F : (Y : A → UU j) → isFibrant {i ⊔ j} (Πᵉ A (λ a → C (Y a)))) →
                      ((Y : A → UU j) → ((f g : Πᵉ A (λ a → C (Y a))) → (Πᵉ A (λ a → C (Id (ic (f a)) (ic (g a))))) →
                      Id (ic (pr1ᵉ (isFibrant.fibrant-witness (F Y)) f)) (ic (pr1ᵉ (isFibrant.fibrant-witness (F Y)) g)))) →
                      isCofibrant {i} A j
Π-fibrant-witness (new-funext-to-cofib F Q Y) = F Y
contr-preserve-witness (new-funext-to-cofib {A = A} F Q Y)
  = λ T →
    ic (h (λ a → c (pr1 (T a)))) ,
      λ x → =ᵉ-to-Id (exo-inv (hk (c x))) · Q Y (k (c x)) (λ a → c (pr1 (T a))) (λ a → c (pr2 (T a) (ic (k (c x) a))))
    where
      FM = isFibrant.fibrant-match (F Y)

      k : C FM → Πᵉ A (λ a → C (Y a))
      k = pr1ᵉ (pr2ᵉ (isFibrant.fibrant-witness (F Y)))

      h : Πᵉ A (λ a → C (Y a)) → C FM
      h = pr1ᵉ (isFibrant.fibrant-witness (F Y))

      hk : (X : C FM) → (h ∘ᵉ k) X =ᵉ X
      hk = pr2ᵉ (pr2ᵉ (pr2ᵉ (isFibrant.fibrant-witness (F Y))))
                      
