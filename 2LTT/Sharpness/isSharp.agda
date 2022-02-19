{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Sharpness.isSharp where

open import 2LTT.Cofibration.isCofibrant public

--precomposition maps of cofibrant types
precomp : {i j : Level} (A : UUᵉ i) (P : isCofibrant {i} A)
          (RA : UU i) (f : A → RA) (Y : RA → UU j)
          → Π RA Y → isFibrant.fibrant-match (isCofibrant-at.Π-fibrant-witness
                                                       (P j (λ (a : A) → Y (f a))))
precomp {i} {j} A P RA f Y = let (iscofibrant-at (isfibrant crA (F , G , htpy)) ctpA) = P j (λ a → Y (f a))
                   in λ u → G (λ x → u (f x))
          

--For exo-type B, being sharp
record isSharp {i : Level} (B : UUᵉ i) : SSetω where
  eta-equality
  constructor issharp
  field 
    cofibrant-witness : isCofibrant {i} B
    fibrant-replacement : UU i
    fibrant-transfer : B → fibrant-replacement
    precomp-is-equiv : (j : Level) (Y : fibrant-replacement → UU j)
                       → isEquiv {i ⊔ j} {i ⊔ j} (precomp {i} {j} B cofibrant-witness fibrant-replacement fibrant-transfer Y)


-------------------------------------------------------------------------
--If A and B are exo-equal exo-types, then A is sharp iff B is sharp.
=ₛᵉ-preserve-Sharp : {i : Level} {A B : UUᵉ i}
                     → A =ₛᵉ B
                     → isSharp {i} A
                     → isSharp {i} B 
=ₛᵉ-preserve-Sharp reflₛᵉ P = P

--------------------------------------------------------------------------
--Fibrant types are sharp
is-Fibrant-Sharp : {i : Level}{B : UU i}
                   → isSharp {i} B
is-Fibrant-Sharp {i} {B} = issharp (is-Fibrant-Cofibrant {i} B )
                                    B
                                    id
                                    λ j Y → id-is-equiv


is-Fibrant-Sharp' : {i : Level}{B : UUᵉ i} → isFibrant {i} B → isSharp {i} B
is-Fibrant-Sharp' {i} {B} (isfibrant fm fw) =  let (D , d) =  (T3 {i} {B} {fm} (≅-sym fw)) in
                                                   =ₛᵉ-preserve-Sharp (exo-invᵉ d) (is-Fibrant-Sharp {i} {D})

---------------------------------------------------------------------------
--⊥ᵉ is sharp
is-⊥ᵉ-Sharp : isSharp ⊥ᵉ
is-⊥ᵉ-Sharp = issharp ⊥ᵉ-is-cofibrant
                      ⊥
                      map-⊥ᵉ
                      λ j Y → invertibles-are-equiv _ ((λ {star → ind-⊥}) ,
                                                         (λ x → funext λ {x₁ → ex-falso x₁}) ,
                                                         (λ x → refl))


-------------------------------------------------------------------------
--⊤̂ᵉ is sharp
is-⊤ᵉ-Sharp : isSharp {lzero} ⊤ᵉ
is-⊤ᵉ-Sharp = issharp (⊤ᵉ-is-cofibrant)
                      ⊤
                      map-⊤ᵉ
                      λ j Y → id-is-equiv

-----------------------------------------------------------------------------------------
--If A and B are sharp, then A + B is sharp
+ᵉ-preserve-Sharp : {i j : Level}{A : UUᵉ i}{B : UUᵉ j}
                               → isSharp {i} A → isSharp {j} B
                               → isSharp {i ⊔ j} (A +ᵉ B)
+ᵉ-preserve-Sharp {i} {j} {A} {B} (issharp cwA frA ftA pcmpeqA)
                                      (issharp cwB frB ftB pcmpeqB)
 = issharp (+ᵉ-preserve-Cofibrant {i} {j} {A} {B} cwA cwB)
           (_+_ {i} {j} frA frB)
           (λ {(inlᵉ x) → inl (ftA x) ; (inrᵉ x) → inr (ftB x)})
           λ k Y
           → let f = (precomp {i ⊔ j} {k} (_+ᵉ_ {i} {j} A B) (+ᵉ-preserve-Cofibrant cwA cwB) (frA + frB)
                                                                       (λ { (inlᵉ x) → inl (ftA x) ; (inrᵉ x) → inr (ftB x) }) Y) ;
                  g = (Π-+-expansion {i} {j} {k} {frA} {frB} {Y}) ;
                  f' = (×-of-maps {i ⊔ k} {i ⊔ k} {j ⊔ k} {j ⊔ k} (precomp A cwA frA ftA (λ x₁ → Y (inl x₁)))
                                                                     (precomp B cwB frB ftB (λ x₁ → Y (inr x₁))));
                  g' = id ;
                  CS = λ a → pair⁼ _ _ (refl , refl)
              in First-3-out-of-4-rule {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} {i ⊔ j ⊔ k} {i ⊔ j ⊔ k}
                                  f f' g g'
                                  CS
                                  (×-of-maps-is-equiv (pcmpeqA k (λ x₁ → Y (inl x₁))) (pcmpeqB k (λ x₁ → Y (inr x₁))))
                                  (Π-+-expansion-is-equiv {i} {j} {k})
                                  id-is-equiv
