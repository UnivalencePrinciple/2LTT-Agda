{-# OPTIONS --without-K --exact-split --two-level #-}

module 2LTT_C.Types.Retraction where

open import 2LTT_C.Types.Functions
open import 2LTT_C.Types.Id_Type
open import 2LTT_C.Primitive
open import 2LTT_C.Types.Sigma
open import 2LTT_C.Types.Type_Hierarchy

--Source: Introduction to Univalent Foundations of Mathematics with Agda by
--Martín Hötzel Escardó


has-section : {i j : Level} {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
has-section f = Σ (_) (λ g → (f ∘ g) ~ id)

_◃_ : {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ◃ B = Σ (B → A) (λ f → has-section f)

retraction : {i j : Level} {A : UU i} {B : UU j}
             → A ◃ B → B → A
retraction (r , s , η) = r

section : {i j : Level} {A : UU i} {B : UU j}
             → A ◃ B → A → B
section (r , s , η) = s

retraction-equation :  {i j : Level} {A : UU i} {B : UU j}
                      → (p : A ◃ B)
                      → ((retraction {i} {j} p) ∘ (section {i} {j} p)) ~ id
retraction-equation (r , s , η) = η

id-◃ : {i : Level} (A : UU i) → A ◃ A
id-◃ A = id , id , λ x → refl

_◃∘_ : {i j k : Level}{A : UU i} {B : UU j} {C : UU k}
       → A ◃ B → B ◃ C → A ◃ C
_◃∘_ {i} {j} {k} (r , s , η) (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
   η'' = λ x → _≡⟨_⟩_ {i} (r (r' (s' (s x)))) (ap r (η' (s x)))
                (_≡⟨_⟩_ {i} (r (s x) ) (η x)          
                (x ▮))

_◃⟨_⟩_ : {i j k : Level}(A : UU i) {B : UU j} {C : UU k}
       → A ◃ B → B ◃ C → A ◃ C
A ◃⟨ p ⟩ q = p ◃∘ q

_◂ : {i : Level}(A : UU i) → A ◃ A
A ◂ = id-◃ A

retract-of-singleton : {i j : Level} {A : UU i} {B : UU j}
                       → B ◃ A → is-contr A → is-contr B
retract-of-singleton {i} {j} (r , s , η) (d , p) = (r d) , q
 where
  q = λ y → (_≡⟨_⟩_ {j} (r d) (ap r ((p (s y)) ⁻¹))
            (_≡⟨_⟩_  {j} (r (s y)) (η y)
            (y ▮ ))) ⁻¹

Nat : {i j k : Level} {A : UU i} → (A → UU j) → (A → UU k)
      → UU (i ⊔ j ⊔ k)
Nat {A = A} B C = (a : A) → B a → C a

NatΣ : {i j k : Level} {A : UU i} {B : A → UU j}{C : A → UU k}
       → Nat B C → Σ A B → Σ A C
NatΣ s (x , a) = (x , s x a)

Σ-retract : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
            → ((a : A) → B a ◃ C a) → Σ A B ◃ Σ A C
Σ-retract {i} {j} {k} {A} {B} {C} p = NatΣ r , NatΣ s , η'
 where
  r : (a : A) → C a → B a
  r a = retraction (p a)

  s : (a : A) → B a → C a
  s a = section (p a)

  η : (a : A)(b : B a) → Id (r a (s a b)) b
  η a = retraction-equation (p a)

  η' : (σ : Σ {i} {j} A B) → Id {i ⊔ j} (NatΣ r (NatΣ s σ)) σ
  η' (a , b) = _≡⟨_⟩_ {i ⊔ j} (_,_ {i} {j} a (r a (s a b))) (dep-pair⁼ {i} {j} _ _ (refl , (η a b)))
               (_▮ {i ⊔ j} (a , b) )


Σ-reindexing-retract : {i j k : Level} {A : UU i} {B : UU j} {C : A → UU k} (r : B → A) → has-section r
 → (Σ A C) ◃ (Σ B (λ b → C (r b)))
Σ-reindexing-retract {i} {j} {k} {A} {B} {C} r (s , η) = γ , ϕ , γϕ
 where
  γ : (Σ B (λ b → C (r b))) → (Σ A C)
  γ (y , a) = (r y , a)

  ϕ : (Σ A C) → (Σ B (λ b → C (r b)))
  ϕ (x , a) = (s x , tr C ((η x) ⁻¹) a)

  γϕ : (u : (Σ A C)) → Id (γ (ϕ u)) u
  γϕ (x , a) = p
   where
    p : Id {i ⊔ k} (r (s x) , (tr C ((η x) ⁻¹) a)) (x , a)
    p = dep-pair⁼ _ _ (η x , tr-is-retraction {i} {k} C (η x) a)

