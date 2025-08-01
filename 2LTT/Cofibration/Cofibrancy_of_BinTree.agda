{-# OPTIONS --without-K --two-level --cumulativity #-}

module 2LTT.Cofibration.Cofibrancy_of_BinTree where

open import 2LTT.Cofibration.isCofibrant public
open import 2LTT.Cofibration.Cofibrancy_of_Fibrant_Types
open import 2LTT.Cofibration.Cofibrancy_of_Finite_Types
open import 2LTT.Cofibration.Cofibrancy_of_Exo_Empty
open import 2LTT.Cofibration.Cofibrancy_of_Sigma
open import 2LTT.Cofibration.Cofibrancy_of_List
open import 2LTT.Cofibration.Properties

--Balanced parantheses.
--Since Parens is finite, it's cofibrant. So if ℕᵉ is cofibrant, so is Listᵉ Parens.
--Using this, we can show type of balanced parantheses is cofibrant.

data Parens : UUᵉ lzero where
  popen pclose : Parens

is-balanced : Listᵉ Parens → ℕᵉ → UUᵉ lzero
is-balanced []ᵉ zeroᵉ = ⊤ᵉ
is-balanced []ᵉ (succᵉ n) = ⊥ᵉ
is-balanced (popen ::ᵉ l) n = is-balanced l (succᵉ n)
is-balanced (pclose ::ᵉ l) zeroᵉ = ⊥ᵉ
is-balanced (pclose ::ᵉ l) (succᵉ n) = is-balanced l n

is-balanced-cofib : {j : Level} → (l : Listᵉ Parens) → (n : ℕᵉ) → isCofibrant (is-balanced l n) j
is-balanced-cofib []ᵉ zeroᵉ = ⊤ᵉ-is-cofibrant _
is-balanced-cofib []ᵉ (succᵉ n) = ⊥ᵉ-is-cofibrant _
is-balanced-cofib (popen ::ᵉ l) n = is-balanced-cofib l (succᵉ n)
is-balanced-cofib (pclose ::ᵉ l) zeroᵉ = ⊥ᵉ-is-cofibrant _
is-balanced-cofib (pclose ::ᵉ l) (succᵉ n) = is-balanced-cofib l n

--type of balanced parantheses
Balanced : (n : ℕᵉ) → UUᵉ lzero
Balanced n = Σᵉ (Listᵉ Parens) (λ l → is-balanced l n)

--List Parens is cofibrant
is-List-Parens-cofib : {j : Level} → isCofibrant ℕᵉ j → isCofibrant (Listᵉ Parens) j
is-List-Parens-cofib P = List-isCofibrant Parens (isCofibrant-iso iso-Parens (Fin-is-cofibrant twoᵉ _)) P
  where
   iso-Parens : ℕᵉ< twoᵉ ≅ Parens
   iso-Parens = (λ { (inlᵉ (inrᵉ starᵉ)) → popen ; (inrᵉ starᵉ) → pclose}) ,ᵉ
                (λ { popen → inlᵉ (inrᵉ starᵉ) ; pclose → inrᵉ starᵉ}) ,ᵉ
                (λ { (inlᵉ (inrᵉ starᵉ)) → reflᵉ ; (inrᵉ starᵉ) → reflᵉ}) ,ᵉ
                (λ { popen → reflᵉ ; pclose → reflᵉ})

--Balanced is a family of cofibrant exo-types
is-Balanced-cofib : {j : Level} → isCofibrant ℕᵉ j → (n : ℕᵉ) → isCofibrant (Balanced n) j
is-Balanced-cofib {j} P n = Σᵉ-preserve-Cofibrant (is-List-Parens-cofib P) (λ a → is-balanced-cofib a n)
------------------------------------------------------------

--The following gives an isomorphism between Balanced zeroᵉ and UnL-BinTreeᵉ.

--maps
UnL-BinTreeᵉ→Balanced' : UnL-BinTreeᵉ →  ∀ n → Balanced n → Balanced n
UnL-BinTreeᵉ→Balanced' ul-leafᵉ n b = b
UnL-BinTreeᵉ→Balanced' (ul-nodeᵉ t t₁) n b
  = UnL-BinTreeᵉ→Balanced' t₁ n ((popen ::ᵉ (pr1ᵉ (UnL-BinTreeᵉ→Balanced'  t (succᵉ n) (pclose ::ᵉ (pr1ᵉ b) ,ᵉ pr2ᵉ b)))) ,ᵉ
                                               (pr2ᵉ (UnL-BinTreeᵉ→Balanced'  t (succᵉ n) (pclose ::ᵉ (pr1ᵉ b) ,ᵉ pr2ᵉ b))))

UnL-BinTreeᵉ→Balanced : UnL-BinTreeᵉ → Balanced zeroᵉ
UnL-BinTreeᵉ→Balanced t = UnL-BinTreeᵉ→Balanced' t zeroᵉ ([]ᵉ ,ᵉ starᵉ)

data Stack : ℕᵉ → UUᵉ lzero where
  sempty : Stack zeroᵉ
  scons  : ∀ {n} → UnL-BinTreeᵉ → Stack n → Stack (succᵉ n)
  
Balanced→UnL-BinTreeᵉ'  :  ∀ n → Balanced n → Stack (succᵉ n) → UnL-BinTreeᵉ
Balanced→UnL-BinTreeᵉ' n ([]ᵉ ,ᵉ p) (scons x s) = x
Balanced→UnL-BinTreeᵉ' n (popen ::ᵉ l ,ᵉ p) s
  = Balanced→UnL-BinTreeᵉ' (succᵉ n) (l ,ᵉ p) (scons ul-leafᵉ s)
Balanced→UnL-BinTreeᵉ' (succᵉ n) (pclose ::ᵉ l ,ᵉ p) (scons x (scons x₁ s))
  = Balanced→UnL-BinTreeᵉ' n (l ,ᵉ p) (scons (ul-nodeᵉ x x₁) s)

Balanced→UnL-BinTreeᵉ : Balanced zeroᵉ → UnL-BinTreeᵉ
Balanced→UnL-BinTreeᵉ p = Balanced→UnL-BinTreeᵉ' zeroᵉ p (scons ul-leafᵉ sempty)

--------------------------------
--Example of the conversion

--()(())()()((()))
t = popen ::ᵉ pclose ::ᵉ popen ::ᵉ popen ::ᵉ pclose ::ᵉ pclose ::ᵉ popen ::ᵉ pclose ::ᵉ popen ::ᵉ pclose ::ᵉ popen ::ᵉ popen ::ᵉ popen ::ᵉ pclose ::ᵉ pclose ::ᵉ pclose ::ᵉ []ᵉ

--            *
--         /     \
--       *         *
--     /   \     /   \
--    *     *   *     *
--   / \             / \ 
--  *   *           *   *
--                     / \
--                   *     *
--                  / \   / \
--                 *   * *   *
s = ul-nodeᵉ (ul-nodeᵉ (ul-nodeᵉ ul-leafᵉ ul-leafᵉ) ul-leafᵉ) (ul-nodeᵉ ul-leafᵉ  (ul-nodeᵉ ul-leafᵉ (ul-nodeᵉ (ul-nodeᵉ ul-leafᵉ ul-leafᵉ) (ul-nodeᵉ ul-leafᵉ ul-leafᵉ))))

path1 : Balanced→UnL-BinTreeᵉ (t ,ᵉ starᵉ) =ᵉ s
path1 = reflᵉ

path2 : UnL-BinTreeᵉ→Balanced s =ᵉ (t ,ᵉ starᵉ)
path2 = reflᵉ
---------------------------------------

--isomorphisms
Stack→Balanced : ∀ n → Stack (succᵉ n) → Balanced n → Balanced zeroᵉ
Stack→Balanced zeroᵉ (scons x s) b = UnL-BinTreeᵉ→Balanced' x zeroᵉ b
Stack→Balanced (succᵉ n) (scons x s) b
  = Stack→Balanced n s (popen ::ᵉ (pr1ᵉ (UnL-BinTreeᵉ→Balanced' x (succᵉ n) b)) ,ᵉ
                                     pr2ᵉ (UnL-BinTreeᵉ→Balanced' x (succᵉ n) b))


lemma : ∀ n → (x y : UnL-BinTreeᵉ) → (s : Stack n) → (b : Balanced n) →
          Stack→Balanced n (scons (ul-nodeᵉ x y) s) b
        =ᵉ Stack→Balanced n (scons y s) (popen ::ᵉ (pr1ᵉ (UnL-BinTreeᵉ→Balanced' x (succᵉ n) ((pclose ::ᵉ (pr1ᵉ b)) ,ᵉ pr2ᵉ b))) ,ᵉ
                                                      pr2ᵉ (UnL-BinTreeᵉ→Balanced' x (succᵉ n) ((pclose ::ᵉ (pr1ᵉ b)) ,ᵉ pr2ᵉ b)))
lemma zeroᵉ x y s b = reflᵉ
lemma (succᵉ n) x y s b = reflᵉ

Balanced→UnL-BinTree'↔ : ∀ n → (b : Balanced n) → (s : Stack (succᵉ n))
                          → (UnL-BinTreeᵉ→Balanced' (Balanced→UnL-BinTreeᵉ' n b s) zeroᵉ ([]ᵉ ,ᵉ starᵉ))
                             =ᵉ Stack→Balanced n s b
Balanced→UnL-BinTree'↔ zeroᵉ ([]ᵉ ,ᵉ p) (scons x sempty) = reflᵉ
Balanced→UnL-BinTree'↔ n (popen ::ᵉ l ,ᵉ p) s
  = Balanced→UnL-BinTree'↔ (succᵉ n) (l ,ᵉ p) (scons ul-leafᵉ s)
Balanced→UnL-BinTree'↔ (succᵉ n) (pclose ::ᵉ l ,ᵉ p) (scons x (scons x₁ s))
  = exo-concat (Balanced→UnL-BinTree'↔ n (l ,ᵉ p) (scons (ul-nodeᵉ x x₁) s)) (lemma _ _ _ _ (l ,ᵉ p))

Balanced→UnL-BinTree↔ : ∀ b → UnL-BinTreeᵉ→Balanced (Balanced→UnL-BinTreeᵉ b) =ᵉ b
Balanced→UnL-BinTree↔ b = Balanced→UnL-BinTree'↔ zeroᵉ b (scons ul-leafᵉ sempty)

bintree-append : UnL-BinTreeᵉ → UnL-BinTreeᵉ → UnL-BinTreeᵉ
bintree-append ul-leafᵉ ys = ys
bintree-append (ul-nodeᵉ x xs) ys = ul-nodeᵉ x (bintree-append xs ys)

bintree-append-right : ∀ {xs} → bintree-append xs ul-leafᵉ =ᵉ xs
bintree-append-right {ul-leafᵉ} = reflᵉ
bintree-append-right {ul-nodeᵉ t t₁} = exo-ap (ul-nodeᵉ t) bintree-append-right

stack-append : ∀ {n} → UnL-BinTreeᵉ → Stack (succᵉ n) → Stack (succᵉ n)
stack-append f (scons x s) = scons (bintree-append f x) s

UnL-BinTree→Balanced'↔ : ∀ n → (f : UnL-BinTreeᵉ) → (b : Balanced n) → (s : Stack (succᵉ n))
                            → Balanced→UnL-BinTreeᵉ' n (UnL-BinTreeᵉ→Balanced' f n b) s
                               =ᵉ Balanced→UnL-BinTreeᵉ' n b (stack-append f s)
UnL-BinTree→Balanced'↔ n ul-leafᵉ b (scons x s) = reflᵉ
UnL-BinTree→Balanced'↔ n (ul-nodeᵉ f f₁) b (scons x s)
  = exo-concat (UnL-BinTree→Balanced'↔ _ f₁ _ _)
      (exo-concat (UnL-BinTree→Balanced'↔ _ f _ _)
         (exo-ap (λ z →
                 (Balanced→UnL-BinTreeᵉ' _ b (scons (ul-nodeᵉ z (bintree-append f₁ x)) s))) bintree-append-right))

UnL-BinTree→Balanced↔ : ∀ t → Balanced→UnL-BinTreeᵉ (UnL-BinTreeᵉ→Balanced t) =ᵉ t
UnL-BinTree→Balanced↔ t = exo-concat (UnL-BinTree→Balanced'↔ zeroᵉ t ([]ᵉ ,ᵉ starᵉ) (scons ul-leafᵉ sempty)) (bintree-append-right)
-------------------------------------------------------------------

--Balanced is isomorphic to Unlabeled Binary Tree
Balanced≅UnL-BinTreeᵉ : Balanced zeroᵉ ≅ UnL-BinTreeᵉ
Balanced≅UnL-BinTreeᵉ = Balanced→UnL-BinTreeᵉ ,ᵉ (UnL-BinTreeᵉ→Balanced ,ᵉ (Balanced→UnL-BinTree↔ ,ᵉ UnL-BinTree→Balanced↔))

-------------------------------------------------------------------

--Unlabeled Binary Tree is cofibrant if ℕᵉ is cofibrant
is-UnL-BinTreeᵉ-cofib : {j : Level} → isCofibrant ℕᵉ j → isCofibrant UnL-BinTreeᵉ j
is-UnL-BinTreeᵉ-cofib {j} P = isCofibrant-iso Balanced≅UnL-BinTreeᵉ (is-Balanced-cofib {j} P zeroᵉ )

-----------------------------------------------------

--Binary Tree is cofibrant if ℕᵉ is cofibrant
is-BinTreeᵉ-cofib : {i j k : Level}{N : UUᵉ i}{L : UUᵉ j}
                      → isCofibrant N (i ⊔ k) → isCofibrant L (i ⊔ j ⊔ k)  → isCofibrant ℕᵉ (i ⊔ j ⊔ k)
                      → isCofibrant (BinTreeᵉ N L) k
is-BinTreeᵉ-cofib {i} {j} {k} Q R P =
  isCofibrant-iso BinTree-to-UnLBinTree-iso
                  (Σᵉ-preserve-Cofibrant (is-UnL-BinTreeᵉ-cofib {i ⊔ j ⊔ k} P)
                   λ a → ×ᵉ-preserve-Cofibrant {j} {i} {k} (folded-×-cofib R _) (folded-×-cofib Q _))
                   
------------------------------------------------------------------------------

--Binary Tree with labeled leaf, unlabeled node, is cofibrant if ℕᵉ is cofibrant
is-LeafLabeledBinTreeᵉ-cofib : {i k : Level}{L : UUᵉ i}
                                → isCofibrant L (i ⊔ k) → isCofibrant ℕᵉ (i ⊔ k) 
                                → isCofibrant (BinTreeᵉ ⊤ᵉ L) k
is-LeafLabeledBinTreeᵉ-cofib Q P = is-BinTreeᵉ-cofib (⊤ᵉ-is-cofibrant _) Q P 

------------------------------------------------------------------------------

--Binary Tree with labeled node, unlabeled leaf, is cofibrant if ℕᵉ is cofibrant
is-NodeLabeledBinTreeᵉ-cofib : {i k : Level}{N : UUᵉ i}
                                → isCofibrant N (i ⊔ k) → isCofibrant ℕᵉ (i ⊔ k) 
                                → isCofibrant (BinTreeᵉ N ⊤ᵉ) k
is-NodeLabeledBinTreeᵉ-cofib {i} {k} Q P = is-BinTreeᵉ-cofib {i} {lzero} {k} Q (⊤ᵉ-is-cofibrant _) P

