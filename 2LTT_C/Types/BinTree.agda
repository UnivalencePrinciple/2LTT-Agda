{-# OPTIONS --without-K --two-level #-}

module 2LTT_C.Types.BinTree where

open import 2LTT_C.Primitive

--Binary Trees with labeled vertices
data BinTree {i j : Level}(N : UU i) (L : UU j) : UU (i ⊔ j) where
  leaf : L → BinTree N L
  node : BinTree N L → N → BinTree N L → BinTree N L

--Binary Trees without labeled vertices
data UnL-BinTree : UU lzero  where
  ul-leaf : UnL-BinTree
  ul-node : UnL-BinTree → UnL-BinTree → UnL-BinTree
