module experimental.OrdBag where

import Level as L
open import Algebra
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

record Ord (T : Set) : Set₁ where
  field
    { _<_ } : Rel T L.zero
    isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_

import Data.AVL

module Dict {T} (ValueFun : T → Set) (o : Ord T) = Data.AVL ValueFun (Ord.isStrictTotalOrder o)

