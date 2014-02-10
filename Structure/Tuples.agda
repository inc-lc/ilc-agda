------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Tuples with a uniform constructor `cons`.
------------------------------------------------------------------------
module Structure.Tuples where

record Pair
  (A : Set) (B : A → Set) : Set where
  constructor cons
  field
    car : A
    cdr : B car

record Triple
  (A : Set) (B : A → Set) (C : (a : A) → B a → Set) : Set where
  constructor cons
  field
    car  : A
    cadr : B car
    cddr : C car cadr

record Quadruple
  (A : Set) (B : A → Set) (C : (a : A) → B a → Set)
  (D : (a : A) → (b : B a) → (c : C a b) → Set): Set where
  constructor cons
  field
    car   : A
    cadr  : B car
    caddr : C car cadr
    cdddr : D car cadr caddr
