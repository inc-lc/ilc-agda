------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Reexport Data.List.All from the standard library.
--
-- At one point, we reinvented Data.List.All from the Agda
-- standard library, under the name dependent list. We later
-- replaced our reinvention by this adapter module that just
-- exports the standard library's version with partly different
-- names.
------------------------------------------------------------------------

module Base.Data.DependentList where

open import Base.Data.ContextList public
open import Data.List.All public
  using
    ( head
    ; tail
    ; map
    ; tabulate
    )
  renaming
    ( All to DependentList
    ; _∷_ to _•_
    ; [] to ∅
    )

-- Maps a binary function over two dependent lists.
-- Should this be in the Agda standard library?
zipWith : ∀ {a p q r} {A : Set a} {P : A → Set p} {Q : A → Set q} {R : A → Set r} →
  (f : {a : A} → P a → Q a → R a) →
  ∀ {xs} → DependentList P xs → DependentList Q xs → DependentList R xs
zipWith f ∅ ∅ = ∅
zipWith f (p • ps) (q • qs) = f p q • zipWith f ps qs
