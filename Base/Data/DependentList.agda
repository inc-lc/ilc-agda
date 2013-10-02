module Base.Data.DependentList where

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

zipWith : ∀ {a p q r} {A : Set a} {P : A → Set p} {Q : A → Set q} {R : A → Set r} →
  (f : {a : A} → P a → Q a → R a) →
  ∀ {xs} → DependentList P xs → DependentList Q xs → DependentList R xs
zipWith f ∅ ∅ = ∅
zipWith f (p • ps) (q • qs) = f p q • zipWith f ps qs
