module Base.Data.DependentList where

open import Data.List.All public
  renaming
    ( All to DependentList
    ; _∷_ to _•_
    ; [] to ∅
    )
