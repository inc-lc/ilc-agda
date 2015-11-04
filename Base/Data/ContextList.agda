------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Reexport Data.List from the standard library.
--
-- Here we expose different names, for use in Contexts.
------------------------------------------------------------------------

module Base.Data.ContextList where

import Data.List as List
open List public
  using ()
  renaming
    ( [] to ∅ ; _∷_ to _•_
    ; map to mapContext
    )
