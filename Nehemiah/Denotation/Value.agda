------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Values for standard evaluation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Denotation.Value where

open import Nehemiah.Syntax.Type public
open import Nehemiah.Change.Type public
open import Base.Denotation.Notation public

open import Structure.Bag.Nehemiah
open import Data.Integer

import Parametric.Denotation.Value Base as Value

⟦_⟧Base : Value.Structure
⟦ base-int ⟧Base = ℤ
⟦ base-bag ⟧Base = Bag

open Value.Structure ⟦_⟧Base public
