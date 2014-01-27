module Nehemiah.Denotation.Value where

open import Nehemiah.Syntax.Type public
open import Nehemiah.Change.Type public
open import Base.Denotation.Notation public

open import Structure.Bag.Nehemiah
open import Data.Integer

-- Values of Calculus Nehemiah
--
-- Contents
-- - Domains associated with types
-- - `diff` and `apply` in semantic domains

import Parametric.Denotation.Value Base as Value

⟦_⟧Base : Value.Structure
⟦ base-int ⟧Base = ℤ
⟦ base-bag ⟧Base = Bag

open Value.Structure ⟦_⟧Base public
