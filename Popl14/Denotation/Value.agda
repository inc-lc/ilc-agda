module Popl14.Denotation.Value where

open import Popl14.Syntax.Type public
open import Popl14.Change.Type public
open import Base.Denotation.Notation public

open import Structure.Bag.Popl14
open import Data.Integer

-- Values of Calculus Popl14
--
-- Contents
-- - Domains associated with types
-- - `diff` and `apply` in semantic domains

import Parametric.Denotation.Value Base as Value

⟦_⟧Base : Value.Structure
⟦ base-int ⟧Base = ℤ
⟦ base-bag ⟧Base = Bag

open Value.Structure ⟦_⟧Base public
