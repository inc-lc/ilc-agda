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

⟦_⟧Base : Base → Set
⟦ base-int ⟧Base = ℤ
⟦ base-bag ⟧Base = Bag

⟦_⟧Type : Type -> Set
⟦ base ι ⟧Type = ⟦ ι ⟧Base
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type
