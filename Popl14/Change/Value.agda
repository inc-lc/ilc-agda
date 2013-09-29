module Popl14.Change.Value where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value

open import Data.Integer
open import Structure.Bag.Popl14

import Parametric.Change.Value Const ⟦_⟧Base ΔBase as ChangeValue

⟦apply-base⟧ : ChangeValue.ApplyStructure
⟦apply-base⟧ base-int n Δn = n +  Δn
⟦apply-base⟧ base-bag b Δb = b ++ Δb

⟦diff-base⟧ : ChangeValue.DiffStructure
⟦diff-base⟧ base-int m n = m -  n
⟦diff-base⟧ base-bag a b = a \\ b

open ChangeValue.Structure ⟦apply-base⟧ ⟦diff-base⟧ public
