module Nehemiah.Change.Value where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value

open import Data.Integer
open import Structure.Bag.Nehemiah

import Parametric.Change.Value Const ⟦_⟧Base ΔBase as ChangeValue

⟦apply-base⟧ : ChangeValue.ApplyStructure
⟦apply-base⟧ base-int n Δn = n +  Δn
⟦apply-base⟧ base-bag b Δb = b ++ Δb

⟦diff-base⟧ : ChangeValue.DiffStructure
⟦diff-base⟧ base-int m n = m -  n
⟦diff-base⟧ base-bag a b = a \\ b

open ChangeValue.Structure ⟦apply-base⟧ ⟦diff-base⟧ public
