------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The values of terms in Nehemiah.Change.Term.
------------------------------------------------------------------------

module Nehemiah.Change.Value where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value

open import Data.Product
open import Data.Integer
open import Structure.Bag.Nehemiah

import Parametric.Change.Value Const ⟦_⟧Base ΔBase as ChangeValue

{-# TERMINATING #-}
⟦apply-base⟧ : ChangeValue.ApplyStructure
⟦diff-base⟧ : ChangeValue.DiffStructure
⟦nil-base⟧ : ChangeValue.NilStructure
open ChangeValue.Structure ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧ public

⟦apply-base⟧ base-int n Δn = n +  Δn
⟦apply-base⟧ base-bag b Δb = b ++ Δb
⟦apply-base⟧ (base-pair τ₁ τ₂) (a , b) (da , db) = ⟦apply⟧ τ₁ a da , ⟦apply⟧ τ₂ b db

⟦diff-base⟧ base-int m n = m -  n
⟦diff-base⟧ base-bag a b = a \\ b
⟦diff-base⟧ (base-pair τ₁ τ₂) (a₂ , b₂) (a₁ , b₁) = ⟦diff⟧ τ₁ a₂ a₁ , ⟦diff⟧ τ₂ b₂ b₁

⟦nil-base⟧ base-int n = + 0
⟦nil-base⟧ base-bag b = emptyBag
⟦nil-base⟧ (base-pair τ₁ τ₂) (a , b) = (⟦nil₍ τ₁ ₎⟧ a) , (⟦nil₍ τ₂ ₎⟧ b)
