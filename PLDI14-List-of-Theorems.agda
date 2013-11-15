module PLDI14-List-of-Theorems where

open import Function

-- List of theorems in PLDI submission
--
-- For hints about installation and execution, please refer
-- to README.agda.
--
-- Agda modules corresponding to definitions, lemmas and theorems
-- are listed here with the most important name. For example,
-- after this file type checks (C-C C-L), placing the cursor
-- on the purple "Base.Change.Algebra" and pressing M-. will
-- bring you to the file where change structures are defined.
-- The name for change structures in that file is
-- "ChangeAlgebra", given in the using-clause.

-- Definition 2.1 (Change structures)
-- (d) ChangeAlgebra.diff
-- (e) IsChangeAlgebra.update-diff
open import Base.Change.Algebra using (ChangeAlgebra)
---- Carrier in record ChangeAlgebra                        --(a)
open Base.Change.Algebra.ChangeAlgebra   using (Change)     --(b)
open Base.Change.Algebra.ChangeAlgebra   using (update)     --(c)
open Base.Change.Algebra.ChangeAlgebra   using (diff)       --(d)
open Base.Change.Algebra.IsChangeAlgebra using (update-diff)--(e)

-- Definition 2.2 (Nil change)
-- IsChangeAlgebra.nil
open Base.Change.Algebra using (IsChangeAlgebra)

-- Lemma 2.3 (Behavior of nil)
-- IsChangeAlgebra.update-nil
open Base.Change.Algebra using (IsChangeAlgebra)

-- Definition 2.4 (Derivatives)
open Base.Change.Algebra using (Derivative)

-- Definition 2.5 (Carrier set of function changes)
open Base.Change.Algebra.FunctionChanges

-- Definition 2.6 (Operations on function changes)
-- ChangeAlgebra.update FunctionChanges.changeAlgebra
-- ChangeAlgebra.diff   FunctionChanges.changeAlgebra
open Base.Change.Algebra.FunctionChanges using (changeAlgebra)

-- Theorem 2.7 (Function changes form a change structure)
-- (In Agda, the proof of Theorem 2.7 has to be included in the
-- definition of function changes, here
-- FunctionChanges.changeAlgebra.)
open Base.Change.Algebra.FunctionChanges using (changeAlgebra)

-- Lemma 2.8 (Incrementalization)
open Base.Change.Algebra.FunctionChanges using (incrementalization)

-- Theorem 2.9 (Nil changes are derivatives)
open Base.Change.Algebra.FunctionChanges using (nil-is-derivative)

-- For each plugin requirement, we include its definition and
-- a concrete instantiation called "Popl14" with integers and
-- bags of integers as base types.

-- Plugin Requirement 3.1 (Domains of base types)
open import Parametric.Denotation.Value using (Structure)
open import     Popl14.Denotation.Value using (⟦_⟧Base)

-- Definition 3.2 (Domains)
open Parametric.Denotation.Value.Structure using (⟦_⟧Type)

-- Plugin Requirement 3.3 (Evaluation of constants)
open import Parametric.Denotation.Evaluation using (Structure)
open import     Popl14.Denotation.Evaluation using (⟦_⟧Const)

-- Definition 3.4 (Environments)
open import Base.Denotation.Environment using (⟦_⟧Context)

-- Definition 3.5 (Evaluation)
open Parametric.Denotation.Evaluation.Structure using (⟦_⟧Term)

-- Plugin Requirement 3.6 (Changes on base types)
open import Parametric.Change.Validity using (Structure)
open import     Popl14.Change.Validity using (change-algebra-base-family)

-- Definition 3.7 (Changes)
open Parametric.Change.Validity.Structure using (change-algebra)

-- Definition 3.8 (Change environments)
open Parametric.Change.Validity.Structure using (environment-changes)

-- Plugin Requirement 3.9 (Change semantics for constants)
open import Parametric.Change.Specification using (Structure)
open import     Popl14.Change.Specification using (specification-structure)

-- Definition 3.10 (Change semantics)
open Parametric.Change.Specification.Structure using (⟦_⟧Δ)

-- Lemma 3.11 (Change semantics is the derivative of semantics)
open Parametric.Change.Specification.Structure using (correctness)

-- Definition 3.12 (Erasure)
import Parametric.Change.Implementation
open Parametric.Change.Implementation.Structure using (_≈_)
open import Popl14.Change.Implementation using (implements-base)

-- Lemma 3.13 (The erased version of a change is almost the same)
open Parametric.Change.Implementation.Structure using (carry-over)

-- Lemma 3.14 (⟦ t ⟧Δ erases to Derive(t))
import Parametric.Change.Correctness
open Parametric.Change.Correctness.Structure using (main-theorem)
