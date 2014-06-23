module PLDI14-List-of-Theorems where

-- List of theorems in PLDI submission
--
-- For hints about installation and execution, please refer
-- to README.agda.
--
-- Agda modules corresponding to definitions, lemmas and theorems
-- are listed here with the most important names. For example,
-- after this file type checks (C-C C-L), placing the cursor
-- on the purple "Base.Change.Algebra" and pressing M-. will
-- bring you to the file where change structures are defined.
-- The name for change structures in that file is
-- "ChangeAlgebra", given in the using-clause.

-- Definition 2.1 (Change structures)
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

-- Lemma 2.5 (Behavior of derivatives on nil)
open import Base.Change.Equivalence using (deriv-zero)

-- Definition 2.4 (Derivatives)
open Base.Change.Algebra using (Derivative)

-- Definition 2.6 (Carrier set of function changes)
open Base.Change.Algebra.FunctionChanges

-- Definition 2.7 (Operations on function changes)
-- ChangeAlgebra.update FunctionChanges.changeAlgebra
-- ChangeAlgebra.diff   FunctionChanges.changeAlgebra
open Base.Change.Algebra.FunctionChanges using (changeAlgebra)

-- Theorem 2.8 (Function changes form a change structure)
-- (In Agda, the proof of Theorem 2.8 has to be included in the
-- definition of function changes, here
-- FunctionChanges.changeAlgebra.)
open Base.Change.Algebra.FunctionChanges using (changeAlgebra)

-- Theorem 2.9 (Incrementalization)
open Base.Change.Algebra.FunctionChanges using (incrementalization)

-- Theorem 2.10 (Nil changes are derivatives)
open Base.Change.Algebra.FunctionChanges using (nil-is-derivative)

-- Definition 3.1 (Domains)
import Parametric.Denotation.Value
open Parametric.Denotation.Value.Structure using (⟦_⟧Type)

-- Definition 3.2 (Environments)
open import Base.Denotation.Environment using (⟦_⟧Context)

-- Definition 3.3 (Evaluation)
import Parametric.Denotation.Evaluation
open Parametric.Denotation.Evaluation.Structure using (⟦_⟧Term)

-- Definition 3.4 (Changes)
-- Definition 3.5 (Change environments)
import Parametric.Change.Validity
open Parametric.Change.Validity.Structure using (change-algebra)
open Parametric.Change.Validity.Structure using (environment-changes)

-- Definition 3.6 (Change semantics)
-- Lemma 3.7 (Change semantics is the derivative of semantics)
import Parametric.Change.Specification
open Parametric.Change.Specification.Structure using (⟦_⟧Δ)
open Parametric.Change.Specification.Structure using (correctness)

-- Definition 3.8 (Erasure)
-- Lemma 3.9 (The erased version of a change is almost the same)
import Parametric.Change.Implementation
open Parametric.Change.Implementation.Structure using (_≈_)
open Parametric.Change.Implementation.Structure using (carry-over)

-- Lemma 3.10 (⟦ t ⟧Δ erases to Derive(t))
-- Theorem 3.11 (Correctness of differentiation)
import Parametric.Change.Correctness
open Parametric.Change.Correctness.Structure using (derive-correct-closed)
open Parametric.Change.Correctness.Structure using (main-theorem)
