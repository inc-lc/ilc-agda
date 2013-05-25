module README where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * Δ e describes how e changes when its free variables or its arguments change
--   * denotational semantics including semantics of changes
--
-- Note that Δ is *not* the same as the ∂ operator in
-- definition/intro.tex. See discussion at:
--
--   https://github.com/ps-mr/ilc/pull/34#discussion_r4290325
--
-- Work in Progress:
--   * lemmas about behavior of changes
--   * lemmas about behavior of Δ
--   * correctness proof for symbolic derivation

-- The formalization is split across the following files.
-- TODO: document them more.

-- Note that we use two postulates currently:

-- 1. function extensionality (in
--    `Denotational.ExtensionalityPostulate`), known to be consistent
--    with intensional type theory.
--
-- 2. Temporarily, we use `diff-apply` as a postulate, which is only
--    true in a slightly weaker form, `diff-apply-proof` - we are
--    adapting the proofs to use the latter.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.ChangeTypes.ChangesAreDerivatives
open import Syntactic.ChangeContexts
open import Syntactic.Terms.Total
open import Syntactic.Changes

open import Denotational.Notation
open import Denotational.Values
open import Denotational.ExtensionalityPostulate
open import Denotational.EqualityLemmas
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Changes
open import Denotational.Equivalence
open import Denotational.ValidChanges

open import ChangeContexts
open import ChangeContextLifting
open import PropsDelta
open import SymbolicDerivation

-- This finishes the correctness proof of the above work.
open import total


-- EXAMPLES

open import Examples.Examples1


-- NATURAL semantics

open import Syntactic.Closures
open import Denotational.Closures

open import Natural.Lookup
open import Natural.Evaluation

open import Natural.Soundness


-- Other calculi

open import partial
open import lambda
