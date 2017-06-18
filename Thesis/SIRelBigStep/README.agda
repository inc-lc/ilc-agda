-- Step-indexed logical relations based on relational big-step semantics
-- for ILC-based incremental computation.

-- Goal: prove the fundamental lemma for a ternary logical relation (change
-- validity) across t1, dt and t2. The fundamnetal lemma relates t, derive t and
-- t. That is, we relate a term evaluated relative to an original environment,
-- its derivative evaluated relative to a valid environment change, and the
-- original term evaluated relative to an updated environment.
--
-- Missing goal: here ⊕ isn't defined and wouldn't yet agree with change
-- validity.
--
-- This development is strongly inspired by "Imperative self-adjusting
-- computation" (ISAC below), POPL'08, including the choice of using ANF syntax
-- to simplify some step-indexing proofs.
--
-- In fact, this development is typed, hence some parts of the model are closer
-- to Ahmed (ESOP 2006), "Step-Indexed Syntactic Logical Relations for Recursive
-- and Quantified Types". But for many relevant aspects, the two papers are
-- very similar. In fact, I first defined similar logical relations
-- without types, but they require a trickier recursion scheme for well-founded
-- recursion, and I failed to do any proof in that setting.
--
-- The original inspiration came from Dargaye and Leroy (2010), "A verified
-- framework for higher-order uncurrying optimizations", but we ended up looking
-- at their source.
--
-- The main insight from the ISAC paper missing from the other one is how to
-- step-index a big-step semantics correctly: just ensure that the steps in the
-- big-step semantics agree with the ones in the small-step semantics. *Then*
-- everything just works with big-step semantics. Quite a few other details are
-- fiddly, but those are the same in small-step semantics.
--
-- The crucial novelty here is that we relate two computations on different
-- inputs. So we only conclude their results are related if both terminate; the
-- relation for computations does not prove that if the first computation
-- terminates, then the second terminates as well.
--
-- Instead, e1, de and e2 are related at k steps if, whenever e1 terminates in j
-- < k steps and e2 terminates with any step count, then de terminates (with any
-- step count) and their results are related at k - j steps.
--
-- Even when e1 terminates in j steps implies that e2 terminates, e2 gets no
-- bound. Similarly, we do not bound in how many steps de terminates, since on
-- big inputs it might take long.

module Thesis.SIRelBigStep.README where

-- Base language
import Thesis.SIRelBigStep.Lang
-- Which comprises:
import Thesis.SIRelBigStep.Types
import Thesis.SIRelBigStep.Syntax
-- Denotational semantics:
import Thesis.SIRelBigStep.DenSem
-- Big-step operations semantics:
import Thesis.SIRelBigStep.OpSem
-- Show these two semantics are equivalent:
import Thesis.SIRelBigStep.SemEquiv
-- It follows that the big-step semantics is deterministic.

-- To show that the big-step semantics is total, give a proof of (CBV) strong
-- normalization for this calculus, using a unary logical relation.
-- This is just TAPL Ch. 12, adapted to our environment-based big-step
-- semantics.
import Thesis.SIRelBigStep.Normalization

-- Change language
import Thesis.SIRelBigStep.DLang

-- Which comprises:
import Thesis.SIRelBigStep.DSyntax
-- The operational semantics also defines ⊕:
import Thesis.SIRelBigStep.DOpSem

-- Differentiation:
import Thesis.SIRelBigStep.DLangDerive

-- Small extra arithmetic lemmas for step-indexes.
import Thesis.SIRelBigStep.ArithExtra
-- Step-indexed logical relations for validity, their monotonicity and agreement with ⊕
import Thesis.SIRelBigStep.IlcSILR
-- Prove the fundamental lemma:
import Thesis.SIRelBigStep.FundLemma
