module README where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * multiple calculi
--
-- To typecheck this formalization, you need to install the appropriate version
-- of Agda, the Agda standard library (version 0.7), generate Everything.agda
-- with the attached Haskell helper, and finally run Agda on this file.
--
-- Given a Unix-like environment (including Cygwin), running the ./agdaCheck.sh
-- script and following instructions given on output will help with the
-- "generate Everything.agda" part.
--
-- We use Agda HEAD from September 2013; Agda 2.3.2.1 might happen to work, but
-- has some bugs with serialization of code using some recent syntactic sugar
-- which we use (https://code.google.com/p/agda/issues/detail?id=756), so it
-- might work or not. When it does not, removing Agda caches (.agdai files)
-- appears to often help.

import Postulate.Extensionality

import Base.Data.DependentList

-- Variables and contexts
import Base.Syntax.Context

-- Sets of variables
import Base.Syntax.Vars

import Base.Denotation.Notation

-- Environments
import Base.Denotation.Environment

-- Change contexts
import Base.Change.Context

-- # Base, parametric proof.
--
-- This is for a parametric calculus where:
-- types are parametric in base types
-- terms are parametric in constants
--
--
-- Modules are ordered and grouped according to what they represent.

-- ## Definitions

import Parametric.Syntax.Type
import Parametric.Syntax.Term

import Parametric.Denotation.Value
import Parametric.Denotation.Evaluation

import Parametric.Change.Type
import Parametric.Change.Term

import Parametric.Change.Derive

import Parametric.Change.Value
import Parametric.Change.Evaluation

-- ## Proofs

import Parametric.Change.Validity
import Parametric.Change.Specification
import Parametric.Change.Implementation
import Parametric.Change.Correctness

-- # Popl14 plugin
--
-- The structure is the same as the parametric proof (down to the
-- order and the grouping of modules), except for the postulate module.

-- Postulate an abstract data type for integer Bags.
import Postulate.Bag-Popl14

-- ## Definitions
import Popl14.Syntax.Type
import Popl14.Syntax.Term

import Popl14.Denotation.Value
import Popl14.Denotation.Evaluation

import Popl14.Change.Term
import Popl14.Change.Type

import Popl14.Change.Derive

import Popl14.Change.Value
import Popl14.Change.Evaluation

-- ## Proofs

import Popl14.Change.Validity
import Popl14.Change.Specification
import Popl14.Change.Implementation
import Popl14.Change.Correctness

-- Some other calculus (remove from here?)

import Atlas.Syntax.Type
import Atlas.Syntax.Term
import Atlas.Change.Type
import Atlas.Change.Term
import Atlas.Change.Derive

-- Import everything else.
import Everything

-- XXX: Do we still care about these?

import Property.Uniqueness

import Structure.Bag.Popl14
import Structure.Tuples

import Theorem.CongApp
import Theorem.EqualityUnique
import Theorem.Groups-Popl14
import Theorem.Irrelevance-Popl14
import Theorem.IrrelevanceUnique-Popl14
import Theorem.ProductUnique

-- Old stuff.
-- XXX Update and integrate those descriptions where appropriate.

{-
-- Correctness theorem for canonical derivation
import Popl14.Change.Correctness

-- Denotation-as-specification for canonical derivation
import Popl14.Change.Specification

-- The idea of implementing a denotational specification
import Popl14.Change.Implementation
-}
