module README where

----------------------------
-- INCREMENTAL λ-CALCULUS --
----------------------------
--
--
-- IMPORTANT FILES
--
-- modules.pdf
--   The graph of dependencies between Agda modules.
--
-- README.agda
--   This file. A coarse-grained introduction to the Agda formalization.
--
-- PLDI14-List-of-Theorems.agda
--   For each theorem, lemma or definition in the PLDI 2014 submission,
--   it points to the corresponding Agda object.
--
--
-- LOCATION OF AGDA MODULES
--
-- To find the file containing an Agda module, replace the dots in its
-- full name by directory separators. The result is the file's path relative
-- to this directory. For example, Parametric.Syntax.Type is defined in
-- Parametric/Syntax/Type.agda.
--
--
-- HOW TO TYPE CHECK EVERYTHING
--
-- To typecheck this formalization, you need to install the appropriate version
-- of Agda, the Agda standard library (version 0.7), generate Everything.agda
-- with the attached Haskell helper, and finally run Agda on this file.
--
-- Given a Unix-like environment (including Cygwin), running the ./agdaCheck.sh
-- script and following instructions given on output will eventually generate
-- Everything.agda and proceed to type check everything on command line.
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

-- # Nehemiah plugin
--
-- The structure is the same as the parametric proof (down to the
-- order and the grouping of modules), except for the postulate module.

-- Postulate an abstract data type for integer Bags.
import Postulate.Bag-Nehemiah

-- ## Definitions
import Nehemiah.Syntax.Type
import Nehemiah.Syntax.Term

import Nehemiah.Denotation.Value
import Nehemiah.Denotation.Evaluation

import Nehemiah.Change.Term
import Nehemiah.Change.Type

import Nehemiah.Change.Derive

import Nehemiah.Change.Value
import Nehemiah.Change.Evaluation

-- ## Proofs

import Nehemiah.Change.Validity
import Nehemiah.Change.Specification
import Nehemiah.Change.Implementation
import Nehemiah.Change.Correctness
