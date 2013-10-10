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


import Popl14.Syntax.Term
import Base.Syntax.Context
import Base.Change.Context
import Popl14.Change.Derive
{- Language definition of Calc. Atlas -}
import Atlas.Syntax.Term
{- Terms of a calculus described in Plotkin style
  - types are parametric in base types
  - terms are parametric in constants
  This style of language description is employed in:
  G. D. Plotkin. "LCF considered as a programming language."
  Theoretical Computer Science 5(3) pp. 223--255, 1997.
  http://dx.doi.org/10.1016/0304-3975(77)90044-5 -}
import Parametric.Syntax.Term
import Popl14.Change.Term
import Atlas.Syntax.Type
import Parametric.Syntax.Type
import Popl14.Syntax.Type
import Base.Syntax.Vars

import Popl14.Change.Validity
{- Correctness theorem for canonical derivation of Calc. Popl14 -}
import Popl14.Change.Correctness
import Theorem.Irrelevance-Popl14
import Base.Denotation.Environment
import Popl14.Denotation.Evaluation
{- The idea of implementing a denotational specification for Calc. Popl14 -}
import Popl14.Change.Implementation
import Base.Denotation.Notation
{- Denotation-as-specification for canonical derivation of Calc. Popl14 -}
import Popl14.Change.Specification
import Popl14.Denotation.Value
import experimental.DecidableEq
import experimental.FoldableBag
import experimental.FoldableBagParametric
import experimental.NormalizationByEvaluation
import experimental.OrdBag
import experimental.Sorting
import Postulate.Bag-Popl14
import Postulate.Extensionality
import Property.Uniqueness
import Structure.Bag.Popl14
import Structure.Tuples

import Theorem.CongApp
import Theorem.EqualityUnique
import Theorem.Groups-Popl14
import Theorem.IrrelevanceUnique-Popl14
import Theorem.ProductUnique
import UNDEFINED

import Everything
