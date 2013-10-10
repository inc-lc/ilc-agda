module README where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * multiple calculi


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
