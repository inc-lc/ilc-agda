module README where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * multiple calculi

import Denotation.Change.Popl14
{- Correctness theorem for canonical derivation of Calc. Popl14 -}
import Denotation.Derive.Canon-Popl14
{- Correctness theorem for optimized derivation of Calc. Popl14 -}
import Denotation.Derive.Optimized-Popl14
import Denotation.Environment.Popl14
import Denotation.Environment
import Denotation.Evaluation.Popl14
import Denotation.FreeVars.Popl14
{- The idea of implementing a denotational specification for Calc. Popl14 -}
import Denotation.Implementation.Popl14
import Denotation.Notation
{- Denotation-as-specification for canonical derivation of Calc. Popl14 -}
import Denotation.Specification.Canon-Popl14
import Denotation.Specification.Optimized-Popl14
import Denotation.Value.Popl14
import Postulate.Bag-Popl14
import Postulate.Extensionality
import Property.Uniqueness
import Structure.Bag.Popl14
import Structure.Tuples
import Syntax.Context.Popl14
import Syntax.Context
import Syntax.Derive.Canon-Popl14
import Syntax.Derive.Optimized-Popl14
import Syntax.FreeVars.Popl14
{- Language definition of Calc. Atlas -}
import Syntax.Language.Atlas
import Syntax.Language.Calculus
{- Terms of a calculus described in Plotkin style
- types are parametric in base types
- terms are parametric in constants
This style of language description is employed in:
G. D. Plotkin. "LCF considered as a programming language."
Theoretical Computer Science 5(3) pp. 223--255, 1997.
http://dx.doi.org/10.1016/0304-3975(77)90044-5
 -}
import Syntax.Term.Plotkin
import Syntax.Term.Popl14
import Syntax.Type.Plotkin
import Syntax.Type.Popl14
import Syntax.Vars
import Theorem.CongApp
import Theorem.EqualityUnique
import Theorem.Groups-Popl14
import Theorem.IrrelevanceUnique-Popl14
import Theorem.ProductUnique
import Theorem.ValidityUnique-Popl14
