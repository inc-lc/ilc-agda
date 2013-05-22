module Examples.Examples1 where


open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Changes
open import Syntactic.Closures

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence
open import Denotational.ValidChanges

open import Changes
open import ChangeContexts
open import ChangeContextLifting
open import PropsDelta
open import SymbolicDerivation
open import Natural.Evaluation
open import Relation.Binary.PropositionalEquality

-- only some finger exercises to get used to the definitions
 
bool-identity : Term ∅ (bool ⇒ bool)
bool-identity = abs (var this)

term1 : Term ∅ bool
term1 = app bool-identity true

res : ⟦ bool ⟧
res = ⟦ term1 ⟧ ∅

-- test the denotational semantics

-- is this a good way to write unit tests in Agda?
test1 : res ≡ true
test1 = refl

-- test the natural semantics
open import Natural.Lookup
test2 : ∅ ⊢ term1 ↓ vtrue
test2 = app abs e-true (var this)
