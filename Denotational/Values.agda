module Denotational.Values where

-- VALUES
--
-- This module defines the model theory of simple types, that is,
-- it defines for every type, the set of values of that type.
--
-- In fact, we only describe a single model here.

open import Data.Bool public
open import Denotational.Notation
open import Syntactic.Types

-- Denotational Semantics

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ bool ⟧Type = Bool

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type
