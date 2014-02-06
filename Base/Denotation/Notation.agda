------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Overloading ⟦_⟧ notation
--
-- This module defines a general mechanism for overloading the
-- ⟦_⟧ notation, using Agda’s instance arguments.
------------------------------------------------------------------------

module Base.Denotation.Notation where

open import Level

record Meaning (Syntax : Set) {ℓ : Level} : Set (suc ℓ) where
  constructor
    meaning
  field
    {Semantics} : Set ℓ
    ⟨_⟩⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public
  renaming (⟨_⟩⟦_⟧ to ⟦_⟧)

open Meaning public
  using (⟨_⟩⟦_⟧)
