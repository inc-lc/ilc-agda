module Syntactic.Types where

-- SIMPLE TYPES
--
-- This module defines the syntax of simple types.

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type
  bool : Type

infixr 5 _⇒_
