module Parametric.Change.Type
  (Base : Set)
  where

open import Parametric.Syntax.Type Base

Structure : Set
Structure = Base → Base

module Structure (ΔBase : Structure) where
  ΔType : Type → Type
  ΔType (base ι) = base (ΔBase ι)
  ΔType (σ ⇒ τ) = σ ⇒ ΔType σ ⇒ ΔType τ

  open import Base.Change.Context ΔType public
