module Parametric.Change.Type
  {Base : Set}
  (ΔBase : Base → Base)
  where

open import Parametric.Syntax.Type Base

ΔType : Type → Type
ΔType (base ι) = base (ΔBase ι)
ΔType (σ ⇒ τ) = σ ⇒ ΔType σ ⇒ ΔType τ
