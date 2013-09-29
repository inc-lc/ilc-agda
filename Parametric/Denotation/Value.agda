import Parametric.Syntax.Type as Type

module Parametric.Denotation.Value
    (Base : Type.Structure)
  where

open import Base.Denotation.Notation

open Type.Structure Base

Structure : Set₁
Structure = Base → Set

module Structure (⟦_⟧Base : Structure) where
  ⟦_⟧Type : Type -> Set
  ⟦ base ι ⟧Type = ⟦ ι ⟧Base
  ⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

  open import Base.Denotation.Environment Type ⟦_⟧Type public
