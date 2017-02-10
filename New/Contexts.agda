module New.Contexts where

open import New.Types public

-- Instantiate generic Context support
open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public
open import Base.Data.DependentList public
open import Base.Denotation.Environment Type ⟦_⟧Type public
