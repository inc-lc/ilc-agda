module Syntax.Language.Atlas where

-- Base types of the calculus Atlas
-- to be used with Plotkin-style language description
--
-- Atlas supports maps with neutral elements. The change type to
-- `Map κ ι` is `Map κ Δι`, where Δι is the change type of the
-- ground type ι. Such a change to maps can support insertions
-- and deletions as well: Inserting `k -> v` means mapping `k` to
-- the change from the neutral element to `v`, and deleting
-- `k -> v` means mapping `k` to the change from `v` to the
-- neutral element.

open import Syntax.Language.Calculus

data Atlas-type : Set where
  Bool : Atlas-type
  Map : (key : Atlas-type) (val : Atlas-type) → Atlas-type

data Atlas-const : Set where
  xor : Atlas-const

Atlas-Base : Base
Atlas-Base = record
  { type  = Atlas-type
  ; const = Atlas-const
  }

Atlas-lookup : Atlas-const → Type Atlas-type
Atlas-lookup xor = base Bool ⇒ base Bool ⇒ base Bool

Atlas-Δtype : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δtype Bool = Bool
-- change to a map is change to all
Atlas-Δtype (Map key val) = (Map key (Atlas-Δtype val))

Atlas-Typing : Typing Atlas-Base
Atlas-Typing = record
  { lookup = Atlas-lookup
  ; Δtype  = lift-Δbase Atlas-Δtype
  }

-- Atlas-Δprim : Δprimitive
