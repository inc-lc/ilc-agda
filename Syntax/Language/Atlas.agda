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

Atlas-lookup : Atlas-const → Type Atlas-type
Atlas-lookup xor = base Bool ⇒ base Bool ⇒ base Bool

Atlas-Δtype : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δtype Bool = Bool
-- change to a map is change to its values
Atlas-Δtype (Map key val) = (Map key (Atlas-Δtype val))

-- Type signature of Atlas-Δconst is boilerplate.
Atlas-Δconst : ∀ {Γ} → (c : Atlas-const) →
      Term {Atlas-type} {Atlas-const} {Atlas-lookup}
      Γ (lift₀ Atlas-Δtype (Atlas-lookup c))

-- Δxor = λ x Δx y Δy → Δx xor Δy
Atlas-Δconst xor =
  let
    Δx = var (that (that this))
    Δy = var this
  in abs (abs (abs (abs (app (app (const xor) Δx) Δy))))

Atlas = calculus-with
  Atlas-type
  Atlas-const
  Atlas-lookup
  (lift₀ Atlas-Δtype)
  Atlas-Δconst
