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
  Map : (κ : Atlas-type) (ι : Atlas-type) → Atlas-type

data Atlas-const : Set where

  true  : Atlas-const
  false : Atlas-const
  xor   : Atlas-const

  empty  : ∀ {κ ι : Atlas-type} → Atlas-const
  update : ∀ {κ ι : Atlas-type} → Atlas-const
  zip    : ∀ {κ a b c : Atlas-type} → Atlas-const

Atlas-lookup : Atlas-const → Type Atlas-type

Atlas-lookup true  = base Bool
Atlas-lookup false = base Bool
Atlas-lookup xor   = base Bool ⇒ base Bool ⇒ base Bool

Atlas-lookup (empty {κ} {ι}) = base (Map κ ι)

-- `update key val my-map` would
-- - insert if `key` is not present in `my-map`
-- - delete if `val` is the neutral element
-- - make an update otherwise
Atlas-lookup (update {κ} {ι}) =
  base κ ⇒ base ι ⇒ base (Map κ ι) ⇒ base (Map κ ι)

-- Model of zip = Haskell Data.List.zipWith
-- zipWith :: (a → b → c) → [a] → [b] → [c]
Atlas-lookup (zip {κ} {a} {b} {c}) =
  (base κ ⇒ base a ⇒ base b ⇒ base c) ⇒
  base (Map κ a) ⇒ base (Map κ b) ⇒ base (Map κ c)

Atlas-Δtype : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δtype Bool = Bool
-- change to a map is change to its values
Atlas-Δtype (Map key val) = (Map key (Atlas-Δtype val))

Atlas-context : Set
Atlas-context = Context {Type Atlas-type}

Atlas-term : Atlas-context → Type Atlas-type → Set
Atlas-term = Term {Atlas-type} {Atlas-const} {Atlas-lookup}

-- Every base type has a known nil-change.
-- The nil-change of ι is also the neutral element of Map κ Δι.

neutral : ∀ {ι : Atlas-type} → Atlas-const
neutral {Bool} = false
neutral {Map κ ι} = empty {κ} {ι}

nil-const : ∀ {ι : Atlas-type} → Atlas-const
nil-const {ι} = neutral {Atlas-Δtype ι}

nil-term : ∀ {ι Γ} → Atlas-term Γ (base (Atlas-Δtype ι))
nil-term {Bool} = const (nil-const {Bool})
nil-term {Map κ ι} = const (nil-const {Map κ ι})

-- Type signature of Atlas-Δconst is boilerplate.
Atlas-Δconst : ∀ {Γ} → (c : Atlas-const) →
      Atlas-term Γ (lift-Δtype₀ Atlas-Δtype (Atlas-lookup c))

Atlas-Δconst true  = const false
Atlas-Δconst false = const false

-- Δxor = λ x Δx y Δy → Δx xor Δy
Atlas-Δconst xor =
  let
    Δx = var (that (that this))
    Δy = var this
  in abs (abs (abs (abs (app (app (const xor) Δx) Δy))))

Atlas-Δconst empty = const empty

-- If k ⊕ Δk ≡ k, then
--   Δupdate k Δk v Δv m Δm = update k Δv Δm
-- otherwise it is a deletion followed by insertion.
--   Δupdate k Δk v Δv m Δm =
--     insert (k ⊕ Δk) (v ⊕ Δv) (delete k v Δm)
--
-- TODO: diff-term, apply-term
Atlas-Δconst update = {!!}

Atlas-Δconst zip = {!!}

Atlas = calculus-with
  Atlas-type
  Atlas-const
  Atlas-lookup
  (lift-Δtype₀ Atlas-Δtype)
  Atlas-Δconst
