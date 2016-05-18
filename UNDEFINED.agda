-- Allow holes in modules to import, by introducing a single general postulate.

module UNDEFINED where

open import Data.Unit.NonEta using (Hidden)
open import Data.Unit.NonEta public using (reveal)

postulate
  -- If this postulate would produce a T, it could be used as instance argument, triggering many ambiguities.
  -- This postulate is named in capitals because it introduces an inconsistency.
  -- Hence, this must be used through `reveal UNDEFINED`.
  UNDEFINED : ∀ {ℓ} → {T : Set ℓ} → Hidden T
