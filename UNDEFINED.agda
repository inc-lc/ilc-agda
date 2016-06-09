-- Allow holes in modules to import, by introducing a single general postulate.

module UNDEFINED where

postulate
  UNDEFINED : ∀ {ℓ} → {T : Set ℓ} → T
