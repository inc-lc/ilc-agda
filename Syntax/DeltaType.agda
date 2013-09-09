module Syntax.DeltaType
  {Base : Set}
  (ΔBase : Base → Base)
  where

open import Syntax.Type.Plotkin Base

open import Function


-- Note: the above is *not* a monadic bind.
--
-- Proof. base` is the most straightforward `return` of the
-- functor `Type`.
--
--     return : Base → Type Base
--     return = base
--
-- Let
--
--     m : Type Base
--     m = base κ ⇒ base ι
--
-- then
--
--     m >>= return = lift-Δtype return m
--                  = base κ ⇒ base κ ⇒ base ι
--
-- violating the second monadic law, m >>= return ≡ m. ∎

-- Variant of lift-Δtype for (Δ : Base → Base).
ΔType : Type → Type
ΔType = lift-Δtype $ base ∘ ΔBase
-- This has a similar type to the type of `fmap`,
-- and `base` has a similar type to the type of `return`.
--
-- Similarly, for collections map can be defined from flatMap,
-- like lift-Δtype₀ can be defined in terms of lift-Δtype.
