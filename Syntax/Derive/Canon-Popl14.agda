module Syntax.Derive.Canon-Popl14 where

open import Syntax.Term.Popl14 public
open import Syntax.Type.Popl14
open import Syntax.Language.Popl14

open import Data.Integer

deriveConst : ∀ {Γ Σ τ} → Const Σ τ →
      Terms (ΔContext Γ) (ΔContext Σ) →
      Term (ΔContext Γ) (ΔType τ)

deriveConst (intlit-c n) ∅ = intlit (+ 0)
deriveConst add-c        (ds • s • dt • t • ∅) = add ds dt
deriveConst minus-c      (dt • t • ∅) = minus dt
deriveConst empty-c      ∅ = empty
deriveConst insert-c     (ds • s • dt • t • ∅) = insert (s ⊕ ds) (t ⊕ dt) ⊝ insert s t
deriveConst union-c      (ds • s • dt • t • ∅) = union ds dt
deriveConst negate-c     (dt • t • ∅) = negate dt
deriveConst flatmap-c    (ds • s • dt • t • ∅) = flatmap (s ⊕ ds) (t ⊕ dt) ⊝ flatmap s t
deriveConst sum-c        (dt • t • ∅) = sum dt

open import Parametric.Change.Derive Popl14-Δbase deriveConst public
