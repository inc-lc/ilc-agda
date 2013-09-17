module Atlas.Change.Term where

open import Atlas.Syntax.Type
open import Atlas.Syntax.Term
open import Atlas.Change.Type

-- nil-changes

nil-const : ∀ {ι : Base} → Const  ∅ (base (ΔBase ι))
nil-const {ι} = neutral {ΔBase ι}

nil-term : ∀ {ι Γ} → Term Γ (base (ΔBase ι))
nil-term {Bool}   = curriedConst (nil-const {Bool})
nil-term {Map κ ι} = curriedConst (nil-const {Map κ ι})

-- diff-term and apply-term

import Parametric.Change.Term Const ΔBase as ChangeTerm

-- b₀ ⊝ b₁ = b₀ xor b₁
-- m₀ ⊝ m₁ = zip _⊝_ m₀ m₁

diff-base : ChangeTerm.DiffStructure
diff-base {Bool} = abs₂ (λ b₁ b₂ → xor! b₁ b₂)
diff-base {Map κ ι} = abs₂ (λ m₁ m₂ → zip! (abs diff-base) m₁ m₂)

-- b ⊕ Δb = b xor Δb
-- m ⊕ Δm = zip _⊕_ m Δm

apply-base : ChangeTerm.ApplyStructure
apply-base {Bool} = abs₂ (λ b₁ b₂ → xor! b₁ b₂)
apply-base {Map κ ι} = abs₂ (λ m₁ m₂ → zip! (abs apply-base) m₁ m₂)

-- Shorthands for working with diff-term and apply-term

open ChangeTerm.Structure

diff : ∀ {τ Γ} →
  Term Γ τ → Term Γ τ →
  Term Γ (ΔType τ)
diff = app₂ (lift-diff diff-base apply-base)

apply : ∀ {τ Γ} →
  Term Γ (ΔType τ) → Term Γ τ →
  Term Γ τ
apply = app₂ (lift-apply diff-base apply-base)

-- Shorthands for creating changes corresponding to
-- insertion/deletion.

insert : ∀ {κ ι Γ} →
  Term Γ (base κ) → Term Γ (base ι) →
  -- last argument is the change accumulator
  Term Γ (ΔType (base (Map κ ι))) →
  Term Γ (ΔType (base (Map κ ι)))

delete : ∀ {κ ι Γ} →
  Term Γ (base κ) → Term Γ (base ι) →
  Term Γ (ΔType (base (Map κ ι))) →
  Term Γ (ΔType (base (Map κ ι)))

insert k v acc = update! k (diff v neutral-term) acc
delete k v acc = update! k (diff neutral-term v) acc

