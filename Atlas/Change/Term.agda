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

open import Parametric.Change.Term Const ΔBase

-- b₀ ⊝ b₁ = b₀ xor b₁
-- m₀ ⊝ m₁ = zip _⊝_ m₀ m₁

diff-base : ∀ {ι Γ} →
  Term Γ (base ι ⇒ base ι ⇒ ΔType (base ι))
diff-base {Bool} = abs₂ (λ b₁ b₂ → xor! b₁ b₂)
diff-base {Map κ ι} = abs₂ (λ m₁ m₂ → zip! (abs diff-base) m₁ m₂)

-- b ⊕ Δb = b xor Δb
-- m ⊕ Δm = zip _⊕_ m Δm

Atlas-apply : ∀ {ι Γ} →
  Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)
Atlas-apply {Bool} = abs₂ (λ b₁ b₂ → xor! b₁ b₂)
Atlas-apply {Map κ ι} = abs₂ (λ m₁ m₂ → zip! (abs Atlas-apply) m₁ m₂)

-- Shorthands for working with diff-term and apply-term

diff : ∀ {τ Γ} →
  Term Γ τ → Term Γ τ →
  Term Γ (ΔType τ)
diff = app₂ (lift-diff diff-base Atlas-apply)

apply : ∀ {τ Γ} →
  Term Γ (ΔType τ) → Term Γ τ →
  Term Γ τ
apply = app₂ (lift-apply diff-base Atlas-apply)

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

