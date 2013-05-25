module derivation where

open import lambda

-- This file contains an alternative calculus, where there are no
-- additional primitives in the calculus, derivatives are distinct
-- from changes (hence the different Δ-Type definition), and changes
-- are intentionally boring and easy.

-- I am not sure about the status of this file though, and whether it
-- is possible to build such a calculus (which I think it is).

-- KO: The inductive cases look boring since they don't actually do
-- anything (which explains why compose and apply are the same)

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₂
Δ-Type bool = bool

apply : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ τ ⇒ τ)
apply {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app apply (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λf.  λx.           apply (     df                       x        )  (     f                 x        )
apply {bool} = {!!}

compose : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ Δ-Type τ ⇒ Δ-Type τ)
compose {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app (compose {τ₂}) (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λdg. λx.           compose (     df                       x         ) (     dg                x      )
compose {bool} = {!!}

nil : ∀ {τ Γ} → Term Γ (Δ-Type τ)
nil {τ₁ ⇒ τ₂} =
    abs (nil {τ₂})
 -- λx. nil
nil {bool} = {!!}

-- Hey, apply is α-equivalent to compose, what's going on?
-- Oh, and `Δ-Type` is the identity function?

-- CHANGE CONTEXTS

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = τ • Δ-Type τ • Δ-Context Γ

-- CHANGE VARIABLES

-- changes 'x' to 'dx'

rename : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
rename this = that this
rename (that x) = that (that (rename x))

-- Weakening of a term needed during derivation - change x to x in a context which also includes dx.
-- The actual specification is more complicated, study the type signature.
adaptVar : ∀ {τ} Γ₁ Γ₂ → Var (Γ₁ ⋎ Γ₂) τ → Var (Γ₁ ⋎ Δ-Context Γ₂) τ
adaptVar ∅ (τ₂ • Γ₂) this = this
adaptVar ∅ (τ₂ • Γ₂) (that x) = that (that (adaptVar ∅ Γ₂ x))
adaptVar (τ₁ • Γ₁) Γ₂ this = this
adaptVar (τ₁ • Γ₁) Γ₂ (that x) = that (adaptVar Γ₁ Γ₂ x)

adapt : ∀ {τ} Γ₁ Γ₂ → Term (Γ₁ ⋎ Γ₂) τ → Term (Γ₁ ⋎ Δ-Context Γ₂) τ
adapt {τ₁ ⇒ τ₂} Γ₁ Γ₂ (abs t) = abs (adapt (τ₁ • Γ₁) Γ₂ t)
adapt Γ₁ Γ₂ (app t₁ t₂) = app (adapt Γ₁ Γ₂ t₁) (adapt Γ₁ Γ₂ t₂)
adapt Γ₁ Γ₂ (var t) = var (adaptVar Γ₁ Γ₂ t)
adapt Γ₁ Γ₂ true = true
adapt Γ₁ Γ₂ false = false
adapt Γ₁ Γ₂ (cond tc t₁ t₂) = cond (adapt Γ₁ Γ₂ tc) (adapt Γ₁ Γ₂ t₁) (adapt Γ₁ Γ₂ t₂)

-- changes 'x' to 'nil' (if internally bound) or 'dx' (if externally bound)

Δ-var : ∀ {Γ₁ Γ₂ τ} → Var (Γ₁ ⋎ Γ₂) τ → Term (Δ-Context Γ₂) (Δ-Type τ)
Δ-var {∅} x = var (rename x)
Δ-var {τ • Γ} this = nil {τ}
Δ-var {τ • Γ} (that x) = Δ-var {Γ} x

-- Note: this should be the derivative with respect to the first variable.
nabla : ∀ {Γ τ₁ τ₂} → (t₀ : Term Γ (τ₁ ⇒ τ₂)) → Term Γ (τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂)
nabla = {!!}

-- CHANGE TERMS
Δ-term : ∀ {Γ₁ Γ₂ τ} → Term (Γ₁ ⋎ Γ₂) τ → Term (Γ₁ ⋎ Δ-Context Γ₂) (Δ-Type τ)
Δ-term {Γ} (abs {τ₁ = τ} t) = abs (Δ-term {τ • Γ} t)

-- To recheck: which is the order in which to apply the changes? When I did my live proof to Klaus, I came up with this order:
-- (Δ-term t₁) (t₂ ⊕ (Δ-term t₂)) ∘ (∇ t₁) t₂ (Δ-term t₂)
-- corresponding to:
Δ-term {Γ₁} {Γ₂} {τ} (app t₁ t₂) = app (app (compose {τ}) (app (Δ-term {Γ₁} t₁) (app (app apply (Δ-term {Γ₁} {Γ₂} t₂)) (adapt Γ₁ Γ₂ t₂))))
  (app (adapt Γ₁ Γ₂ (app (nabla {Γ₁ ⋎ Γ₂} t₁) t₂)) (Δ-term {Γ₁} {Γ₂} t₂))

Δ-term {Γ} (var x) = weaken {∅} {Γ} (Δ-var {Γ} x)
Δ-term {Γ} true = {!!}
Δ-term {Γ} false = {!!}
Δ-term {Γ} (cond t₁ t₂ t₃) = {!!}
