module derivation where

open import lambda

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₂

apply : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ τ ⇒ τ)
apply {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app apply (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λf.  λx.           apply (     df                       x        )  (     f                 x        )

compose : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ Δ-Type τ ⇒ Δ-Type τ)
compose {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app compose (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λdg. λx.           compose (     df                       x         ) (     dg                x      )

nil : ∀ {τ Γ} → Term Γ (Δ-Type τ)
nil {τ₁ ⇒ τ₂} =
    abs nil
 -- λx. nil

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

-- changes 'x' to 'nil' (if internally bound) or 'dx' (if externally bound)

Δ-var : ∀ {Γ₁ Γ₂ τ} → Var (Γ₁ ⋎ Γ₂) τ → Term (Δ-Context Γ₂) (Δ-Type τ)
Δ-var {∅} x = var (rename x)
Δ-var {τ • Γ} this = nil
Δ-var {τ • Γ} (that x) = Δ-var {Γ} x

-- CHANGE TERMS

Δ-term : ∀ {Γ₁ Γ₂ τ} → Term (Γ₁ ⋎ Γ₂) τ → Term (Γ₁ ⋎ Δ-Context Γ₂) (Δ-Type τ)
Δ-term {Γ} (abs {τ₁ = τ} t) = abs (Δ-term {τ • Γ} t)
Δ-term {Γ} (app t₁ t₂) = {!!}
Δ-term {Γ} (var x) = weaken {∅} {Γ} (Δ-var {Γ} x)
