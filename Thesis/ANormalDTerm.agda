module Thesis.ANormalDTerm where

open import Thesis.ANormal

{-
Try defining an alternative syntax for differential terms. We'll need this for
cache terms. Maybe?

Two options:

1. use standard untyped lambda calculus as a target language.

2. use a specialized syntax as a target language. This requires much more
  weakening in the syntax, which is a nuisance in proofs. Maybe use deBruijn
  levels instead?

Also, caching uses quite a bit of sugar on top of lambda calculus, with pairs
and what not.
-}

{-
-- To define an alternative syntax for the derivation output, let's remember that:
derive (var x) = dvar dx
derive (let y = f x in t) = let y = f x ; dy = df x dx in derive t
-}

-- Attempt 1 leads to function calls in datatype indexes. That's very very bad!
module Try1 where

-- data DTerm : (Γ : Context) (τ : Type) → Set where
--   dvar : ∀ {Γ τ} (x : Var Γ τ) →
--     DTerm (ΔΓ Γ) (Δt τ)
--   dlett : ∀ {Γ σ τ₁ τ} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → DTerm (Δt τ₁ • τ₁ • ΔΓ Γ) (Δt τ) → DTerm (ΔΓ Γ) (Δt τ)

-- derive-dterm : ∀ {Γ τ} → Term Γ τ → DTerm (ΔΓ Γ) (Δt τ)
-- derive-dterm (var x) = dvar x
-- derive-dterm (lett f x t) = dlett f x (derive-dterm t)

-- Case split on dt FAILS!
-- ⟦_⟧DTerm : ∀ {Γ τ} → DTerm (ΔΓ Γ) (Δt τ) → ⟦ ΔΓ Γ ⟧Context → ⟦ Δt τ ⟧Type
-- ⟦ dt ⟧DTerm ρ = {!dt!}


module Try3 where
  -- A DTerm evaluates in context (ΔΓ Γ) (Δt τ).
  data DTerm : (Γ : Context) (τ : Type) → Set where
    dvar : ∀ {Γ τ} (x : Var (ΔΓ Γ) (Δt τ)) →
      DTerm Γ τ
    dlett : ∀ {Γ τ σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → DTerm (τ₁ • Γ) τ → DTerm Γ τ

module Try2 where
  -- This is literally isomorphic to the source type :-| derivation is part of erasure...
  data DTerm : (Γ : Context) (τ : Type) → Set where
    dvar : ∀ {Γ τ} (x : Var Γ τ) →
      DTerm Γ τ
  --  dlett : ∀ {Γ σ τ₁ τ} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → DTerm (Δt τ₁ • τ₁ • ΔΓ Γ) (Δt τ) → DTerm (ΔΓ Γ) (Δt τ)

    dlett : ∀ {Γ τ σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) →
      DTerm (τ₁ • Γ) τ →
      DTerm Γ τ

  derive-dterm : ∀ {Γ τ} → Term Γ τ → DTerm Γ τ
  derive-dterm (var x) = dvar x
  derive-dterm (lett f x t) = dlett f x (derive-dterm t)

  -- Incremental semantics over terms. Same results as base semantics over change
  -- terms. But less weakening.
  ⟦_⟧DTerm : ∀ {Γ τ} → DTerm Γ τ → ⟦ ΔΓ Γ ⟧Context → ⟦ Δt τ ⟧Type
  ⟦ dvar x ⟧DTerm dρ = ⟦ derive-var x ⟧Var dρ
  ⟦ dlett f x dt ⟧DTerm dρ =
    let ρ = ⟦ Γ≼ΔΓ ⟧≼ dρ
    in ⟦ dt ⟧DTerm
      ( ⟦ derive-var f ⟧Var dρ (⟦ x ⟧Var ρ) (⟦ derive-var x ⟧Var dρ)
      • ⟦ f ⟧Var ρ (⟦ x ⟧Var ρ)
      • dρ)
