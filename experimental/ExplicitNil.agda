{-
Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).
-}

module ExplicitNil where

open import TaggedDeltaTypes

open import Data.NatBag renaming
  (map to mapBag ; empty to emptyBag ; update to updateBag)

open import Data.Bool
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

-- Debug tool
absurd! : ∀ {A B : Set} → A → A → B → B
absurd! _ _ b = b

-- A term is stable if all its free variables are unchanging
-- Alternative definition:
--
--     stable t vars = isNil t (derive t) bzgl. vars

stableVar : ∀ {τ Γ} → Var Γ τ → Vars Γ → Bool
stableVar this (abide _) = true
stableVar this (alter _) = false
stableVar (that x) (abide vars) = stableVar x vars
stableVar (that x) (alter vars) = stableVar x vars

stable : ∀ {τ Γ} → Term Γ τ → Vars Γ → Bool
stable (nat n) vars = true
stable (bag b) vars = true
stable (var x) vars = stableVar x vars
stable (abs t) vars = stable t (abide vars)
stable (app f x) vars = stable f vars ∧ stable x vars
stable (add m n) vars = stable m vars ∧ stable n vars
stable (map f b) vars = stable f vars ∧ stable b vars

-- Optimized derivation

derive' : ∀ {τ Γ} →
  Term Γ τ → {args : Args τ} → {vars : Vars Γ} → Δ-Term (Δ Γ) (Δ τ)

validity' : ∀ {τ Γ vars}
  {t : Term Γ τ}
  {ρ : Δ-Env Γ} {honesty : Honest ρ vars} →
  valid (⟦ t ⟧ (ignore ρ)) (⟦ derive' t {fickle-args} {vars} ⟧ ρ)

derive' (nat n) = derive (nat n)
derive' (bag b) = derive (bag b)
derive' (var x) = derive (var x)

derive' (add s t) {∅-nat} {vars} =
  Δadd (derive' s {∅-nat} {vars}) (derive' t {∅-nat} {vars})

derive' (map s t) {∅-bag} {vars} =
  if stable s vars
  then Δmap₁ s (derive' t {∅-bag} {vars})
  else Δmap₀ s (derive' s {abide ∅-nat} {vars})
             t (derive' t {∅-bag} {vars})

derive' (app s t) {args} {vars} =
  if stable t vars
  then Δapp (derive' s {abide args} {vars})
          t (derive' t {fickle-args} {vars})
            (λ {ρ vars honesty} →
               validity' {vars = vars} {t = t} {ρ}
                         {honesty = ?})
  else Δapp (derive' s {alter args} {vars})
          t (derive' t {fickle-args} {vars}) validity'

derive' t = {!!}

validity' = {!!}

