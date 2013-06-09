{-
Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).
-}

module ExplicitNil where

open import NatBag

open import Data.Bool
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

data Args : (τ : Type) → Set where
  ∅-nat : Args nats
  ∅-bag : Args bags
  abide : ∀ {τ₁ τ₂} → (args : Args τ₂) → Args (τ₁ ⇒ τ₂)
  alter : ∀ {τ₁ τ₂} → (args : Args τ₂) → Args (τ₁ ⇒ τ₂)

-- Totally like subcontext relation _≼_ : (Γ₁ Γ₂ : Context) → Set
data Vars : Context → Set where
  ∅ : Vars ∅
  abide : ∀ {τ Γ} → Vars Γ → Vars (τ • Γ) -- is in the set
  alter : ∀ {τ Γ} → Vars Γ → Vars (τ • Γ) -- is out of the set

stableVar : ∀ {τ Γ} → Var Γ τ → Vars Γ → Bool
stableVar this (abide _) = true
stableVar this (alter _) = false
stableVar (that x) (abide vars) = stableVar x vars
stableVar (that x) (alter vars) = stableVar x vars

-- A term is stable if all its free variables are unchanging
-- Alternative definition:
--
--     stable t vars = isNil t (derive t)
--
stable : ∀ {τ Γ} → Term Γ τ → Vars Γ → Bool
stable (nat n) vars = true
stable (bag b) vars = true
stable (var x) vars = stableVar x vars
stable (abs t) vars = stable t (abide vars)
stable (app f x) vars = stable f vars ∧ stable x vars
stable (add m n) vars = stable m vars ∧ stable n vars
stable (map f b) vars = stable f vars ∧ stable b vars
stable (diff b d) vars = stable b vars ∧ stable d vars
stable (union b d) vars = stable b vars ∧ stable d vars

expect-volatility : {τ : Type} → Args τ
expect-volatility {τ₁ ⇒ τ₂} = alter expect-volatility
expect-volatility {nats} = ∅-nat
expect-volatility {bags} = ∅-bag

-- Type of `derive'`
derive' : ∀ {τ Γ} → Args τ → Vars Γ →
                    Term Γ τ → Term (Δ-Context Γ) (Δ-Type τ)

derive' {τ₁ ⇒ τ₂} (abide args) vars (abs t) =
  abs (abs (derive' args (abide vars) t))

derive' (alter args) vars (abs t) =
  abs (abs (derive' args (alter vars) t))

-- Assume, for safety, that all arguments that `t` will
-- eventually receive in `s` or receive curried out of `s`
-- are volatile.
derive' args vars (app s t) =
  if stable t vars
  then app (app (derive' (abide args) vars s) (weaken Γ≼ΔΓ t))
                (derive' expect-volatility vars t)
  else app (app (derive' (alter args) vars s) (weaken Γ≼ΔΓ t))
                (derive' expect-volatility vars t)

derive' args vars (map f b) =
  if stable f vars
  then map (weaken Γ≼ΔΓ f) (derive' args vars b)
  else map (weaken Γ≼ΔΓ f ⊕ derive' (abide ∅-nat) vars f)
           (weaken Γ≼ΔΓ b ⊕ derive' args vars b)
       ⊝ weaken Γ≼ΔΓ (map f b)

derive' args vars (diff b d) =
  diff (derive' args vars b) (derive' args vars d)

derive' args vars (union b d) =
  union (derive' args vars b) (derive' args vars d)

-- derive(x + y) = replace (x + y) by (dx snd + dy snd)
--               = λ f. f (x + y) (dx snd + dy snd)
derive' args vars (add m n) =
  abs (app (app (var this)
    (add (weaken (drop _ • Γ≼ΔΓ) m) (weaken (drop _ • Γ≼ΔΓ) n)))
    (add (app (weaken (drop _ • Γ≼Γ) (derive' args vars m)) snd)
         (app (weaken (drop _ • Γ≼Γ) (derive' args vars n)) snd)))

derive' args vars constant-or-variable = derive constant-or-variable

-- A description of variables is honest w.r.t. a Δ-environment
-- if every variable described as stable receives the nil change.
data Honest : ∀ {Γ} → Vars Γ → ⟦ Δ-Context Γ ⟧ → Set where
  clearly : Honest ∅ ∅
  alter : ∀ {Γ τ v dv} → {vars : Vars Γ} → {ρ : ⟦ Δ-Context Γ ⟧} →
          Honest {τ • Γ} (alter vars) (dv • v • ρ)
  abide : ∀ {Γ τ v dv} → {vars : Vars Γ} → {ρ : ⟦ Δ-Context Γ ⟧} →
          v ⟦⊕⟧ dv ≡ v →
          Honest {τ • Γ} (abide vars) (dv • v • ρ)

-- Two Δ-values are close enough w.r.t. a set of arguments if they
-- behave the same when fully applied (cf. extensionality) given
-- that each argument declared stable receives the nil change.
close-enough : ∀ {τ : Type} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → Args τ → Set
close-enough {nats} df dg args = df ≡ dg -- extensionally
close-enough {bags} df dg args = df ≡ dg -- literally
close-enough {τ₁ ⇒ τ₂} df dg (alter args) =
  ∀ {x dx} → close-enough (df x dx) (dg x dx) args
close-enough {τ₁ ⇒ τ₂} df dg (abide args) =
  ∀ {x dx} → x ⟦⊕⟧ dx ≡ x → close-enough (df x dx) (dg x dx) args

syntax close-enough df dg args = df ≈ dg WRT args

too-close : ∀ {τ Γ} {args : Args τ} →
  {df dg : Term (Δ-Context Γ) (Δ-Type τ)} {ρ : ⟦ Δ-Context Γ ⟧} →
  df ≡ dg → ⟦ df ⟧ ρ ≈ ⟦ dg ⟧ ρ WRT args

too-close {nats}{_}{_} {df} {dg} {ρ} = cong (λ hole → ⟦ hole ⟧ ρ)
too-close {bags}{_}{_} {df} {dg} {ρ} = {!!}
too-close {τ₁ ⇒ τ₂}{_}{_} {df} {dg} {ρ} = {!!}

honestyVar : {τ : Type} → {Γ : Context} →
  (args : Args τ) → (vars : Vars Γ) →
  (x : Var Γ τ) → derive (var x) ≡ derive' args vars (var x)
honestyVar ∅-nat vars x = refl
honestyVar ∅-bag vars x = refl
honestyVar (abide args) vars x = refl
honestyVar (alter args) vars x = refl

honesty-is-the-best-policy : ∀ {τ Γ} (t : Term Γ τ) →
  (args : Args τ) → (vars : Vars Γ) →
  (ρ : ⟦ Δ-Context Γ ⟧) → Honest vars ρ →
  ⟦ derive t ⟧ ρ ≈ ⟦ derive' args vars t ⟧ ρ WRT args

honesty-is-the-best-policy {nats} {Γ} (nat n) args vars ρ honesty =
  begin
    ⟦ derive (nat n) ⟧ ρ
  ≡⟨ cong (λ hole → ⟦ hole ⟧ ρ) (lemma Γ args vars) ⟩
    ⟦ derive' args vars (nat n) ⟧ ρ
  ∎ where
    open ≡-Reasoning
    lemma : (Γ : Context) (args : Args nats) (vars : Vars Γ) →
      derive (nat n) ≡ derive' {nats} {Γ} args vars (nat n)
    lemma ∅ ∅-nat ∅ = refl
    lemma (τ • Γ) ∅-nat (abide vars) = refl
    lemma (τ • Γ) ∅-nat (alter vars) = refl

honesty-is-the-best-policy {bags} {Γ} (bag b) args vars ρ honesty =
  begin
    ⟦ derive (bag b) ⟧ ρ
  ≡⟨ cong (λ hole → ⟦ hole ⟧ ρ) (lemma Γ args vars) ⟩
    ⟦ derive' args vars (bag b) ⟧ ρ
  ∎ where
    open ≡-Reasoning
    lemma : (Γ : Context) (args : Args bags) (vars : Vars Γ) →
      derive (bag b) ≡ derive' {bags} {Γ} args vars (bag b)
    lemma ∅ ∅-bag ∅ = refl
    lemma (τ • Γ) ∅-bag (abide vars) = refl
    lemma (τ • Γ) ∅-bag (alter vars) = refl

honesty-is-the-best-policy {τ} {Γ} (var x) args vars ρ honesty =
  too-close {τ} {Γ} (honestyVar args vars x)

honesty-is-the-best-policy (abs t) args vars ρ honesty = {!!}
honesty-is-the-best-policy (app f x) args vars ρ honesty = {!!}
honesty-is-the-best-policy (add m n) args vars ρ honesty = {!!}
honesty-is-the-best-policy (map f b) args vars ρ honesty = {!!}
honesty-is-the-best-policy (diff b d) args vars ρ honesty = {!!}
honesty-is-the-best-policy (union b d) args vars ρ honesty = {!!}

