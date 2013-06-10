{-
Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).
-}

module ExplicitNil where

open import NatBag

open import Data.Bool
open import Data.Product hiding (map)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

-- Debug tool
absurd! : ∀ {A B : Set} → B → A → A → B
absurd! b _ _ = b


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

{-
-- Reformulating stableness as a decidable relation
-- Not sure if it is necessary or not.
data StableVar : ∀ {τ Γ} → Var Γ τ → Vars Γ → Set where
  abide-this : ∀ {τ Γ} → {vars : Vars Γ} → StableVar this (abide {τ} vars)
  abide-that : ∀ {τ Γ τ′} → {x : Var Γ τ} → {vars : Vars Γ} →
    StableVar x vars → StableVar (that {τ} {τ′} x) (abide vars)
  alter-that : ∀ {τ Γ τ′} → {x : Var Γ τ} → {vars : Vars Γ} →
    StableVar x vars → StableVar (that {τ} {τ′} x) (alter vars)

data Stable : ∀ {τ Γ} → Term Γ τ → Vars Γ → Set where
  stable-nat : ∀ {Γ n vars} → Stable {nats} {Γ} (nat n) vars
  stable-bag : ∀ {Γ b vars} → Stable {bags} {Γ} (bag b) vars
  stable-var : ∀ {τ Γ x vars} →
               StableVar {τ} {Γ} x vars → Stable (var x) vars
  stable-abs : ∀ {τ₁ τ₂ Γ vars} {t : Term (τ₁ • Γ) τ₂} →
               Stable t (abide vars) → Stable (abs t) vars
  -- TODO app add map diff union
-}

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
          Honest {Γ} vars ρ →
          Honest {τ • Γ} (alter vars) (dv • v • ρ)
  abide : ∀ {Γ τ v dv} → {vars : Vars Γ} → {ρ : ⟦ Δ-Context Γ ⟧} →
          v ⟦⊕⟧ dv ≡ v →
          Honest {Γ} vars ρ →
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

volatility⇒identity :
  ∀ {τ} {df dg : ⟦ Δ-Type τ ⟧} →
    df ≈ dg WRT (expect-volatility {τ}) → df ≡ dg

volatility⇒identity {nats} df≈dg = df≈dg
volatility⇒identity {bags} df≈dg = df≈dg
volatility⇒identity {τ₁ ⇒ τ₂} {df} {dg} df≈dg =
  extensionality (λ x → extensionality (λ dx →
    volatility⇒identity {τ₂} (df≈dg {x} {dx})))

df≈df : ∀ {τ} {df : ⟦ Δ-Type τ ⟧} {args : Args τ} → df ≈ df WRT args
df≈df {nats} = refl
df≈df {bags} = refl
df≈df {τ₁ ⇒ τ₂} {df} {abide args} =
  λ {x} {dx} _ → df≈df {τ₂} {df x dx} {args}
df≈df {τ₁ ⇒ τ₂} {df} {alter args} =
  λ {x} {dx}   → df≈df {τ₂} {df x dx} {args}

too-close : ∀ {τ Γ} {args : Args τ} →
  {df dg : Term (Δ-Context Γ) (Δ-Type τ)} {ρ : ⟦ Δ-Context Γ ⟧} →
  df ≡ dg → ⟦ df ⟧ ρ ≈ ⟦ dg ⟧ ρ WRT args

too-close {τ}{_} {args} {df} {dg} {ρ} df=dg
  rewrite df=dg = df≈df {τ} {⟦ dg ⟧ ρ} {args}

-- A variable does not change if its value is unchanging.
stabilityVar : ∀ {τ Γ} → (x : Var Γ τ) (vars : Vars Γ) →
  stableVar x vars ≡ true →
  ∀ {ρ : ⟦ Δ-Context Γ ⟧} → Honest vars ρ →
    ⟦ weakenVar Γ≼ΔΓ x ⟧ ρ ⟦⊕⟧ ⟦ deriveVar x ⟧ ρ ≡ ⟦ weakenVar Γ≼ΔΓ x ⟧ ρ

stabilityVar this (alter vars) () (alter honesty)
stabilityVar this (abide vars) refl (abide proof honesty) = proof

stabilityVar {τ} {τ′ • Γ } (that x) (abide vars) truth (abide _ honesty) =
  stabilityVar x vars (trans eq2 truth) honesty
  where
    eq2 : stableVar x vars ≡ stableVar (that {τ} {τ′} {Γ} x) (abide vars)
    eq2 = refl

stabilityVar (that x) (alter vars) truth honesty = {!ditto!}

-- A term does not change if its free variables are unchanging.
stability : ∀ {τ Γ} → (t : Term Γ τ) (vars : Vars Γ) →
  stable t vars ≡ true →
  ∀ {ρ : ⟦ Δ-Context Γ ⟧} → Honest vars ρ →
    ⟦ weaken Γ≼ΔΓ t ⟧ ρ ⟦⊕⟧ ⟦ derive t ⟧ ρ ≡ ⟦ weaken Γ≼ΔΓ t ⟧ ρ

stability (nat n) vars truth {ρ} _ = refl

stability (bag b) vars truth {ρ} _ = b++∅=b

stability (var x) vars truth {ρ} honesty =
  {!!}
  where
    eq1  : stableVar x vars ≡ stable (var x) vars
    eq1  = refl
    tVar : stableVar x vars ≡ true
    tVar = trans eq1 truth

stability (abs t) vars truth {ρ} honesty = {!!}
stability (app t t₁) vars truth {ρ} honesty = {!!}
stability (add t t₁) vars truth {ρ} honesty = {!!}
stability (map t t₁) vars truth {ρ} honesty = {!!}
stability (diff t t₁) vars truth {ρ} honesty = {!!}
stability (union t t₁) vars truth {ρ} honesty = {!!}

honestyVar : {τ : Type} → {Γ : Context} →
  (args : Args τ) → (vars : Vars Γ) →
  (x : Var Γ τ) → derive (var x) ≡ derive' args vars (var x)
honestyVar ∅-nat vars x = refl
honestyVar ∅-bag vars x = refl
honestyVar (abide args) vars x = refl
honestyVar (alter args) vars x = refl

-- If both the environment and the future arguments are honest
-- about nil changes, then the optimized derivation delivers
-- the same result as the original derivation.
honesty-is-the-best-policy : ∀ {τ Γ} (t : Term Γ τ) →
  (args : Args τ) → (vars : Vars Γ) →
  (ρ : ⟦ Δ-Context Γ ⟧) → Honest vars ρ →
  ⟦ derive t ⟧ ρ ≈ ⟦ derive' args vars t ⟧ ρ WRT args

honesty-is-the-best-policy (app f s) args vars ρ honesty
  with stable s vars | inspect (stable s) vars
... | true  | [ truth ] = {!!}
--  absurd! {!!} (stability s vars truth {ρ}) {!!}

... | false | [ falsehood ] = {!!}

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

honesty-is-the-best-policy (abs t) (abide args) vars ρ honesty =
  λ {x} {dx} x⊕dx=x → honesty-is-the-best-policy
    t args (abide vars) (dx • x • ρ) (abide x⊕dx=x honesty)

honesty-is-the-best-policy (abs t) (alter args) vars ρ honesty =
  λ {x} {dx} → honesty-is-the-best-policy
    t args (alter vars) (dx • x • ρ) (alter honesty)

honesty-is-the-best-policy (add m n) args vars ρ honesty = {!!}
honesty-is-the-best-policy (map f b) args vars ρ honesty = {!!}
honesty-is-the-best-policy (diff b d) args vars ρ honesty = {!!}
honesty-is-the-best-policy (union b d) args vars ρ honesty = {!!}

