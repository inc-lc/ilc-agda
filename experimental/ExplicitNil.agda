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

-- Useful statements about Boolean
∧-proj₁ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-proj₁ {false} {_} ()
∧-proj₁ {true} {false} ()
∧-proj₁ {true} {true} eq = refl

∧-proj₂ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-proj₂ {false} {_} ()
∧-proj₂ {true} {false} ()
∧-proj₂ {true} {true} eq = refl

-- Extending correctness-on-closed-terms
extended-correctness : ∀ {τ₁ τ₂ Γ} →
  (f : Term Γ (τ₁ ⇒ τ₂)) (x : Term Γ τ₁)
    {ρ : ⟦ Δ-Context Γ ⟧} {consistency : Consistent-Δenv ρ} →
    ⟦ weaken Γ≼ΔΓ f ⟧ ρ (⟦ weaken Γ≼ΔΓ x ⟧ ρ)
    ⟦⊕⟧ ⟦ derive f ⟧ ρ (⟦ weaken Γ≼ΔΓ x ⟧ ρ) (⟦ derive x ⟧ ρ)
  ≡ (⟦ weaken Γ≼ΔΓ f ⟧ ρ ⟦⊕⟧ ⟦ derive f ⟧ ρ)
    (⟦ weaken Γ≼ΔΓ x ⟧ ρ ⟦⊕⟧ ⟦ derive x ⟧ ρ)

extended-correctness {τ₁} {τ₂} {Γ} f x {ρ} {consistency} = sym (proj₂
  (validity-of-derive′ ρ {consistency} f
    (⟦ weaken Γ≼ΔΓ x ⟧ ρ) (⟦ derive x ⟧ ρ)
    (validity-of-derive′ ρ {consistency} x)))

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
  ∀ {x dx} {R[x,dx] : valid-Δ x dx}
  → close-enough (df x dx) (dg x dx) args
close-enough {τ₁ ⇒ τ₂} df dg (abide args) =
  ∀ {x dx} {validity : valid-Δ x dx}
  → x ⟦⊕⟧ dx ≡ x → close-enough (df x dx) (dg x dx) args

syntax close-enough df dg args = df ≈ dg WRT args

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

stabilityVar {τ} {τ′ • Γ } (that x) (abide vars) truth (abide _ honesty)
  = stabilityVar x vars truth honesty

stabilityVar {τ} {τ′ • Γ } (that x) (alter vars) truth (alter honesty)
  = stabilityVar x vars truth honesty

-- A term does not change if its free variables are unchanging.
stability : ∀ {τ Γ} → (t : Term Γ τ) (vars : Vars Γ) →
  stable t vars ≡ true →
  ∀ {ρ : ⟦ Δ-Context Γ ⟧} {_ : Consistent-Δenv ρ} → Honest vars ρ →
    ⟦ weaken Γ≼ΔΓ t ⟧ ρ ⟦⊕⟧ ⟦ derive t ⟧ ρ ≡ ⟦ weaken Γ≼ΔΓ t ⟧ ρ

stability (nat n) vars truth {ρ} _ = refl

stability (bag b) vars truth {ρ} _ = b++∅=b

stability (var x) vars truth {ρ} honesty =
  stabilityVar x vars truth honesty

stability (abs {τ₁} {τ₂} {Γ} t) vars truth {ρ} {consistency} honesty =
  extensionality (λ v → let
    dv : ⟦ Δ-Type τ₁ ⟧
    dv = ⟦derive⟧ v
    mutual-weakening : ⟦ weaken (keep τ₁ • Γ≼ΔΓ) t ⟧ (v • ρ)
                     ≡ ⟦ weaken Γ≼ΔΓ t ⟧ (dv • v • ρ)
    mutual-weakening =
      trans (weaken-sound t (v • ρ))
            (trans (cong (λ hole → ⟦ t ⟧ hole)
                     {x = ⟦ keep τ₁ • Γ≼ΔΓ ⟧ (v • ρ)}
                     {y = ⟦ Γ≼ΔΓ ⟧ (dv • v • ρ)}
                     refl)
                   (sym (weaken-sound t (dv • v • ρ))))
  in
    begin
      ⟦ weaken (keep τ₁ • Γ≼ΔΓ) t ⟧ (v • ρ) ⟦⊕⟧ ⟦ derive t ⟧ (dv • v • ρ)
    ≡⟨ cong (λ hole → hole ⟦⊕⟧ ⟦ derive t ⟧ (dv • v • ρ))
            mutual-weakening ⟩
      ⟦ weaken Γ≼ΔΓ t ⟧ (dv • v • ρ) ⟦⊕⟧ ⟦ derive t ⟧ (dv • v • ρ)
    ≡⟨ stability t (abide vars) truth
         {dv • v • ρ}
         {dρ=dv•v•dρ₀ (R[f,Δf] v) consistency}
         (abide (f⊕Δf=f v) honesty) ⟩
      ⟦ weaken Γ≼ΔΓ t ⟧ (dv • v • ρ)
    ≡⟨ sym mutual-weakening ⟩
      ⟦ weaken (keep τ₁ • Γ≼ΔΓ) t ⟧ (v • ρ)
    ∎
  ) where open ≡-Reasoning

stability (app s t) vars truth {ρ} {consistency} honesty =
  let
    f  = ⟦ weaken Γ≼ΔΓ s ⟧ ρ
    x  = ⟦ weaken Γ≼ΔΓ t ⟧ ρ
    df = ⟦ derive s ⟧ ρ
    dx = ⟦ derive t ⟧ ρ
  in
    begin
      f x ⟦⊕⟧ df x dx
    ≡⟨ extended-correctness s t {ρ} {consistency} ⟩
      (f ⟦⊕⟧ df) (x ⟦⊕⟧ dx)
    ≡⟨ stability s vars (∧-proj₁ truth) {ρ} {consistency} honesty ⟨$⟩
       stability t vars
         (∧-proj₂ {stable s vars} truth)
         {ρ} {consistency} honesty ⟩
      f x
    ∎ where open ≡-Reasoning

stability (add s t) vars truth {ρ} honesty = {!!}
stability (map s t) vars truth {ρ} honesty = {!!}
stability (diff s t) vars truth {ρ} honesty = {!!}
stability (union s t) vars truth {ρ} honesty = {!!}

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
  (ρ : ⟦ Δ-Context Γ ⟧) → {_ : Consistent-Δenv ρ} → Honest vars ρ →
  ⟦ derive t ⟧ ρ ≈ ⟦ derive' args vars t ⟧ ρ WRT args

honesty-is-the-best-policy (app f s) args vars ρ {consistency} honesty
  with stable s vars | inspect (stable s) vars
... | true  | [ truth ] = {!!}
-- Task after stability
-- --------------------
-- To use close-enough on f, must have validity of optimized derivative
-- of s. Validity should follow from constant expectation of volatility.
--
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

honesty-is-the-best-policy (abs t) (abide args)
  vars ρ {consistency} honesty =
  λ {x} {dx} {R[x,dx]} x⊕dx=x → honesty-is-the-best-policy
    t args (abide vars)
    (dx • x • ρ) {dρ=dv•v•dρ₀ R[x,dx] consistency}
    (abide x⊕dx=x honesty)

honesty-is-the-best-policy (abs t) (alter args)
  vars ρ {consistency} honesty =
  λ {x} {dx} {R[x,dx]} → honesty-is-the-best-policy
    t args (alter vars)
    (dx • x • ρ) {dρ=dv•v•dρ₀ R[x,dx] consistency}
    (alter honesty)

honesty-is-the-best-policy (add m n) args vars ρ honesty = {!!}
honesty-is-the-best-policy (map f b) args vars ρ honesty = {!!}
honesty-is-the-best-policy (diff b d) args vars ρ honesty = {!!}
honesty-is-the-best-policy (union b d) args vars ρ honesty = {!!}

