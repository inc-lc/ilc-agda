{-
Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).
-}

module ExplicitNil where

open import TaggedDeltaTypes

open import Data.Nat
open import Data.Bool
open import Data.Product hiding (map)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

-----------------------------------
-- Describing the lack of change --
-----------------------------------

data Args : (τ : Type) → Set where
  ∅-nat : Args nats
  ∅-bag : Args bags
  alter : ∀ {τ₁ τ₂} → (args : Args τ₂) → Args (τ₁ ⇒ τ₂)
  abide : ∀ {τ₁ τ₂} → (args : Args τ₂) → Args (τ₁ ⇒ τ₂)

expect-volatility : {τ : Type} → Args τ
expect-volatility {τ₁ ⇒ τ₂} = alter expect-volatility
expect-volatility {nats} = ∅-nat
expect-volatility {bags} = ∅-bag

proj-∧ : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
proj-∧ {false} {_} ()
proj-∧ {true} {false} ()
proj-∧ {true} {true} truth = refl , refl

--------------------------
-- Optimized derivation --
--------------------------

derive' : ∀ {τ Γ} →
  Term Γ τ → {args : Args τ} → {vars : Vars Γ} → ΔTerm Γ τ

derive' (nat n) = derive (nat n)
derive' (bag b) = derive (bag b)
derive' (var x) = derive (var x)

derive' (add s t) {∅-nat} {vars} =
  Δadd (derive' s {∅-nat} {vars}) (derive' t {∅-nat} {vars})

derive' (abs t) {alter args} {vars} = Δabs (derive' t {args} {alter vars})
derive' (abs t) {abide args} {vars} = Δabs (derive' t {args} {abide vars})

derive' (app s t) {args} {vars} =
  if stable t vars
  then Δapp (derive' s {abide args} {vars})
          t (derive' t {expect-volatility} {vars})
  else Δapp (derive' s {alter args} {vars})
          t (derive' t {expect-volatility} {vars})

derive' (map s t) {∅-bag} {vars} with stable s vars
... | true  = Δmap₁ s (derive' t {∅-bag} {vars})
... | false = Δmap₀ s (derive' s {abide ∅-nat} {vars})
                t (derive' t {∅-bag} {vars})

-----------------------------------------------------
-- A program equivalence preserved by optimization --
-----------------------------------------------------

-- Two Δ-values are close enough w.r.t. a set of arguments if they
-- behave the same when fully applied (cf. extensionality) given
-- that each argument declared stable receives the nil change.
--
--     du ≈ dv wrt args
--
close-enough : ∀ {τ : Type} → ΔVal τ → ΔVal τ → Args τ → Set
close-enough {nats} du dv args = du ≡ dv -- extensionally
close-enough {bags} du dv args = du ≡ dv -- literally
close-enough {σ ⇒ τ} df dg (alter args) = ∀ {v dv R[v,dv]} →
  close-enough (df v dv R[v,dv]) (dg v dv R[v,dv]) args
close-enough {σ ⇒ τ} df dg (abide args) = ∀ {v dv R[v,dv]} →
  v ⊕ dv ≡ v → close-enough (df v dv R[v,dv]) (dg v dv R[v,dv]) args

syntax close-enough du dv args = du ≈ dv wrt args

ext³ : ∀
  {A : Set}
  {B : A → Set}
  {C : (a : A) → B a → Set }
  {D : (a : A) → (b : B a) → C a b → Set}
  {f g : (a : A) → (b : B a) → (c : C a b) → D a b c} →
  ((a : A) (b : B a) (c : C a b) → f a b c ≡ g a b c) → f ≡ g

ext³ fabc=gabc = ext (λ a → ext (λ b → ext (λ c → fabc=gabc a b c)))
  where ext = extensionality

≡to≈ : ∀ {τ args} {df dg : ΔVal τ} →
  df ≡ dg → df ≈ dg wrt args

≡to≈ {nats} df≡dg = df≡dg
≡to≈ {bags} df≡dg = df≡dg
≡to≈ {σ ⇒ τ} {alter args} df≡dg = λ {v} {dv} {R[v,dv]} →
  ≡to≈ (cong (λ hole → hole v dv R[v,dv]) df≡dg)
≡to≈ {σ ⇒ τ} {abide args} df≡dg = λ {v} {dv} {R[v,dv]} v⊕dv=v →
  ≡to≈ (cong (λ hole → hole v dv R[v,dv]) df≡dg)

≈to≡ : ∀ {τ} {df dg : ΔVal τ} →
  df ≈ dg wrt (expect-volatility {τ}) → df ≡ dg

≈to≡ {nats} df≈dg = df≈dg
≈to≡ {bags} df≈dg = df≈dg
≈to≡ {σ ⇒ τ} {df} {dg} df≈dg =
  ext³ (λ v dv R[v,dv] → ≈to≡ {τ} (df≈dg {v} {dv} {R[v,dv]}))

------------------------
-- Stability of terms --
------------------------

-- A variable does not change if its value is unchanging.

stabilityVar : ∀ {τ Γ} {x : Var Γ τ} {vars} →
  (S : stableVar x vars ≡ true) → ∀ {ρ : ΔEnv Γ}
  (H : Honest ρ vars) →
  ⟦ x ⟧ (ignore ρ) ⊕ ⟦ x ⟧ΔVar ρ ≡ ⟦ x ⟧ (ignore ρ)

stabilityVar {x = this} {alter vars} () _
stabilityVar {x = this} {abide vars} refl (abide proof _) = proof
stabilityVar {x = that y} {alter vars} S (alter H) =
  stabilityVar {x = y} {vars} S H
stabilityVar {x = that y} {abide vars} S (abide _ H) =
  stabilityVar {x = y} {vars} S H

-- A term does not change if its free variables are unchanging.

stability : ∀ {τ Γ} {t : Term Γ τ} {vars} →
  (S : stable t vars ≡ true) → ∀ {ρ : ΔEnv Γ}
  (H : Honest ρ vars) →
    ⟦ t ⟧ (ignore ρ) ⊕ ⟦ derive t ⟧Δ ρ (unrestricted t)
  ≡ ⟦ t ⟧ (ignore ρ)

stability {t = nat n} _ _ = refl
stability {t = bag b} _ _ = b++∅=b
stability {t = var x} {vars} S H = stabilityVar {x = x} {vars} S H

stability {t = abs t} {vars} S {ρ} H = extensionality
  (λ w → stability {t = t} {abide vars} S (abide v⊕[u⊝v]=u H))

stability {t = app s t} {vars} S {ρ} H =
  let
    f = ⟦ s ⟧ (ignore ρ)
    v = ⟦ t ⟧ (ignore ρ)
    df = ⟦ derive s ⟧Δ ρ (unrestricted s)
    dv = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Ss , St = proj-∧ S
  in
    begin
      f v ⊕ df v dv (validity {t = t})
    ≡⟨ sym (corollary s t) ⟩
      (f ⊕ df) (v ⊕ dv)
    ≡⟨ stability {t = s} Ss H ⟨$⟩ stability {t = t} St H ⟩
      f v
    ∎ where open ≡-Reasoning

stability {t = add s t} {vars} S {ρ} H =
  let
    Ss , St = proj-∧ S
  in cong₂ _+_ (stability {t = s} Ss H) (stability {t = t} St H)

stability {t = map s t} {vars} S {ρ} H =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    df = ⟦ derive s ⟧Δ ρ (unrestricted s)
    db = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Ss , St = proj-∧ S
    map = mapBag
  in
  begin
    map f b ⊕ (map (f ⊕ df) (b ⊕ db) ⊝ map f b)
  ≡⟨ b++[d\\b]=d ⟩
    map (f ⊕ df) (b ⊕ db)
  ≡⟨ cong₂ map (stability {t = s} Ss H) (stability {t = t} St H) ⟩
    map f b
  ∎ where open ≡-Reasoning

-----------------------------------------
-- Correctness of optimized derivation --
-----------------------------------------

-- The result of optimized derivation is valid for every environment
-- that does not lie about nil changes.

honesty⇒validity : ∀ {τ Γ} (t : Term Γ τ) {vars ρ} →
  Honest ρ vars →
  ∀ {args} → derive' t {args} {vars} is-valid-for ρ

-- If both the environment and the future arguments are honest
-- about nil changes, then the optimized derivation delivers
-- the same result as the original derivation.

honesty :
  ∀ {τ Γ} {t : Term Γ τ} {args vars} {ρ : ΔEnv Γ} {H : Honest ρ vars} →
    ⟦ derive t ⟧Δ ρ (unrestricted t)
  ≈ ⟦ derive' t {args} {vars} ⟧Δ ρ (honesty⇒validity t H) wrt args

honesty⇒validity (nat n) H = tt
honesty⇒validity (bag b) H = tt
honesty⇒validity (var x) H = tt

honesty⇒validity (abs t) {vars} H {alter args} = λ v dv R[v,dv] →
  honesty⇒validity t (alter H)
honesty⇒validity (abs t) {vars} H {abide args} = {!λ v dv R[v,dv] →
     ??? Where to get proof that v⊕dv=v ???
  !}

honesty⇒validity (app s t) H = {!!}

honesty⇒validity (add s t) H {∅-nat} =
  cons (honesty⇒validity s H) (honesty⇒validity t H) tt tt

honesty⇒validity (map s t) {vars} H {∅-bag}
  with stable s vars
... | true  = honesty⇒validity t H
... | false = cons (honesty⇒validity s H) (honesty⇒validity t H) tt tt

honesty = {!!}

{-
honestMap-conclusion : ∀ {Γ}
  (s : Term Γ (nats ⇒ nats)) (t : Term Γ bags) (vars : Vars Γ)
  (ρ : ΔEnv Γ) (H : Honest ρ vars) → Set

honestMap : ∀ {Γ}
  (s : Term Γ (nats ⇒ nats)) (t : Term Γ bags) {vars} →
  ∀ {ρ} (H : Honest ρ vars)
  honestMap-conclusion s t vars ρ H

honestMap-conclusion s t vars ρ H = 
    ⟦ derive (map s t) ⟧Δ ρ (unrestricted (map s t))
  ≡ ⟦ Δmap₁ s (derive' t {∅-bag} {vars}) ⟧Δ
  --⟦ derive' (map s t) {∅-bag} {vars} ⟧Δ
    ρ (honesty⇒validity (map s t) H {∅-bag})
--     ^^^^^^ THIS IS PROBLEMATIC

honestMap s t {vars} with stable s vars | inspect (stable s) vars
... | false | Unstable = λ {ρ} H → {!!}
  where open ≡-Reasoning
... | true | [ S ] rewrite S = λ {ρ} H →
  {!!}
  where open ≡-Reasoning
-}

