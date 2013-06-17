{-
Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).
-}

module ExplicitNil where

open import TaggedDeltaTypes

open import Data.Nat
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)
open import Relation.Binary.Core using (Decidable)
open import Relation.Nullary.Core using (yes ; no)

ext³ : ∀
  {A : Set}
  {B : A → Set}
  {C : (a : A) → B a → Set }
  {D : (a : A) → (b : B a) → C a b → Set}
  {f g : (a : A) → (b : B a) → (c : C a b) → D a b c} →
  ((a : A) (b : B a) (c : C a b) → f a b c ≡ g a b c) → f ≡ g

ext³ fabc=gabc = ext (λ a → ext (λ b → ext (λ c → fabc=gabc a b c)))
  where ext = extensionality

proj-H : ∀ {Γ : Context} {ρ : ΔEnv Γ} {us vs} →
  Honest ρ (FV-union us vs) → Honest ρ us × Honest ρ vs
proj-H {∅} {us = ∅} {vs = ∅} clearly = clearly , clearly
proj-H {us = alter us} {alter vs} (alter H) =
  let uss , vss = proj-H H in alter uss , alter vss
proj-H {us = alter us} {abide vs} (abide eq H) =
  let uss , vss = proj-H H in
  alter uss , abide eq vss
proj-H {us = abide us} {alter vs} (abide eq H) =
  let uss , vss = proj-H H in
  abide eq uss , alter vss
proj-H {us = abide us} {abide vs} (abide eq H) =
  let uss , vss = proj-H H in
  abide eq uss , abide eq vss

stabilityVar : ∀ {τ Γ} {x : Var Γ τ} →
  ∀ {ρ : ΔEnv Γ} (H : Honest ρ (select-just x)) →
  ⟦ x ⟧ (ignore ρ) ⊕ ⟦ x ⟧ΔVar ρ ≡ ⟦ x ⟧ (ignore ρ)

stabilityVar {x = this} (abide proof _) = proof
stabilityVar {x = that y} (alter H) = stabilityVar {x = y} H

stability : ∀ {τ Γ} {t : Term Γ τ} →
  ∀ {ρ : ΔEnv Γ} (H : Honest ρ (FV t)) →
    ⟦ t ⟧ (ignore ρ) ⊕ ⟦ derive t ⟧Δ ρ (unrestricted t)
  ≡ ⟦ t ⟧ (ignore ρ)

-- Boilerplate begins
stabilityAbs : ∀ {σ τ Γ} {t : Term (σ • Γ) τ} →
  ∀ {ρ : ΔEnv Γ} (H : Honest ρ (FV (abs t))) →
  (v : ⟦ σ ⟧) →
    ⟦ t ⟧ (v • ignore ρ) ⊕
    ⟦ derive t ⟧Δ (cons v (v ⊝ v) R[v,u⊝v] ρ) (unrestricted t)
  ≡ ⟦ t ⟧ (v • ignore ρ)
stabilityAbs {t = t} {ρ} H v with FV t | inspect FV t
... | abide vars | [ case0 ] = stability {t = t} Ht
  where
  Ht : Honest (cons v (v ⊝ v) R[v,u⊝v] ρ) (FV t)
  Ht rewrite case0 = abide v⊕[u⊝v]=u H
... | alter vars | [ case1 ] = stability {t = t} Ht
  where
  Ht : Honest (cons v (v ⊝ v) R[v,u⊝v] ρ) (FV t)
  Ht rewrite case1 = alter H
-- Boilerplate ends

stability {t = nat n} H = refl
stability {t = bag b} H = b++∅=b
stability {t = var x} H = stabilityVar H
stability {t = abs t} {ρ} H = extensionality (stabilityAbs {t = t} H)
stability {t = app s t} {ρ} H =
  let
    f = ⟦ s ⟧ (ignore ρ)
    v = ⟦ t ⟧ (ignore ρ)
    df = ⟦ derive s ⟧Δ ρ (unrestricted s)
    dv = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Hs , Ht = proj-H H
  in
    begin
      f v ⊕ df v dv (validity {t = t})
    ≡⟨ sym (corollary s t) ⟩
      (f ⊕ df) (v ⊕ dv)
    ≡⟨ stability {t = s} Hs ⟨$⟩ stability {t = t} Ht ⟩
      f v
    ∎ where open ≡-Reasoning
stability {t = add s t} H =
  let Hs , Ht = proj-H H
  in cong₂ _+_ (stability {t = s} Hs) (stability {t = t} Ht)
stability {t = map s t} {ρ} H =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    df = ⟦ derive s ⟧Δ ρ (unrestricted s)
    db = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Hs , Ht = proj-H H
    map = mapBag
  in
  begin
    map f b ⊕ (map (f ⊕ df) (b ⊕ db) ⊝ map f b)
  ≡⟨ b++[d\\b]=d ⟩
    map (f ⊕ df) (b ⊕ db)
  ≡⟨ cong₂ map (stability {t = s} Hs) (stability {t = t} Ht) ⟩
    map f b
  ∎ where open ≡-Reasoning

eq-map : ∀ {Γ}
  (s    : Term Γ (nats ⇒ nats))
  (t    : Term Γ bags)
  (ρ    : ΔEnv Γ)
  (H    : Honest ρ (FV s)) →
    ⟦ Δmap₀ s (derive s) t (derive t) ⟧Δ ρ (unrestricted (map s t))
  ≡ ⟦ Δmap₁ s (derive t) ⟧Δ ρ (cons (unrestricted t) H tt tt)

eq-map s t ρ H =
  let
    ds = derive s
    dt = derive t
    f  = ⟦ s ⟧ (ignore ρ)
    v  = ⟦ t ⟧ (ignore ρ)
    df = ⟦ ds ⟧Δ ρ (unrestricted s)
    dv = ⟦ dt ⟧Δ ρ (unrestricted t)

    eq1 : ⟦ Δmap₀ s ds t dt ⟧Δ ρ (unrestricted (map s t))
        ≡ mapBag (f ⊕ df) (v ⊕ dv) ⊝ mapBag f v
    eq1 = refl

    eq2 : mapBag (f ⊕ df) (v ⊕ dv) ⊝ mapBag f v
        ≡ mapBag f dv
    eq2 = trans
      (cong (λ hole → hole ⊝ mapBag f v) (trans
        (cong (λ hole → mapBag hole (v ⊕ dv)) (stability {t = s} H))
        map-over-++))
      [b++d]\\b=d

    eq3 : mapBag f dv
        ≡ ⟦ Δmap₁ s (derive t) ⟧Δ ρ (cons (unrestricted t) H tt tt)
    eq3 = refl

  in trans eq1 (trans eq2 eq3)

-- Vars test
none-selected? : ∀ {Γ} → (vs : Vars Γ) → (vs ≡ select-none) ⊎ ⊤
none-selected? ∅ = inj₁ refl
none-selected? (abide vs) = inj₂ tt
none-selected? (alter vs) with none-selected? vs
... | inj₁ vs=∅ rewrite vs=∅ = inj₁ refl
... | inj₂ _ = inj₂ tt

closed? : ∀ {τ Γ} → (t : Term Γ τ) → (FV t ≡ select-none) ⊎ ⊤
closed? t = none-selected? (FV t)

vacuous-honesty : ∀ {Γ} {ρ : ΔEnv Γ} → Honest ρ select-none
vacuous-honesty {∅} {∅} = clearly
vacuous-honesty {τ • Γ} {cons _ _ _ ρ} = alter (vacuous-honesty {ρ = ρ})

-- Immunity of closed terms to dishonest environments
immune : ∀ {τ Γ} {t : Term Γ τ} →
  (FV t ≡ select-none) → ∀ {ρ} → Honest ρ (FV t)
immune {t = t} eq rewrite eq = vacuous-honesty

-- Ineffectual first optimization step
derive1 : ∀ {τ Γ} → Term Γ τ → ΔTerm Γ τ
derive1 (map s t) with closed? s
... | inj₁ is-closed = Δmap₁ s (derive t)
... | inj₂ tt = derive (map s t)
derive1 others = derive others

valid1 : ∀ {τ Γ} (t : Term Γ τ) {ρ : ΔEnv Γ} → derive1 t is-valid-for ρ
valid1 (nat n) = tt
valid1 (bag b) = tt
valid1 (var x) = tt
valid1 (abs t) = λ _ _ _ → unrestricted t
valid1 (app s t) =
  cons (unrestricted s) (unrestricted t) (validity {t = t}) tt
valid1 (add s t) =
  cons (unrestricted s) (unrestricted t) tt tt
valid1 (map s t) {ρ} with closed? s
... | inj₂ tt = cons (unrestricted s) (unrestricted t) tt tt
... | inj₁ if-closed =
  cons (unrestricted t) (immune {t = s} if-closed) tt tt

correct1 : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  ⟦ derive t ⟧Δ ρ (unrestricted t) ≡ ⟦ derive1 t ⟧Δ ρ (valid1 t)

correct1 {t = nat n} = refl
correct1 {t = bag b} = refl
correct1 {t = var x} = refl
correct1 {t = abs t} = refl
correct1 {t = app s t} = refl
correct1 {t = add s t} = refl
correct1 {t = map s t} {ρ} with closed? s
... | inj₂ tt = refl
... | inj₁ if-closed = eq-map s t ρ (immune {t = s} if-closed)

