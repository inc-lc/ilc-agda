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

-- Equivalence proofs are unique
equivalence-unique : ∀ {A : Set} {a b : A} → ∀ {p q : a ≡ b} → p ≡ q
equivalence-unique {p = refl} {refl} = refl

-- Product of singletons are singletons (for example)
product-unique : ∀ {A : Set} {B : A → Set} →
  (∀ {a b : A} → a ≡ b) →
  (∀ {a : A} {c d : B a} → c ≡ d) →
  (∀ {p q : Σ A B} → p ≡ q)
product-unique {A} {B} lhs rhs {a , c} {b , d}
  rewrite lhs {a} {b} = cong (_,_ b) rhs

-- Validity proofs are (extensionally) unique (as functions)
validity-unique : ∀ {τ} {v : ⟦ τ ⟧} {dv : ΔVal τ} →
  ∀ {p q : valid v dv} → p ≡ q
validity-unique {nats} = equivalence-unique
validity-unique {bags} = refl
validity-unique {σ ⇒ τ} =  ext³ (λ v dv R[v,dv] →
  product-unique validity-unique equivalence-unique)

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
stability {t = union s t} {ρ} H =
  let
    a = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    da = ⟦ derive s ⟧Δ ρ (unrestricted s)
    db = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Hs , Ht = proj-H H
  in
    begin
      (a ++ b) ++ (da ++ db)
    ≡⟨ [a++b]++[c++d]=[a++c]++[b++d] ⟩
      (a ++ da) ++ (b ++ db)
    ≡⟨ cong₂ _++_ (stability {t = s} Hs) (stability {t = t} Ht) ⟩
      a ++ b
    ∎ where open ≡-Reasoning
stability {t = diff s t} {ρ} H =
  let
    a = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    da = ⟦ derive s ⟧Δ ρ (unrestricted s)
    db = ⟦ derive t ⟧Δ ρ (unrestricted t)
    Hs , Ht = proj-H H
  in
    begin
      (a \\ b) ++ (da \\ db)
    ≡⟨ [a\\b]++[c\\d]=[a++c]\\[b++d] ⟩
      (a ++ da) \\ (b ++ db)
    ≡⟨ cong₂ _\\_ (stability {t = s} Hs) (stability {t = t} Ht) ⟩
      a \\ b
    ∎ where open ≡-Reasoning
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
    ⟦ Δmap₁ s (derive t) ⟧Δ ρ (cons (unrestricted t) H tt tt)
  ≡ ⟦ Δmap₀ s (derive s) t (derive t) ⟧Δ ρ (unrestricted (map s t))

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

  in sym (trans eq1 (trans eq2 eq3))

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
valid1 (union s t) = cons (unrestricted s) (unrestricted t) tt tt
valid1 (diff s t) = cons (unrestricted s) (unrestricted t) tt tt
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
  ⟦ derive1 t ⟧Δ ρ (valid1 t) ≡ ⟦ derive t ⟧Δ ρ (unrestricted t)

correct1 {t = nat n} = refl
correct1 {t = bag b} = refl
correct1 {t = var x} = refl
correct1 {t = abs t} = refl
correct1 {t = app s t} = refl
correct1 {t = union s t} = refl
correct1 {t = diff s t} = refl
correct1 {t = add s t} = refl
correct1 {t = map s t} {ρ} with closed? s
... | inj₂ tt = refl
... | inj₁ if-closed = eq-map s t ρ (immune {t = s} if-closed)

-- derive2 = derive1 + congruence
derive2 : ∀ {τ Γ} → Term Γ τ → ΔTerm Γ τ
derive2 (abs t) = Δabs (derive2 t)
derive2 (app s t) = Δapp (derive2 s) t (derive2 t)
derive2 (add s t) = Δadd (derive2 s) (derive2 t)
derive2 (union s t) = Δunion (derive2 s) (derive2 t)
derive2 (diff s t) = Δdiff (derive2 s) (derive2 t)
derive2 (map s t) with closed? s
... | inj₁ is-closed = Δmap₁ s (derive2 t)
... | inj₂ tt = Δmap₀ s (derive2 s) t (derive2 t)
derive2 others = derive others

valid2 : ∀ {τ Γ} (t : Term Γ τ) {ρ : ΔEnv Γ} → derive2 t is-valid-for ρ
correct2 : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  ⟦ derive2 t ⟧Δ ρ (valid2 t) ≡ ⟦ derive t ⟧Δ ρ (unrestricted t)

valid2 (nat n) = tt
valid2 (bag b) = tt
valid2 (var x) = tt
valid2 (abs t) = λ _ _ _ → valid2 t
valid2 (app s t) {ρ} = cons (valid2 s) (valid2 t) V tt
  where
  V : valid (⟦ t ⟧ (ignore ρ)) (⟦ derive2 t ⟧Δ ρ (valid2 t))
  V rewrite correct2 {t = t} {ρ} = validity {t = t} {ρ}
valid2 (add s t) = cons (valid2 s) (valid2 t) tt tt
valid2 (union s t) = cons (valid2 s) (valid2 t) tt tt
valid2 (diff s t) = cons (valid2 s) (valid2 t) tt tt
valid2 (map s t) {ρ} with closed? s
... | inj₂ tt = cons (valid2 s) (valid2 t) tt tt
... | inj₁ if-closed =
  cons (valid2 t) (immune {t = s} if-closed) tt tt

correct2 {t = nat n} = refl
correct2 {t = bag b} = refl
correct2 {t = var x} = refl
correct2 {t = abs t} = ext³ (λ _ _ _ → correct2 {t = t})
correct2 {t = app {σ} {τ} s t} {ρ} = ≅-to-≡ eq-all where
  open import Relation.Binary.HeterogeneousEquality hiding (cong₂)
  import Relation.Binary.HeterogeneousEquality as HET
  df0 : ΔVal (σ ⇒ τ)
  df0 = ⟦ derive s ⟧Δ ρ (unrestricted s)
  df2 : ΔVal (σ ⇒ τ)
  df2 = ⟦ derive2 s ⟧Δ ρ (valid2 s)
  dv0 : ΔVal σ
  dv0 = ⟦ derive t ⟧Δ ρ (unrestricted t)
  dv2 : ΔVal σ
  dv2 = ⟦ derive2 t ⟧Δ ρ (valid2 t)
  v   : ⟦ σ ⟧
  v   = ⟦ t ⟧ (ignore ρ)
  eq-df : df2 ≡ df0
  eq-df = correct2 {t = s}
  eq-dv : dv2 ≡ dv0
  eq-dv = correct2 {t = t}
  eq-all : df2 v dv2 (caddr (valid2 (app s t) {ρ}))
         ≅ df0 v dv0 (validity {t = t} {ρ})
  eq-all rewrite eq-dv = HET.cong
    (λ hole → hole v dv0 (validity {t = t} {ρ})) (≡-to-≅ eq-df)
    -- found without intuition by trial-and-error
correct2 {t = add s t} {ρ} =
  let
    cs = correct2 {t = s} {ρ}
    ct = correct2 {t = t} {ρ}
  in cong₂ _,_ (cong₂ _+_ (cong proj₁ cs) (cong proj₁ ct))
               (cong₂ _+_ (cong proj₂ cs) (cong proj₂ ct))
correct2 {t = union s t} {ρ} =
  cong₂ _++_ (correct2 {t = s} {ρ}) (correct2 {t = t} {ρ})
correct2 {t = diff s t} {ρ} =
  cong₂ _\\_ (correct2 {t = s} {ρ}) (correct2 {t = t} {ρ})
correct2 {t = map s t} {ρ} with closed? s
... | inj₂ tt =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
  in
    cong₂ (λ h1 h2 → mapBag (f ⊕ h1) (b ⊕ h2) \\ mapBag f b)
    (correct2 {t = s}) (correct2 {t = t})
... | inj₁ if-closed = trans
  (cong (mapBag (⟦ s ⟧ (ignore ρ))) (correct2 {t = t}))
  (eq-map s t ρ (immune {t = s} if-closed))

---------------
-- Example 3 --
---------------

-- [+1] = λ x → x + 1
[+1] : ∀ {Γ} → Term Γ (nats ⇒ nats)
[+1] = (abs (add (var this) (nat 1)))

-- inc = λ bag → map [+1] bag
inc : Term ∅ (bags ⇒ bags)
inc = abs (map [+1] (var this))

-- Program transformation in example 3
-- Sadly, `inc` is not executable, for `Bag` is an abstract type
-- whose existence we postulated.
--
-- derive2 inc = λ bag dbag → map [+1] dbag
example-3 : derive2 inc ≡ Δabs (Δmap₁ [+1] (Δvar this))
example-3 = refl

-- Correctness of optimized derivation on `inc`
--
-- ⟦ derive2 inc ⟧ <embedded-proof> = ⟦ derive inc ⟧ <another-proof>
example-3-correct :
  ⟦ derive2 inc ⟧Δ ∅ (valid2 inc) ≡ ⟦ derive inc ⟧Δ ∅ (unrestricted inc)
example-3-correct = correct2 {t = inc} {∅}
