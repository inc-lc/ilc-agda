{-
The goal of this file is to make the domain of Δ types smaller
so as to be nearer to full abstraction and hopefully close
enough for the purpose of having explicit nil changes.
-}

module TaggedDeltaTypes where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Unit using (⊤ ; tt)
import Data.Integer as ℤ
import Data.Product as Product
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)
import Level

---------------------------------------------------------
-- Postulates: Extensionality and bag properties (#55) --
---------------------------------------------------------

postulate extensionality : Extensionality Level.zero Level.zero
-- Instead of:
-- open import Data.NatBag renaming
---  (map to mapBag ; empty to emptyBag ; update to updateBag)
-- open import Data.NatBag.Properties
postulate Bag : Set
postulate emptyBag : Bag
postulate mapBag : (ℕ → ℕ) → Bag → Bag
postulate _++_ : Bag → Bag → Bag
postulate _\\_ : Bag → Bag → Bag
infixr 5 _++_
infixl 9 _\\_
postulate b++∅=b : ∀ {b : Bag} → b ++ emptyBag ≡ b
postulate b++[d\\b]=d : ∀ {b d} → b ++ (d \\ b) ≡ d

----------------------------
-- Useful data structures --
----------------------------

record Quadruple
  (A : Set) (B : A → Set) (C : (a : A) → B a → Set)
  (D : (a : A) → (b : B a) → (c : C a b) → Set): Set where
  constructor cons
  field
    car   : A
    cadr  : B car
    caddr : C car cadr
    cdddr : D car cadr caddr

open Quadruple public

couple : Set → Set → Set
couple A B = Quadruple A (λ _ → B) (λ _ _ → ⊤) (λ _ _ _ → ⊤)

triple : Set → Set → Set → Set
triple A B C = Quadruple A (λ _ → B) (λ _ _ → C) (λ _ _ _ → ⊤)

------------------------
-- Syntax of programs --
------------------------

data Type : Set where
  nats : Type
  bags : Type
  _⇒_ : (σ τ : Type) → Type

infixr 5 _⇒_

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

data Var : Context → Type → Set where
  this : ∀ {τ Γ} → Var (τ • Γ) τ
  that : ∀ {σ τ Γ} → (x : Var Γ σ) → Var (τ • Γ) σ

data Term : Context -> Type -> Set where

  nat : ∀ {Γ} → (n : ℕ) → Term Γ nats
  bag : ∀ {Γ} → (b : Bag) → Term Γ bags

  var : ∀ {τ Γ} → (x : Var Γ τ) → Term Γ τ
  abs : ∀ {σ τ Γ} → (t : Term (σ • Γ) τ) → Term Γ (σ ⇒ τ)
  app : ∀ {σ τ Γ} → (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) → Term Γ τ

  add : ∀ {Γ} → (s : Term Γ nats) → (t : Term Γ nats) → Term Γ nats
  map : ∀ {Γ} → (f : Term Γ (nats ⇒ nats)) → (b : Term Γ bags) →
    Term Γ bags

infix 8 _≼_

data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅≼∅ : ∅ ≼ ∅
  keep_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → τ • Γ₁ ≼ τ • Γ₂
  drop_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → Γ₁ ≼ τ • Γ₂

Γ≼Γ : ∀ {Γ} → Γ ≼ Γ
Γ≼Γ {∅} = ∅≼∅
Γ≼Γ {τ • Γ} = keep τ • Γ≼Γ {Γ}

weakenVar : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weakenVar ∅≼∅ x = x
weakenVar (keep τ₁ • subctx) this = this
weakenVar (keep τ₁ • subctx) (that y) = that (weakenVar subctx y)
weakenVar (drop τ₁ • subctx) x = that (weakenVar subctx x)

weaken : ∀ {Γ₁ Γ₂ τ} → (subctx : Γ₁ ≼ Γ₂) → Term Γ₁ τ → Term Γ₂ τ
weaken subctx (abs {τ} t) = abs (weaken (keep τ • subctx) t)
weaken subctx (app t₁ t₂) = app (weaken subctx t₁) (weaken subctx t₂)
weaken subctx (var x) = var (weakenVar subctx x)
weaken subctx (nat x) = nat x
weaken subctx (bag b) = bag b
weaken subctx (add t₁ t₂) = add (weaken subctx t₁) (weaken subctx t₂)
weaken subctx (map f b) = map (weaken subctx f) (weaken subctx b)

---------------------------
-- Semantics of programs --
---------------------------

record Meaning (Syntax : Set) {ℓ : Level.Level} : Set (Level.suc ℓ) where
  constructor
    meaning
  field
    {Semantics} : Set ℓ
    ⟨_⟩⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public
  renaming (⟨_⟩⟦_⟧ to ⟦_⟧)

⟦_⟧Type : Type -> Set
⟦ nats ⟧Type = ℕ
⟦ bags ⟧Type = Bag
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

data EmptySet : Set where
  ∅ : EmptySet

data Bind A B : Set where
  _•_ : (v : A) (ρ : B) → Bind A B

⟦_⟧Context : Context → Set
⟦ ∅ ⟧Context = EmptySet
⟦ τ • Γ ⟧Context = Bind ⟦ τ ⟧ ⟦ Γ ⟧Context

meaningOfContext : Meaning Context
meaningOfContext = meaning ⟦_⟧Context

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ this ⟧Var (v • ρ) = v
⟦ that x ⟧Var (v • ρ) = ⟦ x ⟧Var ρ

meaningOfVar : ∀ {Γ τ} → Meaning (Var Γ τ)
meaningOfVar = meaning ⟦_⟧Var

⟦_⟧≼ : ∀ {Γ₁ Γ₂} → Γ₁ ≼ Γ₂ → ⟦ Γ₂ ⟧ → ⟦ Γ₁ ⟧
⟦ ∅≼∅ ⟧≼ ∅ = ∅
⟦ keep τ • subctx ⟧≼ (v • ρ) = v • ⟦ subctx ⟧≼ ρ
⟦ drop τ • subctx ⟧≼ (v • ρ) = ⟦ subctx ⟧≼ ρ

meaningOf≼ : ∀ {Γ₁ Γ₂} → Meaning (Γ₁ ≼ Γ₂)
meaningOf≼ = meaning ⟦_⟧≼

identity-weakening : ∀ {Γ} {ρ : ⟦ Γ ⟧} → ⟦ Γ≼Γ {Γ} ⟧ ρ ≡ ρ
identity-weakening {∅} {∅} = refl
identity-weakening {τ • Γ} {v • ρ} =
  cong₂ _•_ {x = v} refl (identity-weakening {Γ} {ρ})

weakenVar-sound : ∀ {Γ₁ Γ₂ τ} (subctx : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weakenVar subctx x ⟧ ρ ≡ ⟦ x ⟧ (⟦ subctx ⟧ ρ)
weakenVar-sound ∅≼∅ () ρ
weakenVar-sound (keep τ • subctx) this (v • ρ) = refl
weakenVar-sound (keep τ • subctx) (that x) (v • ρ) =
  weakenVar-sound subctx x ρ
weakenVar-sound (drop τ • subctx) this (v • ρ) =
  weakenVar-sound subctx this ρ
weakenVar-sound (drop τ • subctx) (that x) (v • ρ) =
  weakenVar-sound subctx (that x) ρ

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ nat n ⟧Term ρ = n
⟦ bag b ⟧Term ρ = b
⟦ add m n ⟧Term ρ = ⟦ m ⟧Term ρ + ⟦ n ⟧Term ρ
⟦ map f b ⟧Term ρ = mapBag (⟦ f ⟧Term ρ) (⟦ b ⟧Term ρ)

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

_⟨$⟩_ : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
_⟨$⟩_ = cong₂ (λ x y → x y)

-- infix 0 $ in Haskell
infixl 0 _⟨$⟩_

weaken-sound : ∀ {Γ₁ Γ₂ τ} {subctx : Γ₁ ≼ Γ₂} (t : Term Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken subctx t ⟧ ρ ≡ ⟦ t ⟧ (⟦ subctx ⟧ ρ)
weaken-sound (abs t) ρ = extensionality (λ v → weaken-sound t (v • ρ))
weaken-sound (app t₁ t₂) ρ = weaken-sound t₁ ρ ⟨$⟩ weaken-sound t₂ ρ
weaken-sound {subctx = subctx} (var x) ρ = weakenVar-sound subctx x ρ
weaken-sound (nat n) ρ = refl

weaken-sound (bag b) ρ = refl
weaken-sound (add m n) ρ = cong₂ _+_ (weaken-sound m ρ) (weaken-sound n ρ)
weaken-sound (map f b) ρ =
  cong₂ mapBag (weaken-sound f ρ) (weaken-sound b ρ)

-----------------------
-- Syntax of changes --
-----------------------

-- Validity proofs are not literally embedded in terms.
-- They are introduced and checked at interpretation time.
-- Invalid programs are well-formed terms,
-- they just denote the empty function.
--
-- Thus do we avoid the horrible mutual recursions between
-- the syntax and semantics of changes and between the
-- program transformation and its correctness, which drives
-- the type checker to thrashing.

data ΔTerm : Context → Type → Set where
  -- changes to numbers are replacement pairs
  Δnat : ∀ {Γ} → (old : ℕ) → (new : ℕ) → ΔTerm Γ nats
  -- changes to bags are bags
  Δbag : ∀ {Γ} → (db : Bag) → ΔTerm Γ bags
  -- changes to variables are variables
  Δvar : ∀ {τ Γ} → (x : Var Γ τ) → ΔTerm Γ τ
  -- changes to abstractions are binders of x and dx
  Δabs : ∀ {τ₁ τ₂ Γ} → (dt : ΔTerm (τ₁ • Γ) τ₂) →
         ΔTerm Γ (τ₁ ⇒ τ₂)
  -- changes to applications are applications of a value and a change
  Δapp : ∀ {σ τ Γ}
    (ds : ΔTerm Γ (σ ⇒ τ))
    ( t :  Term Γ σ)
    (dt : ΔTerm Γ σ) →
    ΔTerm Γ τ
  -- changes to addition are changes to their components
  Δadd : ∀ {Γ}
    (ds : ΔTerm Γ nats)
    (dt : ΔTerm Γ nats) →
    ΔTerm Γ nats
  -- There are two kinds of changes to maps:
  -- 0. recomputation,
  -- 1. mapping over changes,
  -- the latter used only with some form of isNil available.
  Δmap₀ : ∀ {Γ}
    ( s :   Term Γ (nats ⇒ nats))
    (ds : ΔTerm Γ (nats ⇒ nats))
    ( t :   Term Γ bags)
    (dt : ΔTerm Γ bags) →
    ΔTerm Γ bags
  Δmap₁ : ∀ {Γ}
    ( s :   Term Γ (nats ⇒ nats))
    (dt : ΔTerm Γ bags) →
    ΔTerm Γ bags

---------------------------------
-- Semantic domains of changes --
---------------------------------

ΔVal : Type → Set
ΔEnv : Context → Set
valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set

-- ΔVal : Type → Set
ΔVal nats = ℕ × ℕ
ΔVal bags = Bag
ΔVal (σ ⇒ τ) = (v : ⟦ σ ⟧) → (dv : ΔVal σ) → valid v dv → ΔVal τ

-- ΔEnv : Context → Set
ΔEnv ∅ = EmptySet
ΔEnv (τ • Γ) = Quadruple
  ⟦ τ ⟧
  (λ _ → ΔVal τ)
  (λ v dv → valid v dv)
  (λ _ _ _ → ΔEnv Γ)

_⊕_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
_⊝_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
infixl 6 _⊕_ _⊝_ -- as with + - in GHC.Num

-- valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set
valid {nats} n dn = n ≡ proj₁ dn
valid {bags} b db = ⊤
valid {σ ⇒ τ} f df =
  ∀ (v : ⟦ σ ⟧) (dv : ΔVal σ) (R[v,dv] : valid v dv)
  → valid (f v) (df v dv R[v,dv])
  × (f ⊕ df) (v ⊕ dv) ≡ f v ⊕ df v dv R[v,dv]

R[v,u⊝v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊝ v)

-- _⊕_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
_⊕_ {nats}   n dn = proj₂ dn
_⊕_ {bags}   b db = b ++ db
_⊕_ {τ₁ ⇒ τ₂} f df = λ v → f v ⊕ df v (v ⊝ v) R[v,u⊝v]

-- _⊝_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
_⊝_ {nats}   m n = (n , m)
_⊝_ {bags}   b d = b \\ d
_⊝_ {τ₁ ⇒ τ₂} f g = λ v dv R[v,dv] → f (v ⊕ dv) ⊝ g v

v⊕[u⊝v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊕ (u ⊝ v) ≡ u
v⊕[u⊝v]=u {nats} {u} {v} = refl
v⊕[u⊝v]=u {bags} {u} {v} = b++[d\\b]=d {v} {u}
v⊕[u⊝v]=u {σ ⇒ τ} {u} {v} = extensionality (λ w →
  begin
    (v ⊕ (u ⊝ v)) w
  ≡⟨ refl ⟩ -- for clarity
    v w ⊕ (u (w ⊕ (w ⊝ w)) ⊝ v w)
  ≡⟨ cong (λ hole → v w ⊕ (u hole ⊝ v w)) v⊕[u⊝v]=u ⟩
    v w ⊕ (u w ⊝ v w)
  ≡⟨ v⊕[u⊝v]=u ⟩
    u w
  ∎) where open ≡-Reasoning

-- R[v,u⊝v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊝ v)
R[v,u⊝v] {nats} {u} {v} = refl
R[v,u⊝v] {bags} {u} {v} = tt
R[v,u⊝v] {σ ⇒ τ} {u} {v} = λ w dw R[w,dw] →
  let
    w′ = w ⊕ dw
  in
    R[v,u⊝v]
    ,
    (begin
      (v ⊕ (u ⊝ v)) w′
    ≡⟨ cong (λ hole → hole w′) (v⊕[u⊝v]=u {u = u} {v}) ⟩
      u w′
    ≡⟨ sym (v⊕[u⊝v]=u {u = u w′} {v w}) ⟩
      v w ⊕ (u ⊝ v) w dw R[w,dw]
    ∎) where open ≡-Reasoning

ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
ignore {∅} ρ = ∅
ignore {τ • Γ} (cons v dv R[v,dv] ρ) = v • ignore ρ

update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
update {∅} ρ = ∅
update {τ • Γ} (cons v dv R[v,dv] ρ) = (v ⊕ dv) • update ρ

--------------------------
-- Semantics of changes --
--------------------------

⟦_⟧ΔVar : ∀ {τ Γ} → Var Γ τ → ΔEnv Γ → ΔVal τ
⟦ this   ⟧ΔVar (cons v dv R[v,dv] ρ) = dv
⟦ that x ⟧ΔVar (cons v dv R[v,dv] ρ) = ⟦ x ⟧ΔVar ρ

-- Used to signal free variables of a term.
-- Totally like subcontext relation _≼_ : (Γ₁ Γ₂ : Context) → Set
data Vars : Context → Set where
  ∅ : Vars ∅
  alter : ∀ {τ Γ} → Vars Γ → Vars (τ • Γ)
  abide : ∀ {τ Γ} → Vars Γ → Vars (τ • Γ)

-- Declare everything in Γ to be volatile.
select-none-in : (Γ : Context) → Vars Γ
select-none-in ∅ = ∅
select-none-in (τ • Γ) = alter (select-none-in Γ)

select-just : ∀ {τ Γ} → Var Γ τ → Vars Γ
select-just {Γ = τ • Γ₀} this = abide (select-none-in Γ₀)
select-just (that x) = alter (select-just x)

-- De-facto union of free variables
FV-union : ∀ {Γ} → Vars Γ → Vars Γ → Vars Γ
FV-union ∅ ∅ = ∅
FV-union (alter us) (alter vs) = alter (FV-union us vs)
FV-union (alter us) (abide vs) = abide (FV-union us vs)
FV-union (abide us) (alter vs) = abide (FV-union us vs)
FV-union (abide us) (abide vs) = abide (FV-union us vs)

tail : ∀ {τ Γ} → Vars (τ • Γ) → Vars Γ
tail (abide vars) = vars
tail (alter vars) = vars

-- Free variables of a term.
-- Free variables are marked as abiding, bound variables altering.
FV : ∀ {τ Γ} → Term Γ τ → Vars Γ
FV {Γ = Γ} (nat n) = select-none-in Γ
FV {Γ = Γ} (bag b) = select-none-in Γ
FV (var x) = select-just x
FV (abs t) = tail (FV t)
FV (app s t) = FV-union (FV s) (FV t)
FV (add s t) = FV-union (FV s) (FV t)
FV (map s t) = FV-union (FV s) (FV t)

-- A description of variables is honest w.r.t. a Δ-environment
-- if every variable described as stable receives the nil change.
data Honest : ∀ {Γ} → ΔEnv Γ → Vars Γ → Set where
  clearly : Honest ∅ ∅
  alter : ∀ {Γ τ} {v : ⟦ τ ⟧} {dv R[v,dv] vars ρ} →
          Honest {Γ} ρ vars →
          Honest {τ • Γ} (cons v dv R[v,dv] ρ) (alter vars)
  abide : ∀ {Γ τ} {v : ⟦ τ ⟧} {dv R[v,dv] vars ρ} →
          v ⊕ dv ≡ v →
          Honest {Γ} ρ vars →
          Honest {τ • Γ} (cons v dv R[v,dv] ρ) (abide vars)

_is-valid-for_ : ∀ {τ Γ} → ΔTerm Γ τ → ΔEnv Γ → Set

⟦_⟧Δ : ∀ {τ Γ} →
  (t : ΔTerm Γ τ) → (ρ : ΔEnv Γ) → t is-valid-for ρ →
  ΔVal τ

-- _is-valid-for_ : ∀ {τ Γ} → ΔTerm Γ τ → ΔEnv Γ → Set
Δnat old new is-valid-for ρ = ⊤
Δbag db is-valid-for ρ = ⊤
Δvar x is-valid-for ρ = ⊤

_is-valid-for_ {σ ⇒ τ} (Δabs dt) ρ =
  (v : ⟦ σ ⟧) (dv : ΔVal σ) (R[v,dv] : valid v dv) →
  _is-valid-for_ dt (cons v dv R[v,dv] ρ)

Δapp ds t dt is-valid-for ρ = Quadruple
  (ds is-valid-for ρ)
  (λ _ → dt is-valid-for ρ)
  (λ _ v-dt → valid (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧Δ ρ v-dt))
  (λ _ _ _ → ⊤)

Δadd ds dt is-valid-for ρ = couple
  (ds is-valid-for ρ)
  (dt is-valid-for ρ)

Δmap₀ s ds t dt is-valid-for ρ = couple
  (ds is-valid-for ρ)
  (dt is-valid-for ρ)

Δmap₁ s db is-valid-for ρ = couple
  (db is-valid-for ρ)
  (Honest ρ (FV s))

⟦ Δnat old new ⟧Δ ρ tt = old , new
⟦ Δbag db ⟧Δ ρ tt = db
⟦ Δvar x ⟧Δ ρ tt = ⟦ x ⟧ΔVar ρ

⟦ Δabs dt ⟧Δ ρ make-valid = λ v dv R[v,dv] →
  ⟦ dt ⟧Δ (cons v dv R[v,dv] ρ) (make-valid v dv R[v,dv])

⟦ Δapp ds t dt ⟧Δ ρ (cons v-ds v-dt R[ds,dt] _) =
  ⟦ ds ⟧Δ ρ v-ds (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧Δ ρ v-dt) R[ds,dt]

⟦ Δadd ds dt ⟧Δ ρ (cons v-ds v-dt _ _) =
  let
    (old-s , new-s) = ⟦ ds ⟧Δ ρ v-ds
    (old-t , new-t) = ⟦ dt ⟧Δ ρ v-dt
  in
    (old-s + old-t , new-s + new-t)

⟦ Δmap₀ s ds t dt ⟧Δ ρ (cons v-ds v-dt _ _) =
  let
    f  = ⟦ s ⟧ (ignore ρ)
    v  = ⟦ t ⟧ (ignore ρ)
    df = ⟦ ds ⟧Δ ρ v-ds
    dv = ⟦ dt ⟧Δ ρ v-dt
  in
    mapBag (f ⊕ df) (v ⊕ dv) ⊝ mapBag f v

⟦ Δmap₁ s dt ⟧Δ ρ (cons v-dt honesty _ _) =
  mapBag (⟦ s ⟧ (ignore ρ)) (⟦ dt ⟧Δ ρ v-dt)

-- Minor issue about concrete syntax
--
-- Because ⟦_⟧Δ have dependently typed arguments,
-- we can't make it an instance of the Meaning
-- type class and can't use ⟦_⟧ on ΔTerms.
--
-- Error message:
-- Cannot instantiate the metavariable _872 to solution ((ρ : ΔEnv .Γ)
-- → t is-valid-for ρ → ΔVal .τ) since it contains the variable t
-- which is not in scope of the metavariable or irrelevant in the
-- metavariable but relevant in the solution
-- when checking that the expression ⟦_⟧Δ has type
-- ΔTerm .Γ .τ → _Semantics_872
--
--     meaning-ΔTerm : ∀ {τ Γ} → Meaning (ΔTerm Γ τ)
--     meaning-ΔTerm = meaning ⟦_⟧Δ

----------------------------
-- Program transformation --
----------------------------

derive : ∀ {τ Γ} → Term Γ τ → ΔTerm Γ τ

derive (nat n) = Δnat n n
derive (bag b) = Δbag emptyBag
derive (var x) = Δvar x
derive (abs t) = Δabs (derive t)
derive (app s t) = Δapp (derive s) t (derive t)
derive (add s t) = Δadd (derive s) (derive t)
derive (map f b) = Δmap₀ f (derive f) b (derive b)

-----------------
-- Correctness --
-----------------

unrestricted : ∀ {τ Γ} (t : Term Γ τ) {ρ : ΔEnv Γ} →
  derive t is-valid-for ρ

validity : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  valid (⟦ t ⟧ (ignore ρ)) (⟦ derive t ⟧Δ ρ (unrestricted t))

correctness : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ}
  → ⟦ t ⟧ (ignore ρ) ⊕ ⟦ derive t ⟧Δ ρ (unrestricted t)
  ≡ ⟦ t ⟧ (update ρ)

-- Corollary: (f ⊕ df) (v ⊕ dv) = f v ⊕ df v dv

corollary : ∀ {σ τ Γ}
  (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) {ρ : ΔEnv Γ} →
    (⟦ s ⟧ (ignore ρ) ⊕ ⟦ derive s ⟧Δ ρ (unrestricted s))
    (⟦ t ⟧ (ignore ρ) ⊕ ⟦ derive t ⟧Δ ρ (unrestricted t))
  ≡  ⟦ s ⟧ (ignore ρ) (⟦ t ⟧ (ignore ρ)) ⊕
     ⟦ derive s ⟧Δ ρ (unrestricted s) (⟦ t ⟧ (ignore ρ))
    (⟦ derive t ⟧Δ ρ (unrestricted t)) (validity {t = t})

corollary s t {ρ} = proj₂
  (validity {t = s} (⟦ t ⟧ (ignore ρ))
    (⟦ derive t ⟧Δ ρ (unrestricted t)) (validity {t = t}))

unrestricted (nat n) = tt
unrestricted (bag b) = tt
unrestricted (var x) {ρ} = tt
unrestricted (abs t) {ρ} = (λ _ _ _ → unrestricted t)
unrestricted (app s t) {ρ} = cons
  (unrestricted (s))
  (unrestricted (t))
  (validity {t = t}) tt
unrestricted (add s t) {ρ} = cons
  (unrestricted (s))
  (unrestricted (t)) tt tt
unrestricted (map s t) {ρ} = cons
  (unrestricted (s))
  (unrestricted (t)) tt tt

validity-var : ∀ {τ Γ} → (x : Var Γ τ) →
  ∀ {ρ : ΔEnv Γ} → valid (⟦ x ⟧ (ignore ρ)) (⟦ x ⟧ΔVar ρ)

validity-var this {cons v dv R[v,dv] ρ} = R[v,dv]
validity-var (that x) {cons v dv R[v,dv] ρ} = validity-var x

validity {t = nat n} = refl
validity {t = bag b} = tt
validity {t = var x} = validity-var x
validity {t = map f b} = tt
validity {t = add s t} = cong₂ _+_ (validity {t = s}) (validity {t = t})

validity {t = app s t} {ρ} =
  let
    v = ⟦ t ⟧ (ignore ρ)
    dv = ⟦ derive t ⟧Δ ρ (unrestricted t)
  in
    proj₁ (validity {t = s} {ρ} v dv (validity {t = t} {ρ}))

validity {t = abs t} {ρ} = λ v dv R[v,dv] →
  let
    v′ = v ⊕ dv
    dv′ = v′ ⊝ v′
    ρ₁ = cons v dv R[v,dv] ρ
    ρ₂ = cons v′ dv′ R[v,u⊝v] ρ
  in
    validity {t = t} {ρ₁}
    ,
    (begin
      ⟦ t ⟧ (ignore ρ₂) ⊕ ⟦ derive t ⟧Δ ρ₂ (unrestricted t)
    ≡⟨ correctness {t = t} {ρ₂} ⟩
      ⟦ t ⟧ (update ρ₂)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) v⊕[u⊝v]=u ⟩
      ⟦ t ⟧ (update ρ₁)
    ≡⟨ sym (correctness {t = t} {ρ₁}) ⟩
      ⟦ t ⟧ (ignore ρ₁) ⊕ ⟦ derive t ⟧Δ ρ₁ (unrestricted t)
    ∎) where open ≡-Reasoning

correctVar : ∀ {τ Γ} {x : Var Γ τ} {ρ : ΔEnv Γ} →
  ⟦ x ⟧ (ignore ρ) ⊕ ⟦ x ⟧ΔVar ρ ≡ ⟦ x ⟧ (update ρ)

correctVar {x = this  } {cons v dv R[v,dv] ρ} = refl
correctVar {x = that y} {cons v dv R[v,dv] ρ} = correctVar {x = y} {ρ}

correctness {t = nat n} = refl
correctness {t = bag b} = b++∅=b
correctness {t = var x} = correctVar {x = x}

correctness {t = add s t} =
  cong₂ _+_ (correctness {t = s}) (correctness {t = t})

correctness {t = map s t} {ρ} =
  trans (b++[d\\b]=d {mapBag f b} {mapBag (f ⊕ df) (b ⊕ db)})
        (cong₂ mapBag (correctness {t = s}) (correctness {t = t}))
  where
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    df = ⟦ derive s ⟧Δ ρ (unrestricted s)
    db = ⟦ derive t ⟧Δ ρ (unrestricted t)

correctness {t = app s t} {ρ} =
  let
    v = ⟦ t ⟧ (ignore ρ)
    dv = ⟦ derive t ⟧Δ ρ (unrestricted t)
  in trans
     (sym (proj₂ (validity {t = s} {ρ} v dv (validity {t = t} {ρ}))))
     (correctness {t = s} ⟨$⟩ correctness {t = t})

correctness {τ₁ ⇒ τ₂} {Γ} {abs t} {ρ} = extensionality (λ v →
  let
    ρ′ : ΔEnv (τ₁ • Γ)
    ρ′ = cons v (v ⊝ v) R[v,u⊝v] ρ
  in
    begin
      ⟦ t ⟧ (ignore ρ′) ⊕ ⟦ derive t ⟧Δ ρ′ (unrestricted t)
    ≡⟨ correctness {t = t} {ρ′} ⟩
      ⟦ t ⟧ (update ρ′)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) v⊕[u⊝v]=u ⟩
      ⟦ t ⟧ (v • update ρ)
    ∎
  ) where open ≡-Reasoning
