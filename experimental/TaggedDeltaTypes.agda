{-
The goal of this file is to make the domain of Δ types smaller
so as to be nearer to full abstraction and hopefully close
enough for the purpose of having explicit nil changes.
-}

module TaggedDeltaTypes where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.Unit using (⊤ ; tt)
import Data.Integer as ℤ
import Data.Product as Product
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)
import Level

-- Postulates: Extensionality and bag properties (#55)
postulate extensionality : Extensionality Level.zero Level.zero
--
-- open import Data.NatBag renaming
--   (map to mapBag ; empty to emptyBag ; update to updateBag)
-- open import Data.NatBag.Properties
postulate Bag : Set
postulate emptyBag : Bag
postulate mapBag : (ℕ → ℕ) → Bag → Bag
postulate _++_ : Bag → Bag → Bag
postulate _\\_ : Bag → Bag → Bag
infixr 5 _++_
infixl 9 _\\_
postulate b\\b=∅ : ∀ {b : Bag} → b \\ b ≡ emptyBag
postulate b++∅=b : ∀ {b : Bag} → b ++ emptyBag ≡ b
postulate ∅++b=b : ∀ {b : Bag} → emptyBag ++ b ≡ b
postulate b++[d\\b]=d : ∀ {b d} → b ++ (d \\ b) ≡ d
postulate [b++d]\\b=d : ∀ {b d} → (b ++ d) \\ b ≡ d
postulate
  [a++b]\\[c++d]=[a\\c]++[b\\d] : ∀ {a b c d} →
    (a ++ b) \\ (c ++ d) ≡ (a \\ c) ++ (b \\ d)
postulate
  [a\\b]\\[c\\d]=[a\\c]\\[b\\d] : ∀ {a b c d} →
    (a \\ b) \\ (c \\ d) ≡ (a \\ c) \\ (b \\ d)

------------------------
-- Syntax of programs --
------------------------

data Type : Set where
  nats : Type
  bags : Type
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

data Var : Context → Type → Set where
  this : ∀ {τ Γ} → Var (τ • Γ) τ
  that : ∀ {τ τ′ Γ} → (x : Var Γ τ) → Var (τ′ • Γ) τ

data Term : Context -> Type -> Set where

  nat : ∀ {Γ} → (n : ℕ) → Term Γ nats
  bag : ∀ {Γ} → (b : Bag) → Term Γ bags

  var : ∀ {τ Γ} → (x : Var Γ τ) → Term Γ τ
  abs : ∀ {τ₁ τ₂ Γ} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂ Γ} → (s : Term Γ (τ₁ ⇒ τ₂)) (t : Term Γ τ₁)
                   → Term Γ τ₂

  add : ∀ {Γ} → (s : Term Γ nats) → (t : Term Γ nats) → Term Γ nats
  map : ∀ {Γ} → (f : Term Γ (nats ⇒ nats)) → (b : Term Γ bags) → Term Γ bags

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

----------------------------------------------------------
-- Syntax and semantics of changes (they are entangled) --
----------------------------------------------------------

data Δ-Type : Set where
  nats : Δ-Type
  bags : Δ-Type
  alter_⇒_ : Δ-Type → Δ-Type → Δ-Type
  abide_⇒_ : Δ-Type → Δ-Type → Δ-Type

data Δ-Context : Set where
  ∅ : Δ-Context
  alter_•_ : Δ-Type → Δ-Context → Δ-Context
  abide_•_ : Δ-Type → Δ-Context → Δ-Context

erase : Δ-Type → Type
erase nats = nats
erase bags = bags
erase (alter τ₁ ⇒ τ₂) = erase τ₁ ⇒ erase τ₂
erase (abide τ₁ ⇒ τ₂) = erase τ₁ ⇒ erase τ₂

forget : Δ-Context → Context
forget ∅ = ∅
forget (alter τ • ρ) = erase τ • forget ρ
forget (abide τ • ρ) = erase τ • forget ρ

-- Convert a type/context to a Δ-type/Δ-context without any
-- assumption about arguments

Δ-type : Type → Δ-Type
Δ-type nats = nats
Δ-type bags = bags
Δ-type (τ₁ ⇒ τ₂) = alter Δ-type τ₁ ⇒ Δ-type τ₂

Δ-context : Context → Δ-Context
Δ-context ∅ = ∅
Δ-context (τ • Γ) = alter Δ-type τ • Δ-context Γ

data Δ-Term : Δ-Context → Δ-Type → Set
data ⟦_⟧ΔContext : Δ-Context → Set

⟦_⟧ΔType : Δ-Type → Set
⟦_⟧ΔTerm : ∀ {τ Γ} → Δ-Term Γ τ → ⟦ Γ ⟧ΔContext → ⟦ τ ⟧ΔType
_⊕_ : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType → ⟦ erase τ ⟧
_⊝_ : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType
valid : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType → Set
R[v,u⊝v] : ∀ {τ} {u v : ⟦ erase τ ⟧} → valid {τ} v (u ⊝ v)
v⊕[u⊝v]=u : ∀ {τ} {u v : ⟦ erase τ ⟧} → v ⊕ (_⊝_ {τ} u v) ≡ u
ignore : ∀ {Γ} → ⟦ Γ ⟧ΔContext → ⟦ forget Γ ⟧
update : ∀ {Γ} → ⟦ Γ ⟧ΔContext → ⟦ forget Γ ⟧
infixl 6 _⊕_ _⊝_ -- as with + - in GHC.Num

data Δ-Term where
  -- changes to numbers are replacement pairs
  Δnat : ∀ {Γ} → (old : ℕ) → (new : ℕ) → Δ-Term Γ nats
  -- changes to bags are bags
  Δbag : ∀ {Γ} → (db : Bag) → Δ-Term Γ bags
  -- changes to variables are variables
  Δvar : ∀ {τ Γ} → (x : Var (forget Γ) (erase τ)) → Δ-Term Γ τ
  -- changes to abstractions are binders of x and dx
  -- There are two kinds of those: One who expects the argument
  -- to change, and one who does not.
  Δabs₀ : ∀ {τ₁ τ₂ Γ}
    (t : Δ-Term (abide τ₁ • Γ) τ₂) →
    Δ-Term Γ (abide τ₁ ⇒ τ₂)
  Δabs₁ : ∀ {τ₁ τ₂ Γ}
    (t : Δ-Term (alter τ₁ • Γ) τ₂) →
    Δ-Term Γ (alter τ₁ ⇒ τ₂)
{-
  Δapp₀ : ∀ {τ₁ τ₂ Γ}
    (ds : Δ-Term Γ (abide τ₁ ⇒ τ₂))
    (t : Term (forget Γ) (erase τ₁))
    (dt : Δ-Term Γ τ₁)
    {R[t,dt] : ∀ {ρ : ⟦
-}
    
{-
  -- changes to applications are applications of a value and a change
  Δapp : ∀ {τ₁ τ₂ Γ vars}
    (ds : Δ-Term Γ (τ₁ ⇒ τ₂) {vars})
    ( t :   Term Γ τ₁)
    (dt : Δ-Term Γ τ₁ {vars})
    (R[t,dt] : {ρ : Δ-Env Γ {-vars-}} →
      valid (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧ΔTerm ρ)) →
    Δ-Term Γ τ₂ {vars}
  -- changes to addition are changes to their components
  Δadd : ∀ {Γ vars}
    (ds : Δ-Term Γ nats {vars})
    (dt : Δ-Term Γ nats {vars}) →
    Δ-Term Γ nats {vars}
  -- There are two kinds of changes to maps:
  -- 0. recomputation,
  -- 1. mapping over changes,
  -- the latter used only with some form of isNil available.
  Δmap₀ : ∀ {Γ vars} →
    ( f :   Term Γ (nats ⇒ nats))
    (df : Δ-Term Γ (nats ⇒ nats) {vars})
    ( b :   Term Γ bags)
    (db : Δ-Term Γ bags {vars}) →
    Δ-Term Γ bags {vars}
  Δmap₁ : ∀ {Γ vars} →
    ( f :   Term Γ (nats ⇒ nats)) (db : Δ-Term Γ bags {vars}) →
    Δ-Term Γ bags {vars}
-}

-- ⟦_⟧ΔType : Δ-Type → Set
⟦ nats ⟧ΔType = ℕ × ℕ
⟦ bags ⟧ΔType = Bag
⟦ alter τ₁ ⇒ τ₂ ⟧ΔType =
  (v : ⟦ erase τ₁ ⟧) → (dv : ⟦ τ₁ ⟧ΔType) →
  valid {τ₁} v dv →
  ⟦ τ₂ ⟧ΔType
⟦ abide τ₁ ⇒ τ₂ ⟧ΔType =
  (v : ⟦ erase τ₁ ⟧) → (dv : ⟦ τ₁ ⟧ΔType) →
  valid {τ₁} v dv → _⊕_ {τ₁} v dv ≡ v →
  ⟦ τ₂ ⟧ΔType

meaning-ΔType : Meaning Δ-Type
meaning-ΔType = meaning ⟦_⟧ΔType


-- _⊕_ : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType → ⟦ erase τ ⟧
_⊕_ = {!!}
{-
_⊕_ {nats}   n dn = proj₂ dn
_⊕_ {bags}   b db = b ++ db
_⊕_ {τ₁ ⇒ τ₂} f df = λ v → f v ⊕ df v (v ⊝ v) R[v,u⊝v]
-}

-- _⊝_ : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType
_⊝_ = {!!}
{-
_⊝_ {nats}   m n = (n , m)
_⊝_ {bags}   b d = b \\ d
_⊝_ {τ₁ ⇒ τ₂} f g = λ v dv R[v,dv] → f (v ⊕ dv) ⊝ g v
-}

-- valid : ∀ {τ} → ⟦ erase τ ⟧ → ⟦ τ ⟧ΔType → Set
valid _ _ = ⊤
{-
valid {nats} n dn = n ≡ proj₁ dn
valid {bags} b db = ⊤
valid {τ₁ ⇒ τ₂} f df =
  ∀ (v : ⟦ τ₁ ⟧) (dv : ⟦ τ₁ ⟧ΔType) (R[v,dv] : valid v dv)
  → valid (f v) (df v dv R[v,dv])
  × (f ⊕ df) (v ⊕ dv) ≡ f v ⊕ df v dv R[v,dv]
-}

-- v⊕[u⊝v]=u : ∀ {τ} {u v : ⟦ erase τ ⟧} → v ⊕ (_⊝_ {τ} u v) ≡ u
v⊕[u⊝v]=u = {!!}
{-
v⊕[u⊝v]=u {nats}   {u} {v} = refl
v⊕[u⊝v]=u {bags}   {u} {v} = b++[d\\b]=d {v} {u}
v⊕[u⊝v]=u {τ₁ ⇒ τ₂} {u} {v} = extensionality (λ w →
  begin
    (v ⊕ (u ⊝ v)) w
  ≡⟨ refl ⟩ -- for clarity
    v w ⊕ (u (w ⊕ (w ⊝ w)) ⊝ v w)
  ≡⟨ cong (λ hole → v w ⊕ (u hole ⊝ v w)) v⊕[u⊝v]=u ⟩
    v w ⊕ (u w ⊝ v w)
  ≡⟨ v⊕[u⊝v]=u ⟩
    u w
  ∎) where open ≡-Reasoning
-}

-- R[v,u⊝v] : ∀ {τ} {u v : ⟦ erase τ ⟧} → valid {τ} v (u ⊝ v)
R[v,u⊝v] = tt
{-
R[v,u⊝v] {nats} {u} {v} = refl
R[v,u⊝v] {bags} {u} {v} = tt
R[v,u⊝v] {τ₁ ⇒ τ₂} {u} {v} = λ w dw R[w,dw] →
  let
    w′ = w ⊕ dw
  in
    R[v,u⊝v] -- NOT a self recursion: implicit arguments are different.
    ,
    (begin
      (v ⊕ (u ⊝ v)) w′
    ≡⟨ cong (λ hole → hole w′) (v⊕[u⊝v]=u {u = u} {v}) ⟩
      u w′
    ≡⟨ sym (v⊕[u⊝v]=u {u = u w′} {v w}) ⟩
      v w ⊕ (u ⊝ v) w dw R[w,dw]
    ∎) where open ≡-Reasoning
-}


-- The type of environments ensures their consistency and honesty.
-- data ⟦_⟧ΔContext : Δ-Context → Set
data ⟦_⟧ΔContext where
  ∅ : ⟦ ∅ ⟧ΔContext
  quad : ∀ {τ Γ}
    (v : ⟦ erase τ ⟧)
    (dv : ⟦ τ ⟧ΔType)
    (R[v,dv] : valid {τ} v dv)
    (ρ : ⟦ Γ ⟧ΔContext) →
    ⟦ alter τ • Γ ⟧ΔContext
  quint : ∀ {τ Γ}
    (v : ⟦ erase τ ⟧)
    (dv : ⟦ τ ⟧ΔType)
    (R[v,dv] : valid {τ} v dv)
    (v⊕dv=v : _⊕_ {τ} v dv ≡ v)
    (ρ : ⟦ Γ ⟧ΔContext) →
    ⟦ abide τ • Γ ⟧ΔContext

meaning-ΔContext : Meaning Δ-Context
meaning-ΔContext = meaning ⟦_⟧ΔContext


-- ignore : ∀ {Γ} → ⟦ Γ ⟧ΔContext → ⟦ forget Γ ⟧
ignore ∅ = ∅
ignore (quad v dv R[v,dv] ρ) = v • ignore ρ
ignore (quint v dv R[v,dv] v⊕dv=v ρ) = v • ignore ρ

-- update : ∀ {Γ} → ⟦ Γ ⟧ΔContext → ⟦ forget Γ ⟧
update ∅ = ∅
update (quad {τ} v dv R[v,dv] ρ) = (_⊕_ {τ} v dv) • update ρ
update (quint {τ} v dv R[v,dv] v⊕dv=v ρ) = (_⊕_ {τ} v dv) • update ρ

--⟦_⟧ΔVar : ∀ {τ} {Γ} → Var (forget Γ) (erase τ) → ⟦ Γ ⟧ → ⟦ τ ⟧

{-
⟦_⟧ΔVar {alter τ • _} {.τ} this (quad _ dv _ _) = dv
⟦_⟧ΔVar {abide τ • _} {.τ} this (quint _ dv _ _ _) = dv
⟦_⟧ΔVar {alter _ • _} (that x) (quad _ _ _ ρ) = ⟦ x ⟧ΔVar ρ
⟦_⟧ΔVar {abide _ • _} (that x) (quint _ _ _ _ ρ) = ⟦ x ⟧ΔVar ρ
-}


-- ⟦_⟧ΔTerm : ∀ {τ Γ} → Δ-Term Γ τ → ⟦ Γ ⟧ΔContext → ⟦ τ ⟧ΔType
⟦_⟧ΔTerm _ _ = {!!}
{-
⟦ Δnat old new ⟧ΔTerm ρ = (old , new)
⟦ Δbag db ⟧ΔTerm ρ = db
⟦ Δvar x ⟧ΔTerm ρ = ⟦ x ⟧ΔVar ρ
⟦ Δabs t ⟧ΔTerm ρ =
  λ v dv R[v,dv]          → ⟦ t ⟧ΔTerm (alter v dv R[v,dv] ρ)
⟦ Δabs₀ t ⟧ΔTerm ρ =
  λ v dv R[v,dv] {-v⊕dv=v-} → ⟦ t ⟧ΔTerm (abide v dv R[v,dv] {!v⊕dv=v!} ρ)
⟦ Δapp ds t dt R[dt,t] ⟧ΔTerm ρ =
  ⟦ ds ⟧ΔTerm ρ (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧ΔTerm ρ) R[dt,t]
  --(R[dt,t] {ρ} {honesty = {!!}})
⟦ Δadd ds dt ⟧ΔTerm ρ =
  let
    (old-s , new-s) = ⟦ ds ⟧ΔTerm ρ
    (old-t , new-t) = ⟦ dt ⟧ΔTerm ρ
  in
    (old-s + old-t , new-s + new-t)
⟦ Δmap₀ f df b db ⟧ΔTerm ρ =
  let
    v  = ⟦ b ⟧ (ignore ρ)
    h  = ⟦ f ⟧ (ignore ρ)
    dv = ⟦ db ⟧ΔTerm ρ
    dh = ⟦ df ⟧ΔTerm ρ
  in
    mapBag (h ⊕ dh) (v ⊕ dv) \\ mapBag h v
⟦ Δmap₁ f db ⟧ΔTerm ρ = mapBag (⟦ f ⟧ (ignore ρ)) (⟦ db ⟧ΔTerm ρ)
-}

meaning-ΔTerm : ∀ {τ Γ} → Meaning (Δ-Term Γ τ)
meaning-ΔTerm = meaning ⟦_⟧ΔTerm



{-
--------------------------------------------------------
-- Program transformation and correctness (entangled) --
--------------------------------------------------------

derive : ∀ {τ Γ} → Term Γ τ → Δ-Term Γ τ

validity : ∀ {τ Γ} {t : Term Γ τ} {ρ : Δ-Env Γ} →
  valid (⟦ t ⟧ (ignore ρ)) (⟦ derive t ⟧ ρ)

correctness : ∀ {τ Γ} {t : Term Γ τ} {ρ : Δ-Env Γ} →
  ⟦ t ⟧ (ignore ρ) ⊕ ⟦ derive t ⟧ ρ ≡ ⟦ t ⟧ (update ρ)

-- derive : ∀ {τ Γ} → Term Γ τ → Δ-Term Γ τ
derive (nat n) = Δnat n n
derive (bag b) = Δbag emptyBag
derive (var x) = Δvar x
derive (abs t) = Δabs (derive t)
derive (app s t) = Δapp (derive s) t (derive t) validity
derive (add s t) = Δadd (derive s) (derive t)
derive (map f b) = Δmap₀ f (derive f) b (derive b)

validity-var : ∀ {τ Γ} → (x : Var Γ τ) →
  ∀ {ρ : Δ-Env Γ} → valid (⟦ x ⟧ (ignore ρ)) (⟦ x ⟧ΔVar ρ)

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
    dv = ⟦ derive t ⟧ ρ
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
      ⟦ t ⟧ (ignore ρ₂) ⊕ ⟦ derive t ⟧ ρ₂
    ≡⟨ correctness {t = t} {ρ₂} ⟩
      ⟦ t ⟧ (update ρ₂)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) v⊕[u⊝v]=u ⟩
      ⟦ t ⟧ (update ρ₁)
    ≡⟨ sym (correctness {t = t} {ρ₁}) ⟩
      ⟦ t ⟧ (ignore ρ₁) ⊕ ⟦ derive t ⟧ ρ₁
    ∎) where open ≡-Reasoning

correctVar : ∀ {τ Γ} {x : Var Γ τ} {ρ : Δ-Env Γ} →
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
    df = ⟦ derive s ⟧ ρ
    db = ⟦ derive t ⟧ ρ

correctness {t = app s t} {ρ} =
  let
    v = ⟦ t ⟧ (ignore ρ)
    dv = ⟦ derive t ⟧ ρ
  in trans
     (sym (proj₂ (validity {t = s} {ρ} v dv (validity {t = t} {ρ}))))
     (correctness {t = s} ⟨$⟩ correctness {t = t})

correctness {τ₁ ⇒ τ₂} {Γ} {abs t} {ρ} = extensionality (λ v →
  let
    ρ′ : Δ-Env (τ₁ • Γ)
    ρ′ = cons v (v ⊝ v) R[v,u⊝v] ρ
  in
    begin
      ⟦ t ⟧ (ignore ρ′) ⊕ ⟦ derive t ⟧ ρ′
    ≡⟨ correctness {t = t} {ρ′} ⟩
      ⟦ t ⟧ (update ρ′)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) v⊕[u⊝v]=u ⟩
      ⟦ t ⟧ (v • update ρ)
    ∎
  ) where open ≡-Reasoning
-}

