{-
Bug generator for Agda 2.3.2

Typechecking this file yields the following message:

An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Conversion.hs:428
-}

module TaggedDeltaTypes where

open import Data.NatBag renaming
  (map to mapBag ; empty to emptyBag ; update to updateBag)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
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
-- open import Data.NatBag.Properties
postulate b\\b=∅ : ∀ {{b : Bag}} → b \\ b ≡ emptyBag
postulate b++∅=b : ∀ {{b : Bag}} → b ++ emptyBag ≡ b
postulate ∅++b=b : ∀ {{b : Bag}} → emptyBag ++ b ≡ b
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
  Δ : (τ : Type) → Δ-Type

data Δ-Context : Set where
  Δ : (Γ : Context) → Δ-Context

Env : Context → Set
Env Γ = ⟦ Γ ⟧Context

private data Δ-Term : Δ-Context → Δ-Type → Set

-- Syntax of Δ-Types
-- ...   is mutually recursive with semantics of Δ-Terms,
-- (because it embeds validity proofs)
-- which is mutually recursive with validity and Δ-environments,
-- which is mutually recursive with ⊕,
-- which is mutually recursive with ⊝ and R[v,v⊝v],
-- which is mutually recursive with v⊕[u⊝v]=v, et cetera.
⟦_⟧Δτ : Δ-Type → Set
Δ-Env : Context → Set
⟦_⟧Δ : ∀ {τ : Type} {Γ : Context}
    → Δ-Term (Δ Γ) (Δ τ) → Δ-Env Γ → ⟦ Δ τ ⟧Δτ
_⊕_ : ∀ {τ : Type} → ⟦ τ ⟧ → ⟦ Δ τ ⟧Δτ → ⟦ τ ⟧
_⊝_ : ∀ {τ : Type} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ τ ⟧Δτ
valid : {τ : Type} → ⟦ τ ⟧ → ⟦ Δ τ ⟧Δτ → Set
R[v,u⊝v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊝ v)
v⊕[u⊝v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊕ (u ⊝ v) ≡ u
ignore : ∀ {Γ : Context} → (ρ : Δ-Env Γ) → ⟦ Γ ⟧
update : ∀ {Γ : Context} → (ρ : Δ-Env Γ) → ⟦ Γ ⟧

infixl 6 _⊕_ _⊝_ -- as with + - in GHC.Num

abstract
 data Δ-Term where
  -- changes to numbers are replacement pairs
  Δnat : ∀ {Γ} → (old : ℕ) → (new : ℕ) → Δ-Term (Δ Γ) (Δ nats)
  -- changes to bags are bags
  Δbag : ∀ {Γ} → (db : Bag) → Δ-Term (Δ Γ) (Δ bags)
  -- changes to variables are variables
  Δvar : ∀ {τ Γ} → (x : Var Γ τ) → Δ-Term (Δ Γ) (Δ τ)
  -- changes to abstractions are binders of x and dx
  Δabs : ∀ {τ₁ τ₂ Γ} → (t : Δ-Term (Δ (τ₁ • Γ)) (Δ τ₂)) →
         Δ-Term (Δ Γ) (Δ (τ₁ ⇒ τ₂))
  -- changes to applications are applications of a value and a change
  Δapp : ∀ {τ₁ τ₂ Γ} →(ds : Δ-Term (Δ Γ) (Δ (τ₁ ⇒ τ₂)))
                    → ( t :   Term    Γ      τ₁)
                    → (dt : Δ-Term (Δ Γ) (Δ  τ₁))
                    → (R[t,dt] : {ρ : Δ-Env Γ} → -- 'Tis but a proof.
                                 valid (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧Δ ρ)) →
         Δ-Term (Δ Γ) (Δ τ₂)
  -- changes to addition are changes to their components
  Δadd : ∀ {Γ} → (ds : Δ-Term (Δ Γ) (Δ nats))
               → (dt : Δ-Term (Δ Γ) (Δ nats)) →
         Δ-Term (Δ Γ) (Δ nats)
  -- There are two kinds of changes to maps:
  -- 0. recomputation,
  -- 1. mapping over changes,
  -- the latter used only with some form of isNil available.
  Δmap₀ : ∀ {Γ} → ( f :   Term    Γ     (nats ⇒ nats))
                → (df : Δ-Term (Δ Γ) (Δ (nats ⇒ nats)))
                → ( b :   Term    Γ     bags)
                → (db : Δ-Term (Δ Γ) (Δ bags))
          → Δ-Term (Δ Γ) (Δ bags)
  Δmap₁ : ∀ {Γ} → ( f :   Term    Γ     (nats ⇒ nats))
                → (db : Δ-Term (Δ Γ) (Δ bags))
          → Δ-Term (Δ Γ) (Δ bags)

-- ⟦_⟧Δτ : Δ-Type → Set
⟦ Δ nats ⟧Δτ = ℕ × ℕ
⟦ Δ bags ⟧Δτ = Bag
⟦ Δ (τ₁ ⇒ τ₂) ⟧Δτ =
  (v : ⟦ τ₁ ⟧) → (dv : ⟦ Δ τ₁ ⟧Δτ) → valid v dv → ⟦ Δ τ₂ ⟧Δτ

meaning-Δτ : Meaning Δ-Type
meaning-Δτ = meaning ⟦_⟧Δτ

_⊕_ {nats}   n dn = proj₂ dn
_⊕_ {bags}   b db = b ++ db
_⊕_ {τ₁ ⇒ τ₂} f df = λ v → f v ⊕ df v (v ⊝ v) R[v,u⊝v]

_⊝_ {nats}   m n = (n , m)
_⊝_ {bags}   b d = b \\ d
_⊝_ {τ₁ ⇒ τ₂} f g = λ v dv R[v,dv] → f (v ⊕ dv) ⊝ g v

-- valid : {τ : Type} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → Set
valid {nats} n dn = n ≡ proj₁ dn
valid {bags} b db = ⊤
valid {τ₁ ⇒ τ₂} f df =
  ∀ (v : ⟦ τ₁ ⟧) (dv : ⟦ Δ τ₁ ⟧Δτ) (R[v,dv] : valid v dv)
  → valid (f v) (df v dv R[v,dv])
  × (f ⊕ df) (v ⊕ dv) ≡ f v ⊕ df v dv R[v,dv]

eq1 : ∀ {τ₁ τ₂ : Type} {f : ⟦ τ₁ ⇒ τ₂ ⟧} {df} {x : ⟦ τ₁ ⟧} {dx} →
      valid f df → (R[x,dx] : valid x dx) →
      (f ⊕ df) (x ⊕ dx) ≡ f x ⊕ df x dx R[x,dx]

eq1 R[f,df] R[x,dx] = proj₂ (R[f,df] _ _ R[x,dx])

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
    ≡⟨ cong (λ hole → hole w′) (v⊕[u⊝v]=u {_} {u} {v}) ⟩
      u w′
    ≡⟨ sym (v⊕[u⊝v]=u {_} {u w′} {v w}) ⟩
      v w ⊕ (u ⊝ v) w dw R[w,dw]
    ∎) where open ≡-Reasoning

record Quadruple
  (A : Set) (B : A → Set) (C : (a : A) → B a → Set)
  (D : (a : A) → (b : B a) → (c : C a b) → Set): Set where
  constructor cons
  field
    car    : A
    cadr   : B car
    caddr  : C car cadr
    cadddr : D car cadr caddr

open Quadruple public

-- The type of environments ensures their consistency.
-- Δ-Env : Context → Set
Δ-Env ∅ = EmptySet
Δ-Env (τ • Γ) = Quadruple
  ⟦ τ ⟧
  (λ v → ⟦ Δ τ ⟧Δτ)
  (λ v dv → valid v dv)
  (λ v dv R[v,dv] → Δ-Env Γ)

-- ignore : ∀ {Γ : Context} → (ρ : Δ-Env Γ) → Env Γ
ignore {∅} ρ = ∅
ignore {τ • Γ} (cons v dv R[v,dv] ρ) = v • ignore ρ

-- update : ∀ {Γ : Context} → (ρ : Δ-Env Γ) → Env Γ
update {∅} ρ = ∅
update {τ • Γ} (cons v dv R[v,dv] ρ) = (v ⊕ dv) • update ρ

⟦_⟧ΔVar : ∀ {τ Γ} → Var Γ τ → Δ-Env Γ → ⟦ Δ τ ⟧Δτ
⟦ this   ⟧ΔVar (cons v dv R[v,dv] ρ) = dv
⟦ that x ⟧ΔVar (cons v dv R[v,dv] ρ) = ⟦ x ⟧ΔVar ρ

-- ⟦_⟧ΔVar is not put into the Meaning type class
-- because its argument is identical to that of ⟦_⟧Var.

-- ⟦_⟧Δ : ∀ {τ Γ} → Δ-Term (Δ Γ) (Δ τ) → Δ-Env Γ → ⟦ Δ τ ⟧Δτ
abstract
 ⟦ Δnat old new ⟧Δ ρ = (old , new)
 ⟦ Δbag db ⟧Δ ρ = db
 ⟦ Δvar x ⟧Δ ρ = ⟦ x ⟧ΔVar ρ
 ⟦ Δabs t ⟧Δ ρ = λ v dv R[v,dv] → ⟦ t ⟧Δ (cons v dv R[v,dv] ρ)
 ⟦ Δapp ds t dt R[dt,t] ⟧Δ ρ =
   ⟦ ds ⟧Δ ρ (⟦ t ⟧ (ignore ρ)) (⟦ dt ⟧Δ ρ) R[dt,t]
 ⟦ Δadd ds dt ⟧Δ ρ =
   let
     (old-s , new-s) = ⟦ ds ⟧Δ ρ
     (old-t , new-t) = ⟦ dt ⟧Δ ρ
   in
     (old-s + old-t , new-s + new-t)
 ⟦ Δmap₀ f df b db ⟧Δ ρ =
   let
     v  = ⟦ b ⟧ (ignore ρ)
     h  = ⟦ f ⟧ (ignore ρ)
     dv = ⟦ db ⟧Δ ρ
     dh = ⟦ df ⟧Δ ρ
   in
     mapBag (h ⊕ dh) (v ⊕ dv) \\ mapBag h v
 ⟦ Δmap₁ f db ⟧Δ ρ = mapBag (⟦ f ⟧ (ignore ρ)) (⟦ db ⟧Δ ρ)

meaning-ΔTerm : ∀ {τ Γ} → Meaning (Δ-Term (Δ Γ) (Δ τ))
meaning-ΔTerm = meaning ⟦_⟧Δ

--------------------------------------------------------
-- Program transformation and correctness (entangled) --
--------------------------------------------------------

derive : ∀ {τ Γ} → Term Γ τ → Δ-Term (Δ Γ) (Δ τ)

validity : ∀ {τ Γ} {t : Term Γ τ} {ρ : Δ-Env Γ} →
  valid (⟦ t ⟧ (ignore ρ)) (⟦ derive t ⟧ ρ)

-- derive : ∀ {τ Γ} → Term Γ τ → Δ-Term (Δ Γ) (Δ τ)
derive (nat n) = Δnat n n
derive (bag b) = Δbag b
derive (var x) = Δvar x
derive (abs t) = Δabs (derive t)
derive (app s t) = Δapp (derive s) t (derive t) validity
derive (add s t) = Δadd (derive s) (derive t)
derive (map f b) = Δmap₀ f (derive f) b (derive b)

validity-var : ∀ {τ Γ} → (x : Var Γ τ) →
  ∀ {ρ : Δ-Env Γ} → valid (⟦ x ⟧ (ignore ρ)) (⟦ x ⟧ΔVar ρ)

validity-var this {cons v dv R[v,dv] ρ} = R[v,dv]
validity-var (that x) {cons v dv R[v,dv] ρ} = validity-var x

--validity {nats} {Γ} {nat n} {∅} = ?
validity {nats} {∅}    {nat n} {∅} =
  begin
    n
  ≡⟨ ? ⟩
    proj₁ (n , n)
  ≡⟨ {!!} ⟩
    proj₁ (⟦ Δnat n n ⟧ ∅)
  ∎ where open ≡-Reasoning
validity {nats} {τ • Γ} {nat n} {ρ} = {!!}
validity {bags} {Γ} {bag b} = {!!}
validity {τ} {Γ} {var x} = {!!}
validity {τ₁ ⇒ τ₂} {Γ} {abs t} = {!!}
validity {τ} {Γ} {app t t₁} = {!!}
validity {nats} {Γ} {add t t₁} = {!!}
validity {bags} {Γ} {map t t₁} = {!!}
