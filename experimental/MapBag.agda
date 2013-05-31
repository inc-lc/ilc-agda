{-

Introducing the MapBag, which can be considered a bag
of ℤ with negative multiplicities, or a map from
ℤ to ℤ with default value 0.

The initial goal of this file is to make the 5th example
described in /examples.md, "Map.mapValues", fast:

    -- Haskell's Data.Map.map is Scala's Map.mapValues
    map :: (a -> b) -> Map k a -> Map k b
    
    incVal :: Map Integer Integer -> Map Integer Integer
    incVal = map (+1)

    old = fromAscList  [(1, 1), (2, 2) .. (n, n)]
    res = incVal old = [(1, 2), (2, 3) .. (n, n + 1)]

TODO
X. Replace ℕ by ℤ
2. Introduce addition
3. Add MapBags and map
4. Figure out a way to communicate to a derivative that
   certain changes are always nil (in this case, `+1`).


Checklist: Adding syntactic constructs

- weaken
- ⟦_⟧Term
- weaken-sound
- derive (symbolic derivation)
- validity-of-derive
- correctness-of-derive

Checklist: Adding types

- ⟦_⟧Type
- Δ-Type
- ⟦derive⟧
- _⟦⊝⟧_
- _⟦⊕⟧_
- f⟦⊝⟧f=⟦deriv⟧f
- f⊕[g⊝f]=g
- f⊕Δf=f
- valid-Δ
- R[f,g⊝f]
- df=f⊕df⊝f
- R (inside validity-of-derive)

-}

module MapBag where

open import Data.Unit using
  (⊤)
open import Data.Nat using
  (ℕ ; suc ; _≤′_ ; ≤′-refl ; ≤′-step)
open import Induction.Nat using
  (<-rec)
open import Data.Integer using
  (ℤ ; +_ ; -[1+_] ; _+_ ; _-_)
open import Data.Product using
  (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

open import Relation.Binary.PropositionalEquality

import Level

postulate extensionality : Extensionality Level.zero Level.zero

-- Map nats to ints with default 0
data NatMap : Set where
  ∅ : NatMap
  ℕtree : (v : ℤ) → (left : NatMap) → (right : NatMap) → NatMap

{- To understand why there must be an empty NatMap,
   observe the termination checker's complaint upon
   seeing Haskell's empty NatMap:

emptyMap : NatMap
emptyMap = ℕtree (+ 0) emptyMap emptyMap
-}

data Oddity : Set where
  odd  : Oddity
  even : Oddity

oddity : ℕ → Oddity
oddity 0 = even
oddity 1 = odd
oddity (suc (suc n)) = oddity n

-- Elimination form of Oddity to please termination checker
-- ... eventually.

if-odd_then_else_ : ∀ {A : Set} → ℕ → A → A → A
if-odd k then thenBranch else elseBranch with oddity k
... | odd  = thenBranch
... | even = elseBranch

-- oddity-index k = (oddity k , (k - 1) / 2)
oddity-index : ℕ → Oddity × ℕ
oddity-index 0 = (even , 0)
oddity-index 1 = (odd  , 0)
oddity-index 2 = (even , 0)
oddity-index (suc (suc k)) = (oddity-k , suc [k-1]/2) where
  oddity-index-k = oddity-index k
  oddity-k = proj₁ oddity-index-k
  [k-1]/2  = proj₂ oddity-index-k

-- Copied from Induction.Nat.Examples (declared private)

half₁ : ℕ → ℕ
half₁ 0 = 0
half₁ 1 = 0
half₁ 2 = 0
half₁ (suc (suc n)) = suc (half₁ n)

data Nonzero : ℕ → Set where
  suc : (n : ℕ) → Nonzero (suc n)

≤′-suc : ∀ {m n : ℕ} → m ≤′ n → (suc m) ≤′ (suc n)
≤′-suc ≤′-refl = ≤′-refl
≤′-suc (≤′-step le) = ≤′-step (≤′-suc le)

half₁-β≡ : ∀ {n : ℕ} → Nonzero n → half₁ (suc (suc n)) ≡ suc (half₁ n)
half₁-β≡ {0} ()
half₁-β≡ {suc n} nz = refl

half₁-WF : ∀ (n : ℕ) → Nonzero n → suc (half₁ n) ≤′ n
half₁-WF 0 ()
half₁-WF 1 _ = ≤′-refl
half₁-WF 2 _ = ≤′-step ≤′-refl
half₁-WF (suc (suc (suc n))) _ =
  ≤′-suc {suc (half₁ (suc n))} {suc (suc n)} {!half₁-WF (suc n) ?!}
-- TODO:
-- 0. Stop not getting why hole#0 can't be filled
-- 1. Prove well-foundedness of half₁
-- 2. Fix singleton
-- 3. Make sure this file has no hole
-- 4. Finish ExplicitNils
-- 5. Consider appending ExplicitNils

-- Here to please the termination checker
singleton : ℕ → ℤ → NatMap
singleton k v = loop k where
  loop : ℕ → NatMap
  loop = <-rec _ λ
    { 0 _ → ℕtree v ∅ ∅
    ; n rec →
      let
        next = half₁ n
      in -- TODO: Case distinction
        rec next {!!}
    }

{-
cRec _ λ
  { 0 _ → (0 , ℕtree v ∅ ∅)
  ; 1 _ → (100 , ℕtree (+ 0) (ℕtree v ∅ ∅) ∅)
  ; 2 _ → (200 , ℕtree (+ 0) ∅ (ℕtree v ∅ ∅))
  ; (suc (suc n)) (_ , self , _) →
      let
        [[n+2]-1]/2 = suc (proj₁ self)
        half-map    =      proj₂ self
      in if-odd n
          then ([[n+2]-1]/2 , ℕtree (+ 0) half-map ∅)
          else ([[n+2]-1]/2 , ℕtree (+ 0) ∅ half-map)
  }
-}

ℕlookup : ℕ → NatMap → ℤ
ℕlookup _ ∅ = (+ 0)
ℕlookup 0 (ℕtree v _ _) = v
ℕlookup k (ℕtree _ left right) with oddity-index k
... | (odd  , [k-1]/2) = ℕlookup [k-1]/2 left
... | (even , [k-1]/2) = ℕlookup [k-1]/2 right

-- `→` and `in` are keywords
ℕset_⇒_within_ : ℕ → ℤ → NatMap → NatMap
ℕset k ⇒ v within ∅ = singleton k v
ℕset 0 ⇒ v within (ℕtree v₀ left right) = ℕtree v left right
ℕset k ⇒ v within (ℕtree v₀ left right) with oddity-index k
... | (odd  , [k-1]/2) = ℕtree v₀ left (ℕset [k-1]/2 ⇒ v within right)
... | (even , [k-1]/2) = ℕtree v₀ (ℕset [k-1]/2 ⇒ v within left) right

-- We implement nothing but the necessary NatMap operations to save time:
-- union, difference, mapValues.

ℕmapValues : (ℤ → ℤ) → NatMap → NatMap
ℕmapValues _ ∅ = ∅
ℕmapValues f (ℕtree v left right) =
  ℕtree (f v) (ℕmapValues f left) (ℕmapValues f right)

MapBag = NatMap × NatMap

lookup : ℤ → MapBag → ℤ
lookup -[1+ k ] b = ℕlookup k (proj₁ b)
lookup   (+ k)  b = ℕlookup k (proj₂ b)

set_⇒_within_ : ℤ → ℤ → MapBag → MapBag
set -[1+ k ] ⇒ v within (neg , pos) = (ℕset k ⇒ v within neg , pos)
set    + k   ⇒ v within (neg , pos) = (neg , ℕset k ⇒ v within pos)

mapValues : (ℤ → ℤ) → MapBag → MapBag
mapValues f (neg , pos) = (ℕmapValues f neg , ℕmapValues f pos)

{-

data Type : Set where
  ints : Type
  bags : Type
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

data Term : Context -> Type -> Set where

  int : ∀ {Γ} → (n : ℤ) → Term Γ ints
  bag : ∀ {Γ} → (b : MapBag) → Term Γ bags
  add : ∀ {Γ} → (t₁ : Term Γ ints) → (t₂ : Term Γ ints) → Term Γ ints
  map : ∀ {Γ} → (f : Term Γ (ints ⇒ ints)) → (b : Term Γ bags) → Term Γ bags

  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ
  abs : ∀ {τ₁ τ₂ Γ} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂ Γ} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁)
                   → Term Γ τ₂

  -- Change to ints = replacement Church pairs
  -- 3 -> 5 ::= λf. f 3 5

infix 8 _≼_

data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅≼∅ : ∅ ≼ ∅
  keep_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → τ • Γ₁ ≼ τ • Γ₂
  drop_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → Γ₁ ≼ τ • Γ₂

weakenVar : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weakenVar ∅≼∅ x = x
weakenVar (keep τ₁ • subctx) this = this
weakenVar (keep τ₁ • subctx) (that y) = that (weakenVar subctx y)
weakenVar (drop τ₁ • subctx) x = that (weakenVar subctx x)

weaken : ∀ {Γ₁ Γ₂ τ} → (subctx : Γ₁ ≼ Γ₂) → Term Γ₁ τ → Term Γ₂ τ
weaken subctx (abs {τ} t) = abs (weaken (keep τ • subctx) t)
weaken subctx (app t₁ t₂) = app (weaken subctx t₁) (weaken subctx t₂)
weaken subctx (var x) = var (weakenVar subctx x)
weaken subctx (int x) = int x
weaken subctx (bag b) = bag b
weaken subctx (add t₁ t₂) = add (weaken subctx t₁) (weaken subctx t₂)
weaken subctx (map f b) = map (weaken subctx f) (weaken subctx b)

record Meaning (Syntax : Set) {ℓ : Level.Level} : Set (Level.suc ℓ) where
  constructor
    meaning
  field
    {Semantics} : Set ℓ
    ⟨_⟩⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public
  renaming (⟨_⟩⟦_⟧ to ⟦_⟧)

⟦_⟧Type : Type -> Set
⟦ ints ⟧Type = ℤ
⟦ bags ⟧Type = MapBag
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
⟦ int n ⟧Term ρ = n
⟦ bag b ⟧Term ρ = b
⟦ add m n ⟧Term ρ = ⟦ m ⟧Term ρ + ⟦ n ⟧Term ρ
⟦ map f b ⟧Term ρ = mapValues (⟦ f ⟧Term ρ) (⟦ b ⟧Term ρ)

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

_⟨$⟩_ : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
_⟨$⟩_ = cong₂ (λ x y → x y)
infix 0 _⟨$⟩_ -- infix 0 $ in Haskell

weaken-sound : ∀ {Γ₁ Γ₂ τ} {subctx : Γ₁ ≼ Γ₂} (t : Term Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken subctx t ⟧ ρ ≡ ⟦ t ⟧ (⟦ subctx ⟧ ρ)
weaken-sound (abs t) ρ = extensionality (λ v → weaken-sound t (v • ρ))
weaken-sound (app t₁ t₂) ρ = weaken-sound t₁ ρ ⟨$⟩ weaken-sound t₂ ρ
weaken-sound {subctx = subctx} (var x) ρ = weakenVar-sound subctx x ρ
weaken-sound (int n) ρ = refl

weaken-sound (bag b) ρ = refl
weaken-sound (add m n) ρ = cong₂ _+_ (weaken-sound m ρ) (weaken-sound n ρ)
weaken-sound (map f b) ρ = cong₂ mapValues (weaken-sound f ρ)
                                           (weaken-sound b ρ)

-- Changes to ℤ are replacement Church pairs. The only arguments
-- of conern are `fst` and `snd`, so the Church pairs don't have
-- to be polymorphic.

Δ-Type : Type → Type
Δ-Type ints = (ints ⇒ ints ⇒ ints) ⇒ ints
Δ-Type bags = bags
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂

-- It is clear that ⟦⊝⟧ exists on the semantic level:
-- there exists an Agda value to describe the change between any
-- two Agda values denoted by terms. If we have (not dependently-
-- typed) arrays, no term denotes the change between two arrays
-- of different lengths. Thus no full abstraction.

⟦derive⟧ : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
_⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧
_⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧

infixl 6 _⟦⊕⟧_
infixl 6 _⟦⊝⟧_

⟦fst⟧ : ℤ → ℤ → ℤ
⟦snd⟧ : ℤ → ℤ → ℤ

⟦derive⟧ {ints} n = λ f → f n n
⟦derive⟧ {bags} b = ∅
⟦derive⟧ {τ₁ ⇒ τ₂} f = λ v dv → f (v ⟦⊕⟧ dv) ⟦⊝⟧ f v

_⟦⊝⟧_ {ints} m n = λ f → f n m
_⟦⊝⟧_ {bags} b₁ b₂ = {!!}
_⟦⊝⟧_ {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → f₁ (v ⟦⊕⟧ dv) ⟦⊝⟧ f₂ v
-- m ⟦⊝⟧ n ::= replace n by m

_⟦⊕⟧_ {ints} n dn = dn ⟦snd⟧
_⟦⊕⟧_ {bags} b db = {!!}
_⟦⊕⟧_ {τ₁ ⇒ τ₂} f df = λ v → f v ⟦⊕⟧ df v (⟦derive⟧ v)

⟦fst⟧ m n = m
⟦snd⟧ m n = n

-- Cool lemmas

f⟦⊝⟧f=⟦deriv⟧f : ∀ {τ : Type} (f : ⟦ τ ⟧) → f ⟦⊝⟧ f ≡ ⟦derive⟧ f
f⟦⊝⟧f=⟦deriv⟧f {ints} f = refl
f⟦⊝⟧f=⟦deriv⟧f {bags} b = {!!}
f⟦⊝⟧f=⟦deriv⟧f {τ₁ ⇒ τ₂} f = refl

f⊕[g⊝f]=g : ∀ {τ : Type} (f g : ⟦ τ ⟧) → f ⟦⊕⟧ (g ⟦⊝⟧ f) ≡ g

f⊕Δf=f : ∀ {τ : Type} (f : ⟦ τ ⟧) → f ⟦⊕⟧ (⟦derive⟧ f) ≡ f

f⊕[g⊝f]=g {ints} m n = refl
f⊕[g⊝f]=g {bags} b₁ b₂ = {!!}
f⊕[g⊝f]=g {τ₁ ⇒ τ₂} f g = extensionality (λ x →
    begin
      (f ⟦⊕⟧ (g ⟦⊝⟧ f)) x
    ≡⟨ refl ⟩
      f x ⟦⊕⟧ (g (x ⟦⊕⟧ ⟦derive⟧ x) ⟦⊝⟧ f x)
    ≡⟨ cong₂ _⟦⊕⟧_
            {x = f x} {y = f x} refl
            (cong₂ _⟦⊝⟧_ (cong g (f⊕Δf=f x)) refl) ⟩
      f x ⟦⊕⟧ (g x ⟦⊝⟧ f x)
    ≡⟨ f⊕[g⊝f]=g (f x) (g x) ⟩
      g x
    ∎
  ) where open ≡-Reasoning

f⊕Δf=f {ints} n = refl
f⊕Δf=f {bags} b = {!!}
f⊕Δf=f {τ₁ ⇒ τ₂} f = extensionality (λ x →
    begin
      (f ⟦⊕⟧ ⟦derive⟧ f) x
    ≡⟨ refl ⟩
      f x ⟦⊕⟧ (f (x ⟦⊕⟧ ⟦derive⟧ x) ⟦⊝⟧ f x)
    ≡⟨ cong (λ hole → f x ⟦⊕⟧ (f hole ⟦⊝⟧ f x)) (f⊕Δf=f x) ⟩
      f x ⟦⊕⟧ (f x ⟦⊝⟧ f x)
    ≡⟨ f⊕[g⊝f]=g (f x) (f x) ⟩
      f x
    ∎
  ) where open ≡-Reasoning

valid-Δ : {τ : Type} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → Set
valid-Δ {ints} n dn = n ≡ dn ⟦fst⟧
valid-Δ {bags} b db = {!!}
valid-Δ {τ₁ ⇒ τ₂} f df =
  ∀ (s : ⟦ τ₁ ⟧) (ds : ⟦ Δ-Type τ₁ ⟧) (R[s,ds] : valid-Δ s ds) →
    valid-Δ (f s) (df s ds) ×              -- (valid-Δ:1)
    (f ⟦⊕⟧ df) (s ⟦⊕⟧ ds) ≡ f s ⟦⊕⟧ df s ds -- (valid-Δ:2)

R[f,g⊝f] : ∀ {τ} (f g : ⟦ τ ⟧) → valid-Δ {τ} f (g ⟦⊝⟧ f)
R[f,g⊝f] {ints} m n = refl
R[f,g⊝f] {bags} b₁ b₂ = {!!}
R[f,g⊝f] {τ₁ ⇒ τ₂} f g = λ x dx R[x,dx] →
  R[f,g⊝f] {τ₂} (f x) (g (x ⟦⊕⟧ dx)) -- (valid-Δ:1)
  , -- tuple constructor
  (begin
    (f ⟦⊕⟧ (g ⟦⊝⟧ f)) (x ⟦⊕⟧ dx)
  ≡⟨ refl ⟩
    f (x ⟦⊕⟧ dx) ⟦⊕⟧
      (g ((x ⟦⊕⟧ dx) ⟦⊕⟧ ⟦derive⟧ (x ⟦⊕⟧ dx)) ⟦⊝⟧ f (x ⟦⊕⟧ dx))
  ≡⟨ cong (λ hole → f (x ⟦⊕⟧ dx) ⟦⊕⟧ (g hole ⟦⊝⟧ f (x ⟦⊕⟧ dx)))
          (f⊕Δf=f (x ⟦⊕⟧ dx)) ⟩
    f (x ⟦⊕⟧ dx) ⟦⊕⟧ (g (x ⟦⊕⟧ dx) ⟦⊝⟧ f (x ⟦⊕⟧ dx))
  ≡⟨ f⊕[g⊝f]=g (f (x ⟦⊕⟧ dx)) (g (x ⟦⊕⟧ dx)) ⟩
    g (x ⟦⊕⟧ dx)
  ≡⟨ sym (f⊕[g⊝f]=g (f x) (g (x ⟦⊕⟧ dx))) ⟩
      f x ⟦⊕⟧ (g ⟦⊝⟧ f) x dx
  ∎)
  where open ≡-Reasoning

R[f,Δf] : ∀ {τ} (f : ⟦ τ ⟧) → valid-Δ {τ} f (⟦derive⟧ f)
R[f,Δf] f rewrite sym (f⟦⊝⟧f=⟦deriv⟧f f) = R[f,g⊝f] f f

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ -- push τ, then push Δτ.

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ Δ-Context Γ
Γ≼ΔΓ {∅} = ∅≼∅
Γ≼ΔΓ {τ • Γ} = drop Δ-Type τ • (keep τ • Γ≼ΔΓ)

-- Data type to hold proofs that environments are valid
data Valid-Δenv : {Γ : Context} (ρ : ⟦ Γ ⟧) (Δρ : ⟦ Δ-Context Γ ⟧) → Set
 where
  -- Base case: the empty environment is its own valid Δ-environment.
  ρ=∅ : Valid-Δenv {∅} ∅ ∅
  -- Induction case: the change introduced therein should be valid,
  -- and the smaller Δ-environment should be valid as well.
  ρ=v•ρ₀ : ∀ {τ : Type} {v : ⟦ τ ⟧} {dv : ⟦ Δ-Type τ ⟧}
            {Γ₀ : Context} {ρ₀ : ⟦ Γ₀ ⟧} {dρ₀ : ⟦ Δ-Context Γ₀ ⟧} →
            valid-Δ v dv → Valid-Δenv ρ₀ dρ₀ →
            Valid-Δenv {τ • Γ₀} (v • ρ₀) (dv • v • dρ₀)

-- Data type to hold proofs that a Δ-env is consistent with self
data Consistent-Δenv : {Γ : Context} (dρ : ⟦ Δ-Context Γ ⟧) → Set
 where
  -- Base case: the empty environment is consistent with itself
  dρ=∅ : Consistent-Δenv {∅} ∅
  -- Induction case: the change introduced at top level
  -- should be valid.
  dρ=dv•v•dρ₀ : ∀ {τ : Type} {v : ⟦ τ ⟧} {dv : ⟦ Δ-Type τ ⟧}
                 {Γ₀ : Context} {dρ₀ : ⟦ Δ-Context Γ₀ ⟧} →
                 valid-Δ v dv → Consistent-Δenv dρ₀ →
                 Consistent-Δenv {τ • Γ₀} (dv • v • dρ₀)

-- If a Δ-environment is valid for some other environment,
-- then it is also consistent with itself.

valid-Δenv-is-consistent :
   ∀ {Γ : Context} {ρ : ⟦ Γ ⟧} {dρ : ⟦ Δ-Context Γ ⟧} →
    Valid-Δenv ρ dρ → Consistent-Δenv dρ

valid-Δenv-is-consistent ρ=∅ = dρ=∅
valid-Δenv-is-consistent (ρ=v•ρ₀ valid[v,dv] valid[ρ₀,dρ₀]) =
  dρ=dv•v•dρ₀ valid[v,dv] (valid-Δenv-is-consistent valid[ρ₀,dρ₀])

-- finally, update and ignore

update : ∀ {Γ} → (dρ : ⟦ Δ-Context Γ ⟧) → {_ : Consistent-Δenv dρ} → ⟦ Γ ⟧
update {∅} ∅ {dρ=∅} = ∅
update {τ • Γ} (dv • v • dρ) {dρ=dv•v•dρ₀ valid[v,dv] consistent[dρ₀]} =
  (v ⟦⊕⟧ dv) • update dρ {consistent[dρ₀]}

-- Ignorance is bliss (don't have to pass consistency proofs around :D)

ignore : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
ignore = ⟦ Γ≼ΔΓ ⟧ -- Using a proof to describe computation

-- Naming scheme follows weakenVar/weaken

deriveVar : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

derive : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) (Δ-Type τ)

-- derive(n) = λf. f n n
derive (int n) = abs (app (app (var this) (int n)) (int n))

-- derive(x) = dx
derive (var x) = var (deriveVar x)

-- derive(λx. t) = λx. λdx. derive(t)
derive (abs t) = abs (abs (derive t))

-- derive(f s) = derive(f) s derive(s)
derive (app f s) = app (app (derive f) (weaken Γ≼ΔΓ s)) (derive s)

derive _ = {!!}

-- Extensional equivalence for changes
data Extensionally-equivalent-as-changes :
  ∀ (τ : Type) → (df : ⟦ Δ-Type τ ⟧) → (dg : ⟦ Δ-Type τ ⟧) → Set where
  ext-Δ : ∀ {τ : Type} {df dg : ⟦ Δ-Type τ ⟧} →
          (∀ (f : ⟦ τ ⟧) → valid-Δ f df → valid-Δ f dg →
             (f ⟦⊕⟧ df) ≡ (f ⟦⊕⟧ dg)) →
          Extensionally-equivalent-as-changes τ df dg

syntax Extensionally-equivalent-as-changes τ df dg = df ≈ dg :Δ τ

-- Question: How to declare fixity for infix syntax?
-- infix 4 _≈_:Δ_ -- same as ≡

-- Extractor for extensional-equivalence-as-changes:
-- Given a value of the data type holding the proof,
-- returns the proof in applicable form.
--
-- It would not be necessary if such
-- proof-holding types were defined as a function in
-- the first place, say in the manner of `valid-Δ`.
--
extract-Δequiv :
  ∀ {τ : Type} {df dg : ⟦ Δ-Type τ ⟧} →
    df ≈ dg :Δ τ →
    (f : ⟦ τ ⟧) → valid-Δ f df → valid-Δ f dg → (f ⟦⊕⟧ df) ≡ (f ⟦⊕⟧ dg)

extract-Δequiv (ext-Δ proof-method) = proof-method

-- Distribution lemmas of validity over ⟦⊝⟧ and ⟦⊕⟧

application-over-⊕-and-⊝ :
  ∀ {τ₁ τ₂ : Type}
    (f g : ⟦ τ₁ ⇒ τ₂ ⟧) (df : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧) (v : ⟦ τ₁ ⟧) →
    (f v ⟦⊕⟧ df v (⟦derive⟧ v) ⟦⊝⟧ f v) ≡ (f ⟦⊕⟧ df ⟦⊝⟧ f) v (⟦derive⟧ v)
application-over-⊕-and-⊝ f g df v =
  begin
    f v ⟦⊕⟧ df v (⟦derive⟧ v) ⟦⊝⟧ f v
  ≡⟨ cong₂ _⟦⊝⟧_
       (cong₂ _⟦⊕⟧_
         (cong f ((sym (f⊕Δf=f v))))
         (cong₂ df
           (sym (f⊕Δf=f v))
           (cong ⟦derive⟧ (sym (f⊕Δf=f v)))))
       refl ⟩
    f (v ⟦⊕⟧ ⟦derive⟧ v)
    ⟦⊕⟧ df (v ⟦⊕⟧ ⟦derive⟧ v) (⟦derive⟧ (v ⟦⊕⟧ ⟦derive⟧ v))
    ⟦⊝⟧ f v
  ≡⟨ refl ⟩
   (f ⟦⊕⟧ df ⟦⊝⟧ f) v (⟦derive⟧ v)
  ∎ where open ≡-Reasoning

validity-over-⊕-and-⊝ :
  ∀ {τ₁ τ₂ : Type}
    (f g : ⟦ τ₁ ⇒ τ₂ ⟧) (df : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧) (v : ⟦ τ₁ ⟧) →
    valid-Δ g (f ⟦⊕⟧ df ⟦⊝⟧ f) →
    valid-Δ (g v) (f v ⟦⊕⟧ df v (⟦derive⟧ v) ⟦⊝⟧ f v)
validity-over-⊕-and-⊝ f g df v R[g,f⊕df]
  rewrite application-over-⊕-and-⊝ f g df v =
    proj₁ (R[g,f⊕df] v (⟦derive⟧ v) (R[f,Δf] v))

-- diff-apply
df=f⊕df⊝f :
  ∀ {τ} (f : ⟦ τ ⟧) (df : ⟦ Δ-Type τ ⟧) →
    valid-Δ f df → df ≈ (f ⟦⊕⟧ df ⟦⊝⟧ f) :Δ τ

-- Case int: this REFL is more obvious to Agda than to a human.
df=f⊕df⊝f {ints} n dn valid-n-dn =
  ext-Δ (λ m valid-m-dn valid-rhs → refl)

df=f⊕df⊝f {bags} b db valid-b-db = {!!}

df=f⊕df⊝f {τ₁ ⇒ τ₂} f df R[f,df] = ext-Δ (
  λ g R[g,df] R[g,f⊕df⊝f] →
    extensionality (λ v →
      begin
        g v ⟦⊕⟧ df v (⟦derive⟧ v)
      ≡⟨ extract-Δequiv
           (df=f⊕df⊝f
             (f v) (df v (⟦derive⟧ v))
             (proj₁ (R[f,df] v (⟦derive⟧ v) (R[f,Δf] v))))
           (g v)
           (proj₁ (R[g,df] v (⟦derive⟧ v) (R[f,Δf] v)))
           (validity-over-⊕-and-⊝ f g df v R[g,f⊕df⊝f]) ⟩
        g v ⟦⊕⟧ (f v ⟦⊕⟧ df v (⟦derive⟧ v) ⟦⊝⟧ f v)
      ≡⟨ cong₂ _⟦⊕⟧_
           {x = g v} {y = g v} refl
           (application-over-⊕-and-⊝ f g df v) ⟩
        g v ⟦⊕⟧ (f ⟦⊕⟧ df ⟦⊝⟧ f) v (⟦derive⟧ v)
      ∎
    )
  )
  where open ≡-Reasoning



correctness-of-deriveVar : ∀ {Γ τ} →
  ∀ (ρ : ⟦ Δ-Context Γ ⟧) {consistency : Consistent-Δenv ρ} →
  ∀ (x : Var Γ τ) →
  (⟦ deriveVar x ⟧ ρ)
  ≈
  (⟦ x ⟧ (update ρ {consistency}) ⟦⊝⟧ ⟦ x ⟧ (ignore ρ)) :Δ τ

correctness-of-deriveVar {τ • Γ₀} {.τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ {.τ} {.v} {.dv} {.Γ₀} {.ρ} R[v,dv] _}
  this = df=f⊕df⊝f {τ} v dv R[v,dv]

correctness-of-deriveVar {τ₀ • Γ₀} {τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ {.τ₀} {.v} {.dv} {.Γ₀} {.ρ} R[v,dv] _}
  (that x) = correctness-of-deriveVar ρ x



correctness-of-derive : ∀ {Γ τ} →
  ∀ (ρ : ⟦ Δ-Context Γ ⟧) {consistency : Consistent-Δenv ρ} →
  ∀ (t : Term Γ τ) →

    (⟦ derive t ⟧ ρ)
  ≈ (⟦ t ⟧ (update ρ {consistency}) ⟦⊝⟧ ⟦ t ⟧ (ignore ρ)) :Δ τ

-- Mutually recursive lemma: derivatives are valid
validity-of-derive : ∀ {Γ τ} →
  ∀ (ρ : ⟦ Δ-Context Γ ⟧) {consistency : Consistent-Δenv ρ} →
  ∀ (t : Term Γ τ) →
  valid-Δ (⟦ t ⟧ (ignore ρ)) (⟦ derive t ⟧ ρ)

validity-of-deriveVar : ∀ {Γ τ} →
  ∀ (ρ : ⟦ Δ-Context Γ ⟧) {consistency : Consistent-Δenv ρ} →
  ∀ (x : Var Γ τ) →
  valid-Δ (⟦ x ⟧ (ignore ρ)) (⟦ deriveVar x ⟧ ρ)

validity-of-deriveVar {τ • Γ} {.τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ R[v,dv] consistency}
  this = R[v,dv]

validity-of-deriveVar {τ₀ • Γ} {τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ R[v,dv] consistency}
  (that x) = validity-of-deriveVar ρ {consistency} x

validity-of-derive ρ {consistency} (var x) =
  validity-of-deriveVar ρ {consistency} x

validity-of-derive ρ (int n) = refl

validity-of-derive {Γ} {τ₁ ⇒ τ₂}
  ρ {consistency} (abs t) = λ v dv R[v,dv] →
    validity-of-derive (dv • v • ρ) {dρ=dv•v•dρ₀ R[v,dv] consistency} t
    , -- tuple constructor
      (begin
        ⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ) ⟦⊕⟧
          ⟦ derive t ⟧ (⟦derive⟧ (v ⟦⊕⟧ dv) • (v ⟦⊕⟧ dv) • ρ)
      ≡⟨ extract-Δequiv
           (correctness-of-derive
             (⟦derive⟧ (v ⟦⊕⟧ dv) • (v ⟦⊕⟧ dv) • ρ)
             {dρ=dv•v•dρ₀ (R[f,Δf] (v ⟦⊕⟧ dv)) consistency}
             t)
           (⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ))
           (validity-of-derive
             (⟦derive⟧ (v ⟦⊕⟧ dv) • (v ⟦⊕⟧ dv) • ρ)
             {dρ=dv•v•dρ₀ (R[f,Δf] (v ⟦⊕⟧ dv)) consistency}
             t)
           ((R[f,g⊝f] (⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ))
                     (⟦ t ⟧ ((v ⟦⊕⟧ dv ⟦⊕⟧ (⟦derive⟧ (v ⟦⊕⟧ dv))) •
                       update ρ {consistency})))) ⟩
         ⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ) ⟦⊕⟧
          (⟦ t ⟧ ((v ⟦⊕⟧ dv ⟦⊕⟧ (⟦derive⟧ (v ⟦⊕⟧ dv))) •
                  update ρ {consistency})
           ⟦⊝⟧
           ⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ))
      ≡⟨ f⊕[g⊝f]=g (⟦ t ⟧ ((v ⟦⊕⟧ dv) • ⟦ Γ≼ΔΓ ⟧ ρ))
                   (⟦ t ⟧ ((v ⟦⊕⟧ dv ⟦⊕⟧ (⟦derive⟧ (v ⟦⊕⟧ dv))) •
                          update ρ {consistency})) ⟩
        ⟦ t ⟧ ((v ⟦⊕⟧ dv ⟦⊕⟧ (⟦derive⟧ (v ⟦⊕⟧ dv))) •
                  update ρ {consistency})
      ≡⟨ cong ⟦ t ⟧ (cong₂ _•_ (f⊕Δf=f (v ⟦⊕⟧ dv)) refl) ⟩
        ⟦ t ⟧ ((v ⟦⊕⟧ dv) • update ρ {consistency})
      ≡⟨ sym (f⊕[g⊝f]=g (⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ))
                        (⟦ t ⟧ ((v ⟦⊕⟧ dv) • update ρ {consistency}))) ⟩
        ⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ) ⟦⊕⟧
          (⟦ t ⟧ ((v ⟦⊕⟧ dv) • update ρ {consistency})
           ⟦⊝⟧
           ⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ))
      ≡⟨ sym (extract-Δequiv
           (correctness-of-derive
             ((dv • v • ρ))
             {dρ=dv•v•dρ₀ R[v,dv] consistency}
             t)
           (⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ))
           (validity-of-derive
             (dv • v • ρ) {dρ=dv•v•dρ₀ R[v,dv] consistency}
             t)
           (R[f,g⊝f] (⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ))
                     (⟦ t ⟧ ((v ⟦⊕⟧ dv) • update ρ {consistency})))) ⟩
        ⟦ t ⟧ (v • ⟦ Γ≼ΔΓ ⟧ ρ) ⟦⊕⟧ ⟦ derive t ⟧ (dv • v • ρ)
      ∎)
  where open ≡-Reasoning

validity-of-derive ρ {consistency} (app {τ₁} {τ₂} t₁ t₂)
  = R[⟦t₁t₂⟧,⟦Δ[t₁t₂]⟧]
  where
    open ≡-Reasoning
    v₁ : ⟦ τ₁ ⇒ τ₂ ⟧
    v₁ = ⟦ t₁ ⟧ (ignore ρ)
    v₂ : ⟦ τ₁ ⟧
    v₂ = ⟦ weaken Γ≼ΔΓ t₂ ⟧ ρ

    dv₁ : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧
    dv₁ = ⟦ derive t₁ ⟧ ρ
    dv₂ : ⟦ Δ-Type τ₁ ⟧
    dv₂ = ⟦ derive t₂ ⟧ ρ

    v₁′ : ⟦ τ₁ ⇒ τ₂ ⟧
    v₁′ = ⟦ t₁ ⟧ (update ρ {consistency})
    v₂′ : ⟦ τ₁ ⟧
    v₂′ = ⟦ t₂ ⟧ (update ρ {consistency})

    v₂=old-v₂ : v₂ ≡ ⟦ t₂ ⟧ (ignore ρ)
    v₂=old-v₂ = weaken-sound {subctx = Γ≼ΔΓ} t₂ ρ

    valid-dv₁ : valid-Δ v₁ dv₁
    valid-dv₁ = validity-of-derive ρ {consistency} t₁
  
    valid-dv₂ : valid-Δ v₂ dv₂
    valid-dv₂ rewrite v₂=old-v₂ =
      validity-of-derive ρ {consistency} t₂

    R[v₁v₂,dv₁v₂dv₂] : valid-Δ (v₁ v₂) (dv₁ v₂ dv₂)
    R[v₁v₂,dv₁v₂dv₂] = proj₁ (valid-dv₁ v₂ dv₂ valid-dv₂)

    ⟦t₁t₂⟧=v₁v₂ : ⟦ app t₁ t₂ ⟧ (ignore ρ) ≡ v₁ v₂
    ⟦t₁t₂⟧=v₁v₂ rewrite (sym v₂=old-v₂) = refl

    ⟦Δ[t₁t₂]⟧=dv₁v₂dv₂ : ⟦ derive (app t₁ t₂) ⟧ ρ ≡ dv₁ v₂ dv₂
    ⟦Δ[t₁t₂]⟧=dv₁v₂dv₂ = refl

    R[⟦t₁t₂⟧,dv₁v₂dv₂] : valid-Δ (⟦ app t₁ t₂ ⟧ (ignore ρ)) (dv₁ v₂ dv₂)
    R[⟦t₁t₂⟧,dv₁v₂dv₂] rewrite ⟦t₁t₂⟧=v₁v₂ = R[v₁v₂,dv₁v₂dv₂]

    -- What I want to write:
    {-
        R[⟦t₁t₂⟧,⟦Δ[t₁t₂]⟧] :
          valid-Δ (⟦ app t₁ t₂ ⟧ (ignore ρ)) (⟦ derive (app t₁ t₂) ⟧ ρ)
        R[⟦t₁t₂⟧,⟦Δ[t₁t₂]⟧] rewrite ⟦Δ[t₁t₂]⟧=dv₁v₂dv₂ = R[⟦t₁t₂⟧,dv₁v₂dv₂]
    -}

    -- What I have to write:

    R : {τ : Type} → {v : ⟦ τ ⟧} → {dv₁ dv₂ : ⟦ Δ-Type τ ⟧} →
        dv₁ ≡ dv₂ → valid-Δ v dv₁ → valid-Δ v dv₂

    R {ints} dv₁=dv₂ refl = cong₂ (λ f x → f x) dv₁=dv₂ refl

    R {bags} dv₁=dv₂ _ = {!!}

    --R {τ₁ ⇒ τ₂} dv₁=dv₂ valid-dv₁ rewrite dv₁=dv₂ = {!valid-dv₁!}
    R {τ₁ ⇒ τ₂} {v} {dv₁} {dv₂} dv₁=dv₂ valid-dv₁ =
      λ s ds R[s,ds] →
        R {τ₂} {v s} {dv₁ s ds} {dv₂ s ds}
           (cong₂ (λ f x → f x)
                  (cong₂ (λ f x → f x) dv₁=dv₂ refl) refl)
           (proj₁ (valid-dv₁ s ds R[s,ds]))
        ,
        (begin
          v (s ⟦⊕⟧ ds) ⟦⊕⟧ dv₂ (s ⟦⊕⟧ ds) (⟦derive⟧ (s ⟦⊕⟧ ds))
        ≡⟨ cong₂ _⟦⊕⟧_
                 {x = v (s ⟦⊕⟧ ds)} refl
                 (cong₂ (λ f x → f x)
                        (cong₂ (λ f x → f x) (sym dv₁=dv₂) refl) refl) ⟩
          v (s ⟦⊕⟧ ds) ⟦⊕⟧ dv₁ (s ⟦⊕⟧ ds) (⟦derive⟧ (s ⟦⊕⟧ ds))
        ≡⟨ sym (proj₂ (valid-dv₁
               (s ⟦⊕⟧ ds)
               (⟦derive⟧ (s ⟦⊕⟧ ds))
               (R[f,Δf] (s ⟦⊕⟧ ds)))) ⟩
          (v ⟦⊕⟧ dv₁) (s ⟦⊕⟧ ds ⟦⊕⟧ ⟦derive⟧ (s ⟦⊕⟧ ds))
        ≡⟨ cong (v ⟦⊕⟧ dv₁) (f⊕Δf=f (s ⟦⊕⟧ ds)) ⟩
          (v ⟦⊕⟧ dv₁) (s ⟦⊕⟧ ds)
        ≡⟨ proj₂ (valid-dv₁ s ds R[s,ds]) ⟩
          v s ⟦⊕⟧ dv₁ s ds
        ≡⟨ cong₂ _⟦⊕⟧_
                 {x = v s} refl
                 (cong₂ (λ f x → f x)
                        (cong₂ (λ f x → f x) dv₁=dv₂ refl) refl) ⟩
          v s ⟦⊕⟧ dv₂ s ds
        ∎) where open ≡-Reasoning

    R[⟦t₁t₂⟧,⟦Δ[t₁t₂]⟧] :
      valid-Δ (⟦ app t₁ t₂ ⟧ (ignore ρ)) (⟦ derive (app t₁ t₂) ⟧ ρ)
    R[⟦t₁t₂⟧,⟦Δ[t₁t₂]⟧] = R ⟦Δ[t₁t₂]⟧=dv₁v₂dv₂ R[⟦t₁t₂⟧,dv₁v₂dv₂]

validity-of-derive ρ {consistency} _ = {!!}

correctness-of-derive ρ (var x) = correctness-of-deriveVar ρ x

correctness-of-derive ρ (int n) = ext-Δ (λ _ _ _ → refl)

correctness-of-derive {Γ} {τ₁ ⇒ τ₂}
  ρ {consistency} (abs {.τ₁} {.τ₂} t) =
  ext-Δ {τ₁ ⇒ τ₂}
    (λ f R[f,Δt] R[f,t′⊝t] →
      extensionality {⟦ τ₁ ⟧} {λ _ → ⟦ τ₂ ⟧} (λ x →
        begin
          f x ⟦⊕⟧ ⟦ derive t ⟧ (⟦derive⟧ x • x • ρ)
        ≡⟨ extract-Δequiv
            (correctness-of-derive {τ₁ • Γ} {τ₂}
               (⟦derive⟧ x • x • ρ)
               {dρ=dv•v•dρ₀ (R[f,Δf] x) consistency}
               t)
            (f x)
            (proj₁ (R[f,Δt] x (⟦derive⟧ x) (R[f,Δf] x)))
            (proj₁ (R[f,t′⊝t] x (⟦derive⟧ x) (R[f,Δf] x))) ⟩
          f x
          ⟦⊕⟧
          (⟦ t ⟧ (update (⟦derive⟧ x • x • ρ)
                {dρ=dv•v•dρ₀ (R[f,Δf] x) consistency})
          ⟦⊝⟧ ⟦ t ⟧ (x • ⟦ Γ≼ΔΓ ⟧ ρ))
        ∎
  )) where open ≡-Reasoning

correctness-of-derive ρ {consistency} (app {τ₁} {τ₂} {Γ} t₁ t₂) =
  ext-Δ {τ₂}
  (λ f R[f,Δt] R[f,t′⊝t] →
    begin
      f ⟦⊕⟧ ⟦ derive t₁ ⟧ ρ (⟦ weaken Γ≼ΔΓ t₂ ⟧ ρ) (⟦ derive t₂ ⟧ ρ)
    ≡⟨ extract-Δequiv ext-Δ[t₁t₂] f R[f,Δt] R[f,t′⊝t] ⟩
      f ⟦⊕⟧
        (⟦ t₁ ⟧ (update ρ) (⟦ t₂ ⟧ (update ρ))
         ⟦⊝⟧
         ⟦ t₁ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ) (⟦ t₂ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ)))
    ∎)
  where
    open ≡-Reasoning

    v₁ : ⟦ τ₁ ⇒ τ₂ ⟧
    v₁ = ⟦ t₁ ⟧ (ignore ρ)
    v₂ : ⟦ τ₁ ⟧
    v₂ = ⟦ weaken Γ≼ΔΓ t₂ ⟧ ρ

    dv₁ : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧
    dv₁ = ⟦ derive t₁ ⟧ ρ
    dv₂ : ⟦ Δ-Type τ₁ ⟧
    dv₂ = ⟦ derive t₂ ⟧ ρ

    v₁′ : ⟦ τ₁ ⇒ τ₂ ⟧
    v₁′ = ⟦ t₁ ⟧ (update ρ {consistency})
    v₂′ : ⟦ τ₁ ⟧
    v₂′ = ⟦ t₂ ⟧ (update ρ {consistency})

    v₂=old-v₂ : v₂ ≡ ⟦ t₂ ⟧ (ignore ρ)
    v₂=old-v₂ = weaken-sound {subctx = Γ≼ΔΓ} t₂ ρ

    valid-dv₁ : valid-Δ v₁ dv₁
    valid-dv₁ = validity-of-derive ρ {consistency} t₁
  
    valid-dv₂ : valid-Δ v₂ dv₂
    valid-dv₂ rewrite v₂=old-v₂ =
      validity-of-derive ρ {consistency} t₂

    v₁⊕dv₁=v₁′ : v₁ ⟦⊕⟧ dv₁ ≡ v₁′
    v₁⊕dv₁=v₁′ =
      begin
        v₁ ⟦⊕⟧ dv₁
      ≡⟨ extract-Δequiv
           (correctness-of-derive ρ {consistency} t₁)
           v₁ valid-dv₁ (R[f,g⊝f] v₁ v₁′) ⟩
        v₁ ⟦⊕⟧ (v₁′ ⟦⊝⟧ v₁)
      ≡⟨ f⊕[g⊝f]=g v₁ v₁′ ⟩
        v₁′
      ∎

    -- TODO: remove code duplication.
    v₂⊕dv₂=v₂′ : v₂ ⟦⊕⟧ dv₂ ≡ v₂′
    v₂⊕dv₂=v₂′ rewrite v₂=old-v₂ =
      begin
        old-v₂ ⟦⊕⟧ dv₂
      ≡⟨ extract-Δequiv
           (correctness-of-derive ρ {consistency} t₂)
           old-v₂
           (validity-of-derive ρ {consistency} t₂)
           (R[f,g⊝f] old-v₂ v₂′) ⟩
        old-v₂ ⟦⊕⟧ (v₂′ ⟦⊝⟧ old-v₂)
      ≡⟨ f⊕[g⊝f]=g old-v₂ v₂′ ⟩
        v₂′
      ∎
      where old-v₂ = ⟦ t₂ ⟧ (ignore ρ)

    v₁′v₂′=[v₁⊕dv₁][v₂⊕dv₂] : v₁′ v₂′ ≡ (v₁ ⟦⊕⟧ dv₁) (v₂ ⟦⊕⟧ dv₂)
    v₁′v₂′=[v₁⊕dv₁][v₂⊕dv₂] = sym (cong₂ (λ f x → f x) v₁⊕dv₁=v₁′ v₂⊕dv₂=v₂′)

    [v₁⊕dv₁][v₂⊕dv₂]=v₁v₂⊕dv₁v₂dv₂ :
      (v₁ ⟦⊕⟧ dv₁) (v₂ ⟦⊕⟧ dv₂) ≡ v₁ v₂ ⟦⊕⟧ dv₁ v₂ dv₂
    [v₁⊕dv₁][v₂⊕dv₂]=v₁v₂⊕dv₁v₂dv₂ = proj₂ (valid-dv₁ v₂ dv₂ valid-dv₂)

    v₁′v₂′⊝v₁v₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ :
      v₁′ v₂′ ⟦⊝⟧ v₁ v₂ ≡ v₁ v₂ ⟦⊕⟧ dv₁ v₂ dv₂ ⟦⊝⟧ v₁ v₂
    v₁′v₂′⊝v₁v₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ =
      cong₂ _⟦⊝⟧_
        (trans v₁′v₂′=[v₁⊕dv₁][v₂⊕dv₂] [v₁⊕dv₁][v₂⊕dv₂]=v₁v₂⊕dv₁v₂dv₂)
        refl

    R[v₁v₂,dv₁v₂dv₂] : valid-Δ (v₁ v₂) (dv₁ v₂ dv₂)
    R[v₁v₂,dv₁v₂dv₂] = proj₁ (valid-dv₁ v₂ dv₂ valid-dv₂)

    dv₁v₂dv₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ :
      (dv₁ v₂ dv₂) ≈ (v₁ v₂ ⟦⊕⟧ dv₁ v₂ dv₂ ⟦⊝⟧ v₁ v₂) :Δ τ₂
    dv₁v₂dv₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ =
      df=f⊕df⊝f (v₁ v₂) (dv₁ v₂ dv₂) R[v₁v₂,dv₁v₂dv₂]

    dv₁v₂dv₂=v₁′v₂′⊝v₁v₂ : (dv₁ v₂ dv₂) ≈ (v₁′ v₂′ ⟦⊝⟧ v₁ v₂) :Δ τ₂
    dv₁v₂dv₂=v₁′v₂′⊝v₁v₂ rewrite v₁′v₂′⊝v₁v₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ =
      dv₁v₂dv₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂

    ext-Δ[t₁t₂] :
      (⟦ derive t₁ ⟧ ρ (⟦ weaken Γ≼ΔΓ t₂ ⟧ ρ) (⟦ derive t₂ ⟧ ρ))
      ≈
      (⟦ t₁ ⟧ (update ρ {consistency}) (⟦ t₂ ⟧ (update ρ {consistency}))
      ⟦⊝⟧ ⟦ t₁ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ) (⟦ t₂ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ)))
      :Δ τ₂
    ext-Δ[t₁t₂] rewrite sym v₂=old-v₂ = dv₁v₂dv₂=v₁′v₂′⊝v₁v₂

correctness-of-derive ρ {consistency} _ = {!!}

correctness-on-closed-terms : ∀ {τ₁ τ₂} →
  ∀ (f : Term ∅ (τ₁ ⇒ τ₂)) →
  ∀ (s : Term ∅ τ₁) (ds : Term ∅ (Δ-Type τ₁))
    {R[v,dv] : valid-Δ (⟦ s ⟧ ∅) (⟦ ds ⟧ ∅)} →
    ⟦ f ⟧ ∅ (⟦ s ⟧ ∅ ⟦⊕⟧ ⟦ ds ⟧ ∅)
    ≡
    ⟦ f ⟧ ∅ (⟦ s ⟧ ∅) ⟦⊕⟧ ⟦ derive f ⟧ ∅ (⟦ s ⟧ ∅) (⟦ ds ⟧ ∅)

correctness-on-closed-terms {τ₁} {τ₂} f s ds {R[v,dv]} =
  begin
    h (v ⟦⊕⟧ dv)
  ≡⟨ cong₂ (λ f x → f x)
           (sym (f⊕[g⊝f]=g h h))
           refl ⟩
    (h ⟦⊕⟧ (h ⟦⊝⟧ h)) (v ⟦⊕⟧ dv)
  ≡⟨ cong₂ (λ f x → f x)
      (sym (extract-Δequiv
        (correctness-of-derive ∅ f)
        h
        (validity-of-derive ∅ {dρ=∅} f)
        (R[f,g⊝f] h h)))
      refl ⟩
    (h ⟦⊕⟧ Δh) (v ⟦⊕⟧ dv)
  ≡⟨ proj₂ (validity-of-derive ∅ {dρ=∅} f v dv R[v,dv]) ⟩
    h v ⟦⊕⟧ Δh v dv
  ∎
  where
    open ≡-Reasoning
    h : ⟦ τ₁ ⇒ τ₂ ⟧
    h = ⟦ f ⟧ ∅
    Δh : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧
    Δh = ⟦ derive f ⟧ ∅
    v : ⟦ τ₁ ⟧
    v = ⟦ s ⟧ ∅
    dv : ⟦ Δ-Type τ₁ ⟧
    dv = ⟦ ds ⟧ ∅

-}

