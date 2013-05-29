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
1. Replace ℕ by ℤ
2. Introduce addition
3. Add MapBags and map


Checklist of stuff to add when adding syntactic constructs

- weaken
- ⟦_⟧Term
- weaken-sound
- derive (symbolic derivation)
- validity-of-derive
- correctness-of-derive

-}

module MapBag where

open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)

open import Relation.Binary.PropositionalEquality

open import Level using
  (zero ; Level ; suc)
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

postulate extensionality : Extensionality zero zero

data Type : Set where
  nats : Type
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

⟨∅⟩ : ∅ ≡ ∅
⟨∅⟩ = refl

_⟨•⟩_ : ∀ {τ₁ τ₂ Γ₁ Γ₂} → τ₁ ≡ τ₂ → Γ₁ ≡ Γ₂ → τ₁ • Γ₁ ≡ τ₂ • Γ₂
_⟨•⟩_ = cong₂ _•_

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

data Term : Context -> Type -> Set where
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ
  nat : ∀ {Γ} → (n : ℕ) → Term Γ nats
  abs : ∀ {τ₁ τ₂ Γ} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂ Γ} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁)
                   → Term Γ τ₂

  -- Change to nats = replacement Church pairs
  -- 3 -> 5 ::= λf. f 3 5

infix 8 _≼_

data _≼_ : (Γ₁ Γ₂ : Context) → Set where
  ∅≼∅ : ∅ ≼ ∅
  keep_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → τ • Γ₁ ≼ τ • Γ₂
  drop_•_ : ∀ {Γ₁ Γ₂} → (τ : Type) → Γ₁ ≼ Γ₂ → Γ₁ ≼ τ • Γ₂

≼-reflexivity : Reflexive _≼_
≼-reflexivity {∅} = ∅≼∅
≼-reflexivity {τ • x} = keep τ • ≼-reflexivity

≼-reflexive : ∀ {Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₁ ≼ Γ₂
≼-reflexive refl = ≼-reflexivity

≼-transitive : Transitive _≼_
≼-transitive ∅≼∅ rel1 = rel1
≼-transitive (keep τ • rel0) (keep .τ • rel1) =
  keep τ • ≼-transitive rel0 rel1
≼-transitive (keep τ • rel0) (drop τ₁ • rel1) =
  drop τ₁ • ≼-transitive (keep τ • rel0) rel1
≼-transitive (drop τ • rel0) (keep .τ • rel1) =
  drop τ • ≼-transitive rel0 rel1
≼-transitive (drop τ • rel0) (drop τ₁ • rel1) =
  drop τ₁ • ≼-transitive (drop τ • rel0) rel1

≼-isPreorder : IsPreorder _≡_ _≼_
≼-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive = ≼-reflexive
  ; trans = ≼-transitive
  }

≼-preorder : Preorder _ _ _
≼-preorder = record
  { Carrier = Context
  ; _≈_ = _≡_
  ; isPreorder = ≼-isPreorder
  }

module ≼-reasoning where
  open import Relation.Binary.PreorderReasoning ≼-preorder public
    renaming
      ( _≈⟨_⟩_ to _≡⟨_⟩_
      ; _∼⟨_⟩_ to _≼⟨_⟩_
      ; _≈⟨⟩_ to _≡⟨⟩_
      )

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

record Meaning (Syntax : Set) {ℓ : Level} : Set (suc ℓ) where
  constructor
    meaning
  field
    {Semantics} : Set ℓ
    ⟨_⟩⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public
  renaming (⟨_⟩⟦_⟧ to ⟦_⟧)

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ nats ⟧Type = ℕ

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
⟦ nat n ⟧Term ρ = n

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

≡-app : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
≡-app = cong₂ (λ x y → x y)

weaken-sound : ∀ {Γ₁ Γ₂ τ} {subctx : Γ₁ ≼ Γ₂} (t : Term Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken subctx t ⟧ ρ ≡ ⟦ t ⟧ (⟦ subctx ⟧ ρ)
weaken-sound (abs t) ρ = extensionality (λ v → weaken-sound t (v • ρ))
weaken-sound (app t₁ t₂) ρ = ≡-app (weaken-sound t₁ ρ) (weaken-sound t₂ ρ)
weaken-sound {subctx = subctx} (var x) ρ = weakenVar-sound subctx x ρ
weaken-sound (nat n) ρ = refl

-- Changes to ℕ are replacement Church pairs. The only arguments
-- of conern are `fst` and `snd`, so the Church pairs don't have
-- to be polymorphic.

Δ-Type : Type → Type
Δ-Type nats = (nats ⇒ nats ⇒ nats) ⇒ nats
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

⟦fst⟧ : ℕ → ℕ → ℕ
⟦snd⟧ : ℕ → ℕ → ℕ

⟦derive⟧ {τ₁ ⇒ τ₂} f = λ v dv → f (v ⟦⊕⟧ dv) ⟦⊝⟧ f v
⟦derive⟧ {nats} n = λ f → f n n

_⟦⊝⟧_ {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → f₁ (v ⟦⊕⟧ dv) ⟦⊝⟧ f₂ v
_⟦⊝⟧_ {nats} m n = λ f → f n m
-- m ⟦⊝⟧ n ::= replace n by m

_⟦⊕⟧_ {τ₁ ⇒ τ₂} f df = λ v → f v ⟦⊕⟧ df v (⟦derive⟧ v)
_⟦⊕⟧_ {nats} n dn = dn ⟦snd⟧

⟦fst⟧ m n = m
⟦snd⟧ m n = n

-- Strong validity!
data ⟦ValidΔ⟧ : {τ : Type} → (v : ⟦ τ ⟧) → (dv : ⟦ Δ-Type τ ⟧) → Set where
  -- Following Pierce's case names `T-Var`, `T-Abs`, `T-App`
  -- with Agda's capitalization convention
  -- generalized to the semantic (value) domain
  v-nat : (n : ℕ) → (dn : (ℕ → ℕ → ℕ) → ℕ) →
          n ≡ dn ⟦fst⟧ →
          ⟦ValidΔ⟧ n dn

  v-fun : {τ₁ τ₂ : Type} →
          (f : ⟦ τ₁ ⇒ τ₂ ⟧) → (df : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧) →
          -- A strong antecedent: f and df map invalid changes to
          -- valid changes! So long as invalid changes exist,
          -- this is NOT satisfied by
          --
          --      f = ⟦ λ x. x ⟧     = identity
          --     df = ⟦ λ x dx. dx ⟧ = ⟦snd⟧,
          --
          -- negating any hope of ⟦ValidΔ⟧ ⟦ t ⟧ ⟦ derive t ⟧.
          (∀ {s ds} → {-ValidΔ s ds →-} ⟦ValidΔ⟧ (f s) (df s ds)) →
          (∀ {s ds} → (f ⟦⊕⟧ df) (s ⟦⊕⟧ ds) ≡ (f s ⟦⊕⟧ df s ds)) →
          ⟦ValidΔ⟧ f df

absurdity-of-0=1 : 0 ≡ 1 → (∀ {A : Set} → A)
absurdity-of-0=1 ()

it-is-absurd-that : ⟦ValidΔ⟧ {nats} 0 (λ f → f 1 1) → (∀ {A : Set} → A)
it-is-absurd-that (v-nat .0 .(λ f → f 1 1) 0=1) = absurdity-of-0=1 0=1

-- If (λ x dx → dx) is a ⟦ValidΔ⟧ to (λ x → x),
-- then impossible is nothing.
no-way : ⟦ValidΔ⟧ {nats ⇒ nats} (λ x → x) (λ x dx → dx) →
         (∀ {A : Set} → A)
no-way (v-fun .(λ x → x) .(λ x dx → dx) validity correctness) =
  it-is-absurd-that (validity {0} {λ f → f 1 1})

-- Cool lemmas

f⟦⊝⟧f=⟦deriv⟧f : ∀ {τ : Type} (f : ⟦ τ ⟧) → f ⟦⊝⟧ f ≡ ⟦derive⟧ f
f⟦⊝⟧f=⟦deriv⟧f {nats} f = refl
f⟦⊝⟧f=⟦deriv⟧f {τ₁ ⇒ τ₂} f = refl

f⊕[g⊝f]=g : ∀ {τ : Type} (f g : ⟦ τ ⟧) → f ⟦⊕⟧ (g ⟦⊝⟧ f) ≡ g

f⊕Δf=f : ∀ {τ : Type} (f : ⟦ τ ⟧) → f ⟦⊕⟧ (⟦derive⟧ f) ≡ f

f⊕[g⊝f]=g {nats} m n = refl
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

f⊕Δf=f {nats} n = refl
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
valid-Δ {nats} n dn = n ≡ dn ⟦fst⟧
valid-Δ {τ₁ ⇒ τ₂} f df =
  ∀ (s : ⟦ τ₁ ⟧) (ds : ⟦ Δ-Type τ₁ ⟧) (R[s,ds] : valid-Δ s ds) →
    valid-Δ (f s) (df s ds) ×              -- (valid-Δ:1)
    (f ⟦⊕⟧ df) (s ⟦⊕⟧ ds) ≡ f s ⟦⊕⟧ df s ds -- (valid-Δ:2)

R[f,g⊝f] : ∀ {τ} (f g : ⟦ τ ⟧) → valid-Δ {τ} f (g ⟦⊝⟧ f)
R[f,g⊝f] {nats} m n = refl
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
derive (nat n) = abs (app (app (var this) (nat n)) (nat n))

-- derive(x) = dx
derive (var x) = var (deriveVar x)

-- derive(λx. t) = λx. λdx. derive(t)
derive (abs t) = abs (abs (derive t))

-- derive(f s) = derive(f) s derive(s)
derive (app f s) = app (app (derive f) (weaken Γ≼ΔΓ s)) (derive s)

-- Extensional equivalence for changes
data as-Δ_is_ext-equiv-to_ :
  ∀ (τ : Type) → (df : ⟦ Δ-Type τ ⟧) → (dg : ⟦ Δ-Type τ ⟧) → Set where
  ext-Δ : ∀ {τ : Type} {df dg : ⟦ Δ-Type τ ⟧} →
          (∀ (f : ⟦ τ ⟧) → valid-Δ f df → valid-Δ f dg →
             (f ⟦⊕⟧ df) ≡ (f ⟦⊕⟧ dg)) →
          as-Δ τ is df ext-equiv-to dg

infix 3 as-Δ_is_ext-equiv-to_

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
    as-Δ τ is df ext-equiv-to dg →
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
    valid-Δ f df → as-Δ τ is df ext-equiv-to f ⟦⊕⟧ df ⟦⊝⟧ f

-- Case nat: this REFL is more obvious to Agda than to a human.
df=f⊕df⊝f {nats} n dn valid-f-df =
  ext-Δ (λ m valid-m-dn valid-rhs → refl)

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
  as-Δ τ is
  ⟦ deriveVar x ⟧ ρ
  ext-equiv-to
  ⟦ x ⟧ (update ρ {consistency}) ⟦⊝⟧ ⟦ x ⟧ (ignore ρ)

correctness-of-deriveVar {τ • Γ₀} {.τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ {.τ} {.v} {.dv} {.Γ₀} {.ρ} R[v,dv] _}
  this = df=f⊕df⊝f {τ} v dv R[v,dv]

correctness-of-deriveVar {τ₀ • Γ₀} {τ}
  (dv • v • ρ) {dρ=dv•v•dρ₀ {.τ₀} {.v} {.dv} {.Γ₀} {.ρ} R[v,dv] _}
  (that x) = correctness-of-deriveVar ρ x



correctness-of-derive : ∀ {Γ τ} →
  ∀ (ρ : ⟦ Δ-Context Γ ⟧) {consistency : Consistent-Δenv ρ} →
  ∀ (t : Term Γ τ) →
  as-Δ τ is
  ⟦ derive t ⟧ ρ
  ext-equiv-to
  ⟦ t ⟧ (update ρ {consistency}) ⟦⊝⟧ ⟦ t ⟧ (ignore ρ)

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

validity-of-derive ρ (nat n) = refl

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

    R {nats} dv₁=dv₂ refl = cong₂ (λ f x → f x) dv₁=dv₂ refl

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


correctness-of-derive ρ (var x) = correctness-of-deriveVar ρ x

correctness-of-derive ρ (nat n) = ext-Δ (λ _ _ _ → refl)

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
      as-Δ τ₂ is dv₁ v₂ dv₂ ext-equiv-to v₁ v₂ ⟦⊕⟧ dv₁ v₂ dv₂ ⟦⊝⟧ v₁ v₂
    dv₁v₂dv₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ =
      df=f⊕df⊝f (v₁ v₂) (dv₁ v₂ dv₂) R[v₁v₂,dv₁v₂dv₂]

    dv₁v₂dv₂=v₁′v₂′⊝v₁v₂ : as-Δ τ₂ is dv₁ v₂ dv₂ ext-equiv-to v₁′ v₂′ ⟦⊝⟧ v₁ v₂
    dv₁v₂dv₂=v₁′v₂′⊝v₁v₂ rewrite v₁′v₂′⊝v₁v₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂ =
      dv₁v₂dv₂=v₁v₂⊕dv₁v₂dv₂⊝v₁v₂

    ext-Δ[t₁t₂] :
      as-Δ τ₂ is
      ⟦ derive t₁ ⟧ ρ (⟦ weaken Γ≼ΔΓ t₂ ⟧ ρ) (⟦ derive t₂ ⟧ ρ)
      ext-equiv-to
      ⟦ t₁ ⟧ (update ρ {consistency}) (⟦ t₂ ⟧ (update ρ {consistency}))
      ⟦⊝⟧ ⟦ t₁ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ) (⟦ t₂ ⟧ (⟦ Γ≼ΔΓ ⟧ ρ))
    ext-Δ[t₁t₂] rewrite sym v₂=old-v₂ = dv₁v₂dv₂=v₁′v₂′⊝v₁v₂

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

