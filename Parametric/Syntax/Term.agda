------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of terms (Fig. 1a and 1b).
------------------------------------------------------------------------

-- The syntax of terms depends on the syntax of simple types
-- (because terms are indexed by types in order to rule out
-- ill-typed terms). But we are in the Parametric.* hierarchy, so
-- we don't know the full syntax of types, only how to lift the
-- syntax of base types into the syntax of simple types. This
-- means that we have to be parametric in the syntax of base
-- types, too.
--
-- In such parametric modules that depend on other parametric
-- modules, we first import our dependencies under a more
-- convenient name.

import Parametric.Syntax.Type as Type

-- Then we start the module proper, with parameters for all
-- extension points of our dependencies. Note that here, the
-- "Structure" naming convenion makes some sense, because we can
-- say that we need some "Type.Structure" in order to define the
-- "Term.Structure".

module Parametric.Syntax.Term
    (Base : Type.Structure)
  where

-- Now inside the module, we can open our dependencies with the
-- parameters for their extension points. Again, here the name
-- "Structure" makes some sense, because we can say that we want
-- to access the "Type.Structure" that is induced by Base.

open Type.Structure Base

-- At this point, we have dealt with the extension points of our
-- dependencies, and we have all the definitions about simple
-- types, contexts, variables, and variable sets in scope that we
-- provided in Parametric.Syntax.Type. Now we can proceed to
-- define our own extension point, following the pattern
-- explained in Parametric.Syntax.Type.

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (_∘_)
open import Data.Unit
open import Data.Sum

-- Our extension point is a set of primitives, indexed by the
-- types of their arguments and their return type. In general, if
-- you're confused about what an extension point means, you might
-- want to open the corresponding module in the Nehemiah
-- hierarchy to see how it is implemented in the example
-- plugin. In this case, that would be the Nehemiah.Syntax.Term
-- module.

Structure : Set₁
Structure = Context → Type → Set

module Structure (Const : Structure) where
  import Base.Data.DependentList as DependentList
  open DependentList public using (∅ ; _•_)
  open DependentList

  -- Declarations of Term and Terms to enable mutual recursion.
  --
  -- Note that terms are indexed by contexts and types. In the
  -- paper, we define the abstract syntax of terms in Fig 1a and
  -- then define a type system in Fig 1b. All lemmas and theorems
  -- then explicitly specify that they only hold for well-typed
  -- terms. Here, we use the indices to define a type that can
  -- only hold well-typed terms in the first place.
  data Term
    (Γ : Context) :
    (τ : Type) → Set

  -- (Terms Γ Σ) represents a list of terms with types from Σ
  -- with free variables bound in Γ.
  Terms : Context → Context → Set
  Terms Γ = DependentList (Term Γ)

  -- (Term Γ τ) represents a term of type τ
  -- with free variables bound in Γ.
  data Term Γ where
    -- constants aka. primitives can only occur fully applied.
    const : ∀ {Σ τ} →
      (c : Const Σ τ) →
      (args : Terms Γ Σ) →
      Term Γ τ
    var : ∀ {τ} →
      (x : Var Γ τ) →
      Term Γ τ
    app : ∀ {σ τ}
      (s : Term Γ (σ ⇒ τ)) →
      (t : Term Γ σ) →
      Term Γ τ
    -- we use de Bruijn indicies, so we don't need binding occurrences.
    abs : ∀ {σ τ}
      (t : Term (σ • Γ) τ) →
      Term Γ (σ ⇒ τ)

  -- Free variables
  FV : ∀ {τ Γ} → Term Γ τ → Vars Γ
  FV-terms : ∀ {Σ Γ} → Terms Γ Σ → Vars Γ

  FV (const ι ts) = FV-terms ts
  FV (var x) = singleton x
  FV (abs t) = tail (FV t)
  FV (app s t) = FV s ∪ FV t

  FV-terms ∅ = none
  FV-terms (t • ts) = FV t ∪ FV-terms ts

  closed? : ∀ {τ Γ} → (t : Term Γ τ) → (FV t ≡ none) ⊎ ⊤
  closed? t = empty? (FV t)

  -- Weakening

  weaken : ∀ {Γ₁ Γ₂ τ} →
    (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
    Term Γ₁ τ →
    Term Γ₂ τ

  weaken-terms : ∀ {Γ₁ Γ₂ Σ} →
    (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
    Terms Γ₁ Σ →
    Terms Γ₂ Σ

  weaken Γ₁≼Γ₂ (const c ts) = const c (weaken-terms Γ₁≼Γ₂ ts)
  weaken Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
  weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
  weaken Γ₁≼Γ₂ (abs {σ} t) = abs (weaken (keep σ • Γ₁≼Γ₂) t)

  weaken-terms Γ₁≼Γ₂ ∅ = ∅
  weaken-terms Γ₁≼Γ₂ (t • ts) = weaken Γ₁≼Γ₂ t • weaken-terms Γ₁≼Γ₂ ts

  -- Specialized weakening
  weaken₁ : ∀ {Γ σ τ} →
    Term Γ τ → Term (σ • Γ) τ
  weaken₁ t = weaken (drop _ • ≼-refl) t

  weaken₂ : ∀ {Γ α β τ} →
    Term Γ τ → Term (α • β • Γ) τ
  weaken₂ t = weaken (drop _ • drop _ • ≼-refl) t

  weaken₃ : ∀ {Γ α β γ τ} →
    Term Γ τ → Term (α • β • γ • Γ) τ
  weaken₃ t = weaken (drop _ • drop _ • drop _ • ≼-refl) t

  -- Shorthands for nested applications
  app₂ : ∀ {Γ α β γ} →
    Term Γ (α ⇒ β ⇒ γ) →
    Term Γ α → Term Γ β → Term Γ γ
  app₂ f x = app (app f x)

  app₃ : ∀ {Γ α β γ δ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ
  app₃ f x = app₂ (app f x)

  app₄ : ∀ {Γ α β γ δ ε} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε
  app₄ f x = app₃ (app f x)

  app₅ : ∀ {Γ α β γ δ ε ζ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ
  app₅ f x = app₄ (app f x)

  app₆ : ∀ {Γ α β γ δ ε ζ η} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ ⇒ η) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ → Term Γ η
  app₆ f x = app₅ (app f x)

  UncurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
  UncurriedTermConstructor Γ Σ τ = Terms Γ Σ → Term Γ τ

  uncurriedConst : ∀ {Σ τ} → Const Σ τ → ∀ {Γ} → UncurriedTermConstructor Γ Σ τ
  uncurriedConst constant = const constant

  CurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
  CurriedTermConstructor Γ ∅ τ′ = Term Γ τ′
  CurriedTermConstructor Γ (τ • Σ) τ′ = Term Γ τ → CurriedTermConstructor Γ Σ τ′

  curryTermConstructor : ∀ {Σ Γ τ} → UncurriedTermConstructor Γ Σ τ → CurriedTermConstructor Γ Σ τ
  curryTermConstructor {∅} k = k ∅
  curryTermConstructor {τ • Σ} k = λ t → curryTermConstructor (λ ts → k (t • ts))

  curriedConst : ∀ {Σ τ} → Const Σ τ → ∀ {Γ} → CurriedTermConstructor Γ Σ τ
  curriedConst constant = curryTermConstructor (uncurriedConst constant)


  -- HOAS-like smart constructors for lambdas, for different arities.

  -- We could also write this:
  module NamespaceForBadAbs₁ where
    abs₁′ :
      ∀ {Γ τ₁ τ} →
        (Term (τ₁ • Γ) τ₁ → Term (τ₁ • Γ) τ) →
        (Term Γ (τ₁ ⇒ τ))
    abs₁′ {Γ} {τ₁} = λ f → abs (f (var this))

  -- However, this is less general, and it is harder to reuse. In particular,
  -- this cannot be used inside abs₂, ..., abs₆.

  -- Now, let's write other variants with a loop!
  open import Data.Vec using (_∷_; []; Vec; foldr; [_])
  open import Data.Nat
  module AbsNHelpers where
    open import Function
    hoasArgType : ∀ {n} → Context → Type → Vec Type n → Set
    hoasArgType Γ τ = foldr _ (λ a b → a → b) (Term Γ τ) ∘ Data.Vec.map (Term Γ)
    -- That is,
    --hoasArgType Γ τ [] = Term Γ τ
    --hoasArgType Γ τ (τ₀ ∷ τs) = Term Γ τ₀ → hoasArgType Γ τ τs

    hoasResType : ∀ {n} → Type → Vec Type n → Type
    hoasResType τ = foldr _ _⇒_ τ

    absNType : {n : ℕ} → Vec _ n → Set
    absNType τs = ∀ {Γ τ} →
      (f : ∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → hoasArgType Γ′ τ τs) →
      Term Γ (hoasResType τ τs)

    -- A better type for absN but a mess to use due to the proofs (which aren't synthesized, even though maybe they should be?)
    -- absN : (n : ℕ) → {_ : n > 0} → absNType n
    -- XXX See "how to keep your neighbours in order" for tricks.

    -- Please the termination checker by keeping this case separate.
    absNBase : ∀ {τ₁} → absNType [ τ₁ ]
    absNBase {τ₁} f = abs (f {Γ≼Γ′ = drop τ₁ • ≼-refl} (var this))
    -- Otherwise, the recursive step of absN would invoke absN twice, and the
    -- termination checker does not figure out that the calls are in fact
    -- terminating.

    -- What I'd like to write, avoiding the need for absNBase, but can't because of the termination checker.
    {-
    absN {zero}  (τ₁ ∷ []) f = abs (f {Γ≼Γ′ = drop τ₁ • ≼-refl} (var this))
    absN {suc n} (τ₁ ∷ τ₂ ∷ τs) f =
      absN (τ₁ ∷ []) (λ {_} {Γ≼Γ′} x₁ →
        absN {n} (τ₂ ∷ τs) (λ {Γ′₁} {Γ′≼Γ′₁} →
          f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))
    -}
    --What I have to write instead:

    absN : {n : ℕ} → (τs : Vec _ n) → absNType τs
    absN {zero}  [] f = f {Γ≼Γ′ = ≼-refl}
    absN {suc n} (τ₁ ∷ τs) f =
      absNBase (λ {_} {Γ≼Γ′} x₁ →
        absN {n} (τs) (λ {Γ′₁} {Γ′≼Γ′₁} →
          f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))

    -- Using a similar trick, we can declare absV which takes the N implicit
    -- type arguments individually, collects them and passes them on to absN.
    -- This is inspired by what's shown in the Agda 2.4.0 release notes, and
    -- relies critically on support for varying arity. To collect them, we need
    -- to use an accumulator argument.

    absVType : ∀ n {m} (τs : Vec Type m) → Set
    absVType 0       τs = absNType τs
    absVType (suc n) τs = {τᵢ : Type} → absVType n (τᵢ ∷ τs)

    absVAux : ∀ {m} → (τs : Vec Type m) → ∀ n → absVType n τs
    absVAux τs zero    = absN τs
    absVAux τs (suc n) = λ {τᵢ} → absVAux (τᵢ ∷ τs) n

    absV = absVAux []

  open AbsNHelpers using (absV) public

  -- Declare abs₁ .. abs₆ wrappers for more convenient use, allowing implicit
  -- type arguments to be synthesized. Somehow, Agda does not manage to
  -- synthesize τs by unification.
  -- Implicit arguments are reversed when assembling the list, but that's no real problem.

  abs₁ = absV 1
  abs₂ = absV 2
  abs₃ = absV 3
  abs₄ = absV 4
  abs₅ = absV 5
  abs₆ = absV 6

  {-
  Example types:
  abs₁:
    {τ₁ : Type} {Γ : Context} {τ : Type} →
        ({Γ′ : Context} {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ) →
        Term Γ (τ₁ Type.Structure.⇒ τ)

  abs₂:
    {τ₁ : Type} {τ₁ = τ₂ : Type} {Γ : Context} {τ : Type} →
        ({Γ′ : Context} {Γ≼Γ′ : Γ ≼ Γ′} →
         Term Γ′ τ₂ → Term Γ′ τ₁ → Term Γ′ τ) →
        Term Γ (τ₂ Type.Structure.⇒ τ₁ Type.Structure.⇒ τ)

  -}
