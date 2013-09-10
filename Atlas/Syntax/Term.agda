module Atlas.Syntax.Term where

-- Base types of the calculus Atlas
-- to be used with Plotkin-style language description
--
-- Atlas supports maps with neutral elements. The change type to
-- `Map κ ι` is `Map κ Δι`, where Δι is the change type of the
-- ground type ι. Such a change to maps can support insertions
-- and deletions as well: Inserting `k -> v` means mapping `k` to
-- the change from the neutral element to `v`, and deleting
-- `k -> v` means mapping `k` to the change from `v` to the
-- neutral element.

open import Atlas.Syntax.Type
open import Base.Syntax.Context Type

data Const : Context → Type → Set where
  true  : Const
    ∅
    (base Bool)

  false : Const
    ∅
    (base Bool)

  xor   : Const
    (base Bool • base Bool • ∅)
    (base Bool)

  empty  : ∀ {κ ι : Base} → Const
    ∅
    (base (Map κ ι))

  -- `update key val my-map` would
  -- - insert if `key` is not present in `my-map`
  -- - delete if `val` is the neutral element
  -- - make an update otherwise

-- Why do we only allow for base types here? We shouldn't.

  update : ∀ {κ ι : Base} → Const
    (base κ • base ι • base (Map κ ι) • ∅)
    (base (Map κ ι))

  lookup : ∀ {κ ι : Base} → Const
    (base κ • base (Map κ ι) • ∅)
    (base ι)

  -- Model of zip = Haskell Data.List.zipWith
  --
  -- zipWith :: (a → b → c) → [a] → [b] → [c]
  --
  -- Behavioral difference: all key-value pairs present
  -- in *either* (m₁ : Map κ a) *or* (m₂ : Map κ b) will
  -- be iterated over. Neutral element of type `a` or `b`
  -- will be supplied if the key is missing in the
  -- corresponding map.

  zip    : ∀ {κ a b c : Base} → Const
    ((base κ ⇒ base a ⇒ base b ⇒ base c) •
     base (Map κ a) • base (Map κ b) • ∅)
    (base (Map κ c))

  -- Model of fold = Haskell Data.Map.foldWithKey
  --
  -- foldWithKey :: (k → a → b → b) → b → Map k a → b

  fold   : ∀ {κ a b : Base} → Const
   ((base κ ⇒ base a ⇒ base b ⇒ base b) •
    base b • base (Map κ a) • ∅)
   (base b)

open import Parametric.Syntax.Term Const public

-- Shorthands of constants
true! : ∀ {Γ} →
  Term Γ (base Bool)
true! = curriedConst true

false! : ∀ {Γ} →
  Term Γ (base Bool)
false! = curriedConst false

xor! : ∀ {Γ} →
  Term Γ (base Bool) → Term Γ (base Bool) →
  Term Γ (base Bool)
xor! = curriedConst xor

empty! : ∀ {κ ι Γ} →
  Term Γ (base (Map κ ι))
empty! = curriedConst empty

update! : ∀ {κ ι Γ} →
  Term Γ (base κ) → Term Γ (base ι) →
  Term Γ (base (Map κ ι)) →
  Term Γ (base (Map κ ι))
update! = curriedConst update

lookup! : ∀ {κ ι Γ} →
  Term Γ (base κ) → Term Γ (base (Map κ ι)) →
  Term Γ (base ι)
lookup! = curriedConst lookup

zip! : ∀ {κ a b c Γ} →
  Term Γ (base κ ⇒ base a ⇒ base b ⇒ base c) →
  Term Γ (base (Map κ a)) → Term Γ (base (Map κ b)) →
  Term Γ (base (Map κ c))
zip! = curriedConst zip

fold! : ∀ {κ a b Γ} →
  Term Γ (base κ ⇒ base a ⇒ base b ⇒ base b) →
  Term Γ (base b) → Term Γ (base (Map κ a)) →
  Term Γ (base b)
fold! = curriedConst fold

-- Every base type has a neutral element.

neutral : ∀ {ι : Base} → Const ∅ (base ι)
neutral {Bool} = false
neutral {Map κ ι} = empty {κ} {ι}

neutral-term : ∀ {ι Γ} → Term Γ (base ι)
neutral-term {Bool}   = curriedConst (neutral {Bool})
neutral-term {Map κ ι} = curriedConst (neutral {Map κ ι})

-- Nonfunctional products can be encoded.
-- The incremental behavior of products thus encoded is weird:
-- Δ(α × β) = α × Δβ
Pair : Base → Base → Base
Pair α β = Map α β

pair : ∀ {α β Γ} →
  Term Γ (base α) → Term Γ (base β) →
  Term Γ (base (Pair α β))
pair s t = update! s t empty!

pair-term : ∀ {α β Γ} →
  Term Γ (base α ⇒ base β ⇒ base (Pair α β))
pair-term = abs (abs (pair (var (that this)) (var this)))

uncurry : ∀ {α β γ Γ} →
  Term Γ (base α ⇒ base β ⇒ base γ) →
  Term Γ (base (Pair α β)) →
  Term Γ (base γ)
uncurry f p =
  let
    a = var (that (that this))
    b = var (that this)
    g = abs (abs (abs (app₂ (weaken₃ f) a b)))
  in
    fold! g neutral-term p

zip-pair : ∀ {κ a b Γ} →
  Term Γ (base (Map κ a)) → Term Γ (base (Map κ b)) →
  Term Γ (base (Map κ (Pair a b)))
zip-pair = zip! (abs pair-term)

-- Shorthand for 4-way zip
zip4! : ∀ {κ a b c d e Γ} →
  let
    t:_ = λ ι → Term Γ (base ι)
  in
    Term Γ
      (base κ ⇒ base a ⇒ base b ⇒ base c ⇒ base d ⇒ base e) →
    t: Map κ a → t: Map κ b → t: Map κ c → t: Map κ d → t: Map κ e

-- zip₄ f m₁ m₂ m₃ m₄ =
-- zip (λ k p₁₂ p₃₄ → uncurry (λ v₁ v₂ → uncurry (λ v₃ v₄ →
--       f k v₁ v₂ v₃ v₄)
--       p₃₄) p₁₂)
--     (zip-pair m₁ m₂) (zip-pair m₃ m₄)

zip4! f m₁ m₂ m₃ m₄ =
  let
    f′ = weaken₃ (weaken₃ (weaken₁ f))
    k = var (that (that (that (that (that (that this))))))
    p₁₂ = var (that this)
    p₃₄ = var (that (that this))
    v₁ = var (that (that (that this)))
    v₂ = var (that (that this))
    v₃ = var (that this)
    v₄ = var this
    g = abs (abs (abs (uncurry (abs (abs (uncurry (abs (abs
        (app₅ f′ k v₁ v₂ v₃ v₄)))
        p₃₄))) p₁₂)))
  in
    zip! g (zip-pair m₁ m₂) (zip-pair m₃ m₄)
