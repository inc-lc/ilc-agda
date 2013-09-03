module Syntax.Language.Atlas where

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

data Atlas-type : Set where
  Bool : Atlas-type
  Map : (κ : Atlas-type) (ι : Atlas-type) → Atlas-type

open import Syntax.Type.Plotkin Atlas-type

data Atlas-const : Type → Set where
  true  : Atlas-const
    (base Bool)

  false : Atlas-const
    (base Bool)

  xor   : Atlas-const
    (base Bool ⇒ base Bool ⇒ base Bool)

  empty  : ∀ {κ ι : Atlas-type} → Atlas-const
    (base (Map κ ι))

  -- `update key val my-map` would
  -- - insert if `key` is not present in `my-map`
  -- - delete if `val` is the neutral element
  -- - make an update otherwise

  update : ∀ {κ ι : Atlas-type} → Atlas-const
    (base κ ⇒ base ι ⇒ base (Map κ ι) ⇒ base (Map κ ι))

  lookup : ∀ {κ ι : Atlas-type} → Atlas-const
    (base κ ⇒ base (Map κ ι) ⇒ base ι)

  -- Model of zip = Haskell Data.List.zipWith
  --
  -- zipWith :: (a → b → c) → [a] → [b] → [c]
  --
  -- Behavioral difference: all key-value pairs present
  -- in *either* (m₁ : Map κ a) *or* (m₂ : Map κ b) will
  -- be iterated over. Neutral element of type `a` or `b`
  -- will be supplied if the key is missing in the
  -- corresponding map.

  zip    : ∀ {κ a b c : Atlas-type} → Atlas-const
    ((base κ ⇒ base a ⇒ base b ⇒ base c) ⇒
     base (Map κ a) ⇒ base (Map κ b) ⇒ base (Map κ c))

  -- Model of fold = Haskell Data.Map.foldWithKey
  --
  -- foldWithKey :: (k → a → b → b) → b → Map k a → b

  fold   : ∀ {κ a b : Atlas-type} → Atlas-const
   ((base κ ⇒ base a ⇒ base b ⇒ base b) ⇒
    base b ⇒ base (Map κ a) ⇒ base b)

Atlas-Δbase : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δbase Bool = Bool
-- change to a map is change to its values
Atlas-Δbase (Map key val) = (Map key (Atlas-Δbase val))

Atlas-Δtype : Type → Type
Atlas-Δtype = lift-Δtype₀ Atlas-Δbase

open import Syntax.Context {Type}

open import Syntax.Term.Plotkin

Atlas-term : Context → Type → Set
Atlas-term = Term {Atlas-type} {Atlas-const}

-- Shorthands of constants
--
-- There's probably a uniform way to lift constants
-- into term constructors.

true! : ∀ {Γ} →
  Atlas-term Γ (base Bool)
true! = const true

false! : ∀ {Γ} →
  Atlas-term Γ (base Bool)
false! = const false

xor! : ∀ {Γ} →
  Atlas-term Γ (base Bool) → Atlas-term Γ (base Bool) →
  Atlas-term Γ (base Bool)
xor! = app₂ (const xor)

empty! : ∀ {κ ι Γ} →
  Atlas-term Γ (base (Map κ ι))
empty! = const empty

update! : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base ι) →
  Atlas-term Γ (base (Map κ ι)) →
  Atlas-term Γ (base (Map κ ι))
update! = app₃ (const update)

lookup! : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base (Map κ ι)) →
  Atlas-term Γ (base ι)
lookup! = app₂ (const lookup)

zip! : ∀ {κ a b c Γ} →
  Atlas-term Γ (base κ ⇒ base a ⇒ base b ⇒ base c) →
  Atlas-term Γ (base (Map κ a)) → Atlas-term Γ (base (Map κ b)) →
  Atlas-term Γ (base (Map κ c))
zip! = app₃ (const zip)

fold! : ∀ {κ a b Γ} →
  Atlas-term Γ (base κ ⇒ base a ⇒ base b ⇒ base b) →
  Atlas-term Γ (base b) → Atlas-term Γ (base (Map κ a)) →
  Atlas-term Γ (base b)
fold! = app₃ (const fold)

-- Every base type has a known nil-change.
-- The nil-change of ι is also the neutral element of Map κ Δι.

neutral : ∀ {ι : Atlas-type} → Atlas-const (base ι)
neutral {Bool} = false
neutral {Map κ ι} = empty {κ} {ι}

neutral-term : ∀ {ι Γ} → Atlas-term Γ (base ι)
neutral-term {Bool}   = const (neutral {Bool})
neutral-term {Map κ ι} = const (neutral {Map κ ι})

nil-const : ∀ {ι : Atlas-type} → Atlas-const (base (Atlas-Δbase ι))
nil-const {ι} = neutral {Atlas-Δbase ι}

nil-term : ∀ {ι Γ} → Atlas-term Γ (base (Atlas-Δbase ι))
nil-term {Bool}   = const (nil-const {Bool})
nil-term {Map κ ι} = const (nil-const {Map κ ι})

-- Nonfunctional products can be encoded.
-- The incremental behavior of products thus encoded is weird:
-- Δ(α × β) = α × Δβ
Pair : Atlas-type → Atlas-type → Atlas-type
Pair α β = Map α β

pair : ∀ {α β Γ} →
  Atlas-term Γ (base α) → Atlas-term Γ (base β) →
  Atlas-term Γ (base (Pair α β))
pair s t = update! s t empty!

pair-term : ∀ {α β Γ} →
  Atlas-term Γ (base α ⇒ base β ⇒ base (Pair α β))
pair-term = abs (abs (pair (var (that this)) (var this)))

uncurry : ∀ {α β γ Γ} →
  Atlas-term Γ (base α ⇒ base β ⇒ base γ) →
  Atlas-term Γ (base (Pair α β)) →
  Atlas-term Γ (base γ)
uncurry f p =
  let
    a = var (that (that this))
    b = var (that this)
    g = abs (abs (abs (app₂ (weaken₃ f) a b)))
  in
    fold! g neutral-term p

zip-pair : ∀ {κ a b Γ} →
  Atlas-term Γ (base (Map κ a)) → Atlas-term Γ (base (Map κ b)) →
  Atlas-term Γ (base (Map κ (Pair a b)))
zip-pair = zip! (abs pair-term)

-- diff-term and apply-term

-- b₀ ⊝ b₁ = b₀ xor b₁
-- m₀ ⊝ m₁ = zip _⊝_ m₀ m₁

Atlas-diff : ∀ {ι Γ} →
  Atlas-term Γ (base ι ⇒ base ι ⇒ Atlas-Δtype (base ι))
Atlas-diff {Bool} = const xor
Atlas-diff {Map κ ι} = app (const zip) (abs Atlas-diff)

-- b ⊕ Δb = b xor Δb
-- m ⊕ Δm = zip _⊕_ m Δm

Atlas-apply : ∀ {ι Γ} →
  Atlas-term Γ (Atlas-Δtype (base ι) ⇒ base ι ⇒ base ι)
Atlas-apply {Bool} = const xor
Atlas-apply {Map κ ι} = app (const zip) (abs Atlas-apply)

-- Shorthands for working with diff-term and apply-term

diff : ∀ {τ Γ} →
  Atlas-term Γ τ → Atlas-term Γ τ →
  Atlas-term Γ (Atlas-Δtype τ)
diff = app₂ (lift-diff Atlas-diff Atlas-apply)

apply : ∀ {τ Γ} →
  Atlas-term Γ (Atlas-Δtype τ) → Atlas-term Γ τ →
  Atlas-term Γ τ
apply = app₂ (lift-apply Atlas-diff Atlas-apply)

-- Shorthands for creating changes corresponding to
-- insertion/deletion.

insert : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base ι) →
  -- last argument is the change accumulator
  Atlas-term Γ (Atlas-Δtype (base (Map κ ι))) →
  Atlas-term Γ (Atlas-Δtype (base (Map κ ι)))

delete : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base ι) →
  Atlas-term Γ (Atlas-Δtype (base (Map κ ι))) →
  Atlas-term Γ (Atlas-Δtype (base (Map κ ι)))

insert k v acc = update! k (diff v neutral-term) acc
delete k v acc = update! k (diff neutral-term v) acc

-- Shorthand for 4-way zip
zip4! : ∀ {κ a b c d e Γ} →
  let
    t:_ = λ ι → Atlas-term Γ (base ι)
  in
    Atlas-term Γ
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

-- Type signature of Atlas-Δconst is boilerplate.
Atlas-Δconst : ∀ {Γ τ} → (c : Atlas-const τ) →
  Atlas-term Γ (Atlas-Δtype τ)

Atlas-Δconst true  = false!
Atlas-Δconst false = false!

-- Δxor = λ x Δx y Δy → Δx xor Δy
Atlas-Δconst xor =
  let
    Δx = var (that (that this))
    Δy = var this
  in abs (abs (abs (abs (xor! Δx Δy))))

Atlas-Δconst empty = empty!

-- If k ⊕ Δk ≡ k, then
--   Δupdate k Δk v Δv m Δm = update k Δv Δm
-- else it is a deletion followed by insertion:
--   Δupdate k Δk v Δv m Δm =
--     insert (k ⊕ Δk) (v ⊕ Δv) (delete k v Δm)
--
-- We implement the else-branch only for the moment.
Atlas-Δconst update =
  let
    k  = var (that (that (that (that (that this)))))
    Δk = var (that (that (that (that this))))
    v  = var (that (that (that this)))
    Δv = var (that (that this))
    -- m = var (that this) -- unused parameter
    Δm = var this
  in
    abs (abs (abs (abs (abs (abs
      (insert (apply Δk k) (apply Δv v)
        (delete k v Δm)))))))

-- Δlookup k Δk m Δm | true? (k ⊕ Δk ≡ k)
-- ... | true  = lookup k Δm
-- ... | false =
--   (lookup (k ⊕ Δk) m ⊕ lookup (k ⊕ Δk) Δm)
--     ⊝ lookup k m
--
-- Only the false-branch is implemented.
Atlas-Δconst lookup =
  let
    k  = var (that (that (that this)))
    Δk = var (that (that this))
    m  = var (that this)
    Δm = var this
    k′ = apply Δk k
  in
    abs (abs (abs (abs
      (diff (apply (lookup! k′ Δm) (lookup! k′ m))
            (lookup! k m)))))

-- Δzip f Δf m₁ Δm₁ m₂ Δm₂ | true? (f ⊕ Δf ≡ f)
--
-- ... | true =
--   zip (λ k Δv₁ Δv₂ → Δf (lookup k m₁) Δv₁ (lookup k m₂) Δv₂)
--       Δm₁ Δm₂
--
-- ... | false = zip₄ Δf m₁ Δm₁ m₂ Δm₂
--
-- we implement the false-branch for the moment.
Atlas-Δconst zip =
  let
    Δf = var (that (that (that (that this))))
    m₁  = var (that (that (that this)))
    Δm₁ = var (that (that this))
    m₂  = var (that this)
    Δm₂ = var this
    g = abs (app₂ (weaken₁ Δf) (var this) nil-term)
  in
    abs (abs (abs (abs (abs (abs (zip4! g m₁ Δm₁ m₂ Δm₂))))))

-- Δfold f Δf z Δz m Δm = proj₂
--   (fold (λ k [a,Δa] [b,Δb] →
--           uncurry (λ a Δa → uncurry (λ b Δb →
--             pair (f k a b) (Δf k nil a Δa b Δb))
--             [b,Δb]) [a,Δa])
--        (pair z Δz)
--        (zip-pair m Δm))
--
-- Δfold is efficient only if evaluation is lazy and Δf is
-- self-maintainable: it doesn't look at the argument
-- (b = fold f k a b₀) at all.
Atlas-Δconst (fold {κ} {α} {β}) =
    let -- TODO (tedius): write weaken₇
      f  = weaken₃ (weaken₃ (weaken₁
        (var (that (that (that (that (that this))))))))
      Δf = weaken₃ (weaken₃ (weaken₁
        (var (that (that (that (that this)))))))
      z  = var (that (that (that this)))
      Δz = var (that (that this))
      m  = var (that this)
      Δm = var this
      k = weaken₃ (weaken₁ (var (that (that this))))
      [a,Δa] = var (that this)
      [b,Δb] = var this
      a  = var (that (that (that this)))
      Δa = var (that (that this))
      b  = var (that this)
      Δb = var this
      g = abs (abs (abs (uncurry (abs (abs (uncurry (abs (abs
            (pair (app₃ f k a b)
                  (app₆ Δf k nil-term a Δa b Δb))))
            (weaken₂ [b,Δb])))) [a,Δa])))
      proj₂ = uncurry (abs (abs (var this)))
    in
      abs (abs (abs (abs (abs (abs
        (proj₂ (fold! g (pair z Δz) (zip-pair m Δm))))))))

open import Syntax.Language.Calculus

Atlas = calculus-with
  Atlas-type
  Atlas-const
  Atlas-Δtype
  Atlas-Δconst
