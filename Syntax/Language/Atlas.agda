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

open import Syntax.Language.Calculus

data Atlas-type : Set where
  Bool : Atlas-type
  Map : (κ : Atlas-type) (ι : Atlas-type) → Atlas-type

data Atlas-const : Set where

  true  : Atlas-const
  false : Atlas-const
  xor   : Atlas-const

  empty  : ∀ {κ ι : Atlas-type} → Atlas-const
  update : ∀ {κ ι : Atlas-type} → Atlas-const
  zip    : ∀ {κ a b c : Atlas-type} → Atlas-const

Atlas-lookup : Atlas-const → Type Atlas-type

Atlas-lookup true  = base Bool
Atlas-lookup false = base Bool
Atlas-lookup xor   = base Bool ⇒ base Bool ⇒ base Bool

Atlas-lookup (empty {κ} {ι}) = base (Map κ ι)

-- `update key val my-map` would
-- - insert if `key` is not present in `my-map`
-- - delete if `val` is the neutral element
-- - make an update otherwise
Atlas-lookup (update {κ} {ι}) =
  base κ ⇒ base ι ⇒ base (Map κ ι) ⇒ base (Map κ ι)

-- Model of zip = Haskell Data.List.zipWith
-- zipWith :: (a → b → c) → [a] → [b] → [c]
Atlas-lookup (zip {κ} {a} {b} {c}) =
  (base κ ⇒ base a ⇒ base b ⇒ base c) ⇒
  base (Map κ a) ⇒ base (Map κ b) ⇒ base (Map κ c)

Atlas-Δbase : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δbase Bool = Bool
-- change to a map is change to its values
Atlas-Δbase (Map key val) = (Map key (Atlas-Δbase val))

Atlas-Δtype : Type Atlas-type → Type Atlas-type
Atlas-Δtype = lift-Δtype₀ Atlas-Δbase

Atlas-context : Set
Atlas-context = Context {Type Atlas-type}

Atlas-term : Atlas-context → Type Atlas-type → Set
Atlas-term = Term {Atlas-type} {Atlas-const} {Atlas-lookup}

-- Every base type has a known nil-change.
-- The nil-change of ι is also the neutral element of Map κ Δι.

neutral : ∀ {ι : Atlas-type} → Atlas-const
neutral {Bool} = false
neutral {Map κ ι} = empty {κ} {ι}

neutral-term : ∀ {ι Γ} → Atlas-term Γ (base ι)
neutral-term {Bool}   = const (neutral {Bool})
neutral-term {Map κ ι} = const (neutral {Map κ ι})

nil-const : ∀ {ι : Atlas-type} → Atlas-const
nil-const {ι} = neutral {Atlas-Δbase ι}

nil-term : ∀ {ι Γ} → Atlas-term Γ (base (Atlas-Δbase ι))
nil-term {Bool}   = const (nil-const {Bool})
nil-term {Map κ ι} = const (nil-const {Map κ ι})

-- Shorthands of constants
--
-- There's probably a uniform way to lift constants
-- into term constructors.
--
-- TODO: write this and call it Syntax.Term.Plotkin.lift-term

zip! : ∀ {κ a b c Γ} →
  Atlas-term Γ (base κ ⇒ base a ⇒ base b ⇒ base c) →
  Atlas-term Γ (base (Map κ a)) → Atlas-term Γ (base (Map κ b)) →
  Atlas-term Γ (base (Map κ c))

zip! f m₁ m₂ = app (app (app (const zip) f) m₁) m₂

lookup! : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base (Map κ ι)) →
  Atlas-term Γ (base ι)

lookup! = {!!} -- TODO: add constant `lookup`

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
diff s t = app (app (lift-diff Atlas-diff Atlas-apply) s) t

apply : ∀ {τ Γ} →
  Atlas-term Γ (Atlas-Δtype τ) → Atlas-term Γ τ →
  Atlas-term Γ τ
apply s t = app (app (lift-apply Atlas-diff Atlas-apply) s) t

-- Shorthands for creating changes corresponding to
-- insertion/deletion.

update! : ∀ {κ ι Γ} →
  Atlas-term Γ (base κ) → Atlas-term Γ (base ι) →
  Atlas-term Γ (base (Map κ ι)) →
  Atlas-term Γ (base (Map κ ι))

update! k v m = app (app (app (const update) k) v) m

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

-- The binary operator with which all base-type values
-- form a group

union : ∀ {ι Γ} →
  Atlas-term Γ (base ι) → Atlas-term Γ (base ι) →
  Atlas-term Γ (base ι)
union {Bool} s t = app (app (const xor) s) t
union {Map κ ι} s t =
  let
    union-term = abs (abs (union (var (that this)) (var this)))
  in
    zip! (abs union-term) s t

-- Shorthand for 4-way zip
zip4! : ∀ {κ a b c d e Γ} →
  let
    t:_ = λ ι → Atlas-term Γ (base ι)
  in
    Atlas-term Γ
      (base κ ⇒ base a ⇒ base b ⇒ base c ⇒ base d ⇒ base e) →
    t: Map κ a → t: Map κ b → t: Map κ c → t: Map κ d → t: Map κ e

zip4! f m₁ m₂ m₃ m₄ =
  let
    v₁ = var (that this)
    v₂ = var this
    v₃ = var (that this)
    v₄ = var this
    k₁₂ = var (that (that this))
    k₃₄ = var (that (that this))
    f₁₂ = abs (abs (abs (app (app (app (app (app
      (weaken₃ f) k₁₂) v₁) v₂)
      (lookup! k₁₂ (weaken₃ m₃))) (lookup! k₁₂ (weaken₃ m₄)))))
    f₃₄ = abs (abs (abs (app (app (app (app (app
      (weaken₃ f) k₃₄)
      (lookup! k₃₄ (weaken₃ m₁)))
      (lookup! k₃₄ (weaken₃ m₂))) v₃) v₄)))
  in
    -- A correct but inefficient implementation.
    -- May want to speed it up after constants are finalized.
    union (zip! f₁₂ m₁ m₂) (zip! f₃₄ m₃ m₄)

-- Type signature of Atlas-Δconst is boilerplate.
Atlas-Δconst : ∀ {Γ} → (c : Atlas-const) →
  Atlas-term Γ (Atlas-Δtype (Atlas-lookup c))

Atlas-Δconst true  = const false
Atlas-Δconst false = const false

-- Δxor = λ x Δx y Δy → Δx xor Δy
Atlas-Δconst xor =
  let
    Δx = var (that (that this))
    Δy = var this
  in abs (abs (abs (abs (app (app (const xor) Δx) Δy))))

Atlas-Δconst empty = const empty

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
    g = abs (app (app (weaken₁ Δf) (var this)) nil-term)
  in
    abs (abs (abs (abs (abs (abs (zip4! g m₁ Δm₁ m₂ Δm₂))))))

Atlas = calculus-with
  Atlas-type
  Atlas-const
  Atlas-lookup
  Atlas-Δtype
  Atlas-Δconst
