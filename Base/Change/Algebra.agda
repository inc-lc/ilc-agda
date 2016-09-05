------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Change Structures.
--
-- This module defines the notion of change structures,
-- as well as change structures for groups, functions and lists.
--
-- This module corresponds to Section 2 of the PLDI paper.
------------------------------------------------------------------------

module Base.Change.Algebra where

open import Relation.Binary.PropositionalEquality
open import Level

-- Change Algebras
-- ===============
--
-- In the paper, change algebras are called "change structures"
-- and they are described in Section 2.1. We follow the design of
-- the Agda standard library and define change algebras as two
-- records, so Definition 2.1 from the PLDI paper maps to the
-- records IsChangeAlgebra and ChangeAlgebra.
--
-- A value of type (IsChangeAlgebra Change update diff) proves that
-- Change, update and diff together form a change algebra.
--
-- A value of type (ChangeAlgebra Carrier) contains the necessary
-- ingredients to create a change algebra for a carrier set.
--
-- In the paper, Carrier is called V (Def. 2.1a),
-- Change is called Δ (Def. 2.1b),
-- update is written as infix ⊕ (Def. 2.1c),
-- diff is written as infix ⊝ (Def. 2.1d),
-- and update-diff is specified in Def. 2.1e.

record IsChangeAlgebra
    {c} {d}
    {Carrier : Set c}
    (Change : Carrier → Set d)
    (update : (v : Carrier) (dv : Change v) → Carrier)
    (diff : (u v : Carrier) → Change v)
    (nil : (u : Carrier) → Change u) : Set (c ⊔ d) where
  field
    update-diff : ∀ u v → update v (diff u v) ≡ u
    -- This corresponds to Lemma 2.3 from the paper.
    update-nil : ∀ v → update v (nil v) ≡ v

  -- abbreviations
  before : ∀ {v} → Change v → Carrier
  before {v} _ = v

  after : ∀ {v} → Change v → Carrier
  after {v} dv = update v dv

record ChangeAlgebra {c} ℓ
    (Carrier : Set c) : Set (c ⊔ suc ℓ) where
  field
    Change : Carrier → Set ℓ
    update : (v : Carrier) (dv : Change v) → Carrier
    diff : (u v : Carrier) → Change v

    -- This generalizes Def. 2.2. from the paper.
    nil : (u : Carrier) → Change u

    isChangeAlgebra : IsChangeAlgebra Change update diff nil


  infixl 6 update diff

  open IsChangeAlgebra isChangeAlgebra public

-- The following open ... public statement lets us use infix ⊞
-- and ⊟ for update and diff. In the paper, we use infix ⊕ and
-- ⊝.

open ChangeAlgebra {{...}} public
  using
    ( update-diff
    ; update-nil
    ; nil
    ; before
    ; after
    )
  renaming
    ( Change to Δ
    ; update to _⊞_
    ; diff to _⊟_
    )

-- Families of Change Algebras
-- ===========================
--
-- This is some Agda machinery to allow subscripting change
-- algebra operations to avoid ambiguity. In the paper,
-- we simply write (in the paragraph after Def. 2.1):
--
--   We overload operators ∆, ⊝ and ⊕ to refer to the
--   corresponding operations of different change structures; we
--   will subscript these symbols when needed to prevent
--   ambiguity.
--
-- The following definitions implement this idea formally.

record ChangeAlgebraFamily {a p} ℓ {A : Set a} (P : A → Set p): Set (suc ℓ ⊔ p ⊔ a) where
  constructor
    family
  field
    change-algebra : ∀ x → ChangeAlgebra ℓ (P x)

  {-
  instance
    change-algebra-extractor : ∀ {x} → ChangeAlgebra ℓ (P x)
    change-algebra-extractor {x} = change-algebra x
  -}
  module _ x where
    open ChangeAlgebra (change-algebra x) public

module Family = ChangeAlgebraFamily {{...}}

open Family public
  using
    (
    )
  renaming
    ( Change to Δ₍_₎
    ; nil to nil₍_₎
    ; update-diff to update-diff₍_₎
    ; update-nil to update-nil₍_₎
    ; change-algebra to change-algebra₍_₎
    ; before to before₍_₎
    ; after to after₍_₎
    )

-- XXX not clear this is ever used
instance
  change-algebra-family-inst = change-algebra₍_₎

infixl 6 update′ diff′

update′ = Family.update
syntax update′ x v dv = v ⊞₍ x ₎ dv

diff′ = Family.diff
syntax diff′ x u v = u ⊟₍ x ₎ v

-- Derivatives
-- ===========
--
-- This corresponds to Def. 2.4 in the paper.

RawChange : ∀ {a b c d} {A : Set a} {B : Set b} →
  {{CA : ChangeAlgebra c A}} →
  {{CB : ChangeAlgebra d B}} →
  (f : A → B) →
  Set (a ⊔ c ⊔ d)
RawChange f = ∀ a (da : Δ a) → Δ (f a)

IsDerivative : ∀ {a b c d} {A : Set a} {B : Set b} →
  {{CA : ChangeAlgebra c A}} →
  {{CB : ChangeAlgebra d B}} →
  (f : A → B) →
  (df : RawChange f) →
  Set (a ⊔ b ⊔ c)
IsDerivative f df = ∀ a da → f a ⊞ df a da ≡ f (a ⊞ da)

-- This is a variant of IsDerivative for change algebra families.
RawChange₍_,_₎ : ∀ {a b p q c d} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
  {{CP : ChangeAlgebraFamily c P}} →
  {{CQ : ChangeAlgebraFamily d Q}} →
  (x : A) →
  (y : B) →
  (f : P x → Q y) → Set (c ⊔ d ⊔ p)
RawChange₍_,_₎ x y f = ∀ px (dpx : Δ₍_₎ x px) → Δ₍_₎ y (f px)

IsDerivative₍_,_₎ : ∀ {a b p q c d} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
  {{CP : ChangeAlgebraFamily c P}} →
  {{CQ : ChangeAlgebraFamily d Q}} →
  (x : A) →
  (y : B) →
  (f : P x → Q y) →
  (df : RawChange₍_,_₎ x y f) →
  Set (p ⊔ q ⊔ c)
IsDerivative₍_,_₎ {P = P} {{CP}} {{CQ}} x y f df = IsDerivative {{change-algebra₍ _ ₎}} {{change-algebra₍ _ ₎}} f df where
  CPx = change-algebra₍_₎ {{CP}} x
  CQy = change-algebra₍_₎ {{CQ}} y

-- Lemma 2.5 appears in Base.Change.Equivalence.

-- Abelian Groups Induce Change Algebras
-- =====================================
--
-- In the paper, as the first example for change structures after
-- Def. 2.1, we mention that "each abelian group ... induces a
-- change structure". This is the formalization of this result.
--
-- The module GroupChanges below takes a proof that A forms an
-- abelian group and provides a changeAlgebra for A. The proof of
-- Def 2.1e is by equational reasoning using the group axioms, in
-- the definition of changeAlgebra.isChangeAlgebra.update-diff.

open import Algebra.Structures
open import Data.Product
open import Function

module GroupChanges
    {a} (A : Set a) {_⊕_} {ε} {_⁻¹}
    {{isAbelianGroup : IsAbelianGroup {A = A} _≡_ _⊕_ ε _⁻¹}}
  where
    open IsAbelianGroup isAbelianGroup
      hiding
        ( refl
        )
      renaming
        ( _-_ to _⊝_
        ; ∙-cong to _⟨⊕⟩_
        )

    open ≡-Reasoning

    changeAlgebra : ChangeAlgebra a A
    changeAlgebra = record
      { Change = const A
      ; update = _⊕_
      ; diff = _⊝_
      ; nil = const ε
      ; isChangeAlgebra = record
        { update-diff = λ u v →
            begin
              v ⊕ (u ⊝ v)
            ≡⟨ comm _ _ ⟩
              (u ⊝ v ) ⊕ v
            ≡⟨⟩
              (u ⊕ (v ⁻¹)) ⊕ v
            ≡⟨ assoc _ _ _ ⟩
              u ⊕ ((v ⁻¹) ⊕ v)
            ≡⟨  refl ⟨⊕⟩ proj₁ inverse v  ⟩
              u ⊕ ε
            ≡⟨  proj₂ identity u ⟩
              u
            ∎
        ; update-nil = proj₂ identity
        }
      }

-- Function Changes
-- ================
--
-- This is one of our most important results: Change structures
-- can be lifted to function spaces. We formalize this as a module
-- FunctionChanges that takes the change algebras for A and B as
-- arguments, and provides a changeAlgebra for (A → B). The proofs
-- are by equational reasoning using 2.1e for A and B.

module FunctionChanges
    {a} {b} {c} {d} (A : Set a) (B : Set b) {{CA : ChangeAlgebra c A}} {{CB : ChangeAlgebra d B}}
  where
    -- This corresponds to Definition 2.6 in the paper.
    record FunctionChange (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
      field
        -- Definition 2.6a
        apply : RawChange f

        -- Definition 2.6b.
        -- (for some reason, the version in the paper has the arguments of ≡
        -- flipped. Since ≡ is symmetric, this doesn't matter).
        correct : (a : A) (da : Δ a) →
          f (a ⊞ da) ⊞ apply (a ⊞ da) (nil (a ⊞ da)) ≡ f a ⊞ apply a da

    open FunctionChange public
    open ≡-Reasoning
    open import Postulate.Extensionality

    funDiff : (g f : A → B) → FunctionChange f
    funDiff = λ g f → record
        { apply = λ a da → g (a ⊞ da) ⊟ f a
          -- the proof of correct is the first half of what we
          -- have to prove for Theorem 2.7.
        ; correct = λ a da →
          begin
            _⊞_ {{CB}} (f (_⊞_ {{CA}} a da)) (g (_⊞_ {{CA}} (a ⊞ da) (nil (a ⊞ da))) ⊟ f (a ⊞ da))
          ≡⟨ cong (λ □ → _⊞_ {{CB}} (f (a ⊞ da)) (g □ ⊟ f (a ⊞ da)))
               (update-nil {{CA}} (a ⊞ da)) ⟩
            _⊞_ {{CB}} (f (a ⊞ da)) (g (a ⊞ da) ⊟ f (a ⊞ da))
          ≡⟨ update-diff {{CB}} (g (a ⊞ da)) (f (a ⊞ da)) ⟩
            g (a ⊞ da)
          ≡⟨ sym (update-diff {{CB}} (g (a ⊞ da)) (f a)) ⟩
            _⊞_ {{CB}} (f a) (g (a ⊞ da) ⊟ f a)
          ∎
        }

    funUpdate : ∀ (f : A → B) (df : FunctionChange f) → A → B
    funUpdate = λ f df a → f a ⊞ apply df a (nil a)
    funNil = λ f → funDiff f f

    mutual
      -- I have to write the type of funUpdateDiff without using changeAlgebra,
      -- so I just use the underlying implementations.
      funUpdateDiff : ∀ u v → funUpdate v (funDiff u v) ≡ u
      instance
        changeAlgebra : ChangeAlgebra (a ⊔ b ⊔ c ⊔ d) (A → B)

      changeAlgebra = record
        { Change = FunctionChange
          -- in the paper, update and diff below are in Def. 2.7
        ; update = funUpdate
        ; diff = funDiff
        ; nil = funNil
        ; isChangeAlgebra = record
            -- the proof of update-diff is the second half of what
            -- we have to prove for Theorem 2.8.
          { update-diff = funUpdateDiff
          ; update-nil = λ v → funUpdateDiff v v
          }
        }
      -- XXX remove mutual recursion by inlining the algebra in here?
      funUpdateDiff = λ g f → ext (λ a →
        begin
          _⊞_ {{CB}} (f a) (g (_⊞_ {{CA}} a (nil a)) ⊟ f a)
        ≡⟨ cong (λ □ → _⊞_ {{CB}} (f a) (g □ ⊟ f a)) (update-nil {{CA}} a) ⟩
          _⊞_ {{CB}} (f a) (g a ⊟ f a)
        ≡⟨ update-diff {{CB}}  (g a) (f a) ⟩
          g a
        ∎)

    -- This is Theorem 2.9 in the paper.
    incrementalization : ∀ (f : A → B) df a da →
      (f ⊞ df) (a ⊞ da) ≡ f a ⊞ apply df a da
    incrementalization f df a da = correct df a da

    -- This is Theorem 2.10 in the paper. However, the derivative of f is just
    -- the apply component of `nil f`, not the full `nil f`, which also includes
    -- a proof. This is not an issue in the paper, which is formulated in a
    -- proof-irrelevant metalanguage.
    nil-is-derivative : ∀ (f : A → B) →
      IsDerivative f (apply (nil f))
    nil-is-derivative f a da =
      begin
        f a ⊞ apply (nil f) a da
      ≡⟨ sym (incrementalization f (nil f) a da) ⟩
        (f ⊞ nil {{changeAlgebra}} f) (a ⊞ da)
      ≡⟨ cong (λ □ → □ (a ⊞ da))
           (update-nil {{changeAlgebra}} f) ⟩
        f (a ⊞ da)
      ∎

    -- Show that any derivative is a valid function change.

    -- In the paper, this is never actually stated. We just prove that nil
    -- changes are derivatives; the paper keeps talking about "the derivative",
    -- suggesting derivatives are unique. If derivatives were unique, we could
    -- say that the nil change is *the* derivative, hence the derivative is the
    -- nil change (hence also a change).
    --
    -- In fact, derivatives are only unique up to change equivalence and
    -- extensional equality; this is proven in Base.Change.Equivalence.derivative-unique.
    --
    Derivative-is-valid : ∀ {f : A → B} df (IsDerivative-f-df : IsDerivative f df) a da →
      f (a ⊞ da) ⊞ (df (a ⊞ da) (nil (a ⊞ da))) ≡ f a ⊞ df a da
    Derivative-is-valid {f} df IsDerivative-f-df a da rewrite IsDerivative-f-df (a ⊞ da) (nil (a ⊞ da)) | update-nil (a ⊞ da) = sym (IsDerivative-f-df a da)

    DerivativeAsChange : ∀ {f : A → B} df (IsDerivative-f-df : IsDerivative f df) → Δ f
    DerivativeAsChange df IsDerivative-f-df = record { apply = df ; correct = Derivative-is-valid df IsDerivative-f-df }
    -- In Equivalence.agda, derivative-is-nil-alternative then proves that a derivative is also a nil change.


-- List (== Environment) Changes
-- =============================
--
-- Here, we define a change structure on environments, given a
-- change structure on the values in the environments. In the
-- paper, we describe this in Definition 3.5. But note that this
-- Agda formalization uses de Bruijn indices instead of names, so
-- environments are just lists. Therefore, when we use Definition
-- 3.5 in the paper, in this formalization, we use the list-like
-- change structure defined here.

open import Data.List
open import Data.List.All

data All′ {a p q} {A : Set a}
    {P : A → Set p}
    (Q : {x : A} → P x → Set q)
  : {xs : List A} (pxs : All P xs) → Set (p ⊔ q ⊔ a) where
    []  : All′ Q []
    _∷_ : ∀ {x xs} {px : P x} {pxs : All P xs} (qx : Q px) (qxs : All′ Q pxs) → All′ Q (px ∷ pxs)

module ListChanges
    {a} {c} {A : Set a} (P : A → Set) {{C : ChangeAlgebraFamily c P}}
  where
    update-all : ∀ {xs} → (pxs : All P xs) →  All′ (Δ₍_₎ {{C}} _) pxs  → All P xs
    update-all {[]} [] [] = []
    update-all {x ∷ xs} (px ∷ pxs) (dpx ∷ dpxs) = (px ⊞₍ x ₎ dpx) ∷ update-all pxs dpxs

    diff-all : ∀ {xs} → (pxs′ pxs : All P xs) → All′ (Δ₍_₎ {{C}} _) pxs
    diff-all [] [] = []
    diff-all (px′ ∷ pxs′) (px ∷ pxs) = (px′ ⊟₍ _ ₎ px) ∷ diff-all pxs′ pxs

    update-diff-all : ∀ {xs} → (pxs′ pxs : All P xs) → update-all pxs (diff-all pxs′ pxs) ≡ pxs′
    update-diff-all [] [] = refl
    update-diff-all (px′ ∷ pxs′) (px ∷ pxs) = cong₂ _∷_ (update-diff₍_₎ {{C}} _ px′ px) (update-diff-all pxs′ pxs)

    instance
      changeAlgebra : ChangeAlgebraFamily (c ⊔ a) (All P)

    changeAlgebra = record
      { change-algebra = λ xs → record
        { Change = All′ (Δ₍_₎ {{C}} _)
        ; update = update-all
        ; diff = diff-all
        ; nil = λ xs → diff-all xs xs
        ; isChangeAlgebra = record
          { update-diff = update-diff-all
          ; update-nil = λ xs₁ → update-diff-all xs₁ xs₁
          }
        }
      }
