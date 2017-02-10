module New.Equivalence where

open import Function
open import Relation.Binary

open import New.Changes

module _ {a} {A : Set a} {{CA : ChAlg A}} {x : A} where
  -- Delta-observational equivalence: these asserts that two changes
  -- give the same result when applied to a base value.

  -- To avoid unification problems, use a one-field record (a Haskell "newtype")
  -- instead of a "type synonym".
  record _≙_ (dx dy : Ch A) : Set a where
    -- doe = Delta-Observational Equivalence.
    constructor doe
    field
      proof : x ⊕ dx ≡ x ⊕ dy

  open _≙_ public

  -- Same priority as ≡
  infix 4 _≙_

  -- _≙_ is indeed an equivalence relation:
  ≙-refl : ∀ {dx} → dx ≙ dx
  ≙-refl = doe refl

  ≙-sym : ∀ {dx dy} → dx ≙ dy → dy ≙ dx
  ≙-sym ≙ = doe $ sym $ proof ≙

  ≙-trans : ∀ {dx dy dz} → dx ≙ dy → dy ≙ dz → dx ≙ dz
  ≙-trans ≙₁ ≙₂ = doe $ trans (proof ≙₁) (proof ≙₂)

  -- That's standard congruence applied to ≙
  ≙-cong  : ∀ {b} {B : Set b}
       (f : A → B) {dx dy} → dx ≙ dy → f (x ⊕ dx) ≡ f (x ⊕ dy)
  ≙-cong f da≙db = cong f $ proof da≙db

  ≙-isEquivalence : IsEquivalence (_≙_)
  ≙-isEquivalence = record
    { refl  = ≙-refl
    ; sym   = ≙-sym
    ; trans = ≙-trans
    }

  ≙-setoid : Setoid a a
  ≙-setoid = record
    { Carrier       = Ch A
    ; _≈_           = _≙_
    ; isEquivalence = ≙-isEquivalence
    }

≙-syntax : ∀ {a} {A : Set a} {{CA : ChAlg A}} (x : A) (dx₁ dx₂ : Ch A) → Set a
≙-syntax x dx₁ dx₂ = _≙_ {x = x} dx₁ dx₂
syntax ≙-syntax x dx₁ dx₂ = dx₁ ≙[ x ] dx₂


module BinaryValid
  {A : Set} {{CA : ChAlg A}}
  {B : Set} {{CB : ChAlg B}}
  {C : Set} {{CC : ChAlg C}}
  (f : A → B → C) (df : A → Ch A → B → Ch B → Ch C)
  where

  binary-valid-preserve-hp =
    ∀ a da (ada : valid a da)
      b db (bdb : valid b db)
    → valid (f a b) (df a da b db)

  binary-valid-eq-hp =
    ∀ a da (ada : valid a da)
      b db (bdb : valid b db)
    → (f ⊕ df) (a ⊕ da) (b ⊕ db) ≡ f a b ⊕ df a da b db

  binary-valid :
    binary-valid-preserve-hp →
    binary-valid-eq-hp →
    valid f df
  binary-valid ext-valid proof a da ada =
      (λ b db bdb → ext-valid a da ada b db bdb , lem2 b db bdb)
    , ext lem1
    where
      lem1 : ∀ b → f (a ⊕ da) b ⊕ df (a ⊕ da) (nil (a ⊕ da)) b (nil b) ≡
        f a b ⊕ df a da b (nil b)
      lem1 b
        rewrite sym (update-nil b)
        | proof a da ada b (nil b) (nil-valid b)
        | update-nil b = refl
      lem2 : ∀ b (db : Ch B) (bdb : valid b db) →
        f a (b ⊕ db) ⊕ df a da (b ⊕ db) (nil (b ⊕ db)) ≡
        f a b ⊕ df a da b db
      lem2 b db bdb
        rewrite sym (proof a da ada (b ⊕ db) (nil (b ⊕ db)) (nil-valid (b ⊕ db)))
        | update-nil (b ⊕ db) = proof a da ada b db bdb

module TernaryValid
  {A : Set} {{CA : ChAlg A}}
  {B : Set} {{CB : ChAlg B}}
  {C : Set} {{CC : ChAlg C}}
  {D : Set} {{CD : ChAlg D}}
  (f : A → B → C → D) (df : A → Ch A → B → Ch B → C → Ch C → Ch D)
  where


  ternary-valid-preserve-hp =
    ∀ a da (ada : valid a da)
      b db (bdb : valid b db)
      c dc (cdc : valid c dc)
    → valid (f a b c) (df a da b db c dc)

  -- These are explicit definitions only to speed up typechecking.
  CA→B→C→D : ChAlg (A → B → C → D)
  CA→B→C→D = funCA
  f⊕df = (_⊕_ {{CA→B→C→D}} f df)

  -- Already this definition takes a while to typecheck.
  ternary-valid-eq-hp =
    ∀ a (da : Ch A {{CA}}) (ada : valid {{CA}} a da)
      b (db : Ch B {{CB}}) (bdb : valid {{CB}} b db)
      c (dc : Ch C {{CC}}) (cdc : valid {{CC}} c dc)
    → f⊕df (a ⊕ da) (b ⊕ db) (c ⊕ dc) ≡ f a b c ⊕ df a da b db c dc

  ternary-valid :
    ternary-valid-preserve-hp →
    ternary-valid-eq-hp →
    valid f df
  ternary-valid ext-valid proof a da ada =
    binary-valid
      (λ b db bdb c dc cdc → ext-valid a da ada b db bdb c dc cdc)
      lem2
    , ext (λ b → ext (lem1 b))
    where
      open BinaryValid (f a) (df a da)
      lem1 : ∀ b c → f⊕df (a ⊕ da) b c ≡ (f a ⊕ df a da) b c
      lem1 b c
        rewrite sym (update-nil b)
        | sym (update-nil c)
        |
          proof
            a da ada
            b (nil b) (nil-valid b)
            c (nil c) (nil-valid c)
        | update-nil b
        | update-nil c = refl
        -- rewrite
        --   sym
        --   (proof
        --     (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da))
        --     b (nil b) (nil-valid b)
        --     c (nil c) (nil-valid c))
        -- | update-nil (a ⊕ da)
        -- | update-nil b
        -- | update-nil c = {! !}
      lem2 : ∀ b db (bdb : valid b db)
               c dc (cdc : valid c dc) →
                 (f a ⊕ df a da) (b ⊕ db) (c ⊕ dc)
               ≡ f a b c ⊕ df a da b db c dc
      lem2 b db bdb c dc cdc
        rewrite sym
          (proof
            a da ada
            (b ⊕ db) (nil (b ⊕ db)) (nil-valid (b ⊕ db))
            (c ⊕ dc) (nil (c ⊕ dc)) (nil-valid (c ⊕ dc))
          )
        | update-nil (b ⊕ db)
        | update-nil (c ⊕ dc) = proof a da ada b db bdb c dc cdc
