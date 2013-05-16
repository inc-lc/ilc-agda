module total where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * Δ e describes how e changes when its free variables or its arguments change
--   * denotational semantics including semantics of changes
--
-- Work in Progress:
--   * lemmas about behavior of changes
--   * lemmas about behavior of Δ
--   * correctness proof for symbolic derivation

import Relation.Binary as B

open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Relation.Nullary using (¬_)

open import meaning

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type
  bool : Type

infixr 5 _⇒_

-- Denotational Semantics

data Bool : Set where
  true false : Bool

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ bool ⟧Type = Bool

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

-- Value Equivalence

data _≡_ : ∀ {τ} → (v₁ v₂ : ⟦ τ ⟧) → Set where
  ext : ∀ {τ₁ τ₂} {f₁ f₂ : ⟦ τ₁ ⇒ τ₂ ⟧} →
    (∀ v → f₁ v ≡ f₂ v) →
    f₁ ≡ f₂
  bool : ∀ {b : Bool} →
    b ≡ b

≡-refl : ∀ {τ} {v : ⟦ τ ⟧} →
  v ≡ v
≡-refl {τ₁ ⇒ τ₂} = ext (λ v → ≡-refl)
≡-refl {bool} = bool

≡-sym : ∀ {τ} {v₁ v₂ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₁
≡-sym {τ₁ ⇒ τ₂} (ext ≡) = ext (λ v → ≡-sym (≡ v))
≡-sym {bool} bool = bool

≡-trans : ∀ {τ} {v₁ v₂ v₃ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₃ → v₁ ≡ v₃
≡-trans {τ₁ ⇒ τ₂} {f} (ext ≡₁) (ext ≡₂) =
  ext (λ v → ≡-trans (≡₁ v) (≡₂ v))
≡-trans {bool} bool bool = bool

≡-cong : ∀ {τ₂ τ₁ v₁ v₂} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧) →
  v₁ ≡ v₂ → f v₁ ≡ f v₂
≡-cong {τ₁ ⇒ τ₂} f ≡ = ext (λ v → ≡-cong (λ x → f x v) ≡)
--≡-cong {bool} {bool} {v₁} f bool = bool
≡-cong {bool} {bool} f bool = bool
≡-cong {bool} {τ₃ ⇒ τ₄} {v₁} {v₂} f (ext ≡₁) = {!!}

≡-cong₂ : ∀ {τ₃ τ₁ τ₂ v₁ v₂ v₃ v₄} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ₃ ⟧) →
  v₁ ≡ v₂ → v₃ ≡ v₄ → f v₁ v₃ ≡ f v₂ v₄
≡-cong₂ {τ₁ ⇒ τ₂} f ≡₁ ≡₂ = ext (λ v → ≡-cong₂ (λ x y → f x y v) ≡₁ ≡₂)
≡-cong₂ {bool} {bool} {bool} f bool bool = bool
≡-cong₂ {bool} {bool} {τ₂ ⇒ τ₃} f bool (ext ≡₂) = {!!}
≡-cong₂ {bool} {τ₁ ⇒ τ₂} {bool} f (ext ≡₁) (bool) = {!!}
≡-cong₂ {bool} {τ₁ ⇒ τ₂} {τ₃ ⇒ τ₄} f (ext ≡₁) (ext ≡₂) = {!!}

≡-app : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
≡-app = ≡-cong₂ (λ x y → x y)

≡-isEquivalence : ∀ {τ} → IsEquivalence (_≡_ {τ})
≡-isEquivalence = record
  { refl  = ≡-refl
  ; sym   = ≡-sym
  ; trans = ≡-trans
  }

≡-setoid : Type → Setoid _ _
≡-setoid τ = record
  { Carrier       = ⟦ τ ⟧
  ; _≈_           = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

module ≡-Reasoning where
  module _ {τ : Type} where
    open EqR (≡-setoid τ) public
      hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

≡-consistent : ¬ (∀ (τ : Type) → (v₁ v₂ : ⟦ τ ⟧) → v₁ ≡ v₂)
≡-consistent H with H bool true false
... | ()

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂
Δ-Type (bool) = bool -- true means negate, false means nil change

derive : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
apply : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧ → ⟦ τ ⟧
diff : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧

diff {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → diff (f₁ (apply dv v)) (f₂ v)
diff {bool} true true = false
diff {bool} true false = true
diff {bool} false true = true
diff {bool} false false = false

derive {τ₁ ⇒ τ₂} f = λ v dv → diff (f (apply dv v)) (f v)
derive {bool} b = false

apply {τ₁ ⇒ τ₂} df f = λ v → apply (df v (derive v)) (f v)
apply {bool} true true = false
apply {bool} true false = true
apply {bool} false true = true
apply {bool} false false = false

compose : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧
compose {τ₁ ⇒ τ₂} df₁ df₂ = λ v dv → compose (df₁ v dv) (df₂ v dv)
compose {bool} true true = false
compose {bool} true false = true
compose {bool} false true = true
compose {bool} false false = false

-- CONGRUENCE rules for change operations

≡-diff : ∀ {τ : Type} {v₁ v₂ v₃ v₄ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → diff v₁ v₃ ≡ diff v₂ v₄
≡-diff = ≡-cong₂ diff

≡-apply : ∀ {τ : Type} {dv₁ dv₂ : ⟦ Δ-Type τ ⟧} {v₁ v₂ : ⟦ τ ⟧} →
  dv₁ ≡ dv₂ → v₁ ≡ v₂ → apply dv₁ v₁ ≡ apply dv₂ v₂
≡-apply = ≡-cong₂ apply

-- PROPERTIES of changes

diff-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  diff v v ≡ derive v
diff-derive {τ₁ ⇒ τ₂} v = ≡-refl
diff-derive {bool} true = bool
diff-derive {bool} false = bool

diff-apply : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
  diff (apply dv v) v ≡ dv
diff-apply {τ₁ ⇒ τ₂} df f = ext (λ v → ext (λ dv →
  {!!}))
diff-apply {bool} true true = bool
diff-apply {bool} true false = bool
diff-apply {bool} false true = bool
diff-apply {bool} false false = bool

apply-diff : ∀ {τ} (v₁ v₂ : ⟦ τ ⟧) →
  apply (diff v₂ v₁) v₁ ≡ v₂

apply-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  apply (derive v) v ≡ v

apply-diff {τ₁ ⇒ τ₂} f₁ f₂ = ext (λ v →
  begin
    apply (diff f₂ f₁) f₁ v
  ≡⟨ ≡-refl ⟩
    apply (diff (f₂ (apply (derive v) v)) (f₁ v)) (f₁ v)
  ≡⟨ ≡-apply (≡-diff (≡-cong f₂ (apply-derive v)) ≡-refl) ≡-refl ⟩
    apply (diff (f₂ v) (f₁ v)) (f₁ v)
  ≡⟨ apply-diff (f₁ v) (f₂ v) ⟩
    f₂ v
  ∎) where open ≡-Reasoning
apply-diff {bool} true true = bool
apply-diff {bool} true false = bool
apply-diff {bool} false true = bool
apply-diff {bool} false false = bool

apply-derive {τ₁ ⇒ τ₂} f = ext (λ v →
  begin
    apply (derive f) f v
  ≡⟨ ≡-refl ⟩
    apply (diff (f (apply (derive v) v)) (f v)) (f v)
  ≡⟨ ≡-cong (λ x → apply (diff (f x) (f v)) (f v)) (apply-derive v) ⟩
    apply (diff (f v) (f v)) (f v)
  ≡⟨ apply-diff (f v) (f v)⟩
    f v
  ∎) where open ≡-Reasoning
apply-derive {bool} true = bool
apply-derive {bool} false = bool

apply-compose : ∀ {τ} (v : ⟦ τ ⟧) (dv₁ dv₂ : ⟦ Δ-Type τ ⟧) →
  apply (compose dv₁ dv₂) v ≡ apply dv₁ (apply dv₂ v)
apply-compose {τ₁ ⇒ τ₂} f df₁ df₂ = ext (λ v →
  apply-compose (f v) (df₁ v (derive v)) (df₂ v (derive v)))
apply-compose {bool} true true true = bool
apply-compose {bool} true true false = bool
apply-compose {bool} true false true = bool
apply-compose {bool} true false false = bool
apply-compose {bool} false true true = bool
apply-compose {bool} false true false = bool
apply-compose {bool} false false true = bool
apply-compose {bool} false false false = bool

compose-assoc : ∀ {τ} (dv₁ dv₂ dv₃ : ⟦ Δ-Type τ ⟧) →
  compose dv₁ (compose dv₂ dv₃) ≡ compose (compose dv₁ dv₂) dv₃
compose-assoc {τ₁ ⇒ τ₂} df₁ df₂ df₃ = ext (λ v → ext (λ dv →
  compose-assoc (df₁ v dv) (df₂ v dv) (df₃ v dv)))
compose-assoc {bool} true true true = bool
compose-assoc {bool} true true false = bool
compose-assoc {bool} true false true = bool
compose-assoc {bool} true false false = bool
compose-assoc {bool} false true true = bool
compose-assoc {bool} false true false = bool
compose-assoc {bool} false false true = bool
compose-assoc {bool} false false false = bool

-- TYPING CONTEXTS, VARIABLES and WEAKENING

open import binding Type ⟦_⟧Type

-- CHANGE CONTEXTS

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ

update : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
update {∅} ∅ = ∅
update {τ • Γ} (dv • v • ρ) = apply dv v • update ρ

ignore : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
ignore {∅} ∅ = ∅
ignore {τ • Γ} (dv • v • ρ) = v • ignore ρ

Δ-Context′ : (Γ : Context) → Prefix Γ → Context
Δ-Context′ Γ ∅ = Δ-Context Γ
Δ-Context′ (.τ • Γ) (τ • Γ′) = τ • Δ-Context′ Γ Γ′

update′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
update′ ∅ ρ = update ρ
update′ (τ • Γ′) (v • ρ) = v • update′ Γ′ ρ

ignore′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
ignore′ ∅ ρ = ignore ρ
ignore′ (τ • Γ′) (v • ρ) = v • ignore′ Γ′ ρ

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  true false : ∀ {Γ} → Term Γ bool
  if : ∀ {Γ τ} → (t₁ : Term Γ bool) (t₂ t₃ : Term Γ τ) → Term Γ τ

  -- `Δ t` describes how t changes if its free variables or arguments change
  Δ : ∀ {Γ τ} → (t : Term Γ τ) → Term (Δ-Context Γ) (Δ-Type τ)

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ with ⟦ t₁ ⟧Term ρ
... | true = ⟦ t₂ ⟧Term ρ
... | false = ⟦ t₃ ⟧Term ρ
⟦ Δ t ⟧Term ρ = diff (⟦ t ⟧Term (update ρ)) (⟦ t ⟧Term (ignore ρ))

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

-- Term Equivalence

module _ {Γ} {τ} where
  data _≈_ (t₁ t₂ : Term Γ τ) : Set where
    ext :
      (∀ ρ → ⟦ t₁ ⟧ ρ ≡ ⟦ t₂ ⟧ ρ) →
      t₁ ≈ t₂

  ≈-refl : Reflexive _≈_
  ≈-refl = ext (λ ρ → ≡-refl)

  ≈-sym : Symmetric _≈_
  ≈-sym (ext ≈) = ext (λ ρ → ≡-sym (≈ ρ))

  ≈-trans : Transitive _≈_
  ≈-trans (ext ≈₁) (ext ≈₂) = ext (λ ρ → ≡-trans (≈₁ ρ) (≈₂ ρ))

  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

≈-setoid : Context → Type → Setoid _ _
≈-setoid Γ τ = record
  { Carrier       = Term Γ τ
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

≈-app : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term Γ (τ₁ ⇒ τ₂)} {t₃ t₄ : Term Γ τ₁} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → app t₁ t₃ ≈ app t₂ t₄
≈-app (ext ≈₁) (ext ≈₂) = ext (λ ρ →
  ≡-cong₂ (λ x y → x y) (≈₁ ρ) (≈₂ ρ))

≈-abs : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term (τ₁ • Γ) τ₂} →
  t₁ ≈ t₂ → abs t₁ ≈ abs t₂
≈-abs (ext ≈) = ext (λ ρ →
  ext (λ v → ≈ (v • ρ)))

≈-Δ : ∀ {τ Γ} {t₁ t₂ : Term Γ τ} →
  t₁ ≈ t₂ → Δ t₁ ≈ Δ t₂
≈-Δ (ext ≈) = ext (λ ρ → ≡-diff (≈ (update ρ)) (≈ (ignore ρ)))

module ≈-Reasoning where
  module _ {Γ : Context} {τ : Type} where
    open EqR (≈-setoid Γ τ) public
      hiding (_≡⟨_⟩_)

≈-consistent : ¬ (∀ {Γ τ} (t₁ t₂ : Term Γ τ) → t₁ ≈ t₂)
≈-consistent H with H {∅} true false
... | ext x with x ∅
... | ()

-- LIFTING terms into Δ-Contexts

lift-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) τ
lift-var this = that this
lift-var (that x) = that (that (lift-var x))

lift-var′ : ∀ {Γ τ} → (Γ′ : Prefix Γ) → Var Γ τ → Var (Δ-Context′ Γ Γ′) τ
lift-var′ ∅ x = lift-var x
lift-var′ (τ • Γ′) this = this
lift-var′ (τ • Γ′) (that x) = that (lift-var′ Γ′ x)

lift-term′ : ∀ {Γ τ} → (Γ′ : Prefix Γ) → Term Γ τ → Term (Δ-Context′ Γ Γ′) τ
lift-term′ Γ′ (abs t) = abs (lift-term′ (_ • Γ′) t)
lift-term′ Γ′ (app t₁ t₂) = app (lift-term′ Γ′ t₁) (lift-term′ Γ′ t₂)
lift-term′ Γ′ (var x) = var (lift-var′ Γ′ x)
lift-term′ Γ′ true = true
lift-term′ Γ′ false = false
lift-term′ Γ′ (if t₁ t₂ t₃) = if (lift-term′ Γ′ t₁) (lift-term′ Γ′ t₂) (lift-term′ Γ′ t₃)
lift-term′ Γ′ (Δ t) = {!!}

lift-term : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) τ
lift-term = lift-term′ ∅

-- PROPERTIES of lift-term

lift-var-ignore : ∀ {Γ τ} (ρ : ⟦ Δ-Context Γ ⟧) (x : Var Γ τ) →
  ⟦ lift-var x ⟧ ρ ≡ ⟦ x ⟧ (ignore ρ)
lift-var-ignore (v • dv • ρ) this = ≡-refl
lift-var-ignore (v • dv • ρ) (that x) = lift-var-ignore ρ x

lift-var-ignore′ : ∀ {Γ τ} →
  (Γ′ : Prefix Γ) (ρ : ⟦ Δ-Context′ Γ Γ′ ⟧) (x : Var Γ τ) →
  ⟦ lift-var′ Γ′ x ⟧ ρ ≡ ⟦ x ⟧ (ignore′ Γ′ ρ)
lift-var-ignore′ ∅ ρ x = lift-var-ignore ρ x
lift-var-ignore′ (τ • Γ′) (v • ρ) this = ≡-refl
lift-var-ignore′ (τ • Γ′) (v • ρ) (that x) = lift-var-ignore′ Γ′ ρ x

lift-term-ignore′ : ∀ {Γ τ} →
  (Γ′ : Prefix Γ) {ρ : ⟦ Δ-Context′  Γ Γ′ ⟧} (t : Term Γ τ) →
  ⟦ lift-term′ Γ′ t ⟧ ρ ≡ ⟦ t ⟧ (ignore′ Γ′ ρ)
lift-term-ignore′ Γ′ (abs t) =
  ext (λ v → lift-term-ignore′ (_ • Γ′) t)
lift-term-ignore′ Γ′ (app t₁ t₂) =
  ≡-app (lift-term-ignore′ Γ′ t₁) (lift-term-ignore′ Γ′ t₂)
lift-term-ignore′ Γ′ (var x) = lift-var-ignore′ Γ′ _ x
lift-term-ignore′ Γ′ true = ≡-refl
lift-term-ignore′ Γ′ false = ≡-refl
lift-term-ignore′ Γ′ {ρ} (if t₁ t₂ t₃)
  with ⟦ lift-term′ Γ′ t₁ ⟧ ρ
     | ⟦ t₁ ⟧ (ignore′ Γ′ ρ)
     | lift-term-ignore′ Γ′ {ρ} t₁
... | true | true | bool = lift-term-ignore′ Γ′ t₂
... | false | false | bool = lift-term-ignore′ Γ′ t₃
lift-term-ignore′ Γ′ (Δ t) = {!!}

lift-term-ignore : ∀ {Γ τ} {ρ : ⟦ Δ-Context Γ ⟧} (t : Term Γ τ) →
  ⟦ lift-term t ⟧ ρ ≡ ⟦ t ⟧ (ignore ρ)
lift-term-ignore = lift-term-ignore′ ∅


-- PROPERTIES of Δ

Δ-abs : ∀ {Γ τ₁ τ₂} (t : Term (τ₁ • Γ) τ₂) →
  Δ (abs t) ≈ abs (abs (Δ t))
Δ-abs t = ext (λ ρ → ≡-refl)

Δ-app : ∀ {Γ τ₁ τ₂} (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) →
  Δ (app t₁ t₂) ≈ app (app (Δ t₁) (lift-term t₂)) (Δ t₂)
Δ-app t₁ t₂ = ≈-sym (ext (λ ρ →
  begin
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ lift-term t₂ ⟧ ρ)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ lift-term t₂ ⟧ ρ))
  ≡⟨ ≡-cong
       (λ x →
          diff
          (⟦ t₁ ⟧ (update ρ)
           (apply (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) x))
          (⟦ t₁ ⟧ (ignore ρ) x))
       (lift-term-ignore {ρ = ρ} t₂) ⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ t₂ ⟧ (ignore ρ))))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ≡⟨  ≡-cong
       (λ x →
          diff (⟦ t₁ ⟧ (update ρ) x) (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ))))
       (apply-diff (⟦ t₂ ⟧ (ignore ρ)) (⟦ t₂ ⟧ (update ρ)))  ⟩
    diff
      (⟦ t₁ ⟧ (update ρ) (⟦ t₂ ⟧ (update ρ)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ∎)) where open ≡-Reasoning

-- SYMBOLIC DERIVATION

derive-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
derive-var this = this
derive-var (that x) = that (that (derive-var x))

derive-term : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) (Δ-Type τ)
derive-term (abs t) = abs (abs (derive-term t))
derive-term (app t₁ t₂) = app (app (derive-term t₁) (lift-term t₂)) (derive-term t₂)
derive-term (var x) = var (derive-var x)
derive-term true = false
derive-term false = false
derive-term (if t₁ t₂ t₃) = {!!}
derive-term (Δ t) = Δ (derive-term t)

-- CORRECTNESS of derivation

derive-var-correct : ∀ {Γ τ} → (ρ : ⟦ Δ-Context Γ ⟧) → (x : Var Γ τ) →
  diff (⟦ x ⟧ (update ρ)) (⟦ x ⟧ (ignore ρ)) ≡
  ⟦ derive-var x ⟧ ρ
derive-var-correct (dv • v • ρ) this = diff-apply dv v
derive-var-correct (dv • v • ρ) (that x) = derive-var-correct ρ x

derive-term-correct : ∀ {Γ τ} → (t : Term Γ τ) →
   Δ t ≈ derive-term t
derive-term-correct {Γ} (abs t) =
  begin
    Δ (abs t)
  ≈⟨ Δ-abs t ⟩
    abs (abs (Δ t))
  ≈⟨ ≈-abs (≈-abs (derive-term-correct t)) ⟩
    abs (abs (derive-term t))
  ≈⟨ ≈-refl ⟩
    derive-term (abs t)
  ∎ where open ≈-Reasoning
derive-term-correct (app t₁ t₂) =
  begin
    Δ (app t₁ t₂)
  ≈⟨ Δ-app t₁ t₂ ⟩
    app (app (Δ t₁) (lift-term t₂)) (Δ t₂)
  ≈⟨ ≈-app (≈-app (derive-term-correct t₁) ≈-refl) (derive-term-correct t₂) ⟩
    app (app (derive-term t₁) (lift-term t₂)) (derive-term t₂)
  ≈⟨ ≈-refl ⟩
    derive-term (app t₁ t₂)
  ∎ where open ≈-Reasoning
derive-term-correct (var x) = ext (λ ρ → derive-var-correct ρ x)
derive-term-correct true = ext (λ ρ → ≡-refl)
derive-term-correct false = ext (λ ρ → ≡-refl)
derive-term-correct (if t₁ t₂ t₃) = {!!}
derive-term-correct (Δ t) = ≈-Δ (derive-term-correct t)

-- NATURAL SEMANTICS

-- (without support for Δ for now)

-- Syntax

data Env : Context → Set
data Val : Type → Set

data Val where
  ⟨abs_,_⟩ : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) (ρ : Env Γ) → Val (τ₁ ⇒ τ₂)

data Env where
  ∅ : Env ∅
  _•_ : ∀ {Γ τ} → Val τ → Env Γ → Env (τ • Γ)

-- Lookup

infixr 8 _⊢_↓_ _⊢_↦_

data _⊢_↦_ : ∀ {Γ τ} → Env Γ → Var Γ τ → Val τ → Set where
  this : ∀ {Γ τ} {ρ : Env Γ} {v : Val τ} →
    v • ρ ⊢ this ↦ v
  that : ∀ {Γ τ₁ τ₂ x} {ρ : Env Γ} {v₁ : Val τ₁} {v₂ : Val τ₂} →
    ρ ⊢ x ↦ v₂ →
    v₁ • ρ ⊢ that x ↦ v₂

-- Reduction

data _⊢_↓_ : ∀ {Γ τ} → Env Γ → Term Γ τ → Val τ → Set where
  abs : ∀ {Γ τ₁ τ₂ ρ} {t : Term (τ₁ • Γ) τ₂} →
    ρ ⊢ abs t ↓ ⟨abs t , ρ ⟩
  app : ∀ {Γ Γ′ τ₁ τ₂ ρ ρ′ v₂ v′} {t₁ : Term Γ (τ₁ ⇒ τ₂)} {t₂ : Term Γ τ₁} {t′ : Term (τ₁ • Γ′) τ₂} →
    ρ ⊢ t₁ ↓ ⟨abs t′ , ρ′ ⟩ →
    ρ ⊢ t₂ ↓ v₂ →
    v₂ • ρ′ ⊢ t′ ↓ v′ →
    ρ ⊢ app t₁ t₂ ↓ v′
  var : ∀ {Γ τ x} {ρ : Env Γ} {v : Val τ}→
    ρ ⊢ x ↦ v →
    ρ ⊢ var x ↓ v

-- SOUNDNESS of natural semantics

⟦_⟧Env : ∀ {Γ} → Env Γ → ⟦ Γ ⟧
⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ ⟨abs t , ρ ⟩ ⟧Val = λ v → ⟦ t ⟧ (v • ⟦ ρ ⟧Env)

meaningOfEnv : ∀ {Γ} → Meaning (Env Γ)
meaningOfEnv = meaning ⟦_⟧Env

meaningOfVal : ∀ {τ} → Meaning (Val τ)
meaningOfVal = meaning ⟦_⟧Val

↦-sound : ∀ {Γ τ ρ v} {x : Var Γ τ} →
  ρ ⊢ x ↦ v →
  ⟦ x ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↦-sound this = ≡-refl
↦-sound (that ↦) = ↦-sound ↦

↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
  ρ ⊢ t ↓ v →
  ⟦ t ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↓-sound abs = ≡-refl
↓-sound (app ↓₁ ↓₂ ↓′) =
  ≡-trans
    (≡-cong₂ (λ x y → x y) (↓-sound ↓₁) (↓-sound ↓₂))
    (↓-sound ↓′)
↓-sound (var ↦) = ↦-sound ↦

-- WEAKENING

-- Weaken a term to a super context

{-
weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken {Γ₁} {Γ₂} (abs  {τ₁ = τ} t) = abs (weaken {τ • Γ₁} {Γ₂} t)
weaken {Γ₁} {Γ₂} (app t₁ t₂) = app (weaken {Γ₁} {Γ₂} t₁) (weaken {Γ₁} {Γ₂} t₂)
weaken {Γ₁} {Γ₂} (var x) = var (lift {Γ₁} {Γ₂} x)
weaken {Γ₁} {Γ₂} (Δ t) = ?
-}
