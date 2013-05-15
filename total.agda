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

open import meaning

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

-- Denotational Semantics

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

-- Value Equivalence

data _≡_ : ∀ {τ} → (v₁ v₂ : ⟦ τ ⟧) → Set where
  ext : ∀ {τ₁ τ₂} {f₁ f₂ : ⟦ τ₁ ⇒ τ₂ ⟧} →
    (∀ v → f₁ v ≡ f₂ v) →
    f₁ ≡ f₂

≡-refl : ∀ {τ} {v : ⟦ τ ⟧} →
  v ≡ v
≡-refl {τ₁ ⇒ τ₂} = ext (λ v → ≡-refl)

≡-sym : ∀ {τ} {v₁ v₂ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₁
≡-sym {τ₁ ⇒ τ₂} (ext ≡) = ext (λ v → ≡-sym (≡ v))

≡-trans : ∀ {τ} {v₁ v₂ v₃ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₃ → v₁ ≡ v₃
≡-trans {τ₁ ⇒ τ₂} {f} (ext ≡₁) (ext ≡₂) =
  ext (λ v → ≡-trans (≡₁ v) (≡₂ v))

≡-cong : ∀ {τ₂ τ₁ v₁ v₂} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧) →
  v₁ ≡ v₂ → f v₁ ≡ f v₂
≡-cong {τ₁ ⇒ τ₂} f ≡ = ext (λ v → ≡-cong (λ x → f x v) ≡)

≡-cong₂ : ∀ {τ₃ τ₁ τ₂ v₁ v₂ v₃ v₄} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ₃ ⟧) →
  v₁ ≡ v₂ → v₃ ≡ v₄ → f v₁ v₃ ≡ f v₂ v₄
≡-cong₂ {τ₁ ⇒ τ₂} f ≡₁ ≡₂ = ext (λ v → ≡-cong₂ (λ x y → f x y v) ≡₁ ≡₂)

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

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂

derive : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
apply : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧ → ⟦ τ ⟧
diff : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧

diff {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → diff (f₁ (apply dv v)) (f₂ v)

derive {τ₁ ⇒ τ₂} f = λ v dv → diff (f (apply dv v)) (f v)

apply {τ₁ ⇒ τ₂} df f = λ v → apply (df v (derive v)) (f v)

compose : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧
compose {τ₁ ⇒ τ₂} df₁ df₂ = λ v dv → compose (df₁ v dv) (df₂ v dv)

-- PROPERTIES of changes

diff-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  diff v v ≡ derive v
diff-derive {τ₁ ⇒ τ₂} v = ≡-refl

diff-apply : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
  diff (apply dv v) v ≡ dv
diff-apply {τ₁ ⇒ τ₂} df f = ext (λ v → ext (λ dv →
  {!!}))

apply-diff : ∀ {τ} (v₁ v₂ : ⟦ τ ⟧) →
  apply (diff v₂ v₁) v₁ ≡ v₂
apply-diff {τ₁ ⇒ τ₂} f₁ f₂ = ext (λ v → apply-diff (f₁ v) (f₂ v))

apply-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  apply (derive v) v ≡ v
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

apply-compose : ∀ {τ} (v : ⟦ τ ⟧) (dv₁ dv₂ : ⟦ Δ-Type τ ⟧) →
  apply (compose dv₁ dv₂) v ≡ apply dv₁ (apply dv₂ v)
apply-compose {τ₁ ⇒ τ₂} f df₁ df₂ = ext (λ v →
  apply-compose (f v) (df₂ v (derive v)) (df₂ v (derive v)))

compose-assoc : ∀ {τ} (dv₁ dv₂ dv₃ : ⟦ Δ-Type τ ⟧) →
  compose dv₁ (compose dv₂ dv₃) ≡ compose (compose dv₁ dv₂) dv₃
compose-assoc {τ₁ ⇒ τ₂} df₁ df₂ df₃ = ext (λ v → ext (λ dv →
  compose-assoc (df₁ v dv) (df₂ v dv) (df₃ v dv)))

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

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  -- `Δ t` describes how t changes if its free variables or arguments change
  Δ : ∀ {Γ τ} → (t : Term Γ τ) → Term (Δ-Context Γ) (Δ-Type τ)

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
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
≈-Δ {τ₁ ⇒ τ₂} (ext ≈) = ext (λ ρ → ext (λ v → ext (λ dv →
  ≡-cong₂ (λ x y → diff (x v) (y v)) (≈ (update ρ)) (≈ (ignore ρ)))))

module ≈-Reasoning where
  module _ {Γ : Context} {τ : Type} where
    open EqR (≈-setoid Γ τ) public
      hiding (_≡⟨_⟩_)

-- LIFTING terms into Δ-Contexts

lift-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) τ
lift-var this = that this
lift-var (that x) = that (that (lift-var x))

lift-term : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) τ
lift-term (abs t) = abs {!!}
lift-term (app t₁ t₂) = app (lift-term t₁) (lift-term t₂)
lift-term (var x) = var (lift-var x)
lift-term (Δ t) = Δ (lift-term t)

-- PROPERTIES of lift-term

lift-var-ignore : ∀ {Γ τ} (ρ : ⟦ Δ-Context Γ ⟧) (x : Var Γ τ) →
  ⟦ lift-var x ⟧ ρ ≡ ⟦ x ⟧ (ignore ρ)
lift-var-ignore (v • dv • ρ) this = ≡-refl
lift-var-ignore (v • dv • ρ) (that x) = lift-var-ignore ρ x

lift-term-ignore : ∀ {Γ τ} {ρ : ⟦ Δ-Context Γ ⟧} (t : Term Γ τ) →
  ⟦ lift-term t ⟧ ρ ≡ ⟦ t ⟧ (ignore ρ)
lift-term-ignore (abs t) = {!!}
lift-term-ignore (app t₁ t₂) = ≡-app (lift-term-ignore t₁) (lift-term-ignore t₂)
lift-term-ignore (var x) = lift-var-ignore _ x
lift-term-ignore (Δ t) = {!!}

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
  ≡⟨ ≡-cong
       (λ x →
          diff (⟦ t₁ ⟧ (update ρ) x) (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ))))
       (apply-diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) ⟩
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
