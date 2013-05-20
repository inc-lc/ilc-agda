module total where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * Δ e describes how e changes when its free variables or its arguments change
--   * denotational semantics including semantics of changes
--
-- Note that Δ is *not* the same as the ∂ operator in
-- definition/intro.tex. See discussion at:
--
--   https://github.com/ps-mr/ilc/pull/34#discussion_r4290325
--
-- Work in Progress:
--   * lemmas about behavior of changes
--   * lemmas about behavior of Δ
--   * correctness proof for symbolic derivation

open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence

open import Changes
open import ChangeContexts

-- DEFINITION of valid changes via a logical relation

{-
What I wanted to write:

data ValidΔ : {T : Type} → (v : ⟦ T ⟧) → (dv : ⟦ Δ-Type T ⟧) → Set where
  base : (v : ⟦ bool ⟧) → (dv : ⟦ Δ-Type bool ⟧) → ValidΔ v dv
  fun : ∀ {S T} → (f : ⟦ S ⇒ T ⟧) → (df : ⟦ Δ-Type (S ⇒ T) ⟧) →
    (∀ (s : ⟦ S ⟧) ds (valid : ValidΔ s ds) → (ValidΔ (f s) (df s ds)) × ((apply df f) (apply ds s) ≡ apply (df s ds) (f s))) → 
    ValidΔ f df
-}
-- What I had to write:
valid-Δ : {T : Type} → ⟦ T ⟧ → ⟦ Δ-Type T ⟧ → Set
valid-Δ {bool} v dv = ⊤
valid-Δ {S ⇒ T} f df =
  ∀ (s : ⟦ S ⟧) ds (valid-w : valid-Δ s ds) →
    valid-Δ (f s) (df s ds) ×
    (apply df f) (apply ds s) ≡ apply (df s ds) (f s)

-- LIFTING terms into Δ-Contexts

lift-term : ∀ {Γ₁ Γ₂ τ} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} → Term Γ₁ τ → Term Γ₂ τ
lift-term {Γ₁} {Γ₂} {{Γ′}} = weaken (≼-trans ≼-Δ-Context Γ′)

-- PROPERTIES of lift-term

lift-term-ignore : ∀ {Γ₁ Γ₂ τ} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} {ρ : ⟦ Γ₂ ⟧} (t : Term Γ₁ τ) →
  ⟦ lift-term {{Γ′}} t ⟧ ρ ≡ ⟦ t ⟧ (ignore (⟦ Γ′ ⟧ ρ))
lift-term-ignore {{Γ′}} {ρ} t = let Γ″ = ≼-trans ≼-Δ-Context Γ′ in
  begin
    ⟦ lift-term {{Γ′}} t ⟧ ρ
  ≡⟨⟩
    ⟦ weaken Γ″ t ⟧ ρ
  ≡⟨ weaken-sound t ρ ⟩
    ⟦ t ⟧ (⟦ ≼-trans ≼-Δ-Context Γ′ ⟧ ρ)
  ≡⟨ cong (λ x → ⟦ t ⟧ x) (⟦⟧-≼-trans ≼-Δ-Context Γ′ ρ) ⟩
    ⟦ t ⟧Term (⟦ ≼-Δ-Context ⟧≼ (⟦ Γ′ ⟧≼ ρ))
  ≡⟨⟩
    ⟦ t ⟧ (ignore (⟦ Γ′ ⟧ ρ))
  ∎ where open ≡-Reasoning

-- PROPERTIES of Δ

Δ-abs : ∀ {τ₁ τ₂ Γ₁ Γ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t : Term (τ₁ • Γ₁) τ₂) →
  let Γ″ = keep Δ-Type τ₁ • keep τ₁ • Γ′ in
  Δ {{Γ′}} (abs t) ≈ abs (abs (Δ {τ₁ • Γ₁} t))
Δ-abs t = ext-t (λ ρ → refl)

Δ-app : ∀ {Γ₁ Γ₂ τ₁ τ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t₁ : Term Γ₁ (τ₁ ⇒ τ₂)) (t₂ : Term Γ₁ τ₁) →
  Δ {{Γ′}} (app t₁ t₂) ≈ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂)
Δ-app {{Γ′}} t₁ t₂ = ≈-sym (ext-t (λ ρ′ → let ρ = ⟦ Γ′ ⟧ ρ′ in
  begin
    ⟦ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂) ⟧ ρ′
  ≡⟨⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′))
  ≡⟨ ≡-cong
       (λ x →
          diff
          (⟦ t₁ ⟧ (update ρ)
           (apply (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) x))
          (⟦ t₁ ⟧ (ignore ρ) x))
       (lift-term-ignore {{Γ′}} t₂) ⟩
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
  ≡⟨⟩
     ⟦ Δ {{Γ′}} (app t₁ t₂) ⟧ ρ′
  ∎)) where open ≡-Reasoning

-- SYMBOLIC DERIVATION

derive-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
derive-var {τ • Γ} this = this
derive-var {τ • Γ} (that x) = that (that (derive-var x))

_and_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a and b = if a b false

!_ : ∀ {Γ} → Term Γ bool → Term Γ bool
! x = if x false true

-- Term xor
_xor-term_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a xor-term b = if a (! b) b

-- XXX: to finish this, we just need to call lift-term, like in
-- derive-term. Should be easy, just a bit boring.
-- Other problem: in fact, Δ t is not the nil change of t, in this context. That's a problem.
apply-pure-term : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ τ ⇒ τ)
apply-pure-term {bool} = abs (abs (var this xor-term var (that this)))
apply-pure-term {τ₁ ⇒ τ₂} {Γ} = abs (abs (abs (app (app apply-pure-term (app (app (var (that (that this))) (var this)) ({!Δ {Γ} (var this)!}))) (app (var (that this)) (var this)))))
--abs (abs (abs (app (app apply-compose-term (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
-- λdf. λf.  λx.           apply (     df                       x       (Δx))  (     f                 x        )

apply-term : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ
apply-term {τ ⇒ τ₁} = λ df f → app (app apply-pure-term df) f
apply-term {bool} = _xor-term_

diff-term : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)
diff-term {τ ⇒ τ₁} =
  λ f₁ f₂ →
  --λx.  λdx. diff           (     f₁                   (apply      dx         x))                 (f₂                        x)
    abs (abs (diff-term {τ₁} (app (weaken ≼-in-body f₁) (apply-term (var this) (var (that this)))) (app (weaken ≼-in-body f₂) (var (that this)))))
  where
    ≼-in-body = drop (Δ-Type τ) • (drop τ • ≼-refl)

diff-term {bool} = _xor-term_

derive-term : ∀ {Γ₁ Γ₂ τ} → {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} → Term Γ₁ τ → Term Γ₂ (Δ-Type τ)
derive-term {Γ₁} {{Γ′}} (abs {τ} t) = abs (abs (derive-term {τ • Γ₁} {{Γ″}} t))
  where Γ″ = keep Δ-Type τ • keep τ • Γ′
derive-term {{Γ′}} (app t₁ t₂) = app (app (derive-term {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (derive-term {{Γ′}} t₂)
derive-term {{Γ′}} (var x) = var (lift Γ′ (derive-var x))
derive-term {{Γ′}} true = false
derive-term {{Γ′}} false = false
derive-term {{Γ′}} (if c t e) =
  if ((derive-term {{Γ′}} c) and (lift-term {{Γ′}} c))
    (diff-term (apply-term (derive-term {{Γ′}} e) (lift-term {{Γ′}} e)) (lift-term {{Γ′}} t))
    (if ((derive-term {{Γ′}} c) and (lift-term {{Γ′}} (! c)))
      (diff-term (apply-term (derive-term {{Γ′}} t) (lift-term {{Γ′}} t)) (lift-term {{Γ′}} e))
      (if (lift-term {{Γ′}} c)
        (derive-term {{Γ′}} t)
        (derive-term {{Γ′}} e)))
derive-term {{Γ′}} (Δ {{Γ″}} t) = Δ {{Γ′}} (derive-term {{Γ″}} t)

-- CORRECTNESS of derivation

derive-var-correct : ∀ {Γ τ} → (ρ : ⟦ Δ-Context Γ ⟧) → (x : Var Γ τ) →
  diff (⟦ x ⟧ (update ρ)) (⟦ x ⟧ (ignore ρ)) ≡
  ⟦ derive-var x ⟧ ρ
derive-var-correct (dv • v • ρ) this = diff-apply dv v
derive-var-correct (dv • v • ρ) (that x) = derive-var-correct ρ x

derive-term-correct : ∀ {Γ₁ Γ₂ τ} → {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} → (t : Term Γ₁ τ) →
  Δ {{Γ′}} t ≈ derive-term {{Γ′}} t
derive-term-correct {Γ₁} {{Γ′}} (abs {τ} t) =
  begin
     Δ (abs t)
  ≈⟨  Δ-abs t  ⟩
     abs (abs (Δ {τ • Γ₁} t))
  ≈⟨  ≈-abs (≈-abs (derive-term-correct {τ • Γ₁} t))  ⟩
     abs (abs (derive-term {τ • Γ₁} t))
  ≡⟨⟩
     derive-term (abs t)
  ∎ where
      open ≈-Reasoning
      Γ″ = keep Δ-Type τ • keep τ • Γ′
derive-term-correct {Γ₁} {{Γ′}} (app t₁ t₂) =
  begin
    Δ (app t₁ t₂)
  ≈⟨  Δ-app t₁ t₂  ⟩
     app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂)
  ≈⟨  ≈-app (≈-app (derive-term-correct {{Γ′}} t₁) ≈-refl) (derive-term-correct {{Γ′}} t₂)  ⟩
     app (app (derive-term {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (derive-term {{Γ′}} t₂)
  ≡⟨⟩
    derive-term {{Γ′}} (app t₁ t₂)
  ∎ where open ≈-Reasoning
derive-term-correct {Γ₁} {{Γ′}} (var x) = ext-t (λ ρ →
  begin
    ⟦ Δ {{Γ′}} (var x) ⟧ ρ
  ≡⟨⟩
    diff
      (⟦ x ⟧ (update (⟦ Γ′ ⟧ ρ)))
      (⟦ x ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
  ≡⟨  derive-var-correct {Γ₁} (⟦ Γ′ ⟧ ρ) x  ⟩
    ⟦ derive-var x ⟧Var (⟦ Γ′ ⟧ ρ)
  ≡⟨ sym (lift-sound Γ′ (derive-var x) ρ) ⟩
    ⟦ lift Γ′ (derive-var x) ⟧Var ρ
  ∎) where open ≡-Reasoning
derive-term-correct true = ext-t (λ ρ → ≡-refl)
derive-term-correct false = ext-t (λ ρ → ≡-refl)
derive-term-correct (if t₁ t₂ t₃) = {!!}
derive-term-correct (Δ t) = ≈-Δ (derive-term-correct t)
