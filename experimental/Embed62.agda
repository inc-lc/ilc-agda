module Embed62 where

open import TaggedDeltaTypes
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

Δ-Type : Type → Type
Δ-Type nats = (nats ⇒ nats ⇒ nats) ⇒ nats -- Church pairs
Δ-Type bags = bags
Δ-Type (σ ⇒ τ) = σ ⇒ Δ-Type σ ⇒ Δ-Type τ

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ

⟦fst⟧ : ∀ {A : Set} → A → A → A
⟦fst⟧ a b = a
⟦snd⟧ : ∀ {A : Set} → A → A → A
⟦snd⟧ a b = b

translate : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ΔVal τ
translate {nats} dn = dn ⟦fst⟧ , dn ⟦snd⟧
translate {bags} db = db
translate {σ ⇒ τ} df = λ v dv R[v,dv] → translate (df v {!dv!})
-- TODO figure out what to do to dv to put it in the hole

consistent : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → Set
consistent {∅} ∅ = EmptySet
consistent {τ • Γ} (dv • v • ρ) = couple (valid v (translate dv)) (consistent ρ)

recall : ∀ {Γ} (ρ : ⟦ Δ-Context Γ ⟧) (γ : consistent ρ)  → ΔEnv Γ
recall {∅} ∅ ∅ = ∅
recall {τ • Γ} (dv • v • ρ) (cons R[v,dv] γ _ _) = {!!}

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ Δ-Context Γ
Γ≼ΔΓ {∅} = ∅≼∅
Γ≼ΔΓ {τ • Γ} = drop Δ-Type τ • keep τ • Γ≼ΔΓ

weak : ∀ {τ Γ} → Term Γ τ → Term (Δ-Context Γ) τ
weak = weaken Γ≼ΔΓ

deriveVar : ∀ {τ Γ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

absurd : ∀ {A B : Set} → A → A → B → B
absurd _ _ b = b

fst : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ τ)
fst = abs (abs (var (that this)))
snd : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ τ)
snd = abs (abs (var this))

difff : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)
apply : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ

apply {nats} dt t = app dt snd
apply {bags} dt t = union t dt
apply {σ ⇒ τ} dt t = abs (apply
  (app (app (weaken (drop _ • Γ≼Γ) dt)
    (var this)) (difff (var this) (var this)))
  (app (weaken (drop _ • Γ≼Γ) t) (var this)))

difff {nats} s t = abs (app (app (var this)
  (weaken (drop _ • Γ≼Γ) s)) (weaken (drop _ • Γ≼Γ) t))
difff {bags} s t = diff s t
difff {σ ⇒ τ} s t = abs (abs (difff
  (app (weaken (drop _ • drop _ • Γ≼Γ) s)
    (apply (var this) (var (that this))))
  (app (weaken (drop _ • drop _ • Γ≼Γ) t) (var (that this)))))

embed : ∀ {τ Γ} → ΔTerm Γ τ → Term (Δ-Context Γ) (Δ-Type τ)
embed (Δnat old new) = abs (app (app (var this) (nat old)) (nat new))
embed (Δbag db) = bag db
embed (Δvar x) = var (deriveVar x)
embed (Δabs dt) = abs (abs (embed dt))
embed (Δapp ds t dt) = app (app (embed ds) (weak t)) (embed dt)
embed (Δadd ds dt) = abs (app (app (var this)
  (add (app (weaken (drop _ • Γ≼Γ) (embed ds)) fst)
       (app (weaken (drop _ • Γ≼Γ) (embed dt)) fst)))
  (add (app (weaken (drop _ • Γ≼Γ) (embed ds)) snd)
       (app (weaken (drop _ • Γ≼Γ) (embed dt)) snd)))
embed (Δmap₀ s ds t dt) = diff
  (map (apply (embed ds) (weak s)) (apply (embed dt) (weak t)))
  (weak (map s t))
embed (Δmap₁ s dt) = map (weak s) (embed dt)
embed (Δunion ds dt) = union (embed ds) (embed dt)
embed (Δdiff ds dt) = diff (embed ds) (embed dt)

-- embed-correct : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv}

