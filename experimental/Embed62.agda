module Embed62 where

open import TaggedDeltaTypes
open import ExplicitNil using (ext³)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat

Δ-Type : Type → Type
Δ-Type nats = (nats ⇒ nats ⇒ nats) ⇒ nats -- Church pairs
Δ-Type bags = bags
Δ-Type (σ ⇒ τ) = σ ⇒ Δ-Type σ ⇒ Δ-Type τ

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ Δ-Context Γ
Γ≼ΔΓ {∅} = ∅≼∅
Γ≼ΔΓ {τ • Γ} = drop Δ-Type τ • keep τ • Γ≼ΔΓ

weak : ∀ {τ Γ} → Term Γ τ → Term (Δ-Context Γ) τ
weak = weaken Γ≼ΔΓ

deriveVar : ∀ {τ Γ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

absurd! : ∀ {A B : Set} → A → A → B → B
absurd! _ _ b = b

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

⟦fst⟧ : ∀ {A : Set} → A → A → A
⟦fst⟧ a b = a
⟦snd⟧ : ∀ {A : Set} → A → A → A
⟦snd⟧ a b = b

_≈_ : ∀ {τ} → ΔVal τ → ⟦ Δ-Type τ ⟧ → Set
_≈_ {nats} (old , new) v = old ≡ v ⟦fst⟧ × new ≡ v ⟦snd⟧
_≈_ {bags} u v = u ≡ v
_≈_ {σ ⇒ τ} u v = 
  (w : ⟦ σ ⟧) (dw : ΔVal σ) (dw′ : ⟦ Δ-Type σ ⟧)
  (R[w,dw] : valid w dw) (eq : dw ≈ dw′) →
  u w dw R[w,dw] ≈ v w dw′

infix 4 _≈_

compatible : ∀ {Γ} → ΔEnv Γ → ⟦ Δ-Context Γ ⟧ → Set
compatible {∅} ∅ ∅ = EmptySet
compatible {τ • Γ} (cons v dv _ ρ) (dv′ • v′ • ρ′) =
  triple (v ≡ v′) (dv ≈ dv′) (compatible ρ ρ′)

deriveVar-correct : ∀ {τ Γ} {x : Var Γ τ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} {C : compatible ρ ρ′} →
  ⟦ x ⟧ΔVar ρ ≈ ⟦ deriveVar x ⟧ ρ′

deriveVar-correct {x = this} -- pattern-matching on ρ, ρ′ NOT optional
  {cons _ _ _ _} {_ • _ • _} {cons _ dv≈dv′ _ _} = dv≈dv′
deriveVar-correct {x = that y}
  {cons _ _ _ ρ} {_ • _ • ρ′} {cons _ _ C _} =
  deriveVar-correct {x = y} {ρ} {ρ′} {C}

weak-id : ∀ {Γ} {ρ : ⟦ Γ ⟧} → ⟦ Γ≼Γ {Γ} ⟧ ρ ≡ ρ
weak-id {∅} {∅} = refl
weak-id {τ • Γ} {v • ρ} = cong₂ _•_ {x = v} refl (weak-id {Γ} {ρ})

weak-eq : ∀ {Γ} {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧}
  (C : compatible ρ ρ′) → ignore ρ ≡ ⟦ Γ≼ΔΓ ⟧ ρ′

weak-eq {∅} {∅} {∅} _ = refl
weak-eq {τ • Γ} {cons v dv _ ρ} {dv′ • v′ • ρ′} (cons v≡v′ _ C _) =
  cong₂ _•_ v≡v′ (weak-eq C)

weak-eq-term : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} (C : compatible ρ ρ′) →
  ⟦ t ⟧ (ignore ρ) ≡ ⟦ weaken Γ≼ΔΓ t ⟧ ρ′

weak-eq-term t {ρ} {ρ′} C =
  trans (cong ⟦ t ⟧ (weak-eq C)) (sym (weaken-sound t ρ′))

weaken-once : ∀ {τ Γ σ} {t : Term Γ τ} {v : ⟦ σ ⟧} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ≡ ⟦ weaken (drop σ • Γ≼Γ) t ⟧ (v • ρ)

weaken-once {t = t} {v} {ρ} = trans
  (cong ⟦ t ⟧ (sym weak-id))
  (sym (weaken-sound t (v • ρ)))

embed-correct : ∀ {τ Γ}
  {dt : ΔTerm Γ τ}
  {ρ : ΔEnv Γ} {V : dt is-valid-for ρ}
  {ρ′ : ⟦ Δ-Context Γ ⟧} {C : compatible ρ ρ′} →
  ⟦ dt ⟧Δ ρ V ≈ ⟦ embed dt ⟧ ρ′

embed-correct {dt = Δnat old new} = refl , refl

embed-correct {dt = Δbag db} = refl

embed-correct {dt = Δvar x} {ρ} {ρ′ = ρ′} {C} =
  deriveVar-correct {x = x} {ρ} {ρ′} {C}

embed-correct {dt = Δadd ds dt} {ρ} {V} {ρ′} {C} =
  let
    s00 , s01 = ⟦ ds ⟧Δ ρ (car V)
    t00 , t01 = ⟦ dt ⟧Δ ρ (cadr V)
    s10 = ⟦ embed ds ⟧ ρ′ ⟦fst⟧
    s11 = ⟦ embed ds ⟧ ρ′ ⟦snd⟧
    t10 = ⟦ embed dt ⟧ ρ′ ⟦fst⟧
    t11 = ⟦ embed dt ⟧ ρ′ ⟦snd⟧
    rec-s = embed-correct {dt = ds} {ρ} {car V} {ρ′} {C}
    rec-t = embed-correct {dt = dt} {ρ} {cadr V} {ρ′} {C}
  in
    
    (begin
      s00 + t00
    ≡⟨ cong₂ _+_ (proj₁ rec-s) (proj₁ rec-t) ⟩
      s10 + t10
    ≡⟨ cong₂ _+_
        (cong (λ x → ⟦ embed ds ⟧ x ⟦fst⟧) (sym weak-id))
        (cong (λ x → ⟦ embed dt ⟧ x ⟦fst⟧) (sym weak-id)) ⟩
      ⟦ embed ds ⟧ (⟦ drop _ • Γ≼Γ ⟧ (⟦fst⟧ {ℕ} • ρ′)) ⟦fst⟧ +
      ⟦ embed dt ⟧ (⟦ drop _ • Γ≼Γ ⟧ (⟦fst⟧ {ℕ} • ρ′)) ⟦fst⟧
    ≡⟨ cong₂ _+_
      (cong (λ f → f ⟦fst⟧) (sym (weaken-sound (embed ds) (⟦fst⟧ • ρ′))))
      (cong (λ f → f ⟦fst⟧) (sym (weaken-sound (embed dt) (⟦fst⟧ • ρ′)))) ⟩
      ⟦ weaken (drop _ • Γ≼Γ) (embed ds) ⟧ (⟦fst⟧ • ρ′) ⟦fst⟧ +
      ⟦ weaken (drop _ • Γ≼Γ) (embed dt) ⟧ (⟦fst⟧ • ρ′) ⟦fst⟧
    ∎)
    ,
    (begin
      s01 + t01
    ≡⟨ cong₂ _+_ (proj₂ rec-s) (proj₂ rec-t) ⟩
      s11 + t11
    ≡⟨ cong₂ _+_
        (cong (λ x → ⟦ embed ds ⟧ x ⟦snd⟧) (sym weak-id))
        (cong (λ x → ⟦ embed dt ⟧ x ⟦snd⟧) (sym weak-id)) ⟩
      ⟦ embed ds ⟧ (⟦ drop _ • Γ≼Γ ⟧ (⟦snd⟧ {ℕ} • ρ′)) ⟦snd⟧ +
      ⟦ embed dt ⟧ (⟦ drop _ • Γ≼Γ ⟧ (⟦snd⟧ {ℕ} • ρ′)) ⟦snd⟧
    ≡⟨ cong₂ _+_
      (cong (λ f → f ⟦snd⟧) (sym (weaken-sound (embed ds) (⟦snd⟧ • ρ′))))
      (cong (λ f → f ⟦snd⟧) (sym (weaken-sound (embed dt) (⟦snd⟧ • ρ′)))) ⟩
      ⟦ weaken (drop _ • Γ≼Γ) (embed ds) ⟧ (⟦snd⟧ • ρ′) ⟦snd⟧ +
      ⟦ weaken (drop _ • Γ≼Γ) (embed dt) ⟧ (⟦snd⟧ • ρ′) ⟦snd⟧
    ∎)
  where open ≡-Reasoning

embed-correct {dt = Δunion ds dt} {ρ} {V} {ρ′} {C} = cong₂ _++_
  (embed-correct {dt = ds} {ρ} {car  V} {ρ′} {C})
  (embed-correct {dt = dt} {ρ} {cadr V} {ρ′} {C})

embed-correct {dt = Δdiff ds dt} {ρ} {V} {ρ′} {C} = cong₂ _\\_
  (embed-correct {dt = ds} {ρ} {car  V} {ρ′} {C})
  (embed-correct {dt = dt} {ρ} {cadr V} {ρ′} {C})

embed-correct {dt = Δmap₁ s dt} {ρ} {V} {ρ′} {C} = cong₂ mapBag
  (weak-eq-term s C)
  (embed-correct {dt = dt} {ρ} {car V} {ρ′} {C})

embed-correct {dt = Δmap₀ s ds t dt} {ρ} {V} {ρ′} {C} = cong₂ _\\_
  (cong₂ mapBag
    (extensionality (λ v →
    begin
      proj₂ (⟦ ds ⟧Δ ρ (car V) v (v , v) refl)
    ≡⟨ proj₂ (embed-correct {dt = ds} {ρ} {car V} {ρ′} {C}
        v (v , v) (λ f → f v v) refl (refl , refl)) ⟩
      ⟦ embed ds ⟧ ρ′ v (λ f → f v v) ⟦snd⟧
    ≡⟨ cong (λ hole → hole v (λ f → f v v) ⟦snd⟧)
        (weaken-once {t = embed ds} {v} {ρ′}) ⟩
      ⟦ weaken (drop _ • Γ≼Γ) (embed ds) ⟧ (v • ρ′) v (λ f → f v v) ⟦snd⟧
    ∎))
    (cong₂ _++_
      (weak-eq-term t C)
      (embed-correct {dt = dt} {ρ} {cadr V} {ρ′} {C})))
  (cong₂ mapBag (weak-eq-term s C) (weak-eq-term t C))
  where open ≡-Reasoning

embed-correct {dt = Δapp ds t dt} {ρ} {cons vds vdt R[t,dt] _} {ρ′} {C}
  rewrite sym (weak-eq-term t C) =
  embed-correct {dt = ds} {ρ} {vds} {ρ′} {C}
    (⟦ t ⟧Term (ignore ρ)) (⟦ dt ⟧Δ ρ vdt) (⟦ embed dt ⟧Term ρ′)
    R[t,dt] (embed-correct {dt = dt} {ρ} {vdt} {ρ′} {C})

embed-correct {dt = Δabs dt} {ρ} {V} {ρ′} {C} = λ w dw dw′ R[w,dw] dw≈dw′ →
  embed-correct {dt = dt}
    {cons w dw R[w,dw] ρ} {V w dw R[w,dw]}
    {dw′ • w • ρ′} {cons refl dw≈dw′ C tt}
