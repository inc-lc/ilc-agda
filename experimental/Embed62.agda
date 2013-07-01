module Embed62 where

open import TaggedDeltaTypes
open import ExplicitNil using (ext³)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat

natPairVisitor : Type
natPairVisitor = nats ⇒ nats ⇒ nats

Δ-Type : Type → Type
Δ-Type nats = natPairVisitor ⇒ nats -- Church pairs
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

oldFrom newFrom : ∀ {Γ} → Term Γ (Δ-Type nats) → Term Γ nats
oldFrom d = app d fst
newFrom d = app d snd

difff : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)
apply : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ

apply {nats} dt t = app dt snd
apply {bags} dt t = union t dt
apply {σ ⇒ τ} dt t = abs (apply
  (app (app (weaken (drop _ • Γ≼Γ) dt)
    (var this)) (difff (var this) (var this)))
  (app (weaken (drop _ • Γ≼Γ) t) (var this)))

difff {nats} s t = abs (app (app (var this)
  (weaken (drop _ • Γ≼Γ) t)) (weaken (drop _ • Γ≼Γ) s))
difff {bags} s t = diff s t
difff {σ ⇒ τ} s t = abs (abs (difff
  (app (weaken (drop _ • drop _ • Γ≼Γ) s)
    (apply (var this) (var (that this))))
  (app (weaken (drop _ • drop _ • Γ≼Γ) t) (var (that this)))))

natPair : ∀ {Γ} → (old new : Term (natPairVisitor • Γ) nats) → Term Γ (Δ-Type nats)
natPair old new = abs (app (app (var this) old) new)

embed : ∀ {τ Γ} → ΔTerm Γ τ → Term (Δ-Context Γ) (Δ-Type τ)
embed (Δnat old new) = natPair (nat old) (nat new)
embed (Δbag db) = bag db
embed (Δvar x) = var (deriveVar x)
embed (Δabs dt) = abs (abs (embed dt))
embed (Δapp ds t dt) = app (app (embed ds) (weak t)) (embed dt)
embed (Δadd ds dt) = natPair
  (add (oldFrom (embedWeaken ds))
       (oldFrom (embedWeaken dt)))
  (add (newFrom (embedWeaken ds))
       (newFrom (embedWeaken dt)))
  where
    embedWeaken : ∀ {Γ τ} → (d : ΔTerm Γ nats) →
      Term (τ • Δ-Context Γ) (natPairVisitor ⇒ nats)
    embedWeaken d = (weaken (drop _ • Γ≼Γ) (embed d))
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

weaken-twice : ∀ {τ Γ σ₀ σ₁} {t : Term Γ τ}
  {u : ⟦ σ₀ ⟧} {v : ⟦ σ₁ ⟧} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ≡ ⟦ weaken (drop σ₀ • drop σ₁ • Γ≼Γ) t ⟧ (u • v • ρ)

weaken-twice {t = t} {u} {v} {ρ} = trans
  (cong ⟦ t ⟧ (sym weak-id))
  (sym (weaken-sound t (u • v • ρ)))

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

_⊞_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧
_⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
infixl 6 _⊞_ _⊟_ -- as with + - in GHC.Num

_⊞_ {nats}  n dn = dn ⟦snd⟧
_⊞_ {bags}  b db = b ++ db
_⊞_ {σ ⇒ τ} f df = λ v → f v ⊞ df v (v ⊟ v)

_⊟_ {nats} m n = λ f → f n m
_⊟_ {bags} d b = d \\ b
_⊟_ {σ ⇒ τ} g f = λ v dv → g (v ⊞ dv) ⊟ f v

u⊝v≈u⊟v : ∀ {τ : Type} {u v : ⟦ τ ⟧} → u ⊝ v ≈ u ⊟ v

carry-over : ∀ {τ}
  {dv : ΔVal τ} {dv′ : ⟦ Δ-Type τ ⟧} (dv≈dv′ : dv ≈ dv′)
  {v : ⟦ τ ⟧} (R[v,dv] : valid v dv) →
  v ⊕ dv ≡ v ⊞ dv′

u⊝v≈u⊟v {nats} = refl , refl
u⊝v≈u⊟v {bags} = refl
u⊝v≈u⊟v {σ ⇒ τ} {g} {f} = result
  where
  result : ∀ (w : ⟦ σ ⟧) (dw : ΔVal σ) (dw′ : ⟦ Δ-Type σ ⟧)
    (R[w,dw] : valid w dw) (dw≈dw′ : dw ≈ dw′) →
    g (w ⊕ dw) ⊝ f w ≈ g (w ⊞ dw′) ⊟ f w
  result w dw dw′ R[w,dw] dw≈dw′
    rewrite carry-over dw≈dw′ R[w,dw] = u⊝v≈u⊟v
  -- Question: is there anyway not to write the signature
  -- of u⊝v≈u⊟v twice just so as to carry out the rewrite?

carry-over {nats} dv≈dv′ R[v,dv] = proj₂ dv≈dv′
carry-over {bags} dv≈dv′ {v} R[v,dv] = cong (_++_ v) dv≈dv′
carry-over {σ ⇒ τ} {df} {df′} df≈df′ {f} R[f,df] =
  extensionality (λ v → carry-over {τ}
    {df v (v ⊝ v) R[v,u⊝v]} {df′ v (v ⊟ v)}
    (df≈df′ v (v ⊝ v) (v ⊟ v) R[v,u⊝v] u⊝v≈u⊟v)
    {f v}
    (proj₁ (R[f,df] v (v ⊝ v) R[v,u⊝v])))

ignore′ : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
ignore′ {∅} ∅ = ∅
ignore′ {τ • Γ} (dv • v • ρ) = v • ignore′ ρ

update′ : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
update′ {∅} ∅ = ∅
update′ {τ • Γ} (dv • v • ρ) = (v ⊞ dv) • update′ ρ

ignorance : ∀ {Γ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} (C : compatible ρ ρ′) →
  (ignore ρ) ≡ (ignore′ ρ′)

ignorance {∅} {∅} {∅} _ = refl
ignorance {τ • Γ} {cons v dv _ ρ} {dv′ • v′ • ρ′}
  (cons v≡v′ _ C _) = cong₂ _•_ v≡v′ (ignorance C)

-- ... because "updatedness" sounds horrible
actualité : ∀ {Γ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} (C : compatible ρ ρ′) →
  (update ρ) ≡ (update′ ρ′)

actualité {∅} {∅} {∅} _ = refl
actualité {τ • Γ} {cons v dv R[v,dv] ρ} {dv′ • v′ • ρ′}
  (cons v≡v′ dv≈dv′ C _) rewrite v≡v′ =
  cong₂ _•_ (carry-over dv≈dv′ R[v,dv]) (actualité C)

ignore-both : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} (C : compatible ρ ρ′) →
  ⟦ t ⟧ (ignore ρ) ≡ ⟦ t ⟧ (ignore′ ρ′)

ignore-both t C rewrite ignorance C = refl

update-both : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ΔEnv Γ} {ρ′ : ⟦ Δ-Context Γ ⟧} (C : compatible ρ ρ′) →
  ⟦ t ⟧ (update ρ) ≡ ⟦ t ⟧ (update′ ρ′)

update-both t C rewrite actualité C = refl

corollary-closed : ∀ {σ τ} {t : Term ∅ (σ ⇒ τ)}
  {v : ⟦ σ ⟧} {dv : ΔVal σ} {R[v,dv] : valid v dv}
  → ⟦ t ⟧ ∅ (v ⊕ dv)
  ≡ ⟦ t ⟧ ∅ v ⊕ ⟦ derive t ⟧Δ ∅ (unrestricted t) v dv R[v,dv]

corollary-closed {t = t} {v} {dv} {R[v,dv]} =
  let
    f  = ⟦ t ⟧ ∅
    df = ⟦ derive t ⟧Δ ∅ (unrestricted t)
  in
    begin
      f (v ⊕ dv)
    ≡⟨ cong (λ hole → hole (v ⊕ dv)) (sym (correctness {t = t})) ⟩
      (f ⊕ df) (v ⊕ dv)
    ≡⟨ proj₂ (validity {t = t} v dv R[v,dv]) ⟩
      f v ⊕ df v dv R[v,dv]
    ∎ where open ≡-Reasoning

⟦apply⟧ : ∀ {τ Γ}
  {t : Term Γ τ} {dt : Term Γ (Δ-Type τ)} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ⊞ ⟦ dt ⟧ ρ ≡ ⟦ apply dt t ⟧ ρ

⟦difff⟧ : ∀ {τ Γ}
  {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
  ⟦ s ⟧ ρ ⊟ ⟦ t ⟧ ρ ≡ ⟦ difff s t ⟧ ρ

⟦apply⟧ {nats} {Γ} {t} {dt} {ρ} = refl
⟦apply⟧ {bags} {Γ} {t} {dt} {ρ} = refl
⟦apply⟧ {σ ⇒ τ} {Γ} {t} {dt} {ρ} = extensionality (λ v →
  let
    ρ′ : ⟦ σ • Γ ⟧Context
    ρ′ = v • ρ
    dv = ⟦ difff (var this) (var this) ⟧ ρ′
    t-v = app (weaken (drop σ • Γ≼Γ) t) (var this)
    dt-v-dv = app (app
      (weaken (drop σ • Γ≼Γ) dt) (var this)) (difff (var this) (var this))
  in
    begin
      ⟦ t ⟧ ρ v ⊞ ⟦ dt ⟧ ρ v (v ⊟ v)
    ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v ⊞ ⟦ dt ⟧ ρ v hole)
        (⟦difff⟧ {s = var this} {var this} {ρ′}) ⟩
      ⟦ t ⟧ ρ v ⊞ ⟦ dt ⟧ ρ v dv
    ≡⟨ cong₂ _⊞_
        (cong (λ hole → hole v   ) (weaken-once {t = t}))
        (cong (λ hole → hole v dv) (weaken-once {t = dt})) ⟩
      ⟦ t-v ⟧ ρ′ ⊞ ⟦ dt-v-dv ⟧ ρ′
    ≡⟨ ⟦apply⟧ ⟩
      ⟦ apply dt-v-dv t-v ⟧ ρ′
    ∎) where
    open ≡-Reasoning

⟦difff⟧ {nats} {Γ} {s} {t} {ρ} = extensionality result
  where
  result : (f : ⟦ nats ⇒ nats ⇒ nats ⟧)
    → f (⟦ t ⟧ ρ) (⟦ s ⟧ ρ)
    ≡ f (⟦ weaken (drop _ • Γ≼Γ) t ⟧ (f • ρ))
        (⟦ weaken (drop _ • Γ≼Γ) s ⟧ (f • ρ))
  result f rewrite weaken-once {t = s} {f} {ρ}
                 | weaken-once {t = t} {f} {ρ} = refl
⟦difff⟧ {bags} {Γ} {s} {t} {ρ} = refl
⟦difff⟧ {σ ⇒ τ} {Γ} {s} {t} {ρ} = 
  extensionality (λ v → extensionality (λ dv →
  let
    ρ′ : ⟦ (Δ-Type σ) • σ • Γ ⟧Context
    ρ′ = dv • v • ρ
    f = weaken (drop Δ-Type σ • (drop σ • Γ≼Γ)) s
    t-x = app (weaken (drop Δ-Type σ • (drop σ • Γ≼Γ)) t)
              (var (that this))
    x⊞dx = apply (var this) (var (that this))
  in
    begin
      ⟦ s ⟧ ρ (v ⊞ dv) ⊟ ⟦ t ⟧ ρ v
    ≡⟨ cong₂ _⊟_
        (cong₂ (λ f x → f x)
          (weaken-twice {t = s} {dv} {v} {ρ}) ⟦apply⟧)
        (cong (λ hole → hole v)
          (weaken-twice {t = t} {dv} {v} {ρ})) ⟩
      ⟦ f ⟧ ρ′ (⟦ x⊞dx ⟧ ρ′) ⊟ ⟦ t-x ⟧ ρ′
    ≡⟨ ⟦difff⟧ {s = app f x⊞dx} {t-x} ⟩
      ⟦ difff (app f x⊞dx) t-x ⟧ ρ′
    ∎)) where open ≡-Reasoning

main-theorem : ∀ {σ τ}
  {s : Term ∅ (σ ⇒ τ)} {t₀ : Term ∅ σ} {t₁ : Term ∅ σ}
  → ⟦ app s t₁ ⟧ ∅
  ≡ ⟦ apply (app (app (embed (derive s)) t₀) (difff t₁ t₀)) (app s t₀) ⟧ ∅

main-theorem {s = s} {t₀} {t₁} =
  let
    f  = ⟦ s ⟧ ∅
    df = ⟦ derive s ⟧Δ ∅ (unrestricted s)
    df′ = ⟦ embed (derive s) ⟧ ∅
    v  = ⟦ t₀ ⟧ ∅
    u  = ⟦ t₁ ⟧ ∅
  in
    begin
      f u
    ≡⟨ cong (λ hole → f hole) (sym v⊕[u⊝v]=u) ⟩
      f (v ⊕ (u ⊝ v))
    ≡⟨ corollary-closed {t = s} {v} {u ⊝ v} {R[v,u⊝v]} ⟩
      f v ⊕ df v (u ⊝ v) R[v,u⊝v]
    ≡⟨ carry-over
        (embed-correct {Γ = ∅} {dt = derive s}
          {∅} {unrestricted s} {∅} {∅}
          v (u ⊝ v) (u ⊟ v) R[v,u⊝v] u⊝v≈u⊟v)
        (proj₁ (validity {Γ = ∅} {s} v (u ⊝ v) R[v,u⊝v])) ⟩
      f v ⊞ df′ v (u ⊟ v)
    ≡⟨ trans (cong (λ hole → f v ⊞ df′ v hole)
        (⟦difff⟧ {s = t₁} {t₀})) ⟦apply⟧ ⟩
      ⟦ apply (app (app (embed (derive s)) t₀) (difff t₁ t₀))
              (app s t₀) ⟧ ∅
    ∎ where open ≡-Reasoning
