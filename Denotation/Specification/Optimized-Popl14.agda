module Denotation.Specification.Optimized-Popl14 where

-- Optimized denotation-as-specification for Calculus Popl14
--
-- Contents
-- - ⟦_⟧Δ+ : binding-time-shifted derive+
-- - Validity and correctness lemmas for ⟦_⟧Δ+

open import Denotation.Specification.Canon-Popl14 public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Integer
open import Syntax.FreeVars.Popl14 using (closed?)
open import Denotation.FreeVars.Popl14
open import Structure.Bag.Popl14
open import Theorem.CongApp
open import Theorem.Groups-Popl14
open import Theorem.ValidityUnique-Popl14
open import Postulate.Extensionality

⟦_⟧Δ+ : ∀ {τ Γ} (t : Term Γ τ) (ρ : ΔEnv Γ) → ΔVal τ

valid+ : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  valid (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ+ ρ)
correct+ : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  ⟦ t ⟧Δ+ ρ ≡ ⟦ t ⟧Δ ρ

⟦ intlit n ⟧Δ+ ρ = + 0
⟦ add s t ⟧Δ+ ρ = ⟦ s ⟧Δ+ ρ + ⟦ t ⟧Δ+ ρ
⟦ minus t ⟧Δ+ ρ = - ⟦ t ⟧Δ+ ρ

⟦ empty ⟧Δ+ ρ = emptyBag
⟦ insert s t ⟧Δ+ ρ with closed? s
... | inj₁ is-closed = ⟦ t ⟧Δ+ ρ
... | inj₂ tt =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δn = ⟦ s ⟧Δ+ ρ
    Δb = ⟦ t ⟧Δ+ ρ
  in
    (singletonBag (n ⊞ Δn) ++ (b ⊞ Δb)) ⊟ (singletonBag n ++ b)
⟦ union s t ⟧Δ+ ρ = ⟦ s ⟧Δ+ ρ ++ ⟦ t ⟧Δ+ ρ
⟦ negate t ⟧Δ+ ρ = negateBag (⟦ t ⟧Δ+ ρ)

⟦ flatmap s t ⟧Δ+ ρ with closed? s
... | inj₁ is-closed = flatmapBag (⟦ s ⟧ (ignore ρ)) (⟦ t ⟧Δ+ ρ)
... | inj₂ tt =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ+ ρ
    Δb = ⟦ t ⟧Δ+ ρ
  in
    flatmapBag (f ⊞ Δf) (b ⊞ Δb) ⊟ flatmapBag f b
⟦ sum t ⟧Δ+ ρ = sumBag (⟦ t ⟧Δ+ ρ)

⟦ var x ⟧Δ+ ρ = ⟦ x ⟧ΔVar ρ
⟦ app s t ⟧Δ+ ρ = 
  (⟦ s ⟧Δ+ ρ) (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ+ ρ) (valid+ {t = t})
⟦ abs t ⟧Δ+ ρ = λ v Δv R[v,Δv] → ⟦ t ⟧Δ+ (cons v Δv R[v,Δv] ρ)

-- A useless copy of `validity`.
-- All interesting things happen where tt suffices for `validity`.
-- Proofs for t-abs and t-app duplicate those of `validity`.
valid+ {t = intlit n}       = tt
valid+ {t = add s t}     = tt
valid+ {t = minus t}     = tt
valid+ {t = empty}       = tt
valid+ {t = insert s t}  = tt
valid+ {t = union s t}   = tt
valid+ {t = negate t}    = tt
valid+ {t = flatmap s t} = tt
valid+ {t = sum t}       = tt

valid+ {t = var x} = validVar x
valid+ {t = app s t} {ρ} =
  let
    v = ⟦ t ⟧ (ignore ρ)
    Δv = ⟦ t ⟧Δ+ ρ
  in
    proj₁ (valid+ {t = s} {ρ} v Δv (valid+ {t = t} {ρ}))
valid+ {t = abs t} {ρ} = λ v Δv R[v,Δv] →
  let
    v′ = v ⊞ Δv
    Δv′ = v′ ⊟ v′
    ρ₁ = cons v Δv R[v,Δv] ρ
    ρ₂ = cons v′ Δv′ (R[v,u-v] {u = v′} {v′}) ρ
  in
    valid+ {t = t} {ρ₁}
    ,
    (begin
      ⟦ t ⟧ (ignore ρ₂) ⊞ ⟦ t ⟧Δ+ ρ₂
    ≡⟨ cong (λ hole → ⟦ t ⟧ (ignore ρ₂) ⊞ hole)
         (correct+ {t = t}) ⟩
      ⟦ t ⟧ (ignore ρ₂) ⊞ ⟦ t ⟧Δ ρ₂
    ≡⟨ correctness {t = t} {ρ₂} ⟩
      ⟦ t ⟧ (update ρ₂)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) v+[u-v]=u ⟩
      ⟦ t ⟧ (update ρ₁)
    ≡⟨ sym (correctness {t = t} {ρ₁}) ⟩
      ⟦ t ⟧ (ignore ρ₁) ⊞ ⟦ t ⟧Δ ρ₁
    ≡⟨ cong (λ hole → ⟦ t ⟧ (ignore ρ₁) ⊞ hole)
         (sym (correct+ {t = t})) ⟩
      ⟦ t ⟧ (ignore ρ₁) ⊞ ⟦ t ⟧Δ+ ρ₁
    ∎) where open ≡-Reasoning

correct+ {t = intlit n} = refl
correct+ {t = add s t} {ρ} =
  cong₂ _+_ (correct+ {t = s} {ρ}) (correct+ {t = t} {ρ})
correct+ {t = minus t} {ρ} = cong -_ (correct+ {t = t} {ρ})

correct+ {t = empty} = refl
correct+ {t = insert s t} {ρ} with closed? s
... | inj₁ when-closed =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δn = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
    Δn+ = ⟦ s ⟧Δ+ ρ
    Δb+ = ⟦ t ⟧Δ+ ρ
    sin = singletonBag
    neg = negateBag
  in
  begin
    Δb+
  ≡⟨ correct+ {t = t} ⟩
    Δb
  ≡⟨ sym (left-id-bag Δb) ⟩
    emptyBag ++ Δb
  ≡⟨ cong₂ _++_ (sym (right-inv-bag (sin n))) (sym [a++b]\\a=b) ⟩
    (sin n ++ neg (sin n)) ++ ((b ++ Δb) \\ b)
  ≡⟨ ab·cd=ac·bd {sin n} {neg (sin n)} {b ⊞ Δb} {neg b} ⟩
    (sin n ++ (b ++ Δb)) ++ (neg (sin n) ++ neg b)
  ≡⟨ cong (_++_ (sin n ++ (b ++ Δb))) (-a·-b=-ab {sin n} {b}) ⟩
    (sin n ++ (b ++ Δb)) \\ (sin n ++ b)
  ≡⟨ cong (λ hole → (sin hole ++ (b ++ Δb)) \\ (sin n ++ b))
         (sym (stability {t = s} (unaffected {t = s} when-closed))) ⟩
    (sin (n + Δn) ++ (b ++ Δb)) \\ (sin n ++ b)
  ∎ where open ≡-Reasoning
... | inj₂ tt =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    sin = singletonBag
  in
    cong₂ (λ h1 h2 → (sin (n ⊞ h1) ++ (b ⊞ h2)) \\ (sin n ++ b))
      (correct+ {t = s}) (correct+ {t = t})
correct+ {t = union s t} {ρ} =
  cong₂ _++_ (correct+ {t = s} {ρ}) (correct+ {t = t} {ρ})
correct+ {t = negate t} {ρ} = cong negateBag (correct+ {t = t} {ρ})

correct+ {t = flatmap s t} {ρ} with closed? s
... | inj₁ when-closed =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
    Δf+ = ⟦ s ⟧Δ+ ρ
    Δb+ = ⟦ t ⟧Δ+ ρ
    sin = singletonBag
    neg = negateBag
    map = flatmapBag
    hom = homo-flatmap
    inv = neg-flatmap
  in
  begin
    map f Δb+
  ≡⟨ cong (map f) (correct+ {t = t}) ⟩
    map f Δb
  ≡⟨ cong (map f) (sym [a++b]\\a=b) ⟩
    map f ((b ⊞ Δb) ⊟ b)
  ≡⟨ hom ⟩
    map f (b ⊞ Δb) ++ map f (neg b)
  ≡⟨ cong (_++_ (map f (b ⊞ Δb))) inv ⟩
    map f (b ⊞ Δb) ⊟ map f b
  ≡⟨ cong (λ hole → map hole (b ⊞ Δb) ⊟ map f b)
       (sym (stability {t = s} (unaffected {t = s} when-closed))) ⟩
    map (f ⊞ Δf) (b ⊞ Δb) ⊟ map f b
  ∎ where open ≡-Reasoning
... | inj₂ tt =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    map = flatmapBag
  in
    cong₂ (λ h1 h2 → map (f ⊞ h1) (b ⊞ h2) \\ map f b)
      (correct+ {t = s}) (correct+ {t = t})
correct+ {t = sum t} {ρ} = cong sumBag (correct+ {t = t} {ρ})

correct+ {t = var x} = refl
correct+ {t = abs t} = ext³ (λ _ _ _ → correct+ {t = t})
correct+ {t = app {σ} {τ} s t} {ρ} = eq-all where
  import Relation.Binary.HeterogeneousEquality as HET
  open HET hiding (cong₂ ; cong ; sym)
  Δf₀ : ΔVal (σ ⇒ τ)
  Δf₀ = ⟦ s ⟧Δ ρ
  Δf₂ : ΔVal (σ ⇒ τ)
  Δf₂ = ⟦ s ⟧Δ+ ρ
  Δv₀ : ΔVal σ
  Δv₀ = ⟦ t ⟧Δ ρ
  Δv₂ : ΔVal σ
  Δv₂ = ⟦ t ⟧Δ+ ρ
  v   : ⟦ σ ⟧
  v   = ⟦ t ⟧ (ignore ρ)
  eq-f : Δf₂ ≡ Δf₀
  eq-f = correct+ {t = s}
  eq-v : Δv₂ ≡ Δv₀
  eq-v = correct+ {t = t}
  eq-type : valid v Δv₂ ≡ valid v Δv₀
  eq-type = cong (valid v) eq-v

  eq! : ∀ {τ : Type} {v : ⟦ τ ⟧} {Δu Δv}
    {i : valid v Δu} {j : valid v Δv} →
    valid v Δu ≡ valid v Δv → i ≅ j
  eq! {v = v} {Δu} {Δv} {i} {j} eq2
    rewrite eq2 =
    let
      k : valid v Δv
      k = i
      x : i ≅ k
      x = refl
      y : k ≡ j
      y = valid-uniq {v = v}
      z : i ≅ j
      z = HET.trans x (≡-to-≅ y)
    in z

  cong! : ∀ {A B : Set} {C : A → B → Set} {D : Set} →
    {f g : (a : A) → (b : B) → C a b → D}
    {a : A} {b b′ : B} {c : C a b} {c′ : C a b′} →
    b ≡ b′ → f ≡ g → c ≅ c′ →
    f a b c ≡ g a b′ c′
  cong! refl refl refl = refl

  eq-all : Δf₂ v Δv₂ (valid+   {t = t} {ρ})
         ≡ Δf₀ v Δv₀ (validity {t = t} {ρ})
  eq-all = cong!
    {⟦ σ ⟧} {ΔVal σ} {valid} {ΔVal τ}
    {Δf₂} {Δf₀} {v} {Δv₂} {Δv₀}
    {valid+ {t = t} {ρ}} {validity {t = t} {ρ}}
    eq-v eq-f (eq! {σ} eq-type)

-- correct+ with make-up
cool-correct+ : ∀ {τ Γ} {t : Term Γ τ} → ⟦ t ⟧Δ+ ≡ ⟦ t ⟧Δ

cool-correct+ {t = t} = ext (λ ρ → correct+ {t = t} {ρ})
