module Denotation.Derive.Optimized-Popl14 where

-- The denotational properties of the `derive+` transformation
-- for Calculus Popl14. In particular, the main theorem
-- about it producing the correct incremental behavior.

open import Syntax.Derive.Optimized-Popl14 public
open import Denotation.Implementation.Popl14 public
open import Denotation.Specification.Optimized-Popl14 public
open import Denotation.Derive.Canon-Popl14 public using
 (deriveVar-correct)

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Integer
open import Syntax.FreeVars.Popl14 using (closed?)
open import Structure.Bag.Popl14
open import Postulate.Extensionality

-- Almost a straight copy of `derive-correct`.
derive+correct : ∀ {τ Γ} {t : Term Γ τ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧} {C : compatible ρ ρ′} →
  ⟦ t ⟧Δ+ ρ ≈ ⟦ derive+ t ⟧ ρ′

derive+correct {t = intlit n} = refl
derive+correct {t = add s t} {ρ} {ρ′} {C} = cong₂ _+_
  (derive+correct {t = s} {ρ} {ρ′} {C})
  (derive+correct {t = t} {ρ} {ρ′} {C})
derive+correct {t = minus t} {ρ} {ρ′} {C} =
  cong -_ (derive+correct {t = t} {ρ} {ρ′} {C})

derive+correct {t = empty} = refl
derive+correct {t = insert s t} {ρ} {ρ′} {C} with closed? s
... | inj₁ is-closed = derive+correct {t = t} {C = C}
... | inj₂ tt =
  cong₂ _\\_
    (cong₂ _++_
      (cong singletonBag (cong₂ _+_
        (⟦fit⟧ s C)
        (derive+correct {t = s} {ρ} {ρ′} {C})))
      (cong₂ _++_
        (⟦fit⟧ t C)
        (derive+correct {t = t} {ρ} {ρ′} {C})))
    (cong₂ _++_ (cong singletonBag (⟦fit⟧ s C)) (⟦fit⟧ t C))
derive+correct {t = union s t} {ρ} {ρ′} {C} = cong₂ _++_
  (derive+correct {t = s} {ρ} {ρ′} {C})
  (derive+correct {t = t} {ρ} {ρ′} {C})
derive+correct {t = negate t} {ρ} {ρ′} {C} =
  cong negateBag (derive+correct {t = t} {ρ} {ρ′} {C})

derive+correct {t = flatmap s t} {ρ} {ρ′} {C} with closed? s
... | inj₁ is-closed =
  cong₂ flatmapBag (⟦fit⟧ s C) (derive+correct {t = t} {C = C})
... | inj₂ tt =
  cong₂ _\\_
    (cong₂ flatmapBag
      (ext (λ v →
        cong₂ _++_
          (cong (λ hole → hole v) (⟦fit⟧ s C))
          (derive+correct {t = s} {ρ} {ρ′} {C}
            v (v - v) (v - v) tt refl)))
      (cong₂ _++_
        (⟦fit⟧ t C)
        (derive+correct {t = t} {ρ} {ρ′} {C})))
    (cong₂ flatmapBag (⟦fit⟧ s C) (⟦fit⟧ t C))
derive+correct {t = sum t} {ρ} {ρ′} {C} =
  cong sumBag (derive+correct {t = t} {ρ} {ρ′} {C})

derive+correct {t = var x} {ρ} {ρ′} {C} =
  deriveVar-correct {x = x} {ρ} {ρ′} {C}
derive+correct {t = app s t} {ρ} {ρ′} {C}
  rewrite sym (⟦fit⟧ t C) =
  derive+correct {t = s} {ρ} {ρ′} {C}
  (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ+ ρ) (⟦ derive+ t ⟧ ρ′)
  (valid+ {t = t}) (derive+correct {t = t} {ρ} {ρ′} {C})
derive+correct {t = abs t} {ρ} {ρ′} {C} =
  λ w Δw Δw′ R[w,Δw] Δw≈Δw′ →
    derive+correct {t = t}
      {cons w Δw R[w,Δw] ρ} {Δw′ • w • ρ′} {cons refl Δw≈Δw′ C}

main-theorem+ : ∀ {σ τ}
  {f : Term ∅ (σ ⇒ τ)} {x : Term ∅ σ} {y : Term ∅ σ}
  → ⟦ app f y ⟧
  ≡ ⟦ app f x ⊕ app (app (derive+ f) x) (y ⊝ x) ⟧

main-theorem+ {f = f} {x} {y} =
  let
    h  = ⟦ f ⟧ ∅
    Δh₀ = ⟦ f ⟧Δ ∅
    Δh = ⟦ f ⟧Δ+ ∅
    Δh′ = ⟦ derive+ f ⟧ ∅
    v  = ⟦ x ⟧ ∅
    u  = ⟦ y ⟧ ∅
    Δoutput-term = app (app (derive+ f) x) (y ⊝ x)
  in
    ext {A = EmptyEnv} (λ { ∅ →
    begin
      h u
    ≡⟨ cong h (sym v+[u-v]=u) ⟩
      h (v ⊞ (u ⊟ v))
    ≡⟨ corollary-closed {t = f} {v} {u ⊟ v} ⟩
      h v ⊞ Δh₀ v (u ⊟ v) (R[v,u-v] {u = u} {v})
    ≡⟨ cong (λ hole → h v ⊞ hole v (u ⊟ v) (R[v,u-v] {u = u} {v}))
         (sym (correct+ {t = f})) ⟩
      h v ⊞ Δh v (u ⊟ v) (R[v,u-v] {u = u} {v})
    ≡⟨ carry-over
        (proj₁ (valid+ {Γ = ∅} {f} v (u ⊟ v) _))
        (derive+correct {Γ = ∅} {t = f}
          {∅} {∅} v (u ⊟ v) (u ⟦⊝⟧ v) _ (u⊟v≈u⊝v {u = u} {v})) ⟩
      h v ⟦⊕⟧ Δh′ v (u ⟦⊝⟧ v)
    ≡⟨ trans
        (cong (λ hole → h v ⟦⊕⟧ Δh′ v hole) (meaning-⊝ {s = y} {x}))
        (meaning-⊕ {t = app f x} {Δt = Δoutput-term}) ⟩
      ⟦ app f x ⊕ app (app (derive+ f) x) (y ⊝ x) ⟧ ∅
    ∎}) where open ≡-Reasoning
