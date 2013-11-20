module Base.Change.Products where

open import Relation.Binary.PropositionalEquality
open import Level

open import Base.Change.Algebra

open import Data.Product

-- Also try defining sectioned change structures on the positives halves of
-- groups? Or on arbitrary subsets?

-- Restriction: we pair sets on the same level (because right now everything
-- else would risk getting in the way).
module ProductChanges ℓ (A B : Set ℓ) {{CA : ChangeAlgebra ℓ A}} {{CB : ChangeAlgebra ℓ B}} where
  open ≡-Reasoning

  -- The simplest possible definition of changes for products.

  -- The following is probably bullshit:
  -- Does not handle products of functions - more accurately, writing the
  -- derivative of fst and snd for products of functions is hard: fst' p dp must return the change of fst p
  PChange : A × B → Set ℓ
  PChange (a , b) = Δ a × Δ b

  _⊕_ : (v : A × B) → PChange v → A × B
  _⊕_ (a , b) (da , db) = a ⊞ da , b ⊞ db
  _⊝_ : A × B → (v : A × B) → PChange v
  _⊝_ (aNew , bNew) (a , b) = aNew ⊟ a , bNew ⊟ b

  p-update-diff : (u v : A × B) → v ⊕ (u ⊝ v) ≡ u
  p-update-diff (ua , ub) (va , vb) =
    let u = (ua , ub)
        v = (va , vb)
    in
      begin
        v ⊕ (u ⊝ v)
      ≡⟨⟩
        (va ⊞ (ua ⊟ va) , vb ⊞ (ub ⊟ vb))
        --v ⊕ ((ua ⊟ va , ub ⊟ vb))
      ≡⟨ cong₂ _,_ (update-diff ua va) (update-diff ub vb)⟩
        (ua , ub)
      ≡⟨⟩
        u
      ∎

  changeAlgebra : ChangeAlgebra ℓ (A × B)
  changeAlgebra = record
    { Change = PChange
    ; update = _⊕_
    ; diff = _⊝_
    ; isChangeAlgebra = record
      { update-diff = p-update-diff
      }
    }

  proj₁′ : (v : A × B) → Δ v → Δ (proj₁ v)
  proj₁′ (a , b) (da , db) = da

  proj₁′Derivative : Derivative proj₁ proj₁′
  -- Implementation note: we do not need to pattern match on v and dv because
  -- they are records, hence Agda knows that pattern matching on records cannot
  -- fail. Technically, the required feature is the eta-rule on records.
  proj₁′Derivative v dv = refl

  -- An extended explanation.
  proj₁′Derivative₁ : Derivative proj₁ proj₁′
  proj₁′Derivative₁ (a , b) (da , db) =
    let v  = (a  , b)
        dv = (da , db)
    in
      begin
        proj₁ v ⊞ proj₁′ v dv
      ≡⟨⟩
        a ⊞ da
      ≡⟨⟩
        proj₁ (v ⊞ dv)
      ∎

  -- Same for the second extractor.
  proj₂′ : (v : A × B) → Δ v → Δ (proj₂ v)
  proj₂′ (a , b) (da , db) = db

  proj₂′Derivative : Derivative proj₂ proj₂′
  proj₂′Derivative v dv = refl

  -- We should do the same for uncurry instead.

  -- What one could wrongly expect to be the derivative of the constructor:
  _,_′ : (a : A) → (da : Δ a) → (b : B) → (db : Δ b) → Δ (a , b)
  _,_′ a da b db = da , db

  -- That has the correct behavior, in a sense, and it would be in the
  -- subset-based formalization in the paper.
  --
  -- But the above is not even a change, because it does not contain a proof of its own validity, and because after application it does not contain a proof

  -- As a consequence, proving that's a derivative seems too insanely hard. We
  -- might want to provide a proof schema for curried functions at once,
  -- starting from the right correctness equation.

  B→A×B = FunctionChanges.changeAlgebra {c = ℓ} {d = ℓ} B (A × B)
  A→B→A×B = FunctionChanges.changeAlgebra {c = ℓ} {d = ℓ} A (B → A × B) {{CA}} {{B→A×B}}
  module ΔBA×B = FunctionChanges B (A × B) {{CB}} {{changeAlgebra}}
  module ΔA→B→A×B = FunctionChanges A (B → A × B) {{CA}} {{B→A×B}}


  _,_′-real : Δ _,_
  _,_′-real = nil _,_
  _,_′-real-Derivative : Derivative {{CA}} {{B→A×B}} _,_ (ΔA→B→A×B.apply _,_′-real)
  _,_′-real-Derivative =
    FunctionChanges.nil-is-derivative A (B → A × B) {{CA}} {{B→A×B}} _,_

  _,_′′ :  (a : A) → Δ a →
      Δ {{B→A×B}} (λ b → (a , b))
  _,_′′ a da = record
    { apply = _,_′ a da
    ; correct = λ b db →
      begin
        (a , b ⊞ db) ⊞ (_,_′ a da) (b ⊞ db) (nil (b ⊞ db))
      ≡⟨⟩
        a ⊞ da , b ⊞ db ⊞ (nil (b ⊞ db))
      ≡⟨ cong (λ □ →  a ⊞ da , □) (update-nil (b ⊞ db)) ⟩
        a ⊞ da , b ⊞ db
      ≡⟨⟩
        (a , b) ⊞ (_,_′ a da) b db
      ∎
    }
{-
  _,_′′′ : Δ {{A→B→A×B}} _,_
  _,_′′′ = record
    { apply = _,_′′
    ; correct = λ a da →
      begin
        update
        (_,_ (a ⊞ da))
        (_,_′′ (a ⊞ da) (nil (a ⊞ da)))
      ≡⟨ {!!} ⟩
        update (_,_ a) (_,_′′ a da)
      ∎
    }
    where
      -- This is needed to use update above.
      -- Passing the change structure seems hard with the given operators; maybe I'm just using them wrongly.
      open ChangeAlgebra B→A×B hiding (nil)
{-
  {!
      begin
        (_,_ (a ⊞ da)) ⊞ _,_′′ (a ⊞ da) (nil (a ⊞ da))
      {- ≡⟨⟩
        a ⊞ da , b ⊞ db ⊞ (nil (b ⊞ db)) -}
      ≡⟨ ? ⟩
        {-a ⊞ da , b ⊞ db
      ≡⟨⟩-}
       (_,_ a) ⊞ (_,_′′ a da)
      ∎!}
    }
-}
  open import Postulate.Extensionality


  _,_′Derivative :
    Derivative {{CA}} {{B→A×B}} _,_  _,_′′
  _,_′Derivative a da =
    begin
      _⊞_ {{B→A×B}} (_,_ a) (_,_′′ a da)
    ≡⟨⟩
      (λ b → (a , b) ⊞ ΔBA×B.apply (_,_′′ a da) b (nil b))
    --ext (λ b → cong (λ □ →  (a , b) ⊞ □) (update-nil {{?}} b))
    ≡⟨ {!!} ⟩
      (λ b → (a , b) ⊞ ΔBA×B.apply (_,_′′ a da) b (nil b))
    ≡⟨ sym {!ΔA→B→A×B.incrementalization _,_ _,_′′′ a da!} ⟩
  --FunctionChanges.incrementalization A (B → A × B) {{CA}} {{{!B→A×B!}}} _,_ {!!} {!!} {!!}
       _,_ (a ⊞ da)
    ∎
-}
