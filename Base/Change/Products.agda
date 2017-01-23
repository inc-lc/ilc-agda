module Base.Change.Products where

open import Relation.Binary.PropositionalEquality
open import Level

open import Base.Change.Algebra

open import Data.Product

-- Also try defining sectioned change structures on the positives halves of
-- groups? Or on arbitrary subsets?

-- Restriction: we pair sets on the same level (because right now everything
-- else would risk getting in the way).
module ProductChanges ℓ {A B : Set ℓ} {{CA : ChangeAlgebra A}} {{CB : ChangeAlgebra B}} where
  open ≡-Reasoning

  -- The simplest possible definition of changes for products.

  PChange : A × B → Set ℓ
  PChange (a , b) = Δ a × Δ b

  -- An interesting alternative definition allows omitting the nil change of a
  -- component when that nil change can be computed from the type. For instance, the nil change for integers is always the same.

  -- However, the nil change for function isn't always the same (unless we
  -- defunctionalize them first), so nil changes for functions can't be omitted.

  _⊕_ : (v : A × B) → PChange v → A × B
  _⊕_ (a , b) (da , db) = a ⊞ da , b ⊞ db
  _⊝_ : A × B → (v : A × B) → PChange v
  _⊝_ (aNew , bNew) (a , b) = aNew ⊟ a , bNew ⊟ b

  p-nil : (v : A × B) → PChange v
  p-nil (a , b) = (nil a , nil b)

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

  p-update-nil : (v : A × B) → v ⊕ (p-nil v) ≡ v
  p-update-nil (a , b) =
    let v = (a , b)
    in
      begin
        v ⊕ (p-nil v)
      ≡⟨⟩
        (a ⊞ nil a , b ⊞ nil b)
      ≡⟨ cong₂ _,_ (update-nil a) (update-nil b)⟩
         (a , b)
      ≡⟨⟩
        v
      ∎

  instance
    changeAlgebraProducts : ChangeAlgebra (A × B)
    changeAlgebraProducts = record
      { Change = PChange
      ; update = _⊕_
      ; diff = _⊝_
      ; nil = p-nil
      ; isChangeAlgebra = record
        { update-diff = p-update-diff
        ; update-nil = p-update-nil
        }
      }

  proj₁′ : (v : A × B) → Δ v → Δ (proj₁ v)
  proj₁′ (a , b) (da , db) = da

  proj₁′Derivative : IsDerivative proj₁ proj₁′
  -- Implementation note: we do not need to pattern match on v and dv because
  -- they are records, hence Agda knows that pattern matching on records cannot
  -- fail. Technically, the required feature is the eta-rule on records.
  proj₁′Derivative v dv = refl

  -- An extended explanation.
  proj₁′Derivative₁ : IsDerivative proj₁ proj₁′
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

  proj₂′Derivative : IsDerivative proj₂ proj₂′
  proj₂′Derivative v dv = refl

  -- Morally, the following is a change:
  -- What one could wrongly expect to be the derivative of the constructor:
  _,_′-realizer : (a : A) → (da : Δ a) → (b : B) → (db : Δ b) → Δ (a , b)
  _,_′-realizer a da b db = da , db

  -- That has the correct behavior, in a sense, and it would be in the
  -- subset-based formalization in the paper.
  --
  -- But the above is not even a change, because it does not contain a proof of
  -- its own validity, and because after application it does not contain a
  -- proof.
  --
  -- However, the above is (morally) a "realizer" of the actual change, since it
  -- only represents its computational behavior, not its proof manipulation.

  -- Hence, we need to do some additional work.

  _,_′-realizer-correct _,_′-realizer-correct-detailed :
    (a : A) → (da : Δ a) → (b : B) → (db : Δ b) →
      (a , b ⊞ db) ⊞ (_,_′-realizer a da (b ⊞ db) (nil (b ⊞ db))) ≡ (a , b) ⊞ (_,_′-realizer a da b db)
  _,_′-realizer-correct a da b db rewrite update-nil (b ⊞ db) = refl

  _,_′-realizer-correct-detailed a da b db =
    begin
      (a , b ⊞ db) ⊞ (_,_′-realizer a da) (b ⊞ db) (nil (b ⊞ db))
    ≡⟨⟩
      a ⊞ da , b ⊞ db ⊞ (nil (b ⊞ db))
    ≡⟨ cong (λ □ →  a ⊞ da , □) (update-nil (b ⊞ db)) ⟩
      a ⊞ da , b ⊞ db
    ≡⟨⟩
      (a , b) ⊞ (_,_′-realizer a da) b db
    ∎

  _,_′ : (a : A) → (da : Δ a) → Δ (_,_ a)
  _,_′ a da = record { apply = _,_′-realizer a da ; correct = λ b db → _,_′-realizer-correct a da b db }

  _,_′-Derivative : IsDerivative _,_ _,_′
  _,_′-Derivative a da = ext (λ b → cong (_,_ (a ⊞ da)) (update-nil b))
    where
      open import Postulate.Extensionality

  -- Define specialized variant of uncurry, and derive it.
  uncurry₀ : ∀ {C : Set ℓ} → (A → B → C) → A × B → C
  uncurry₀ f (a , b) = f a b

  module _ {C : Set ℓ} {{CC : ChangeAlgebra C}} where
    uncurry₀′-realizer : (f : A → B → C) → Δ f → (p : A × B) → Δ p → Δ (uncurry₀ f p)
    uncurry₀′-realizer f df (a , b) (da , db) = apply (apply df a da) b db

    uncurry₀′-realizer-correct uncurry₀′-realizer-correct-detailed :
      ∀ (f : A → B → C) (df : Δ f) (p : A × B) (dp : Δ p) →
        uncurry₀ f (p ⊕ dp) ⊞ uncurry₀′-realizer f df (p ⊕ dp) (nil (p ⊞ dp)) ≡ uncurry₀ f p ⊞ uncurry₀′-realizer f df p dp

    -- Hard to read
    uncurry₀′-realizer-correct f df (a , b) (da , db)
      rewrite sym (correct (apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db) (nil (b ⊞ db)))
      | update-nil (b ⊞ db)
      | {- cong (λ □ → □ (b ⊞ db)) -} (sym (correct df (a ⊞ da) (nil (a ⊞ da))))
      | update-nil (a ⊞ da)
      | cong (λ □ → □ (b ⊞ db)) (correct df a da)
      | correct (apply df a da) b db
      = refl

    -- Verbose, but it shows all the intermediate steps.
    uncurry₀′-realizer-correct-detailed f df (a , b) (da , db) =
      begin
        uncurry₀ f (a ⊞ da , b ⊞ db) ⊞ uncurry₀′-realizer f df (a ⊞ da , b ⊞ db) (nil (a ⊞ da , b ⊞ db))
      ≡⟨⟩
        f (a ⊞ da) (b ⊞ db) ⊞ apply (apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db) (nil (b ⊞ db))
      ≡⟨ sym (correct (apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db) (nil (b ⊞ db))) ⟩
        (f (a ⊞ da) ⊞ apply df (a ⊞ da) (nil (a ⊞ da))) ((b ⊞ db) ⊞ (nil (b ⊞ db)))
      ≡⟨ cong-lem₀ ⟩
        (f (a ⊞ da) ⊞ apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db)
      ≡⟨ sym cong-lem₂ ⟩
        ((f ⊞ df) ((a ⊞ da) ⊞ (nil (a ⊞ da)))) (b ⊞ db)
      ≡⟨ cong-lem₁ ⟩
        (f ⊞ df) (a ⊞ da) (b ⊞ db)
      ≡⟨ cong (λ □ → □ (b ⊞ db)) (correct df a da) ⟩
        (f a ⊞ apply df a da) (b ⊞ db)
      ≡⟨ correct (apply df a da) b db ⟩
        f a b ⊞ apply (apply df a da) b db
      ≡⟨⟩
        uncurry₀ f (a , b) ⊞ uncurry₀′-realizer f df (a , b) (da ,  db)
      ∎
      where
        cong-lem₀ :
            (f (a ⊞ da) ⊞ apply df (a ⊞ da) (nil (a ⊞ da))) ((b ⊞ db) ⊞ (nil (b ⊞ db)))
            ≡
            (f (a ⊞ da) ⊞ apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db)
        cong-lem₀ rewrite update-nil (b ⊞ db) = refl

        cong-lem₁ :
                  ((f ⊞ df) ((a ⊞ da) ⊞ (nil (a ⊞ da)))) (b ⊞ db)
                  ≡
                  (f ⊞ df) (a ⊞ da) (b ⊞ db)
        cong-lem₁ rewrite update-nil (a ⊞ da) = refl

        cong-lem₂ :
                  ((f ⊞ df) ((a ⊞ da) ⊞ (nil (a ⊞ da)))) (b ⊞ db)
                  ≡
                  (f (a ⊞ da) ⊞ apply df (a ⊞ da) (nil (a ⊞ da))) (b ⊞ db)
        cong-lem₂ = cong (λ □ → □ (b ⊞ db)) (correct df (a ⊞ da) (nil (a ⊞ da)))

    uncurry₀′ : (f : A → B → C) → Δ f → Δ (uncurry f)
    uncurry₀′ f df = record
      { apply = uncurry₀′-realizer f df
      ; correct = uncurry₀′-realizer-correct f df }

    -- Now proving that uncurry₀′ is a derivative is trivial!
    uncurry₀′Derivative₀ : IsDerivative uncurry₀ uncurry₀′
    uncurry₀′Derivative₀ f df = refl

    -- If you wonder what's going on, here's the step-by-step proof, going purely by definitional equality.
    uncurry₀′Derivative : IsDerivative uncurry₀ uncurry₀′
    uncurry₀′Derivative f df =
      begin
        uncurry₀ f ⊞ uncurry₀′ f df
      ≡⟨⟩
        (λ {(a , b) → uncurry₀ f (a , b) ⊞ apply (uncurry₀′ f df) (a , b) (nil (a , b))})
      ≡⟨⟩
        (λ {(a , b) → f a b ⊞ apply (apply df a (nil a)) b (nil b)})
      ≡⟨⟩
        (λ {(a , b) → (f a ⊞ apply df a (nil a)) b})
      ≡⟨⟩
        (λ {(a , b) → (f ⊞ df) a b})
      ≡⟨⟩
        (λ {(a , b) → uncurry₀ (f ⊞ df) (a , b)})
      ≡⟨⟩
        uncurry₀ (f ⊞ df)
      ∎
