module Base.Change.Products where

open import Relation.Binary.PropositionalEquality
open import Level

open import Base.Change.Algebra
open import Base.Change.Equivalence
open import Base.Change.Equivalence.Realizers

-- Also try defining sectioned change structures on the positives halves of
-- groups? Or on arbitrary subsets?

-- Restriction: we pair sets on the same level (because right now everything
-- else would risk getting in the way).
module ProductChanges ℓ {A B : Set ℓ} {{CA : ChangeAlgebra A}} {{CB : ChangeAlgebra B}} where
  -- Avoid having to specify A and B all the time; they'd often be ambiguous
  -- otherwise.
  import Data.Product as DP
  open DP.Σ {A = A} {B = λ _ → B}
  open DP using (_×_; _,_)

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
    where
      open ≡-Reasoning

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
    where
      open ≡-Reasoning

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

  --
  -- Derivatives of introductions and elimination forms for products.
  --
  -- For each one define a naive derivative using nil, write a hand-optimized *realizer* for an efficient derivative, and prove they're equivalent.
  --
  proj₁′ : Δ proj₁
  proj₁′ = nil proj₁

  proj₁′-realizer : (v : A × B) → Δ v → Δ (proj₁ v)
  proj₁′-realizer (a , b) (da , db) = da

  proj₁′-realizer-correct : ∀ (p : A × B) (dp : Δ p) → apply proj₁′ p dp ≙₍ proj₁ p ₎ proj₁′-realizer p dp
  proj₁′-realizer-correct (a , b) (da , db) = diff-update {x = a} {dx = da}

  proj₁′Derivative : IsDerivative proj₁ proj₁′-realizer
  -- Implementation note: we do not need to pattern match on v and dv because
  -- they are records, hence Agda knows that pattern matching on records cannot
  -- fail. Technically, the required feature is the eta-rule on records.
  proj₁′Derivative v dv = refl

  -- An extended explanation.
  proj₁′Derivative₁ : IsDerivative proj₁ proj₁′-realizer
  proj₁′Derivative₁ (a , b) (da , db) =
    let v  = (a  , b)
        dv = (da , db)
    in
      begin
        proj₁ v ⊞ proj₁′-realizer v dv
      ≡⟨⟩
        a ⊞ da
      ≡⟨⟩
        proj₁ (v ⊞ dv)
      ∎
    where
      open ≡-Reasoning

  proj₁′-faster-w-proof : equiv-raw-change-to-change-ResType proj₁ proj₁′-realizer
  proj₁′-faster-w-proof = equiv-raw-change-to-change proj₁ proj₁′ proj₁′-realizer proj₁′-realizer-correct
  proj₁′-faster : Δ proj₁
  proj₁′-faster = DP.proj₁ proj₁′-faster-w-proof

  -- Same for the second extractor.
  proj₂′-realizer : (v : A × B) → Δ v → Δ (proj₂ v)
  proj₂′-realizer (a , b) (da , db) = db

  proj₂′ : Δ proj₂
  proj₂′ = nil proj₂

  proj₂′-realizer-correct : ∀ p (dp : Δ p) → apply proj₂′ p dp ≙₍ proj₂ p ₎ proj₂′-realizer p dp
  proj₂′-realizer-correct (a , b) (da , db) = diff-update

  proj₂′Derivative : IsDerivative proj₂ proj₂′-realizer
  proj₂′Derivative v dv = refl

  proj₂′-faster-w-proof : equiv-raw-change-to-change-ResType proj₂ proj₂′-realizer
  proj₂′-faster-w-proof = equiv-raw-change-to-change proj₂ proj₂′ proj₂′-realizer proj₂′-realizer-correct
  proj₂′-faster : Δ proj₂
  proj₂′-faster = DP.proj₁ proj₂′-faster-w-proof

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

  _,_′ : Δ (_,_ {A = A} {B = λ _ → B})
  _,_′ = _,_ ⊟ _,_
  _,_′-realizer-correct : ∀ a da b db → apply (apply _,_′ a da) b db ≙₍ a , b ₎ _,_′-realizer a da b db
  _,_′-realizer-correct a da b db = doe (≙-cong₂ _,_ diff-update diff-update)

  open import Data.Product using (Σ-syntax)

  _,_′-faster-w-proof : equiv-raw-change-to-change-binary-ResType _,_ _,_′-realizer
  _,_′-faster-w-proof = equiv-raw-change-to-change-binary _,_ _,_′ _,_′-realizer _,_′-realizer-correct

  _,_′-faster : Δ (_,_ {A = A} {B = λ _ → B})
  _,_′-faster = DP.proj₁ _,_′-faster-w-proof

  -- Define specialized variant of uncurry, and derive it.
  uncurry₀ : ∀ {C : Set ℓ} → (A → B → C) → A × B → C
  uncurry₀ f (a , b) = f a b

  module _ {C : Set ℓ} {{CC : ChangeAlgebra C}} where
    uncurry₀′ : Δ uncurry₀
    uncurry₀′ = nil (uncurry₀ {C = C})

    uncurry₀′-realizer : (f : A → B → C) → Δ f → (p : A × B) → Δ p → Δ (uncurry₀ f p)
    uncurry₀′-realizer f df (a , b) (da , db) = apply (apply df a da) b db

    uncurry₀′-realizer-correct : ∀ f df p dp → apply (apply uncurry₀′ f df) p dp ≙₍ uncurry₀ f p ₎ uncurry₀′-realizer f df p dp
    uncurry₀′-realizer-correct f df (a , b) (da , db) =
      begin
        (f ⊞ df) (a ⊞ da) (b ⊞ db) ⊟ f a b
      ≙⟨ equiv-cancel-2 _ _ (incrementalization-binary f df a da b db) ⟩
        apply (apply df a da) b db
      ∎
      where
        open ≙-Reasoning
        open BinaryFunctionChanges A B C

    uncurry₀′-faster-w-proof : equiv-raw-change-to-change-binary-ResType uncurry₀ uncurry₀′-realizer
    uncurry₀′-faster-w-proof = equiv-raw-change-to-change-binary uncurry₀ uncurry₀′ uncurry₀′-realizer uncurry₀′-realizer-correct

    uncurry₀′-faster : Δ uncurry₀
    uncurry₀′-faster = DP.proj₁ uncurry₀′-faster-w-proof
