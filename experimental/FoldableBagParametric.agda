module FoldableBagParametric where


import Level as L
open import Algebra
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

import Data.Nat as N
import Data.Integer as Z

open import Data.Bool using (Bool)
 
open import Data.Maybe
open import Data.List as List using (List)

open import Data.Product as Prod
open import Relation.Nullary
open import Relation.Nullary.Decidable

---- module OrdBag START

-- This could be replaced by StrictTotalOrder from the standard library, except that we can't restrict to _≡_ then.
record Ord (T : Set) : Set₁ where
  field
    { _<_ } : Rel T L.zero
    --isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
    isDecTotalOrder : IsDecTotalOrder _≡_ _<_

  isStrictTotalOrder = isDecTotalOrder⟶isStrictTotalOrder isDecTotalOrder
    where
      open import Relation.Binary.NonStrictToStrict _≡_ _<_

import Data.AVL

--import Data.AVL ValueFun isStrictTotalOrder as T
module Dict {T} (ValueFun : T → Set) (o : Ord T) = Data.AVL ValueFun (Ord.isStrictTotalOrder o)

---- module OrdBag END

module ParametricBag {T : Set} {{oT : Ord T}} where

  --open BagAVL using (sort)
  module BagList2 where
    open List
    open import Sorting
    ord = Ord.isDecTotalOrder oT
    open Sort ord hiding (insert; toList)
    open IsDecTotalOrder ord
    open Z hiding (_≟_)

    Bag : Set
    Bag = UList × UList

    empty : Bag
    empty = unil , unil

    singleton : T → Bag
    singleton v = ucons v unil , unil

    insert : T → Bag → Bag
    insert v (b⁺ , b⁻) = ucons v b⁺ , b⁻

    delete : T → Bag → Bag
    delete v (b⁺ , b⁻) = b⁺ , ucons v b⁻

    -- Note: this does not produce a canonical result, since we need to remove
    -- common elements from the output. Using multiplicities, as in BagList,
    -- might simplify this.
    union : Bag → Bag → Bag
    union (b⁺₁ , b⁻₁) (b⁺₂ , b⁻₂) = uunion b⁺₁ b⁺₂ , uunion b⁻₁ b⁻₂

    count : T → Bag → ℤ
    count v (b⁺ , b⁻) = ucount v b⁺ - ucount v b⁻
      where
        ucount : T → UList → ℤ
        ucount v b = + (length (filter (λ x → ⌊ _≟_ x v ⌋) (uToList b)))

    fromList : List T → Bag
    fromList = < isort′ , const unil >

    invert : Bag → Bag
    invert = swap

    sort : List T → List T
    sort = isort

    map2 : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → A × A → B × B
    map2 f = Prod.map f f

    toList : Bag → List T × List T
    toList = map2 uToList

  module BagAVL where
    private
      open N
      ValueFun : T → Set
      ValueFun _ = ℕ
  
      module T = Dict ValueFun oT
    
    Bag : Set
    Bag = T.Tree
    
    empty : Bag
    empty = T.empty
    
    singleton : T → Bag
    singleton v = T.singleton v 1
    
    insert : T → Bag → Bag
    insert v b = T.insertWith v 1 _+_ b
    
    -- insertWith : (k : Key) → Value k → (Value k → Value k → Value k) →
    --              Tree → Tree
    -- insertWith k v f (tree t) = tree $ proj₂ $ Indexed.insertWith k v f t _
    
    postulate delete : T → Bag → Bag
    -- delete v b = {!!}
      -- WRONG!!
      --T.delete v b
  
    count : T → Bag → ℕ
    count v b = maybe′ id 0 (T.lookup v b) 
  
  -- lookup : (k : Key) → Tree → Maybe (Value k)
  -- lookup k (tree t) = Indexed.lookup k t
  
    fromList : List T → Bag
    fromList = List.foldr insert empty
  
    toList′ : Bag → List (T × ℕ)
    toList′ = T.toList
  
    -- To convert to a list without multiplicities, this replicates elements.
    toList : Bag → List T
    toList = List.concatMap (uncurry (flip List.replicate)) ∘ T.toList
  
    sort : List T → List T
    sort = toList ∘ fromList
  
    union : Bag → Bag → Bag
    union = T.union

  module BagList where
    open List
    open Z
  
    Bag : Set
    --Bag = List (T × ℕ)
    -- To get a group, we need ℤ
    Bag = List (T × ℤ)
  
    module T′ = Dict (λ _ → ℤ) oT
  
    sort′ : List (T × ℤ) → List (T × ℤ) -- T′.Tree → T′.Tree
    sort′ = T′.toList ∘ T′.fromList
    
    empty : Bag
    empty = []
    
    singleton : T → Bag
    singleton v = (v , + 1) ∷ empty
  
    union : Bag → Bag → Bag
    union b₁ b₂ = sort′ (b₁ ++ b₂)
  
    insert : T → Bag → Bag
    insert v b = union (singleton v) b
    
    -- insertWith : (k : Key) → Value k → (Value k → Value k → Value k) →
    --              Tree → Tree
    -- insertWith k v f (tree t) = tree $ proj₂ $ Indexed.insertWith k v f t _
    
    postulate delete : T → Bag → Bag
    --delete v b = (T′.toList ∘ {!!} ∘ T′.fromList) b
      -- WRONG!!
      --T.delete v b
  
    count : T → Bag → ℤ
    count v b = foldr (λ {(el , mult) old → mult}) (+ 0) $ take 1 $ filter (λ {( el , mult ) →  cmp v el}) b
      --maybe′ id 0 (T.lookup v b) 
      where
        open import Data.List
        open IsStrictTotalOrder
        cmp : T → T → Bool
        cmp x y = ⌊ IsStrictTotalOrder._≟_ (Ord.isStrictTotalOrder oT) x y ⌋
  
  -- lookup : (k : Key) → Tree → Maybe (Value k)
  -- lookup k (tree t) = Indexed.lookup k t
  
    fromList : List T → Bag
    fromList = List.foldr insert empty
  
    toList′ : Bag → List (T × ℤ)
    toList′ = id
  
    -- To convert to a list without multiplicities, this replicates elements.
    -- Ehm.... not really, I botched this *and* its interface (which would only
    -- work for bags without negative multiplicities, as in BagAVL.
    --
    --toList : Bag → List T
    --toList = List.map proj₁
  
    invert : Bag → Bag
    invert = List.map (uncurry (λ el count → (el , - count)))
  
    postulate intersect : Bag → Bag → Bag
    --intersect = {!!}

--open BagAVL
  open BagList2 public
  
  import Algebra.Structures
  
  postulate isBagAbelianGroup : Algebra.Structures.IsAbelianGroup _≡_ union empty invert
  
  BagGroup :  AbelianGroup L.zero L.zero
  BagGroup = record
                { Carrier = Bag
                ; _≈_ = _≡_
                ; _∙_ = union
                ; ε = empty
                ; _⁻¹ = invert
                ; isAbelianGroup = isBagAbelianGroup
  {-
                ; isAbelianGroup = record
                   { isGroup = record
                     { isMonoid = record
                       { isSemigroup = record
                         { isEquivalence = P.isEquivalence
                         ; assoc = λ x y z → {!!}
                         ; ∙-cong = λ x≡y u≡v → {!!}
                         }
                       ; identity = (λ x → {!!}) , (λ x → {!!})
                       }
                     ; inverse = (λ x → {!!}) , (λ x → {!!}); ⁻¹-cong = λ ≡₁ → {!!}
                     }
                   ; comm = {!!} 
                   }
  -}
                }
    
  
  -- Slightly difficult to implement on the data structure directly. Forget about it.
  --postulate map₀ : ∀ {T U} (oT : Ord T) (oU : Ord U) → (T → U) → Bag oT → Bag oU
  
  -- A list folds of unknown shape
  listFold listFold' : ∀ {a} {A : Set a} → (A → A → A) → A → List A → A
  listFold = List.foldr
  -- To show that the shape is unknown, we show that we could even implement the same type with foldl:
  listFold' = List.foldl
  
  -- The monoid homomorphism, the base operation of the monoid comprehension calculus:
  hom : (G : AbelianGroup L.zero L.zero) → let U = AbelianGroup.Carrier G in (T → U) → Bag → U
  hom G f = uncurry _-_ ∘ map2 (listFold _∙_ ε ∘ List.map f) ∘ toList
    where
      open AbelianGroup G using (_-_; _∙_; ε)

open ParametricBag public renaming (Bag to Bag′)

Bag : ∀ T {{oT : Ord T}} → Set
Bag T = Bag′ {T}

ΔBag : ∀ T {{oT : Ord T}} → Set
ΔBag = Bag

ordN : Ord N.ℕ
ordN = record { isDecTotalOrder = DecTotalOrder.isDecTotalOrder N.decTotalOrder }

aBag : Bag N.ℕ
aBag = insert 1 empty
