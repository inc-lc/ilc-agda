{-# OPTIONS --allow-unsolved-metas #-}
module Thesis.SIBiortho where

open import Data.Nat using (ℕ; zero; suc; decTotalOrder; _<_; _≤_; _+_)
open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)

-- Untyped deBrujin indexes.
Ctx = ℕ

data Var : Ctx → Set where
  this : ∀ {n} → Var (suc n)
  that : ∀ {n} → Var n → Var (suc n)

data Term (s : Ctx) : Set

data Neu (s : Ctx) : Set where
  var : (x : Var s) → Neu s
  fun : Term (suc (suc s)) → Neu s

Val = Neu 0

data Term (s : Ctx) where
  val : Neu s → Term s
  app : (v1 v2 : Neu s) → Term s
  let[_]in_ : Term s → Term (suc s) → Term s

-- Scoping's broken?
data Cont (s : Ctx) : Set where
  Id : Cont s
  Cons : Term (suc s) → Cont s → Cont s

vsubst : ∀ {s} → Neu s → Term (suc s) → Term s
vsubst = {!!}

weaken-var : ∀ {s} → Var s → Var (suc s)
weaken-var this = that this
weaken-var (that x) = that (that x)

open import Data.Vec
var-lookup : ∀ {s} {A : Set} → Var s → Vec A s → A
var-lookup this (v ∷ vs) = v
var-lookup (that x) (v ∷ vs) = var-lookup x vs

weaken-var-sound : ∀ {s A} x (vs : Vec A s) v' → var-lookup x vs ≡ var-lookup (weaken-var x) (v' ∷ vs)
weaken-var-sound this (v ∷ vs) v' = refl
weaken-var-sound (that x) (v ∷ vs) v' = refl

weaken-neu-1 : ∀ {s} → Neu s → Neu (suc s)
weaken-neu-1 (var x) = var (weaken-var x)
weaken-neu-1 (fun f) = fun {!f!}

-- Termination, as specified by source.
-- Plus a value.
data _⊥[_]_:=_ : ∀ {s} → Cont s → (n : ℕ) → Term s → Neu s → Set where
  Id⊥v : ∀ {n s} {v : Neu s} →

    -------------------------------
    Id ⊥[ n ] val v := v

  Cons⊥ : ∀ {n s v vr} (E : Cont s) (e : Term (suc s)) →

    E ⊥[ n ] vsubst v e := vr →
    -------------------------------
    Cons e E ⊥[ suc n ] val v := vr

  app⊥ :  ∀ {n s v2 vr} (E : Cont s)
    (e : Term (2 + s)) →

    E ⊥[ n ] vsubst (fun e) (vsubst (weaken-neu-1 v2) e) := vr →
    -----------------------------------------------------------
    E ⊥[ suc n ] app (fun e) v2 := vr

  let⊥ : ∀ {n s vr} (E : Cont s) e1 (e2 : Term (suc s)) →
    Cons e2 E ⊥[ n ] e1 := vr →
    ---------------------------------
    E ⊥[ suc n ] let[ e1 ]in e2 := vr
