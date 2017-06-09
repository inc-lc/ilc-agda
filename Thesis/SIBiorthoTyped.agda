{-# OPTIONS --allow-unsolved-metas #-}
module Thesis.SIBiorthoTyped where

open import Data.Nat using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  nat : Type

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ nat ⟧Type = ℕ

-- Typed deBrujin indexes.

open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public

data Neu (Γ : Context) : Type → Set

Val : Type → Set
Val = Neu ∅

data Term (Γ : Context) : (τ : Type) → Set where
  val : ∀ {τ} → Neu Γ τ → Term Γ τ
  app : ∀ {σ τ} → (v1 : Neu Γ (σ ⇒ τ)) (v2 : Neu Γ σ) → Term Γ τ
  let[_]in_ : ∀ {σ τ} → Term Γ σ → Term (σ • Γ) τ → Term Γ τ

data Neu (Γ : Context) where
  var : ∀ {τ} → (x : Var Γ τ) → Neu Γ τ
  fun : ∀ {σ τ} → (t : Term (σ • σ ⇒ τ • Γ) τ) → Neu Γ (σ ⇒ τ)

-- Context scoping?
data Cont (Γ : Context): Type → Type → Set where
  Id : ∀ {τ} → Cont Γ τ τ
  Cons : ∀ {σ τ κ} → Term (σ • Γ) τ → Cont Γ τ κ → Cont Γ σ κ

-- Too restrictive to define
vsubst : ∀ {Γ σ τ} → Neu Γ σ → Term (σ • Γ) τ → Term Γ τ
vsubst = {!!}

weaken-neu-1 : ∀ {Γ σ τ} → Neu Γ τ → Neu (σ • Γ) τ
weaken-neu-1 (var x) = var (weaken-var (drop _ • ≼-refl) x)
weaken-neu-1 (fun t) = fun {!t!}

data _⊥[_]_:=_ : ∀ {Γ σ τ} → Cont Γ σ τ → ℕ → Term Γ σ → Neu Γ τ → Set where
  Id⊥v : ∀ {n Γ τ} {v : Neu Γ τ} →

    -------------------------------
    Id ⊥[ n ] val v := v

  Cons⊥ : ∀ {n σ τ κ Γ v vr} (E : Cont Γ τ κ) (e : Term (σ • Γ) τ) →

    E ⊥[ n ] vsubst v e := vr →
    -------------------------------
    Cons e E ⊥[ suc n ] val v := vr

  app⊥ :  ∀ {n σ τ κ Γ v2 vr} (E : Cont Γ τ κ)
    (e : Term (σ • σ ⇒ τ • Γ) τ) →

    E ⊥[ n ] vsubst (fun e) (vsubst (weaken-neu-1 v2) e) := vr →
    -----------------------------------------------------------
    E ⊥[ suc n ] app (fun e) v2 := vr

  let⊥ : ∀ {n σ τ κ Γ vr} (E : Cont Γ τ κ) e1 (e2 : Term (σ • Γ) τ) →
    Cons e2 E ⊥[ n ] e1 := vr →
    ---------------------------------
    E ⊥[ suc n ] let[ e1 ]in e2 := vr
