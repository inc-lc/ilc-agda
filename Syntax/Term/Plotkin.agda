module Syntax.Term.Plotkin where

-- Terms of languages described in Plotkin style

open import Syntax.Type.Plotkin
open import Syntax.Context.Plotkin
open import Syntax.Language.Base
open import Syntax.Language.Typing

data Term {L : Base} {T : Typing L}
  (Γ : Context {Type (Base.type L)}) :
  (τ : Type (Base.type L)) → Set
  where
  const : (c : Base.const L) → Term Γ (type-of T c)
  app : ∀ {σ τ}
    (s : Term {T = T} Γ (σ ⇒ τ))
    (t : Term {T = T} Γ σ) → Term Γ τ
  abs : ∀ {σ τ} (t : Term {T = T} (σ • Γ) τ) → Term Γ (σ ⇒ τ)
