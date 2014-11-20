import Parametric.Syntax.Type as Type

{--
-- Encoding types of polarized System L, as described in "A dissection of L".
--}

module Parametric.Syntax.LType where

-- The treatment of base type seems questionable. We might want instead to
-- distinguish base value types and base computation types. Or not, I'm not
-- sure.

module Structure (Base : Type.Structure) where
  open Type.Structure Base

  mutual
    -- Polarized L.
    --  Values (positive types)
    data VType : Set where
      vB : (ι : Base) → VType

      _⊗_ : (τ₁ : VType) → (τ₂ : VType) → VType
      vUnit : VType

      _⊕_ : (τ₁ : VType) → (τ₂ : VType) → VType
      vZero : VType

      ! : VType → VType
      ↓ : (c : CType) → VType

    data CType : Set where
      cB : (ι : Base) → CType

      _⅋_ : CType → CType → CType
      c⊥ : CType

      _&_ : CType → CType → CType
      c⊤ : CType

      ¿ : CType → CType
      ↑ : VType → CType

  _†v : VType → CType
  _†c : CType → VType

  vB ι †v = cB ι
  (v₁ ⊗ v₂) †v = (v₁ †v) ⅋ (v₂ †v)
  vUnit †v = c⊥
  (v₁ ⊕ v₂) †v = (v₁ †v) & (v₂ †v)
  vZero †v = c⊤
  ! v †v = ¿ (v †v)
  ↓ c †v = ↑ (c †c)

  cB ι †c = vB ι
  (c₁ ⅋ c₂) †c = c₁ †c ⊗ c₂ †c
  c⊥ †c = vUnit
  (c₁ & c₂) †c = (c₁ †c) ⊕ (c₂ †c)
  c⊤ †c = vZero
  ¿ c †c = ! (c †c)
  ↑ v †c = ↓ (v †v)

  open import Relation.Binary.PropositionalEquality

  -- This proof really calls for tactics, doesn't it?
  invV : ∀ {v} → v ≡ v †v †c
  invC : ∀ {c} → c ≡ c †c †v

  invV {vB ι} = refl
  invV {v₁ ⊗ v₂} = cong₂ _⊗_ invV invV
  invV {vUnit} = refl
  invV {v₁ ⊕ v₂} = cong₂ _⊕_ invV invV
  invV {vZero} = refl
  invV { ! v} = cong ! invV
  invV {↓ c} = cong ↓ invC

  invC {cB ι} = refl
  invC {c₁ ⅋ c₂} = cong₂ _⅋_ invC invC
  invC {c⊥} = refl
  invC {c₁ & c₂} = cong₂ _&_ invC invC
  invC {c⊤} = refl
  invC {¿ c} = cong ¿ invC
  invC {↑ x} = cong ↑ invV

  open import Base.Syntax.Context VType public
    using ()
    renaming
      ( ∅ to ∅∅
      ; _•_ to _••_
      ; _⋎_ to _⋎⋎_
      ; mapContext to mapVCtx
      ; Var to VVar
      ; Context to VContext
      ; this to vThis; that to vThat)

  fromVar : ∀ {Γ τ} → (f : Type → VType) → Var Γ τ → VVar (mapVCtx f Γ) (f τ)
  fromVar {x • Γ} f this = vThis
  fromVar {x • Γ} f (that v) = vThat (fromVar f v)

  data VTerm : (Ξ : VContext) → (Γ : VContext) → VType → Set
  data CTerm : (Ξ : VContext) → (Γ : VContext) → CType → Set

  -- Each constructor of the following types encodes a rule from the paper (Fig.
  -- 4); the original names are given in comments at the end of each row.

  data Cmd : (Ξ : VContext) → (Γ : VContext) → Set where
    -- I swapped the operands compared to the cut rule in the paper (Fig. 4),
    -- but this should be purely cosmetic.
    ⟨_∣_⟩ : ∀ {Ξ Γ Δ τ} → (v : CTerm Ξ Δ (τ †v)) → (u : VTerm Ξ Γ τ) → Cmd Ξ (Γ ⋎⋎ Δ) -- cut

  data VTerm where
    lvar : ∀ {Ξ A} → VTerm Ξ (A •• ∅∅) A        -- id
    vvar : ∀ {Ξ A} → VVar Ξ A → VTerm Ξ ∅∅ A   -- id'
    μ⇑_ : ∀ {Ξ Γ N} → Cmd Ξ (N †c •• Γ) → VTerm Ξ Γ (↓ N) -- ↓

    -- Multiplicative fragment
    _,_ : ∀ {Ξ Γ Δ A B} → VTerm Ξ Γ A → VTerm Ξ Δ B → VTerm Ξ (Γ ⋎⋎ Δ) (A ⊗ B) -- ⊗
    ⟨⟩ : ∀ {Ξ} → VTerm Ξ ∅∅ vUnit --1

    -- Additive fragment
    _₁as_ : ∀ {Ξ Γ A} → VTerm Ξ Γ A → ∀ B → VTerm Ξ Γ (A ⊕ B) -- ⊕L
    _₂as_ : ∀ {Ξ Γ B} → VTerm Ξ Γ B → ∀ A → VTerm Ξ Γ (A ⊕ B) -- ⊕R

    -- No rule for vZero

    -- Exponential fragment (in the sense of linear logic)

    ⦃⦄_ : ∀ {Ξ A} → VTerm Ξ ∅∅ A → VTerm Ξ ∅∅ (! A) -- !
    -- : ∀ {Ξ Γ A} →

  -- Compared to the paper, we avoid using † in indexes of the result, and
  -- exploit the fact that † is involutive. See for instance μ
  data CTerm where
    μ : ∀ {Ξ Γ N} → Cmd Ξ (N †c •• Γ) → CTerm Ξ Γ N
    ⇑ : ∀ {Ξ Γ A} → VTerm Ξ Γ A → CTerm Ξ Γ (↑ A) -- ↑

    -- Multiplicative fragment
    μ, : ∀ {Ξ Γ N M} → Cmd Ξ (N †c •• M †c •• Γ) → CTerm Ξ Γ (N ⅋ M) -- ⅋
    μ⟨⟩ : ∀ {Ξ Γ} → Cmd Ξ Γ → CTerm Ξ Γ c⊥ -- ⊥

    -- Additive fragment
    μ₁_μ₂_ : ∀ {Ξ Γ N M} → Cmd Ξ (N †c •• Γ) → Cmd Ξ (M †c •• Γ) → CTerm Ξ Γ (N & M)

    -- Exponential fragment (in the sense of linear logic)
    μ⦃⦄ : ∀ {Ξ Γ N} → Cmd (N †c •• Ξ) Γ → CTerm Ξ Γ (¿ N) -- ?

    -- : ∀ {Ξ Γ τ} →

  cast-invV : ∀ {Ξ Γ N} → VTerm Ξ Γ N → VTerm Ξ Γ ((N †v) †c)
  cast-invV {Ξ} {Γ} t = subst (VTerm Ξ Γ) invV t

  cast-invV2 : ∀ {Ξ Γ N} → VTerm Ξ Γ ((N †v) †c) → VTerm Ξ Γ N
  cast-invV2 {Ξ} {Γ} t = subst (VTerm Ξ Γ) (sym invV) t

  cast-invC : ∀ {Ξ Γ N} → CTerm Ξ Γ N → CTerm Ξ Γ ((N †c) †v)
  cast-invC {Ξ} {Γ} t = subst (CTerm Ξ Γ) invC t

  -- Check that type rules match by doing eta-expansion.
  -- (Is this checking harmony?)
  η-μ : ∀ {Ξ Γ N} → CTerm Ξ Γ N → CTerm Ξ Γ N
  η-μ t = μ ⟨ cast-invC t ∣ lvar ⟩

  maybe-η-μ⇑ : ∀ {Ξ Γ A} → VTerm Ξ Γ A → VTerm Ξ Γ (↓ (↑ A))
  maybe-η-μ⇑ t = μ⇑ ⟨ cast-invC (⇑ t) ∣ lvar ⟩

  -- A "thunk" combinator (from paper)
  ⇓ : ∀ {Ξ Γ N} → CTerm Ξ Γ N → VTerm Ξ Γ (↓ N)
  ⇓ t = μ⇑ ⟨ cast-invC t ∣ lvar ⟩

  -- from paper
  force : ∀ {Ξ Γ N} → VTerm Ξ Γ (↓ N) → CTerm Ξ Γ N
  force t = {! μ ⟨ ⇑ lvar ∣ t ⟩ !}

  -- XXX Here we "just" need to reorder variables in contexts. OMG, I screwed up
  -- (which is bad), or they use implicit exchange (which would be worse).
  η-μ⇑ : ∀ {Ξ Γ N} → VTerm Ξ Γ (↓ N) → VTerm Ξ Γ (↓ N)
  η-μ⇑ t = μ⇑ {! ⟨ ⇑ lvar ∣ t ⟩ !}

  n-μ, : ∀ {Ξ Γ N M} → CTerm Ξ Γ (N ⅋ M) → CTerm Ξ Γ (N ⅋ M)
  n-μ, t = μ, ⟨ cast-invC t ∣ lvar , lvar ⟩ -- The two lvars are in different contexts, so they have different types!

  η-μ⟨⟩ : ∀ {Ξ Γ} → CTerm Ξ Γ c⊥ → CTerm Ξ Γ c⊥
  η-μ⟨⟩ t = μ⟨⟩ ⟨ t ∣ ⟨⟩ ⟩

  η-μ⦃⦄ : ∀ {Ξ Γ N} → CTerm Ξ Γ (¿ N) → CTerm Ξ Γ (¿ N)
  η-μ⦃⦄ t = μ⦃⦄ ⟨  cast-invC {!weaken t!} ∣ ⦃⦄ (vvar vThis) ⟩

  β-expand-μ⟨⟩ : ∀ {Ξ Γ} → Cmd Ξ Γ → Cmd Ξ Γ
  β-expand-μ⟨⟩ c = ⟨ μ⟨⟩ c ∣ ⟨⟩ ⟩

  -- η-rules for sums look different.
  maybe-η-μ₁ : ∀ {Ξ Γ N M} → CTerm Ξ Γ N → CTerm Ξ Γ M → CTerm Ξ Γ (N & M)
  maybe-η-μ₁ t₁ t₂ = μ₁ ⟨ cast-invC t₁ ∣ lvar ⟩ μ₂  ⟨ cast-invC t₂ ∣ lvar ⟩

  η-μ₁ : ∀ {Ξ Γ N M} → CTerm Ξ Γ N → CTerm Ξ Γ M → CTerm Ξ Γ N
  η-μ₁ {M = M} t₁ t₂ =
    μ ⟨
      μ₁ ⟨ cast-invC (cast-invC t₁) ∣ lvar ⟩  μ₂ ⟨ cast-invC (cast-invC t₂) ∣ lvar ⟩
    ∣
      lvar ₁as (M †c)
    ⟩

  η-μ₂ : ∀ {Ξ Γ N M} → CTerm Ξ Γ N → CTerm Ξ Γ M → CTerm Ξ Γ M
  η-μ₂ {N = N} t₁ t₂ =
    μ ⟨
      μ₁ ⟨ cast-invC (cast-invC t₁) ∣ lvar ⟩  μ₂ ⟨ cast-invC (cast-invC t₂) ∣ lvar ⟩
    ∣
      lvar ₂as (N †c)
    ⟩

  -- Some syntactic sugar.
  _⊸_ : VType → CType → CType
  σ ⊸ τ = (σ †v) ⅋ τ

  _⇛_ : VType → CType → CType
  σ ⇛ τ = ! σ ⊸ τ


  -- Not checked again yet. This code comes from CBPV and was refactored for
  -- renamings done to get polarized L, so it might or might not work.

  cbnToCType : Type → CType
  cbnToCType (base ι) = ↑ (vB ι)
  cbnToCType (σ ⇒ τ) = ↓ (cbnToCType σ) ⇛ cbnToCType τ

  cbvToVType : Type → VType
  cbvToVType (base ι) = vB ι
  cbvToVType (σ ⇒ τ) = ↓ (cbvToVType σ ⇛ ↑ (cbvToVType τ))

  cbnToVType : Type → VType
  cbnToVType τ = ↓ (cbnToCType τ)

  cbvToCType : Type → CType
  cbvToCType τ = ↑ (cbvToVType τ)

  fromCBNCtx : Context → VContext
  fromCBNCtx Γ = mapVCtx cbnToVType Γ

  fromCBVCtx : Context → VContext
  fromCBVCtx Γ = mapVCtx cbvToVType Γ

  open import Data.List
  open Data.List using (List) public
  fromCBVToCompList : Context → List CType
  fromCBVToCompList Γ = mapVCtx cbvToCType Γ
