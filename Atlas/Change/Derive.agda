module Atlas.Change.Derive where

open import Atlas.Syntax.Type
open import Atlas.Syntax.Term
open import Atlas.Change.Type
open import Atlas.Change.Term

ΔConst : ∀ {Γ Σ τ} →
  Const Σ τ →
  Terms (ΔContext Γ) (ΔContext Σ) →
  Term (ΔContext Γ) (ΔType τ)

ΔConst true  ∅ = false!
ΔConst false ∅ = false!

ΔConst xor (Δx • x • Δy • y • ∅) = xor! Δx Δy

ΔConst empty ∅ = empty!

-- If k ⊕ Δk ≡ k, then
--   Δupdate k Δk v Δv m Δm = update k Δv Δm
-- else it is a deletion followed by insertion:
--   Δupdate k Δk v Δv m Δm =
--     insert (k ⊕ Δk) (v ⊕ Δv) (delete k v Δm)
--
-- We implement the else-branch only for the moment.
ΔConst (update {κ} {ι}) (Δk • k • Δv • v • Δm • m • ∅) =
  insert (apply {base κ} Δk k) (apply {base ι} Δv v) (delete k v Δm)

-- Δlookup k Δk m Δm | true? (k ⊕ Δk ≡ k)
-- ... | true  = lookup k Δm
-- ... | false =
--   (lookup (k ⊕ Δk) m ⊕ lookup (k ⊕ Δk) Δm)
--     ⊝ lookup k m
--
-- Only the false-branch is implemented.
ΔConst (lookup {κ} {ι}) (Δk • k • Δm • m • ∅) =
  let
    k′ = apply {base κ} Δk k
  in
    (diff (apply {base _} (lookup! k′ Δm) (lookup! k′ m))
          (lookup! k m))

-- Δzip f Δf m₁ Δm₁ m₂ Δm₂ | true? (f ⊕ Δf ≡ f)
--
-- ... | true =
--   zip (λ k Δv₁ Δv₂ → Δf (lookup k m₁) Δv₁ (lookup k m₂) Δv₂)
--       Δm₁ Δm₂
--
-- ... | false = zip₄ Δf m₁ Δm₁ m₂ Δm₂
--
-- we implement the false-branch for the moment.
ΔConst zip (Δf • f • Δm₁ • m₁ • Δm₂ • m₂ • ∅) =
  let
    g = abs (app₂ (weaken₁ Δf) (var this) nil-term)
  in
    zip4! g m₁ Δm₁ m₂ Δm₂

-- Δfold f Δf z Δz m Δm = proj₂
--   (fold (λ k [a,Δa] [b,Δb] →
--           uncurry (λ a Δa → uncurry (λ b Δb →
--             pair (f k a b) (Δf k nil a Δa b Δb))
--             [b,Δb]) [a,Δa])
--        (pair z Δz)
--        (zip-pair m Δm))
--
-- Δfold is efficient only if evaluation is lazy and Δf is
-- self-maintainable: it doesn't look at the argument
-- (b = fold f k a b₀) at all.
ΔConst (fold {κ} {α} {β}) (Δf′ • f′ • Δz • z • Δm • m • ∅) =
    let -- TODO (tedius): write weaken₇
      f  = weaken₃ (weaken₃ (weaken₁
        f′))
      Δf = weaken₃ (weaken₃ (weaken₁
        Δf′))
      k = weaken₃ (weaken₁ (var (that (that this))))
      [a,Δa] = var (that this)
      [b,Δb] = var this
      a  = var (that (that (that this)))
      Δa = var (that (that this))
      b  = var (that this)
      Δb = var this
      g = abs (abs (abs (uncurry (abs (abs (uncurry (abs (abs
            (pair (app₃ f k a b)
                  (app₆ Δf k nil-term a Δa b Δb))))
            (weaken₂ [b,Δb])))) [a,Δa])))
      proj₂ = uncurry (abs (abs (var this)))
    in
      proj₂ (fold! g (pair z Δz) (zip-pair m Δm))
