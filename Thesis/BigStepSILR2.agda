module Thesis.BigStepSILR2 where

open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat -- using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)
open import Thesis.FunBigStepSILR2

-- Standard relational big-step semantics, with step-indexes matching a small-step semantics.
-- Protip: doing this on ANF terms would be much easier.
data _⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : ∀ {τ} → Term Γ τ → ℕ → Val τ → Set where
  abs : ∀ {τ₁ τ₂} {t : Term (τ₁ • Γ) τ₂} →
    ρ ⊢ abs t ↓[ 0 ] closure t ρ
  app : ∀ n1 n2 n3 {Γ′ τ₁ τ₂ ρ′ v₂ v′} {t₁ : Term Γ (τ₁ ⇒ τ₂)} {t₂ : Term Γ τ₁} {t′ : Term (τ₁ • Γ′) τ₂} →
    ρ ⊢ t₁ ↓[ n1 ] closure t′ ρ′ →
    ρ ⊢ t₂ ↓[ n2 ] v₂ →
    (v₂ • ρ′) ⊢ t′ ↓[ n3 ] v′ →
    ρ ⊢ app t₁ t₂ ↓[ suc n1 + n2 + n3 ] v′
  var : ∀ {τ} (x : Var Γ τ) →
    ρ ⊢ var x ↓[ 0 ] (⟦ x ⟧Var ρ)
  lit : ∀ n →
    ρ ⊢ const (lit n) ↓[ 0 ] intV n

-- Silly lemmas for eval-dec-sound
module _ where
  Done-inj : ∀ {τ} m n {v1 v2 : Val τ} → Done v1 m ≡ Done v2 n → m ≡ n
  Done-inj _ _ refl = refl

  lem1 : ∀ n d → d ≢ suc (n + d)
  lem1 n d eq rewrite +-comm n d = m≢1+m+n d eq

  subd : ∀ n d → n + d ≡ d → n ≡ 0
  subd zero d eq = refl
  subd (suc n) d eq = ⊥-elim (lem1 n d (sym eq))

  comp∸ : ∀ a b → b ≤ a → suc a ∸ b ≡ suc (a ∸ b)
  comp∸ a zero le = refl
  comp∸ zero (suc b) ()
  comp∸ (suc a) (suc b) (s≤s le) = comp∸ a b le

  rearr∸ : ∀ a b c → c ≤ b → a + (b ∸ c) ≡ (a + b) ∸ c
  rearr∸ a b zero c≤b = refl
  rearr∸ a zero (suc c) ()
  rearr∸ a (suc b) (suc c) (s≤s c≤b) rewrite +-suc a b = rearr∸ a b c c≤b

  cancel∸ : ∀ a b → b ≤ a → a ∸ b + b ≡ a
  cancel∸ a zero b≤a = +-right-identity a
  cancel∸ zero (suc b) ()
  cancel∸ (suc a) (suc b) (s≤s b≤a) rewrite +-suc (a ∸ b) b = cong suc (cancel∸ a b b≤a)

  lemR : ∀ {τ} n m {v1 v2 : Val τ} → Done v1 m ≡ Done v2 n → m ≡ n
  lemR n .n refl = refl

  lem2 : ∀ n n3 r → n3 ≤ n → n + n3 ≡ suc r → ∃ λ s → (n ≡ suc s)
  lem2 zero .0 r z≤n ()
  lem2 (suc n) n3 .(n + n3) le refl = n , refl

{-# TERMINATING #-}
eval-dec-sound : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ v m n → eval t ρ m ≡ Done v n → ρ ⊢ t ↓[ m ∸ n ] v
eval-dec-sound (const (lit x)) ρ (intV v) m n eq with lemR n m eq
eval-dec-sound (const (lit x)) ρ (intV .x) m .m refl | refl rewrite n∸n≡0 m = lit x
eval-dec-sound (var x) ρ v m n eq with lemR n m eq
eval-dec-sound (var x) ρ .(⟦ x ⟧Var ρ) m .m refl | refl rewrite n∸n≡0 m  = var x
eval-dec-sound (abs t) ρ v m n eq with lemR n m eq
eval-dec-sound (abs t) ρ .(closure t ρ) m .m refl | refl rewrite n∸n≡0 m  = abs
eval-dec-sound (app s t) ρ v zero n ()
eval-dec-sound (app s t) ρ v (suc r) n eq with eval s ρ r | inspect (eval s ρ) r
eval-dec-sound (app s t) ρ v (suc r) n eq | (Done sv n1) | [ seq ] with eval t ρ n1 | inspect (eval t ρ) n1
eval-dec-sound (app s t) ρ v (suc r) n eq | (Done (closure st sρ) n1) | [ seq ] | (Done tv n2) | [ teq ] with eval st (tv • sρ) n2 | inspect (eval st (tv • sρ)) n2
eval-dec-sound (app s t) ρ .v (suc r) .n3 refl | (Done sv@(closure st sρ) n1) | [ seq ] | (Done tv n2) | [ teq ] | (Done v n3) | [ veq ] = body
  where
    n1≤r : n1 ≤ r
    n1≤r = eval-dec s ρ sv r n1 seq
    n2≤n1 : n2 ≤ n1
    n2≤n1 = eval-dec t ρ tv n1 n2 teq
    n3≤n2 : n3 ≤ n2
    n3≤n2 = eval-dec st (tv • sρ) v n2 n3 veq
    eval1 = eval-dec-sound s ρ sv r n1 seq
    eval2 = eval-dec-sound t ρ tv n1 n2 teq
    eval3 = eval-dec-sound st (tv • sρ) v n2 n3 veq
    l1 : suc r ∸ n3 ≡ suc (r ∸ n3)
    l1 = comp∸ r n3 (≤-trans n3≤n2 (≤-trans n2≤n1 n1≤r))
    l2 : suc r ∸ n3 ≡ suc (((r ∸ n1) + (n1 ∸ n2)) + (n2 ∸ n3))
    l2
      rewrite rearr∸ (r ∸ n1) n1 n2 n2≤n1 | cancel∸ r n1 n1≤r
      | rearr∸ (r ∸ n2) n2 n3 n3≤n2 | cancel∸ r n2 (≤-trans n2≤n1 n1≤r) = l1
    foo : ρ ⊢ app s t ↓[ suc (r ∸ n1 + (n1 ∸ n2) + (n2 ∸ n3)) ] v
    foo = app (r ∸ n1) (n1 ∸ n2) (n2 ∸ n3) {t₁ = s} {t₂ = t} {t′ = st} eval1 eval2 eval3
    body : ρ ⊢ app s t ↓[ suc r ∸ n3 ] v
    body rewrite l2 = foo
eval-dec-sound (app s t) ρ v (suc r) n () | (Done (closure st sρ) n1) | [ seq ] | (Done tv n2) | [ teq ] | Error | [ veq ]
eval-dec-sound (app s t) ρ v (suc r) n () | (Done (closure st sρ) n1) | [ seq ] | (Done tv n2) | [ teq ] | TimeOut | [ veq ]
eval-dec-sound (app s t) ρ v (suc r) n () | (Done sv n1) | [ seq ] | Error | [ teq ]
eval-dec-sound (app s t) ρ v (suc r) n () | (Done sv n1) | [ seq ] | TimeOut | [ teq ]
eval-dec-sound (app s t) ρ v (suc r) n () | Error | [ seq ]
eval-dec-sound (app s t) ρ v (suc r) n () | TimeOut | [ seq ]
-- ↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
--   ((Den.⟦ x ⟧Var) (⟦ ρ ⟧Context)) ≡ (⟦ (⟦ x ⟧Var) ρ ⟧Val)
-- ↦-sound (px • ρ) this = refl
-- ↦-sound (px • ρ) (that x) = ↦-sound ρ x

-- ↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
--   ρ ⊢ t ↓ v →
--   ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
-- ↓-sound abs = refl
-- ↓-sound (app ↓₁ ↓₂ ↓′) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ | ↓-sound ↓′ = refl
-- ↓-sound (var x) = ↦-sound _ x
-- ↓-sound (lit n) = refl

import Data.Integer as I
open I using (ℤ)

mutual
  rrelT3 : ∀ {τ Γ ΔΓ} (t1 : Term Γ τ) (dt : Term ΔΓ (Δτ τ)) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (dρ : ⟦ ΔΓ ⟧Context) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  rrelT3 {τ} t1 dt t2 ρ1 dρ ρ2 k =
    (v1 v2 : Val τ) →
    ∀ j n2 (j<k : j < k) →
    (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t1 ↓[ j ] v1) →
    (ρ2⊢t2↓[n2]v2 : ρ2 ⊢ t2 ↓[ n2 ] v2) →
    Σ[ dv ∈ Val (Δτ τ) ] Σ[ dn ∈ ℕ ]
    dρ ⊢ dt ↓[ dn ] dv ×
    rrelV3 τ v1 dv v2 (k ∸ j)

  rrelV3 : ∀ τ (v1 : Val τ) (dv : Val (Δτ τ)) (v2 : Val τ) → ℕ → Set
  rrelV3 nat (intV v1) (intV dv) (intV v2) n = dv + v1 ≡ v2

  -- XXX What we want for rrelV3:
  -- rrelV3 (σ ⇒ τ) (closure {Γ1} t1 ρ1) (dclosure dt dρ) (closure {Γ2} t2 ρ2) n =
  --     Σ (Γ1 ≡ Γ2) λ { refl →
  --       ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
  --       rrelV3 σ v1 dv v2 k →
  --       rrelT3
  --         t1
  --         dt
  --         t2
  --         (v1 • ρ1)
  --         (dv • v1 • dρ)
  --         (v2 • ρ2) k
  --     }

  -- However, we don't have separate change values, so we write:

  rrelV3 (σ ⇒ τ) (closure {Γ1} t1 ρ1) (closure dt' dρ) (closure {Γ2} t2 ρ2) n =
      -- Require a proof that the two contexts match:
      Σ (Γ1 ≡ Γ2) λ { refl →
        ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
        rrelV3 σ v1 dv v2 k →
        rrelT3
          t1
          -- XXX The next expression is wrong.
          -- rrelV3 should require dv to be a change closure,
          -- (λ x dx . dt , dρ) or (dclosure dt dρ).
          -- Then, here we could write as conclusion.
          -- rrelT3 t1 dt t2 (v1 • ρ1) (dv • v1 • dρ) (v2 • ρ2) k

          -- Instead, with this syntax I can just match dv as a normal closure,
          -- closure dt' dρ or (λ x . dt', dρ), where we hope that dt' evaluates
          -- to λ dx. dt. So, instead of writing dt, I must write dt' dx where
          -- dx is a newly bound variable (hence, var this), and dt' must be
          -- weakened once. Hence, we write instead:
          (app (weaken (drop (Δτ σ) • ≼-refl) dt') (var this))
          t2
          (v1 • ρ1)
          (dv • v1 • dρ)
          (v2 • ρ2)
          k
      }


-- The extra "r" stands for "relational", because unlike relT and relV, rrelV
-- and rrelT are based on a *relational* big-step semantics.
mutual
  rrelT : ∀ {τ Γ} (t1 : Term Γ τ) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  rrelT {τ} t1 t2 ρ1 ρ2 k =
    (v1 : Val τ) →
    ∀ j (j<k : j < k) →
    (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t1 ↓[ j ] v1) →
    Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] ρ2 ⊢ t2 ↓[ n2 ] v2 × rrelV τ v1 v2 (k ∸ j)

  rrelV : ∀ τ (v1 v2 : Val τ) → ℕ → Set
  rrelV nat (intV v1) (intV v2) n = Σ[ dv ∈ ℤ ] dv I.+ (I.+ v1) ≡ (I.+ v2)
  rrelV (σ ⇒ τ) (closure {Γ1} t1 ρ1) (closure {Γ2} t2 ρ2) n =
    Σ (Γ1 ≡ Γ2) λ { refl →
      ∀ (k : ℕ) (k<n : k < n) v1 v2 →
      (vv : rrelV σ v1 v2 k) →
      rrelT t1 t2 (v1 • ρ1) (v2 • ρ2) k
    }

rrelρ : ∀ Γ (ρ1 ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
rrelρ ∅ ∅ ∅ n = ⊤
rrelρ (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = rrelV τ v1 v2 n × rrelρ Γ ρ1 ρ2 n

⟦_⟧RelVar : ∀ {Γ τ n} (x : Var Γ τ) {ρ1 ρ2 : ⟦ Γ ⟧Context} →
  rrelρ Γ ρ1 ρ2 n →
  rrelV τ (⟦ x ⟧Var ρ1) (⟦ x ⟧Var ρ2) n
⟦ this ⟧RelVar {v1 • ρ1} {v2 • ρ2} (vv , ρρ) = vv
⟦ that x ⟧RelVar {v1 • ρ1} {v2 • ρ2} (vv , ρρ) = ⟦ x ⟧RelVar ρρ

rrelV-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → rrelV τ v1 v2 n → rrelV τ v1 v2 m
rrelV-mono m n m≤n nat (intV v1) (intV v2) vv = vv
rrelV-mono m n m≤n (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (refl , ff) = refl , λ k k≤m → ff k (≤-trans k≤m m≤n)

rrelρ-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → rrelρ Γ ρ1 ρ2 n → rrelρ Γ ρ1 ρ2 m
rrelρ-mono m n m≤n ∅ ∅ ∅ tt = tt
rrelρ-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = rrelV-mono m n m≤n _ v1 v2 vv , rrelρ-mono m n m≤n Γ ρ1 ρ2 ρρ

rfundamentalV : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : rrelρ Γ ρ1 ρ2 n) → rrelT (var x) (var x) ρ1 ρ2 n
rfundamentalV x n ρ1 ρ2 ρρ .(⟦ x ⟧Var ρ1) .0 j<n (var .x) = ⟦ x ⟧Var ρ2 , 0 , (var x) , ⟦ x ⟧RelVar ρρ

bar : ∀ m {n o} → o ≤ n → m ≤ (m + n) ∸ o
bar m {n} {o} o≤n rewrite +-∸-assoc m o≤n = m≤m+n m (n ∸ o)

suc∸ : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
suc∸ m zero z≤n = refl
suc∸ (suc m) (suc n) (s≤s n≤m) = suc∸ m n n≤m

suc∸suc : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
suc∸suc (suc m) zero (s≤s n<m) = refl
suc∸suc (suc m) (suc n) (s≤s n<m) = suc∸suc m n n<m

m≡m∸1+1 : ∀ m {n} → n < m → m ≡ suc (m ∸ 1)
m≡m∸1+1 (suc m) (s≤s n<m) = refl

m∸[n+1]<m : ∀ m n → n < m → m ∸ suc n < m
m∸[n+1]<m (suc m) zero (s≤s n<m) = s≤s ≤-refl
m∸[n+1]<m (suc m) (suc n) (s≤s n<m) rewrite sym (suc∸suc m n n<m) = ≤-step (m∸[n+1]<m m n n<m)

sub∸ : ∀ m n o → m + n ≤ o → n ≤ o ∸ m
sub∸ m n o n+m≤o rewrite +-comm m n | cong (_≤ o ∸ m) (sym (m+n∸n≡m n m)) = ∸-mono n+m≤o (≤-refl {m})

rfundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : rrelρ Γ ρ1 ρ2 n) → rrelT t t ρ1 ρ2 n
rfundamental (var x) n ρ1 ρ2 ρρ = rfundamentalV x n ρ1 ρ2 ρρ
rfundamental (const (lit x)) n ρ1 ρ2 ρρ .(intV x) .0 j<n (lit .x) = intV x , 0 , lit x , I.+ 0 , refl
rfundamental (abs t) n ρ1 ρ2 ρρ .(closure t ρ1) .0 j<n abs = closure t ρ2 , 0 , abs , refl , (λ k k<n v1 v2 vv v3 j j<k ρ1⊢t1↓[j]v1 → rfundamental t k (v1 • ρ1) (v2 • ρ2) (vv , rrelρ-mono k n (lt1 k<n) _ _ _ ρρ) v3 j j<k ρ1⊢t1↓[j]v1 )
rfundamental (app s t) n ρ1 ρ2 ρρ v1 .(suc (n1 + n2 + n3)) 1+n1+n2+n3<n (app n1 n2 n3 ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2 ρ1⊢t1↓[j]v3) = body
  where
    open ≤-Reasoning
    n1≤sum : n1 ≤ n1 + n2 + n3
    n1≤sum rewrite +-assoc n1 n2 n3 = m≤m+n n1 (n2 + n3)
    n1<n : n1 < n
    n1<n = ≤-trans (s≤s (≤-step n1≤sum)) 1+n1+n2+n3<n

    n2≤sum : n2 ≤ n1 + n2 + n3
    n2≤sum rewrite +-assoc n1 n2 n3 = ≤-steps {n2} {n2 + n3} n1 (m≤m+n n2 n3)
    n2<n : n2 < n
    n2<n = ≤-trans (s≤s (≤-step n2≤sum)) 1+n1+n2+n3<n
    n1+n2<n : n1 + n2 < n
    n1+n2<n = ≤-trans (s≤s (≤-step (m≤m+n (n1 + n2) n3))) 1+n1+n2+n3<n
    n2+n1<n : n2 + n1 < n
    n2+n1<n rewrite +-comm n2 n1 = n1+n2<n

    n1+n3≤sum : n1 + n3 ≤ (n1 + n2) + n3
    n1+n3≤sum = m≤m+n n1 n2 +-mono (≤-refl {n3})
    foo : suc n2 ≡ suc (n1 + n2 + n3) ∸ (n1 + n3)
    foo rewrite cong suc (sym (m+n∸n≡m n2 (n1 + n3))) | sym (+-assoc n2 n1 n3) | +-comm n2 n1 = suc∸ (n1 + n2 + n3) (n1 + n3) n1+n3≤sum
    n2<n∸n1 : n2 < n ∸ n1
    n2<n∸n1 rewrite foo = ∸-mono {suc (n1 + n2 + n3)} {n} {n1 + n3} {n1} (lt1 1+n1+n2+n3<n) (m≤m+n n1 n3)
    n-[1+n1+n2]<n-n1 : n ∸ n1 ∸ suc n2 < n ∸ n1
    n-[1+n1+n2]<n-n1 = m∸[n+1]<m (n ∸ n1) n2 n2<n∸n1

    n-[1+n1+n2]<n-n2 : n ∸ n1 ∸ suc n2 < n ∸ n2
    n-[1+n1+n2]<n-n2 rewrite ∸-+-assoc n n1 (suc n2) | +-suc n1 n2 | +-comm n1 n2 | suc∸suc n (n2 + n1) n2+n1<n | sym (∸-+-assoc n n2 n1) = n∸m≤n n1 (n ∸ n2)

    baz : n1 + suc (n2 + suc n3) ≤ n
    baz rewrite +-suc n2 n3 | +-suc n1 (suc (n2 + n3)) | +-suc n1 (n2 + n3) | +-assoc n1 n2 n3 = 1+n1+n2+n3<n
    n3<n-n1-[1+n2] : n3 < n ∸ n1 ∸ suc n2
    n3<n-n1-[1+n2] = sub∸ (suc n2) (suc n3) (n ∸ n1) (sub∸ n1 (suc (n2 + suc n3)) n baz)

    l1 : suc (n1 + n2 + n3) ≡ n1 + suc n2 + n3
    l1 = cong (_+ n3) (sym (+-suc n1 n2))
    n-1+sum≡alt : n ∸ suc (n1 + n2 + n3) ≡ n ∸ n1 ∸ suc n2 ∸ n3
    n-1+sum≡alt rewrite l1 | sym (∸-+-assoc n (n1 + suc n2) n3) | sym (∸-+-assoc n n1 (suc n2)) = refl

    body : Σ[ v2 ∈ Val _ ] Σ[ tn ∈ ℕ ] ρ2 ⊢ app s t ↓[ tn ] v2 × rrelV _ v1 v2 (n ∸ suc (n1 + n2 + n3))
    body with rfundamental s n ρ1 ρ2 ρρ _ n1 n1<n ρ1⊢t1↓[j]v1 | rfundamental t n ρ1 ρ2 ρρ _ n2 n2<n ρ1⊢t1↓[j]v2
    ... | sv2@(closure st2 sρ2) , sn2 , ρ2⊢s↓ , refl , sv1v2 | tv2 , tn2 , ρ2⊢t↓ , tv1v2 with sv1v2 (n ∸ n1 ∸ suc n2) n-[1+n1+n2]<n-n1 _ tv2 (rrelV-mono (n ∸ n1 ∸ suc n2) (n ∸ n2) (lt1 n-[1+n1+n2]<n-n2) _ _ tv2 tv1v2) v1 n3 n3<n-n1-[1+n2]  ρ1⊢t1↓[j]v3
    ... | v2 , stn , ρ2⊢st2↓ , vv rewrite n-1+sum≡alt = v2 , suc (sn2 + tn2 + stn) , app _ _ _ ρ2⊢s↓ ρ2⊢t↓  ρ2⊢st2↓ , vv
