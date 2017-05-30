{-# OPTIONS --allow-unsolved-metas #-}
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

-- Standard relational big-step semantics.
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
  rrelT : ∀ {τ Γ} (t1 : Term Γ τ) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  -- To compare this definition, note that the original k is suc n here.
  rrelT {τ} t1 t2 ρ1 ρ2 n =
    (v1 : Val τ) →
    -- Originally we have 0 ≤ j < k, so j < suc n, so k - j = suc n - j.
    -- It follows that 0 < k - j ≤ k, hence suc n - j ≤ suc n, or n - j ≤ n.
    -- Here, instead of binding j we bind n-j = n - j, require n - j ≤ n, and
    -- use suc n-j instead of k - j.
    ∀ j (j<n : j < n) →
    -- The next assumption is important. This still says that evaluation consumes j steps.
    -- Since j ≤ n, it is OK to start evaluation with n steps.
    -- Starting with (suc n) and getting suc n-j is equivalent, per eval-mono
    -- and eval-strengthen. But in practice this version is easier to use.
    (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t1 ↓[ j ] v1) →
    Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] ρ2 ⊢ t2 ↓[ n2 ] v2 × rrelV τ v1 v2 (n ∸ j)

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

rfundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : rrelρ Γ ρ1 ρ2 n) → rrelT t t ρ1 ρ2 n
rfundamental (var x) n ρ1 ρ2 ρρ = rfundamentalV x n ρ1 ρ2 ρρ
rfundamental (const (lit x)) n ρ1 ρ2 ρρ .(intV x) .0 j<n (lit .x) = intV x , 0 , lit x , I.+ 0 , refl
rfundamental (abs t) n ρ1 ρ2 ρρ .(closure t ρ1) .0 j<n abs = closure t ρ2 , 0 , abs , refl , (λ k k<n v1 v2 vv v3 j j<k ρ1⊢t1↓[j]v1 → rfundamental t k (v1 • ρ1) (v2 • ρ2) (vv , rrelρ-mono k n (lt1 k<n) _ _ _ ρρ) v3 j j<k ρ1⊢t1↓[j]v1 )
rfundamental (app s t) n ρ1 ρ2 ρρ v1 .(suc (n1 + n2 + n3)) j<n (app n1 n2 n3 ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2 ρ1⊢t1↓[j]v3) = body
  where
    n1<n : n1 < n
    n1<n = {!!}
    n2<n : n2 < n
    n2<n = {!!}
    n-n1-n2<n-n1 : n ∸ n1 ∸ n2 < n ∸ n1
    n-n1-n2<n-n1 = {!!}
    n-n1-n2≤n-n2 : n ∸ n1 ∸ n2 ≤ n ∸ n2
    n-n1-n2≤n-n2 = {!!}
    n3<n-n1-n2 : n3 < n ∸ n1 ∸ n2
    n3<n-n1-n2 = {!!}
    n-[1+n1+n2+n3]≤n-n1-n2-n3 : n ∸ suc (n1 + n2 + n3) ≤ n ∸ n1 ∸ n2 ∸ n3
    n-[1+n1+n2+n3]≤n-n1-n2-n3 = {!!}
    body : Σ[ v2 ∈ Val _ ] Σ[ tn ∈ ℕ ] ρ2 ⊢ app s t ↓[ tn ] v2 × rrelV _ v1 v2 (n ∸ suc (n1 + n2 + n3))
    body with rfundamental s n ρ1 ρ2 ρρ _ n1 n1<n ρ1⊢t1↓[j]v1 | rfundamental t n ρ1 ρ2 ρρ _ n2 n2<n ρ1⊢t1↓[j]v2
    ... | sv2@(closure st2 sρ2) , sn2 , ρ2⊢s↓ , refl , sv1v2 | tv2 , tn2 , ρ2⊢t↓ , tv1v2 with sv1v2 (n ∸ n1 ∸ n2) n-n1-n2<n-n1 _ tv2 (rrelV-mono (n ∸ n1 ∸ n2) (n ∸ n2) n-n1-n2≤n-n2 _ _ tv2 tv1v2 ) v1 n3 n3<n-n1-n2 ρ1⊢t1↓[j]v3
    ... | v2 , stn , ρ2⊢st2↓ , vv = v2 , suc (sn2 + tn2 + stn) , app _ _ _ ρ2⊢s↓ ρ2⊢t↓  ρ2⊢st2↓ , rrelV-mono (n ∸ suc (n1 + n2 + n3)) (n ∸ n1 ∸ n2 ∸ n3) n-[1+n1+n2+n3]≤n-n1-n2-n3 _ v1 v2 vv
