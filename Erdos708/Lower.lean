import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Erdős Problem #708 — Lower Bounds, Exact Small Values & Split-Clique Construction

## Problem Statement (Erdős–Surányi 1959, Erdős Problem #708)
Let `g(n)` be the minimal integer `k` such that for EVERY finite set `A ⊆ [2, ∞) ∩ ℕ` with
`|A| = n` and EVERY interval `I` of `max(A)` consecutive positive integers, there exists
`B ⊆ I` with `|B| ≤ k` such that `∏ a ∈ A, a ∣ ∏ b ∈ B, b`.

## Main Unconditional Results in This File (Pure Mathlib)
1. **Exact small values**:
   - `erdos708_exact_one`: `g(1) = 1`.
   - `erdos708_exact_two`: `g(2) = 2` (complete proof of both upper and lower bounds).
   - `erdos708_lower_three`: `g(3) ≥ 4` (via `{77, 91, 143}` and CRT).
   - `erdos708_lower_four`: `g(4) ≥ 5` (via `{77, 91, 139, 143}` and CRT).
2. **Split-Clique Lower Bound Theorem (`splitClique_lower_bound_of_clusters`)**:
   Given explicit disjoint prime clusters `P, Q` (all primes `≥ 5`) satisfying
   `p_max * q_max < 2 * (p_min ^ 2 - p_min)` and `p_max * q_max < q_min ^ 2 - q_min`,
   every `1 ≤ n ≤ r(r+1)/2 + r*s` satisfies `g(n) ≥ 2n - (2r + s) + 1`.
3. **Sharp Concrete Lower Bounds**:
   - `erdos708_lower_five : ¬ SatisfiesBound 5 5` (`P = {17, 19}`, `Q = {23}`).
   - `erdos708_lower_six : ¬ SatisfiesBound 6 6` (`P = {29, 31}`, `Q = {37, 41}`).
   - `erdos708_lower_seven : ¬ SatisfiesBound 7 8` (`P = {29, 31}`, `Q = {37, 41}`).
   (Further sharpened to `g(6) ≥ 8` in `Erdos708.G3AndG6Lower`.)
4. **Structural Valuation Barrier (`exists_cover_le_two_mul_of_semiprimes`)**:
   Every valid `(A, I)` admits a cover of size `≤ ∑ a ∈ A, Ω(a)`, so any set of primes
   and semiprimes admits a cover of size `≤ 2n`.
-/

namespace Erdos708

open Finset
open scoped BigOperators

/-! ## Section 1: Native-Mathlib Definitions for Erdős Problem #708 -/

/-- Interval of `M` consecutive positive integers `{x + 1, x + 2, ..., x + M}`. -/
def consecInterval (x M : ℕ) : Finset ℕ :=
  Finset.Icc (x + 1) (x + M)

/-- `A` is a valid `n`-element subset of `[2, ∞) ∩ ℕ`. -/
def IsValidSet (A : Finset ℕ) (n : ℕ) : Prop :=
  A.card = n ∧ ∀ a ∈ A, 2 ≤ a

/-- `B` covers `A` iff `∏ a ∈ A, a ∣ ∏ b ∈ B, b`. -/
def IsCover (A B : Finset ℕ) : Prop :=
  (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

/-- `SatisfiesBound n k` means `g(n) ≤ k`: for every valid `n`-element set `A` and every
interval `I` of `max(A)` consecutive positive integers, some `B ⊆ I` of size `≤ k` covers `A`. -/
def SatisfiesBound (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty), IsValidSet A n →
    ∀ x : ℕ, ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ k ∧ IsCover A B

/-- Convenience lemma: cardinality of `consecInterval x M`. -/
lemma card_consecInterval (x M : ℕ) : (consecInterval x M).card = M := by
  unfold consecInterval
  rw [Nat.card_Icc]
  omega

/-- Every element of `consecInterval x M` is positive. -/
lemma pos_of_mem_consecInterval {x M b : ℕ} (hb : b ∈ consecInterval x M) : 0 < b := by
  unfold consecInterval at hb
  rw [Finset.mem_Icc] at hb
  omega

/-- Every interval of `M` consecutive positive integers contains a multiple of any `d` with `0 < d ≤ M`. -/
lemma exists_multiple_in_consecInterval (x d M : ℕ) (hd : 0 < d) (hdM : d ≤ M) :
    ∃ b ∈ consecInterval x M, d ∣ b := by
  set r := (x + 1) % d with hr_def
  by_cases hr0 : r = 0
  · refine ⟨x + 1, ?_, Nat.dvd_of_mod_eq_zero hr0⟩
    unfold consecInterval
    rw [Finset.mem_Icc]
    omega
  · have hr_lt : r < d := Nat.mod_lt (x + 1) hd
    refine ⟨x + 1 + (d - r), ?_, ?_⟩
    · unfold consecInterval
      rw [Finset.mem_Icc]
      omega
    · have hdiv := Nat.div_add_mod (x + 1) d
      refine ⟨(x + 1) / d + 1, ?_⟩
      rw [mul_add, mul_one]
      omega

/-- If `2 * d ≤ M` and `b₁ ∈ consecInterval x M` is a multiple of `d`, there is a second distinct
multiple `b₂ ∈ consecInterval x M` of `d`. -/
lemma exists_second_multiple_in_consecInterval {x d M b₁ : ℕ} (hd : 0 < d) (h2d : 2 * d ≤ M)
    (hb₁ : b₁ ∈ consecInterval x M) (hdvd : d ∣ b₁) :
    ∃ b₂ ∈ consecInterval x M, b₂ ≠ b₁ ∧ d ∣ b₂ := by
  unfold consecInterval at hb₁ ⊢
  rw [Finset.mem_Icc] at hb₁
  by_cases hhi : b₁ + d ≤ x + M
  · refine ⟨b₁ + d, Finset.mem_Icc.mpr ⟨by omega, hhi⟩, by omega, dvd_add hdvd dvd_rfl⟩
  · refine ⟨b₁ - d, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩
    exact Nat.dvd_sub hdvd dvd_rfl

/-! ## Section 2: Exact Base Cases `g(1) = 1` and `g(2) = 2` -/

/-- Upper bound `g(1) ≤ 1`. -/
theorem erdos708_upper_one : SatisfiesBound 1 1 := by
  intro A hA ⟨hcard, hge2⟩ x
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  have ha2 : 2 ≤ a := hge2 a (Finset.mem_singleton_self a)
  have hmax : ({a} : Finset ℕ).max' hA = a := Finset.max'_singleton a
  rw [hmax]
  obtain ⟨b, hbI, hab⟩ := exists_multiple_in_consecInterval x a a (by omega) le_rfl
  refine ⟨{b}, Finset.singleton_subset_iff.mpr hbI, by simp, ?_⟩
  unfold IsCover
  simpa using hab

/-- Lower bound `g(1) ≥ 1`. -/
theorem erdos708_lower_one : ¬ SatisfiesBound 1 0 := by
  intro h
  have hne : ({2} : Finset ℕ).Nonempty := Finset.singleton_nonempty 2
  have hval : IsValidSet {2} 1 := ⟨by simp, by intro a ha; simp at ha; omega⟩
  obtain ⟨B, _, hBcard, hcov⟩ := h {2} hne hval 0
  have hBemp : B = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hBcard)
  rw [hBemp] at hcov
  unfold IsCover at hcov
  norm_num at hcov

/-- **Exact value `g(1) = 1`.** -/
theorem erdos708_exact_one : SatisfiesBound 1 1 ∧ ¬ SatisfiesBound 1 0 :=
  ⟨erdos708_upper_one, erdos708_lower_one⟩

/-- Helper for `g(2) ≤ 2`: if `2 ≤ a₁ < a₂`, then `2 * gcd(a₁, a₂) ≤ a₂`. -/
private lemma two_mul_gcd_le_of_lt {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (hlt : a₁ < a₂) :
    2 * Nat.gcd a₁ a₂ ≤ a₂ := by
  set d := Nat.gcd a₁ a₂
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left a₂ (by omega)
  have hd1 : d ∣ a₁ := Nat.gcd_dvd_left a₁ a₂
  have hd2 : d ∣ a₂ := Nat.gcd_dvd_right a₁ a₂
  have hd_le1 : d ≤ a₁ := Nat.le_of_dvd (by omega) hd1
  by_cases heq : d = a₁
  · obtain ⟨k, hk⟩ := hd2
    rw [heq] at hk
    have hk2 : 2 ≤ k := by nlinarith
    nlinarith
  · obtain ⟨k, hk⟩ := hd1
    have hk2 : 2 ≤ k := by
      have hne0 : k ≠ 0 := by intro h0; rw [h0, mul_zero] at hk; omega
      have hne1 : k ≠ 1 := by intro h1; rw [h1, mul_one] at hk; exact heq hk.symm
      omega
    nlinarith

/-- Upper bound `g(2) ≤ 2`. -/
theorem erdos708_upper_two : SatisfiesBound 2 2 := by
  intro A hA ⟨hcard, hge2⟩ x
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
  -- WLOG `a₁ < a₂`
  suffices h : ∀ a₁ a₂ : ℕ, 2 ≤ a₁ → a₁ < a₂ →
      ∃ B ⊆ consecInterval x a₂, B.card ≤ 2 ∧ a₁ * a₂ ∣ ∏ b ∈ B, b by
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · have hmax : ({u, v} : Finset ℕ).max' hA = v := by
        apply le_antisymm
        · exact Finset.max'_le _ _ _ (fun y hy => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> omega)
        · exact Finset.le_max' _ _ (by simp)
      rw [hmax]
      obtain ⟨B, hBI, hBcard, hdvd⟩ := h u v (hge2 u (by simp)) hlt
      refine ⟨B, hBI, hBcard, ?_⟩
      unfold IsCover
      rwa [Finset.prod_pair huv]
    · have hmax : ({u, v} : Finset ℕ).max' hA = u := by
        apply le_antisymm
        · exact Finset.max'_le _ _ _ (fun y hy => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> omega)
        · exact Finset.le_max' _ _ (by simp)
      rw [hmax]
      obtain ⟨B, hBI, hBcard, hdvd⟩ := h v u (hge2 v (by simp)) hgt
      refine ⟨B, hBI, hBcard, ?_⟩
      unfold IsCover
      rw [Finset.prod_pair huv, mul_comm]
      exact hdvd
  intro a₁ a₂ ha₁ hlt
  obtain ⟨b₁, hb₁I, ha₁b₁⟩ := exists_multiple_in_consecInterval x a₁ a₂ (by omega) hlt.le
  obtain ⟨b₂, hb₂I, ha₂b₂⟩ := exists_multiple_in_consecInterval x a₂ a₂ (by omega) le_rfl
  by_cases hne : b₁ ≠ b₂
  · refine ⟨{b₁, b₂}, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hb₁I (Finset.singleton_subset_iff.mpr hb₂I)
    · rw [Finset.card_pair hne]
    · rw [Finset.prod_pair hne]
      exact mul_dvd_mul ha₁b₁ ha₂b₂
  · push Not at hne
    subst hne
    set d := Nat.gcd a₁ a₂
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left a₂ (by omega)
    have h2d : 2 * d ≤ a₂ := two_mul_gcd_le_of_lt ha₁ hlt
    have hlcm : Nat.lcm a₁ a₂ ∣ b₁ := Nat.lcm_dvd ha₁b₁ ha₂b₂
    have hdb₁ : d ∣ b₁ := dvd_trans (Nat.gcd_dvd_left a₁ a₂) ha₁b₁
    obtain ⟨b', hb'I, hb'ne, hdb'⟩ :=
      exists_second_multiple_in_consecInterval hd_pos h2d hb₁I hdb₁
    refine ⟨{b₁, b'}, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hb₁I (Finset.singleton_subset_iff.mpr hb'I)
    · rw [Finset.card_pair hb'ne.symm]
    · rw [Finset.prod_pair hb'ne.symm]
      have hprod : a₁ * a₂ = Nat.lcm a₁ a₂ * d := by
        rw [← Nat.gcd_mul_lcm a₁ a₂, mul_comm]
      rw [hprod]
      exact mul_dvd_mul hlcm hdb'

/-- Lower bound `g(2) ≥ 2` via `A = {2, 3}` and `I = {2, 3, 4}`. -/
theorem erdos708_lower_two : ¬ SatisfiesBound 2 1 := by
  intro h
  have hne : ({2, 3} : Finset ℕ).Nonempty := by simp
  have hval : IsValidSet {2, 3} 2 := ⟨by decide, by intro a ha; simp at ha; omega⟩
  obtain ⟨B, hBI, hBcard, hcov⟩ := h {2, 3} hne hval 1
  have hmax : ({2, 3} : Finset ℕ).max' hne = 3 :=
    le_antisymm (Finset.max'_le _ _ _ (by intro a ha; simp at ha; omega))
      (Finset.le_max' _ _ (by simp))
  rw [hmax] at hBI
  unfold IsCover at hcov
  have hprodA : ∏ a ∈ ({2, 3} : Finset ℕ), a = 6 := by decide
  rw [hprodA] at hcov
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hBcard with h0 | h1
  · rw [Finset.card_eq_zero.mp h0] at hcov
    norm_num at hcov
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.prod_singleton] at hcov
    have hb : b ∈ consecInterval 1 3 := hBI (Finset.mem_singleton_self b)
    unfold consecInterval at hb
    rw [Finset.mem_Icc] at hb
    omega

/-- **Exact value `g(2) = 2`.** -/
theorem erdos708_exact_two : SatisfiesBound 2 2 ∧ ¬ SatisfiesBound 2 1 :=
  ⟨erdos708_upper_two, erdos708_lower_two⟩

/-! ## Section 3: General Finite-Set Chinese Remainder Theorem & Factorization Helpers -/

/-- General CRT on a `Finset ℕ` of pairwise coprime positive moduli:
for any lower bound `M₀`, there exists `N > M₀` solving all congruences simultaneously. -/
lemma exists_crt_finset (S : Finset ℕ) (m f : ℕ → ℕ)
    (hm_pos : ∀ u ∈ S, 0 < m u)
    (hcop : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Nat.Coprime (m u) (m v))
    (M₀ : ℕ) :
    ∃ N : ℕ, M₀ < N ∧ ∀ u ∈ S, N ≡ f u [MOD m u] := by
  -- First prove existence without the `M₀ < N` bound, then add a multiple of `∏ u ∈ S, m u`.
  suffices hbase : ∃ N₀ : ℕ, ∀ u ∈ S, N₀ ≡ f u [MOD m u] by
    obtain ⟨N₀, hN₀⟩ := hbase
    set P := ∏ u ∈ S, m u
    have hP_pos : 0 < P := Finset.prod_pos hm_pos
    refine ⟨N₀ + (M₀ + 1) * P, ?_, ?_⟩
    · nlinarith
    · intro u hu
      have hdiv : m u ∣ P := Finset.dvd_prod_of_mem m hu
      have hmod0 : (M₀ + 1) * P ≡ 0 [MOD m u] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hdiv _)
      have hadd := (hN₀ u hu).add hmod0
      simpa using hadd
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    have hm_s : ∀ u ∈ s, 0 < m u := fun u hu => hm_pos u (Finset.mem_insert_of_mem hu)
    have hcop_s : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Nat.Coprime (m u) (m v) := fun u hu v hv hne =>
      hcop u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) hne
    obtain ⟨N₀, hN₀⟩ := ih hm_s hcop_s
    have hcop_aP : Nat.Coprime (m a) (∏ u ∈ s, m u) :=
      Nat.Coprime.prod_right fun u hu =>
        hcop a (Finset.mem_insert_self a s) u (Finset.mem_insert_of_mem hu)
          (fun h => ha (h ▸ hu))
    let res := Nat.chineseRemainder hcop_aP (f a) N₀
    refine ⟨res.1, ?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hus
    · exact res.2.1
    · have hdiv : m u ∣ ∏ v ∈ s, m v := Finset.dvd_prod_of_mem m hus
      exact (res.2.2.of_dvd hdiv).trans (hN₀ u hus)

/-- Factorization of a finset product of positive numbers equals the sum of factorizations. -/
lemma factorization_finset_prod (S : Finset ℕ) (hpos : ∀ a ∈ S, a ≠ 0) (p : ℕ) :
    (∏ a ∈ S, a).factorization p = ∑ a ∈ S, a.factorization p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 : a ≠ 0 := hpos a (Finset.mem_insert_self a s)
    have hs0 : ∀ b ∈ s, b ≠ 0 := fun b hb => hpos b (Finset.mem_insert_of_mem hb)
    have hprod0 : (∏ b ∈ s, b) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.factorization_mul ha0 hprod0,
        Finsupp.add_apply, ih hs0]

/-- Divisibility of products implies valuation inequality for every prime `p`. -/
lemma sum_factorization_le_of_isCover {A B : Finset ℕ}
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0) (hcov : IsCover A B) (p : ℕ) :
    ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B, b.factorization p := by
  rw [← factorization_finset_prod A hA0 p, ← factorization_finset_prod B hB0 p]
  have hBprod0 : (∏ b ∈ B, b) ≠ 0 := Finset.prod_ne_zero_iff.mpr hB0
  exact Nat.factorization_le_iff_dvd (Finset.prod_ne_zero_iff.mpr hA0) hBprod0 |>.mpr hcov p

/-- If `b.factorization p = 0` whenever `¬ (p ∣ b)`, then summing `b.factorization p` over `B`
equals summing over `B.filter (p ∣ ·)`. -/
lemma sum_factorization_eq_filter (B : Finset ℕ) (p : ℕ) :
    ∑ b ∈ B, b.factorization p = ∑ b ∈ B.filter (fun b => p ∣ b), b.factorization p := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ B)
  intro b _ hb
  rw [Finset.mem_filter] at hb
  have hnd : ¬ (p ∣ b) := fun h => hb ⟨‹_›, h⟩
  exact Nat.factorization_eq_zero_of_not_dvd hnd

/-- If `b₀ ≡ r [MOD m]` and `b ∈ [b₀ - L, b₀ + L]` and `m ∣ b`, then either `r ≤ L` or `m - r ≤ L`
(when `r < m`). -/
lemma not_dvd_of_modEq_and_dist {b₀ b m r L : ℕ} (hr : r < m) (hmod : b₀ ≡ r [MOD m])
    (hlo : b₀ - L ≤ b) (hhi : b ≤ b₀ + L) (hL_le : L ≤ b₀)
    (h1 : L < r) (h2 : L < m - r) : ¬ (m ∣ b) := by
  intro hdvd
  have hmod_b : b % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hmod_b0 : b₀ % m = r := by
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt hr]
  obtain ⟨k, hk⟩ := hdvd
  -- `b₀ = m * (b₀ / m) + r`
  have hb0_eq : b₀ = m * (b₀ / m) + r := by
    have := Nat.div_add_mod b₀ m
    omega
  rcases le_or_gt k (b₀ / m) with hkq | hkq
  · -- `b = m * k ≤ m * (b₀ / m) = b₀ - r`, so `b₀ - b ≥ r > L`, contradicting `b₀ - L ≤ b`
    have : m * k ≤ m * (b₀ / m) := Nat.mul_le_mul_left m hkq
    omega
  · -- `k ≥ b₀ / m + 1`, so `b = m * k ≥ m * (b₀ / m + 1) = b₀ + (m - r)`, contradicting `b ≤ b₀ + L`
    have : m * (b₀ / m + 1) ≤ m * k := Nat.mul_le_mul_left m hkq
    rw [mul_add, mul_one] at this
    omega

/-- Pairwise disjointness of `B.filter (u ∣ ·)` across distinct primes when no element of `B`
is divisible by two distinct primes in `U`. -/
lemma sum_card_filter_le_of_no_two_primes (U B : Finset ℕ)
    (hsep : ∀ b ∈ B, ∀ u ∈ U, ∀ v ∈ U, u ≠ v → u ∣ b → ¬ (v ∣ b)) :
    ∑ u ∈ U, (B.filter (fun b => u ∣ b)).card ≤ B.card := by
  have hdisj : Set.PairwiseDisjoint (U : Set ℕ) (fun u => B.filter (fun b => u ∣ b)) := by
    intro u hu v hv huv
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro b hbu hbv
    rw [Finset.mem_filter] at hbu hbv
    exact hsep b hbu.1 u hu v hv huv hbu.2 hbv.2
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro b hb
  rw [Finset.mem_biUnion] at hb
  rcases hb with ⟨_, _, hbf⟩
  exact (Finset.mem_filter.mp hbf).1

/-! ## Section 4: Sharp Concrete Lower Bounds `g(3) ≥ 4` and `g(4) ≥ 5` -/

/-- Helper lemma for `{77, 91, 143}`: given `b₀ > 72` with `b₀ ≡ 7 [MOD 49]`, `b₀ ≡ 11 [MOD 121]`,
`b₀ ≡ 78 [MOD 169]`, any subset `B ⊆ consecInterval (b₀ - 72) 143` covering `77 * 91 * 143`
has `4 ≤ B.card`. -/
private lemma card_ge_four_of_77_91_143 {b₀ : ℕ} (hb0_gt : 72 < b₀)
    (h7 : b₀ ≡ 7 [MOD 49]) (h11 : b₀ ≡ 11 [MOD 121]) (h13 : b₀ ≡ 78 [MOD 169])
    {B : Finset ℕ} (hBI : B ⊆ consecInterval (b₀ - 72) 143)
    (hcov : IsCover {77, 91, 143} B) : 4 ≤ B.card := by
  have hI_bounds : ∀ b ∈ consecInterval (b₀ - 72) 143, b₀ - 71 ≤ b ∧ b ≤ b₀ + 71 := by
    intro b hb
    unfold consecInterval at hb
    rw [Finset.mem_Icc] at hb
    omega
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hA0 : ∀ a ∈ ({77, 91, 143} : Finset ℕ), a ≠ 0 := by decide
  -- Prime divisibilities of `b₀`
  have h7_b0 : 7 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := h7.of_dvd (by norm_num : 7 ∣ 49); simpa [Nat.ModEq] using this)
  have h11_b0 : 11 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := h11.of_dvd (by norm_num : 11 ∣ 121); simpa [Nat.ModEq] using this)
  have h13_b0 : 13 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := h13.of_dvd (by norm_num : 13 ∣ 169); simpa [Nat.ModEq] using this)
  have h49_nb0 : ¬ (49 ∣ b₀) := by
    intro hd; have := Nat.mod_eq_zero_of_dvd hd; rw [Nat.ModEq] at h7; omega
  have h121_nb0 : ¬ (121 ∣ b₀) := by
    intro hd; have := Nat.mod_eq_zero_of_dvd hd; rw [Nat.ModEq] at h11; omega
  have h169_nb0 : ¬ (169 ∣ b₀) := by
    intro hd; have := Nat.mod_eq_zero_of_dvd hd; rw [Nat.ModEq] at h13; omega
  -- Valuations of `b₀`
  have hv7_b0 : b₀.factorization 7 = 1 := by
    have h1 : 1 ≤ b₀.factorization 7 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mp (by simpa using h7_b0)
    have h2 : ¬ (2 ≤ b₀.factorization 7) := by
      intro hge
      exact h49_nb0 ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mpr hge)
    omega
  have hv11_b0 : b₀.factorization 11 = 1 := by
    have h1 : 1 ≤ b₀.factorization 11 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mp (by simpa using h11_b0)
    have h2 : ¬ (2 ≤ b₀.factorization 11) := by
      intro hge
      exact h121_nb0 ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mpr hge)
    omega
  have hv13_b0 : b₀.factorization 13 = 1 := by
    have h1 : 1 ≤ b₀.factorization 13 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mp (by simpa using h13_b0)
    have h2 : ¬ (2 ≤ b₀.factorization 13) := by
      intro hge
      exact h169_nb0 ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by omega)).mpr hge)
    omega
  -- No element of `I` is divisible by `169`, so `b.factorization 13 ≤ 1` for all `b ∈ I`
  have hv13_le1 : ∀ b ∈ consecInterval (b₀ - 72) 143, b.factorization 13 ≤ 1 := by
    intro b hb
    have ⟨hlo, hhi⟩ := hI_bounds b hb
    have hnd : ¬ (169 ∣ b) := not_dvd_of_modEq_and_dist (by norm_num) h13 hlo hhi (by omega)
      (by norm_num) (by norm_num)
    by_contra hgt
    have hge2 : 2 ≤ b.factorization 13 := by omega
    exact hnd ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num)
      (pos_of_mem_consecInterval hb).ne').mpr hge2)
  -- No element of `I \ {b₀}` is divisible by two distinct primes from `{7, 11, 13}`
  have hsep : ∀ b ∈ B.erase b₀, ∀ u ∈ ({7, 11, 13} : Finset ℕ), ∀ v ∈ ({7, 11, 13} : Finset ℕ),
      u ≠ v → u ∣ b → ¬ (v ∣ b) := by
    intro b hb u hu v hv huv hub hvb
    have hne : b ≠ b₀ := (Finset.mem_erase.mp hb).1
    have hbI : b ∈ consecInterval (b₀ - 72) 143 := hBI (Finset.mem_erase.mp hb).2
    have ⟨hlo, hhi⟩ := hI_bounds b hbI
    have hu_b0 : u ∣ b₀ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hv_b0 : v ∣ b₀ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hcop : Nat.Coprime u v := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | exact absurd rfl huv | norm_num
    have huv_ge : 77 ≤ u * v := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | exact absurd rfl huv | norm_num
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hu_sub : u ∣ b₀ - b := Nat.dvd_sub hu_b0 hub
      have hv_sub : v ∣ b₀ - b := Nat.dvd_sub hv_b0 hvb
      have huv_sub : u * v ∣ b₀ - b := hcop.mul_dvd_of_dvd_of_dvd hu_sub hv_sub
      have hle := Nat.le_of_dvd (by omega) huv_sub
      omega
    · have hu_sub : u ∣ b - b₀ := Nat.dvd_sub hub hu_b0
      have hv_sub : v ∣ b - b₀ := Nat.dvd_sub hvb hv_b0
      have huv_sub : u * v ∣ b - b₀ := hcop.mul_dvd_of_dvd_of_dvd hu_sub hv_sub
      have hle := Nat.le_of_dvd (by omega) huv_sub
      omega
  -- Required valuations in `B`: `2` for each of `7, 11, 13`
  have hprod_eq : ∏ a ∈ ({77, 91, 143} : Finset ℕ), a = 7 ^ 2 * 11 ^ 2 * 13 ^ 2 := by norm_num
  have hreq : ∀ p ∈ ({7, 11, 13} : Finset ℕ), 2 ≤ ∑ b ∈ B, b.factorization p := by
    intro p hp
    have hle := sum_factorization_le_of_isCover hA0 hB0 hcov p
    have hfacA : ∑ a ∈ ({77, 91, 143} : Finset ℕ), a.factorization p = 2 := by
      rw [← factorization_finset_prod _ hA0 p, hprod_eq,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply, Finsupp.add_apply,
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 11),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 13)]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp
    omega
  -- Pairwise disjointness sum bound on `B.erase b₀`
  have hsum_card := sum_card_filter_le_of_no_two_primes {7, 11, 13} (B.erase b₀) hsep
  have hsum_expand :
      ∑ u ∈ ({7, 11, 13} : Finset ℕ), ((B.erase b₀).filter (fun b => u ∣ b)).card =
        ((B.erase b₀).filter (fun b => 7 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 11 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 13 ∣ b)).card := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hsum_expand] at hsum_card
  -- Case split on `b₀ ∈ B`
  by_cases hb0B : b₀ ∈ B
  · have hcard_er : (B.erase b₀).card + 1 = B.card := by
      rw [Finset.card_erase_of_mem hb0B]
      have := Finset.card_pos.mpr ⟨b₀, hb0B⟩
      omega
    -- Each of `7, 11, 13` must have sum `≥ 1` on `B.erase b₀`, hence filtered card `≥ 1`
    have hge1 : ∀ p ∈ ({7, 11, 13} : Finset ℕ), b₀.factorization p = 1 →
        1 ≤ ((B.erase b₀).filter (fun b => p ∣ b)).card := by
      intro p hp hvb0
      have htot := hreq p hp
      rw [← Finset.add_sum_erase B (fun b => b.factorization p) hb0B, hvb0] at htot
      rw [sum_factorization_eq_filter] at htot
      by_contra hlt
      have h0 : ((B.erase b₀).filter (fun b => p ∣ b)).card = 0 := by omega
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at htot
      omega
    have c7 := hge1 7 (by decide) hv7_b0
    have c11 := hge1 11 (by decide) hv11_b0
    have c13 := hge1 13 (by decide) hv13_b0
    omega
  · have hBer : B.erase b₀ = B := Finset.erase_eq_of_notMem hb0B
    rw [hBer] at hsum_card
    have hge1 : ∀ p ∈ ({7, 11, 13} : Finset ℕ),
        1 ≤ (B.filter (fun b => p ∣ b)).card := by
      intro p hp
      have htot := hreq p hp
      rw [sum_factorization_eq_filter] at htot
      by_contra hlt
      have h0 : (B.filter (fun b => p ∣ b)).card = 0 := by omega
      rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at htot
      omega
    have c7 := hge1 7 (by decide)
    have c11 := hge1 11 (by decide)
    have c13 : 2 ≤ (B.filter (fun b => 13 ∣ b)).card := by
      have htot := hreq 13 (by decide)
      rw [sum_factorization_eq_filter] at htot
      have hle : ∑ b ∈ B.filter (fun b => 13 ∣ b), b.factorization 13 ≤
          (B.filter (fun b => 13 ∣ b)).card := by
        calc ∑ b ∈ B.filter (fun b => 13 ∣ b), b.factorization 13
            ≤ ∑ _b ∈ B.filter (fun b => 13 ∣ b), 1 :=
              Finset.sum_le_sum fun b hb => hv13_le1 b (hBI (Finset.mem_filter.mp hb).1)
          _ = (B.filter (fun b => 13 ∣ b)).card := by simp
      omega
    omega

/-- **Erdős–Surányi Lower Bound `g(3) ≥ 4` (via `A = {77, 91, 143}`).** -/
theorem erdos708_lower_three : ¬ SatisfiesBound 3 3 := by
  intro h
  -- Solve CRT for `{7, 11, 13}` with moduli `49, 121, 169` and targets `7, 11, 78`
  let m : ℕ → ℕ := fun u => u ^ 2
  let f : ℕ → ℕ := fun u => if u = 13 then 78 else u
  obtain ⟨b₀, hb0_gt, hmod⟩ := exists_crt_finset {7, 11, 13} m f
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl <;> norm_num [m])
    (by intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          first | exact absurd rfl huv | norm_num [m])
    72
  have h7 : b₀ ≡ 7 [MOD 49] := by simpa [m, f] using hmod 7 (by decide)
  have h11 : b₀ ≡ 11 [MOD 121] := by simpa [m, f] using hmod 11 (by decide)
  have h13 : b₀ ≡ 78 [MOD 169] := by simpa [m, f] using hmod 13 (by decide)
  have hne : ({77, 91, 143} : Finset ℕ).Nonempty := by simp
  have hval : IsValidSet {77, 91, 143} 3 := ⟨by decide, by intro a ha; simp at ha; omega⟩
  obtain ⟨B, hBI, hBcard, hcov⟩ := h {77, 91, 143} hne hval (b₀ - 72)
  have hmax : ({77, 91, 143} : Finset ℕ).max' hne = 143 :=
    le_antisymm (Finset.max'_le _ _ _ (by intro a ha; simp at ha; omega))
      (Finset.le_max' _ _ (by simp))
  rw [hmax] at hBI
  have hge4 := card_ge_four_of_77_91_143 hb0_gt h7 h11 h13 hBI hcov
  omega

/-- **Sharp Lower Bound `g(4) ≥ 5` (via `A = {77, 91, 139, 143}`).** -/
theorem erdos708_lower_four : ¬ SatisfiesBound 4 4 := by
  intro h
  let m : ℕ → ℕ := fun u => if u = 139 then 139 else u ^ 2
  let f : ℕ → ℕ := fun u => if u = 139 then 138 else if u = 13 then 78 else u
  obtain ⟨b₀, hb0_gt, hmod⟩ := exists_crt_finset {7, 11, 13, 139} m f
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> norm_num [m])
    (by intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl huv | norm_num [m])
    72
  have h7 : b₀ ≡ 7 [MOD 49] := by simpa [m, f] using hmod 7 (by decide)
  have h11 : b₀ ≡ 11 [MOD 121] := by simpa [m, f] using hmod 11 (by decide)
  have h13 : b₀ ≡ 78 [MOD 169] := by simpa [m, f] using hmod 13 (by decide)
  have h139 : b₀ ≡ 138 [MOD 139] := by simpa [m, f] using hmod 139 (by decide)
  have hne : ({77, 91, 139, 143} : Finset ℕ).Nonempty := by simp
  have hval : IsValidSet {77, 91, 139, 143} 4 := ⟨by decide, by intro a ha; simp at ha; omega⟩
  obtain ⟨B, hBI, hBcard, hcov⟩ := h {77, 91, 139, 143} hne hval (b₀ - 72)
  have hmax : ({77, 91, 139, 143} : Finset ℕ).max' hne = 143 :=
    le_antisymm (Finset.max'_le _ _ _ (by intro a ha; simp at ha; omega))
      (Finset.le_max' _ _ (by simp))
  rw [hmax] at hBI
  -- `b₀ + 1` is the unique multiple of `139` in `I = [b₀ - 71, b₀ + 71]`
  have h139_dvd_b1 : 139 ∣ b₀ + 1 := by
    have : b₀ + 1 ≡ 138 + 1 [MOD 139] := h139.add_right 1
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using this)
  have h139_unique : ∀ b ∈ consecInterval (b₀ - 72) 143, 139 ∣ b → b = b₀ + 1 := by
    intro b hb hdb
    unfold consecInterval at hb
    rw [Finset.mem_Icc] at hb
    by_contra hne1
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have hle := Nat.le_of_dvd (by omega) (Nat.dvd_sub h139_dvd_b1 hdb)
      omega
    · have hle := Nat.le_of_dvd (by omega) (Nat.dvd_sub hdb h139_dvd_b1)
      omega
  -- Since `139 ∣ ∏ A ∣ ∏ B` and `139` is prime, some `b ∈ B` has `139 ∣ b`, hence `b₀ + 1 ∈ B`
  have h139_prodB : 139 ∣ ∏ b ∈ B, b := by
    have h139_A : 139 ∣ ∏ a ∈ ({77, 91, 139, 143} : Finset ℕ), a :=
      Finset.dvd_prod_of_mem id (by decide)
    exact dvd_trans h139_A hcov
  have hb1_mem : b₀ + 1 ∈ B := by
    have hp139 : Nat.Prime 139 := by norm_num
    obtain ⟨b, hbB, hdb⟩ := (hp139.prime.dvd_finsetProd_iff (fun b : ℕ => b)).mp h139_prodB
    have heq := h139_unique b (hBI hbB) hdb
    rwa [← heq]
  -- `b₀ + 1` is coprime to `7 * 11 * 13`, hence coprime to `77 * 91 * 143`
  have hcop_b1 : Nat.Coprime (∏ a ∈ ({77, 91, 143} : Finset ℕ), a) (b₀ + 1) := by
    have h7_b0 : 7 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
      have := h7.of_dvd (by norm_num : 7 ∣ 49); simpa [Nat.ModEq] using this)
    have h11_b0 : 11 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
      have := h11.of_dvd (by norm_num : 11 ∣ 121); simpa [Nat.ModEq] using this)
    have h13_b0 : 13 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
      have := h13.of_dvd (by norm_num : 13 ∣ 169); simpa [Nat.ModEq] using this)
    have hc7 : Nat.Coprime 7 (b₀ + 1) := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by
      intro hd; have := Nat.dvd_sub hd h7_b0; norm_num at this)
    have hc11 : Nat.Coprime 11 (b₀ + 1) := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by
      intro hd; have := Nat.dvd_sub hd h11_b0; norm_num at this)
    have hc13 : Nat.Coprime 13 (b₀ + 1) := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by
      intro hd; have := Nat.dvd_sub hd h13_b0; norm_num at this)
    have hprod_eq : ∏ a ∈ ({77, 91, 143} : Finset ℕ), a = 7 ^ 2 * 11 ^ 2 * 13 ^ 2 := by norm_num
    rw [hprod_eq]
    exact ((hc7.pow_left 2).mul_left (hc11.pow_left 2)).mul_left (hc13.pow_left 2)
  -- Therefore `B.erase (b₀ + 1)` still covers `{77, 91, 143}`!
  have hcov3 : IsCover {77, 91, 143} (B.erase (b₀ + 1)) := by
    unfold IsCover at hcov ⊢
    have hsub : (∏ a ∈ ({77, 91, 143} : Finset ℕ), a) ∣ ∏ b ∈ B, b := by
      have hd : (∏ a ∈ ({77, 91, 143} : Finset ℕ), a) ∣
          ∏ a ∈ ({77, 91, 139, 143} : Finset ℕ), a := by
        apply Finset.prod_dvd_prod_of_subset
        decide
      exact dvd_trans hd hcov
    rw [← Finset.mul_prod_erase B (fun b => b) hb1_mem] at hsub
    exact hcop_b1.dvd_of_dvd_mul_left hsub
  have hge4 := card_ge_four_of_77_91_143 hb0_gt h7 h11 h13
    (Finset.Subset.trans (Finset.erase_subset _ _) hBI) hcov3
  have hcard_er : (B.erase (b₀ + 1)).card + 1 = B.card := by
    rw [Finset.card_erase_of_mem hb1_mem]
    have := Finset.card_pos.mpr ⟨b₀ + 1, hb1_mem⟩
    omega
  omega

/-! ## Section 6: The Split-Clique Lower Bound Theorem (`g(n) ≥ 2n - (2r + s) + 1`) -/

private lemma nat_sq_sub_self (a : ℕ) : a ^ 2 - a = a * (a - 1) := by
  cases a with
  | zero => simp
  | succ k => rw [Nat.succ_sub_one, sq, Nat.mul_succ]; omega

/-- Unique factorization for ordered pairs of primes: if `p₁ ≤ p₂`, `q₁ ≤ q₂` are primes and
`p₁ * p₂ = q₁ * q₂`, then `p₁ = q₁ ∧ p₂ = q₂`. -/
private lemma eq_of_prime_mul_eq_prime_mul {p₁ p₂ q₁ q₂ : ℕ}
    (hp₁ : p₁.Prime) (_hp₂ : p₂.Prime) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) (heq : p₁ * p₂ = q₁ * q₂) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hd : p₁ ∣ q₁ * q₂ := ⟨p₂, heq.symm⟩
  rcases hp₁.dvd_mul.mp hd with h1 | h2
  · have h1' : p₁ = q₁ := (Nat.prime_dvd_prime_iff_eq hp₁ hq₁).mp h1
    subst h1'
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp₁.pos heq⟩
  · have h2' : p₁ = q₂ := (Nat.prime_dvd_prime_iff_eq hp₁ hq₂).mp h2
    have h3 : p₂ = q₁ := by
      rw [h2', mul_comm q₁ q₂] at heq
      exact Nat.eq_of_mul_eq_mul_left hq₂.pos heq
    omega

/-- Cardinality of ordered pairs `{(a, b) ∈ P × P : a ≤ b}` is `P.card * (P.card + 1) / 2`. -/
private lemma card_filter_le_product (P : Finset ℕ) :
    ((P ×ˢ P).filter (fun x => x.1 ≤ x.2)).card = P.card * (P.card + 1) / 2 := by
  set S_le := (P ×ˢ P).filter (fun x => x.1 ≤ x.2)
  set S_gt := (P ×ˢ P).filter (fun x => x.2 < x.1)
  set S_lt := (P ×ˢ P).filter (fun x => x.1 < x.2)
  set S_eq := (P ×ˢ P).filter (fun x => x.1 = x.2)
  -- `S_le` and `S_gt` partition `P ×ˢ P`
  have hpart1 : S_le.card + S_gt.card = P.card * P.card := by
    have hdisj : Disjoint S_le S_gt := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      rw [Finset.mem_filter] at h1 h2
      omega
    have hunion : S_le ∪ S_gt = P ×ˢ P := by
      ext x
      simp only [S_le, S_gt, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases hle : x.1 ≤ x.2
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_product]
  -- `S_lt` and `S_eq` partition `S_le`
  have hpart2 : S_lt.card + S_eq.card = S_le.card := by
    have hdisj : Disjoint S_lt S_eq := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      rw [Finset.mem_filter] at h1 h2
      omega
    have hunion : S_lt ∪ S_eq = S_le := by
      ext x
      simp only [S_lt, S_eq, S_le, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, hlt⟩ | ⟨h, heq⟩) <;> exact ⟨h, by omega⟩
      · rintro ⟨h, hle⟩
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, heq⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- Swap bijection `S_lt.card = S_gt.card`
  have hswap : S_lt.card = S_gt.card := by
    apply Finset.card_bij (fun x _ => (x.2, x.1))
    · intro x hx
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x _ y _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro y hy
      simp only [S_lt, S_gt, Finset.mem_filter, Finset.mem_product] at hy ⊢
      exact ⟨(y.2, y.1), ⟨⟨hy.1.2, hy.1.1⟩, hy.2⟩, rfl⟩
  -- Diagonal bijection `S_eq.card = P.card`
  have hdiag : S_eq.card = P.card := by
    apply Finset.card_bij (fun x _ => x.1)
    · intro x hx
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    · intro x hx y hy h
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      exact Prod.ext h (by omega)
    · intro p hp
      exact ⟨(p, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hp⟩, rfl⟩, rfl⟩
  -- Now `2 * S_le.card = P.card * P.card + P.card = P.card * (P.card + 1)`
  have h2 : 2 * S_le.card = P.card * (P.card + 1) := by
    have : P.card * (P.card + 1) = P.card * P.card + P.card := by ring
    omega
  omega

/-- Valuation sum of a product of two primes `u * v` (with `u, v ∈ U`, all elements of `U` prime)
over `U` is always `2`. -/
private lemma sum_factorization_prime_mul {U : Finset ℕ}
    (hU : ∀ w ∈ U, w.Prime) {u v : ℕ} (hu : u ∈ U) (hv : v ∈ U) :
    ∑ w ∈ U, (u * v).factorization w = 2 := by
  have hpu := hU u hu
  have hpv := hU v hv
  rw [Nat.factorization_mul hpu.ne_zero hpv.ne_zero]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  have hsingle : ∀ z ∈ U, ∑ w ∈ U, z.factorization w = 1 := by
    intro z hz
    have hpz := hU z hz
    rw [Finset.sum_eq_single z]
    · exact hpz.factorization_self
    · intro w _ hwz
      rw [hpz.factorization, Finsupp.single_eq_of_ne hwz]
    · intro hnot; exact absurd hz hnot
  rw [hsingle u hu, hsingle v hv]

/-- **Split-Clique Lower Bound Theorem (Sharp Improvement over Erdős–Surányi 1959):**
For ALL `r ≥ 1, s ≥ 1` and ALL `n` with `1 ≤ n ≤ r(r+1)/2 + r*s`, EVERY `k` with
`k + (2 * r + s - 1) < 2 * n` fails `SatisfiesBound n k` (i.e., `g(n) ≥ 2n - (2r + s) + 1`). -/
theorem splitClique_lower_bound_of_clusters (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (P Q : Finset ℕ) (p_min p_max q_min q_max : ℕ)
    (hPcard : P.card = r) (hQcard : Q.card = s) (hdisjPQ : Disjoint P Q)
    (hP : ∀ p ∈ P, p.Prime ∧ 5 ≤ p ∧ p_min ≤ p ∧ p ≤ p_max)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 5 ≤ q ∧ q_min ≤ q ∧ q ≤ q_max)
    (hpminP : p_min ∈ P) (hpmaxP : p_max ∈ P) (_hqminQ : q_min ∈ Q) (hqmaxQ : q_max ∈ Q)
    (hsepPQ : p_max < q_min)
    (hC1 : p_max * q_max < 2 * (p_min ^ 2 - p_min))
    (hC2 : p_max * q_max < q_min ^ 2 - q_min)
    (n : ℕ) (hn1 : 1 ≤ n) (hn_le : n ≤ r * (r + 1) / 2 + r * s) :
    ∀ k : ℕ, k + (2 * r + s - 1) < 2 * n → ¬ SatisfiesBound n k := by
  intro k hk hsat
  set U := P ∪ Q
  have hU_prime : ∀ u ∈ U, u.Prime := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (hP u h).1
    · exact (hQ u h).1
  have hU_ge5 : ∀ u ∈ U, 5 ≤ u := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (hP u h).2.1
    · exact (hQ u h).2.1
  have hU_ge_pmin : ∀ u ∈ U, p_min ≤ u := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact (hP u h).2.2.1
    · have := (hQ u h).2.2.1
      have := (hP p_min hpminP).2.2.2
      omega
  -- Construct `A_full = E_PP ∪ E_PQ`
  set S_PP := (P ×ˢ P).filter (fun x => x.1 ≤ x.2)
  set E_PP := S_PP.image (fun x => x.1 * x.2)
  set E_PQ := (P ×ˢ Q).image (fun x => x.1 * x.2)
  set A_full := E_PP ∪ E_PQ
  set M := p_max * q_max
  -- Cardinality of `E_PP`
  have hE_PP_card : E_PP.card = r * (r + 1) / 2 := by
    rw [Finset.card_image_of_injOn]
    · rw [card_filter_le_product, hPcard]
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      have ⟨h1, h2⟩ := eq_of_prime_mul_eq_prime_mul
        (hP x.1 hx.1.1).1 (hP x.2 hx.1.2).1 (hP y.1 hy.1.1).1 (hP y.2 hy.1.2).1
        hx.2 hy.2 hxy
      exact Prod.ext h1 h2
  -- Cardinality of `E_PQ`
  have hE_PQ_card : E_PQ.card = r * s := by
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_product, hPcard, hQcard]
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_product] at hx hy
      have hx_le : x.1 ≤ x.2 := by
        have := (hP x.1 hx.1).2.2.2; have := (hQ x.2 hx.2).2.2.1; omega
      have hy_le : y.1 ≤ y.2 := by
        have := (hP y.1 hy.1).2.2.2; have := (hQ y.2 hy.2).2.2.1; omega
      have ⟨h1, h2⟩ := eq_of_prime_mul_eq_prime_mul
        (hP x.1 hx.1).1 (hQ x.2 hx.2).1 (hP y.1 hy.1).1 (hQ y.2 hy.2).1
        hx_le hy_le hxy
      exact Prod.ext h1 h2
  -- Disjointness of `E_PP` and `E_PQ`
  have hdisjE : Disjoint E_PP E_PQ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rcases Finset.mem_image.mp ha1 with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp ha2 with ⟨y, hy, heq⟩
    rw [Finset.mem_filter, Finset.mem_product] at hx
    rw [Finset.mem_product] at hy
    have hy_le : y.1 ≤ y.2 := by
      have := (hP y.1 hy.1).2.2.2; have := (hQ y.2 hy.2).2.2.1; omega
    have ⟨_, h2⟩ := eq_of_prime_mul_eq_prime_mul
      (hP x.1 hx.1.1).1 (hP x.2 hx.1.2).1 (hP y.1 hy.1).1 (hQ y.2 hy.2).1
      hx.2 hy_le heq.symm
    exact Finset.disjoint_left.mp hdisjPQ hx.1.2 (h2 ▸ hy.2)
  have hAfull_card : A_full.card = r * (r + 1) / 2 + r * s := by
    rw [Finset.card_union_of_disjoint hdisjE, hE_PP_card, hE_PQ_card]
  -- `M ∈ A_full`, and every `a ∈ A_full` satisfies `2 ≤ a ≤ M` and `∑ u ∈ U, a.factorization u = 2`
  have hM_mem : M ∈ A_full :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p_max, q_max),
      Finset.mem_product.mpr ⟨hpmaxP, hqmaxQ⟩, rfl⟩)
  have hAfull_props : ∀ a ∈ A_full, 2 ≤ a ∧ a ≤ M ∧ ∑ u ∈ U, a.factorization u = 2 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha1 | ha2
    · rcases Finset.mem_image.mp ha1 with ⟨⟨u, v⟩, huv, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at huv
      have hu := hP u huv.1.1
      have hv := hP v huv.1.2
      have hqmax_ge : q_min ≤ q_max := (hQ q_max hqmaxQ).2.2.1
      refine ⟨by nlinarith, ?_, sum_factorization_prime_mul hU_prime
        (Finset.mem_union_left _ huv.1.1) (Finset.mem_union_left _ huv.1.2)⟩
      calc u * v ≤ p_max * p_max := Nat.mul_le_mul hu.2.2.2 hv.2.2.2
        _ ≤ p_max * q_max := Nat.mul_le_mul_left _ (by omega)
    · rcases Finset.mem_image.mp ha2 with ⟨⟨u, v⟩, huv, rfl⟩
      rw [Finset.mem_product] at huv
      have hu := hP u huv.1
      have hv := hQ v huv.2
      refine ⟨by nlinarith, Nat.mul_le_mul hu.2.2.2 hv.2.2.2,
        sum_factorization_prime_mul hU_prime
          (Finset.mem_union_left _ huv.1) (Finset.mem_union_right _ huv.2)⟩
  -- Pick `A ⊆ A_full` of cardinality `n` containing `M`
  have her_card : n - 1 ≤ (A_full.erase M).card := by
    rw [Finset.card_erase_of_mem hM_mem, hAfull_card]; omega
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq her_card
  have hM_notA' : M ∉ A' := fun h => (Finset.mem_erase.mp (hA'sub h)).1 rfl
  set A := insert M A'
  have hA_sub : A ⊆ A_full := Finset.insert_subset hM_mem (Finset.Subset.trans hA'sub (Finset.erase_subset _ _))
  have hA_card : A.card = n := by rw [Finset.card_insert_of_notMem hM_notA', hA'card]; omega
  have hA_ne : A.Nonempty := ⟨M, Finset.mem_insert_self M A'⟩
  have hA_valid : IsValidSet A n := ⟨hA_card, fun a ha => (hAfull_props a (hA_sub ha)).1⟩
  have hA_max : A.max' hA_ne = M := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun a ha => (hAfull_props a (hA_sub ha)).2.1)
    · exact Finset.le_max' _ _ (Finset.mem_insert_self M A')
  -- Apply CRT on `U = P ∪ Q`:
  -- For `p ∈ P`: `b₀ ≡ p^2 + p [MOD p^3]`
  -- For `q ∈ Q`: `b₀ ≡ (q / 2) * q [MOD q^2]`
  let modU : ℕ → ℕ := fun u => if u ∈ P then u ^ 3 else u ^ 2
  let tgtU : ℕ → ℕ := fun u => if u ∈ P then u ^ 2 + u else (u / 2) * u
  have hmod_pos : ∀ u ∈ U, 0 < modU u := by
    intro u hu
    have hp := (hU_prime u hu).pos
    dsimp only [modU]
    split_ifs <;> positivity
  have hmod_cop : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → Nat.Coprime (modU u) (modU v) := by
    intro u hu v hv huv
    have hc : Nat.Coprime u v := (Nat.coprime_primes (hU_prime u hu) (hU_prime v hv)).mpr huv
    dsimp only [modU]
    split_ifs
    · exact (hc.pow_left 3).pow_right 3
    · exact (hc.pow_left 3).pow_right 2
    · exact (hc.pow_left 2).pow_right 3
    · exact (hc.pow_left 2).pow_right 2
  obtain ⟨b₀, hb0_gt, hcrt⟩ := exists_crt_finset U modU tgtU hmod_pos hmod_cop (M + 10)
  -- Center the interval `I = consecInterval x M` at `b₀`
  set L := M / 2
  set x := b₀ - (L + 1)
  have hI_dist : ∀ b ∈ consecInterval x M, b₀ - L ≤ b ∧ b ≤ b₀ + L := by
    intro b hb
    unfold consecInterval at hb
    rw [Finset.mem_Icc] at hb
    omega
  have hM_pos : 0 < M := Nat.mul_pos (hP p_max hpmaxP).1.pos (hQ q_max hqmaxQ).1.pos
  -- Apply `hsat` to `(A, x)` to obtain cover `B ⊆ consecInterval x M` with `B.card ≤ k`
  obtain ⟨B, hBI, hBcard, hcov⟩ := hsat A hA_ne hA_valid x
  rw [hA_max] at hBI
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => by have := (hAfull_props a (hA_sub ha)).1; omega
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  -- Step 1: For every `u ∈ U`, `u ∣ b₀` and `b₀.factorization u = 1`
  have hu_dvd_b0 : ∀ u ∈ U, u ∣ b₀ := by
    intro u hu
    have hc := hcrt u hu
    dsimp only [modU, tgtU] at hc
    by_cases huP : u ∈ P
    · rw [if_pos huP, if_pos huP] at hc
      have hc' := hc.of_dvd (show u ∣ u ^ 3 by exact ⟨u ^ 2, by ring⟩)
      have h0 : u ^ 2 + u ≡ 0 [MOD u] :=
        Nat.modEq_zero_iff_dvd.mpr ⟨u + 1, by ring⟩
      exact Nat.modEq_zero_iff_dvd.mp (hc'.trans h0)
    · rw [if_neg huP, if_neg huP] at hc
      have hc' := hc.of_dvd (show u ∣ u ^ 2 by exact ⟨u, by ring⟩)
      have h0 : (u / 2) * u ≡ 0 [MOD u] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left u _)
      exact Nat.modEq_zero_iff_dvd.mp (hc'.trans h0)
  have hv_b0_eq1 : ∀ u ∈ U, b₀.factorization u = 1 := by
    intro u hu
    have hpu := hU_prime u hu
    have hu5 := hU_ge5 u hu
    have hge1 : 1 ≤ b₀.factorization u :=
      (hpu.pow_dvd_iff_le_factorization (by omega)).mp (by simpa using hu_dvd_b0 u hu)
    have hnd2 : ¬ (u ^ 2 ∣ b₀) := by
      intro hd2
      have h0 : b₀ % u ^ 2 = 0 := Nat.mod_eq_zero_of_dvd hd2
      have hc := hcrt u hu
      dsimp only [modU, tgtU] at hc
      by_cases huP : u ∈ P
      · rw [if_pos huP, if_pos huP] at hc
        have hc2 := hc.of_dvd (show u ^ 2 ∣ u ^ 3 by exact ⟨u, by ring⟩)
        rw [Nat.ModEq, h0] at hc2
        have hmod_rhs : (u ^ 2 + u) % u ^ 2 = u := by
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by nlinarith)]
        omega
      · rw [if_neg huP, if_neg huP] at hc
        rw [Nat.ModEq, h0] at hc
        have hlt : (u / 2) * u < u ^ 2 := by nlinarith [Nat.div_mul_le_self u 2]
        have hpos : 0 < (u / 2) * u := by
          have : 2 ≤ u / 2 := by omega
          nlinarith
        rw [Nat.mod_eq_of_lt hlt] at hc
        omega
    have hlt2 : ¬ (2 ≤ b₀.factorization u) := fun hge2 =>
      hnd2 ((hpu.pow_dvd_iff_le_factorization (by omega)).mpr hge2)
    omega
  -- Step 2: Pair separation on `B.erase b₀`
  have hsep_B : ∀ b ∈ B.erase b₀, ∀ u ∈ U, ∀ v ∈ U, u ≠ v → u ∣ b → ¬ (v ∣ b) := by
    intro b hb u hu v hv huv hub hvb
    have hne : b ≠ b₀ := (Finset.mem_erase.mp hb).1
    have hbI : b ∈ consecInterval x M := hBI (Finset.mem_erase.mp hb).2
    have ⟨hlo, hhi⟩ := hI_dist b hbI
    have hcop_uv : Nat.Coprime u v := (Nat.coprime_primes (hU_prime u hu) (hU_prime v hv)).mpr huv
    have huv_gtL : L < u * v := by
      have hu_ge := hU_ge_pmin u hu
      have hv_ge := hU_ge_pmin v hv
      have hsq : p_min ^ 2 ≤ u * v := by nlinarith
      have : M < 2 * p_min ^ 2 := by omega
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdvd := hcop_uv.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_sub (hu_dvd_b0 u hu) hub) (Nat.dvd_sub (hu_dvd_b0 v hv) hvb)
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    · have hdvd := hcop_uv.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_sub hub (hu_dvd_b0 u hu)) (Nat.dvd_sub hvb (hu_dvd_b0 v hv))
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
  -- Step 3: For `q ∈ Q`, every `b ∈ consecInterval x M` has `b.factorization q ≤ 1`
  have hQ_val_le1 : ∀ q ∈ Q, ∀ b ∈ consecInterval x M, b.factorization q ≤ 1 := by
    intro q hq b hb
    have hq_notP : q ∉ P := Finset.disjoint_right.mp hdisjPQ hq
    have hq_info := hQ q hq
    have hq_prime := hq_info.1
    have hq5 := hq_info.2.1
    have hq_odd : q % 2 = 1 := by
      have h2 := hq_prime.eq_two_or_odd
      omega
    have hc := hcrt q (Finset.mem_union_right _ hq)
    dsimp only [modU, tgtU] at hc
    rw [if_neg hq_notP, if_neg hq_notP] at hc
    have ⟨hlo, hhi⟩ := hI_dist b hb
    have h2div : 2 * (q / 2) = q - 1 := by omega
    have hmul_lt : (q / 2) * q < q ^ 2 := by
      have : q / 2 < q := by omega
      nlinarith
    have hq_ge_qmin : q_min ^ 2 - q_min ≤ q ^ 2 - q := by
      rw [nat_sq_sub_self, nat_sq_sub_self]
      have hle := hq_info.2.2.1
      exact Nat.mul_le_mul hle (by omega)
    have h2mul_eq : 2 * ((q / 2) * q) = q ^ 2 - q := by
      rw [nat_sq_sub_self, ← mul_assoc, h2div, mul_comm]
    have hL_lt1 : L < (q / 2) * q := by omega
    have hL_lt2 : L < q ^ 2 - (q / 2) * q := by omega
    have hnd : ¬ (q ^ 2 ∣ b) :=
      not_dvd_of_modEq_and_dist hmul_lt hc hlo hhi (by omega) hL_lt1 hL_lt2
    by_contra hgt
    exact hnd ((hq_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb).ne').mpr (by omega))
  -- Step 4: For `p ∈ P`, every `b ∈ consecInterval x M` has `b.factorization p ≤ 1 + (if b = b₀ - p then 1 else 0)`
  have hP_val_le : ∀ p ∈ P, ∀ b ∈ consecInterval x M,
      b.factorization p ≤ 1 + (if b = b₀ - p then 1 else 0) := by
    intro p hp b hb
    have hp_info := hP p hp
    have hp_prime := hp_info.1
    have hp5 := hp_info.2.1
    have hc := hcrt p (Finset.mem_union_left _ hp)
    dsimp only [modU, tgtU] at hc
    rw [if_pos hp, if_pos hp] at hc
    have ⟨hlo, hhi⟩ := hI_dist b hb
    have hp_ge_pmin : p_min ^ 2 - p_min ≤ p ^ 2 - p := by
      rw [nat_sq_sub_self, nat_sq_sub_self]
      have hle := hp_info.2.2.1
      exact Nat.mul_le_mul hle (by omega)
    have hL_lt_sub : L < p ^ 2 - p := by omega
    -- First show `¬ (p ^ 3 ∣ b)` (so `b.factorization p ≤ 2`)
    have hnd3 : ¬ (p ^ 3 ∣ b) := by
      have hr_lt : p ^ 2 + p < p ^ 3 := by nlinarith
      have hL1 : L < p ^ 2 + p := by omega
      have hL2 : L < p ^ 3 - (p ^ 2 + p) := by
        have : 2 * p ^ 2 + p < p ^ 3 := by nlinarith
        omega
      exact not_dvd_of_modEq_and_dist hr_lt hc hlo hhi (by omega) hL1 hL2
    have hle2 : b.factorization p ≤ 2 := by
      by_contra hgt
      exact hnd3 ((hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb).ne').mpr (by omega))
    -- Next show: if `b ≠ b₀ - p`, then `¬ (p ^ 2 ∣ b)` (so `b.factorization p ≤ 1`)
    split_ifs with hbeq
    · omega
    · by_contra hgt
      have hd2 : p ^ 2 ∣ b :=
        (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb).ne').mpr (by omega)
      -- Also `p ^ 2 ∣ b₀ - p` since `b₀ ≡ p^2 + p [MOD p^3]` implies `b₀ ≡ p [MOD p^2]`
      have hc2 : b₀ ≡ p [MOD p ^ 2] := by
        have hstep := hc.of_dvd (show p ^ 2 ∣ p ^ 3 by exact ⟨p, by ring⟩)
        have hsimp : p ^ 2 + p ≡ p [MOD p ^ 2] := by
          rw [Nat.ModEq, Nat.add_mod_left]
        exact hstep.trans hsimp
      have hd2_bp : p ^ 2 ∣ b₀ - p := by
        have hmod_eq : b₀ % p ^ 2 = p := by
          rw [Nat.ModEq] at hc2
          rw [hc2, Nat.mod_eq_of_lt (by nlinarith)]
        have hdiv := Nat.div_add_mod b₀ (p ^ 2)
        refine ⟨b₀ / p ^ 2, ?_⟩
        omega
      rcases lt_or_gt_of_ne hbeq with hlt | hgt'
      · have hle := Nat.le_of_dvd (by omega) (Nat.dvd_sub hd2_bp hd2)
        -- `b₀ - p - b ≥ p^2`, so `b₀ - b ≥ p^2 + p > L`, contradicting `b₀ - L ≤ b`
        omega
      · have hle := Nat.le_of_dvd (by omega) (Nat.dvd_sub hd2 hd2_bp)
        -- `b - (b₀ - p) ≥ p^2`, so `b - b₀ ≥ p^2 - p > L`, contradicting `b ≤ b₀ + L`
        omega
  -- Step 5: Master 4-line valuation counting inequality!
  set χ₀ : ℕ := if b₀ ∈ B then 1 else 0
  set B' := B.erase b₀
  have hBcard_split : B'.card + χ₀ = B.card := by
    dsimp only [B', χ₀]
    split_ifs with hmem
    · rw [Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.mpr ⟨b₀, hmem⟩
      omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  -- Split `∑ b ∈ B, b.factorization u = χ₀ + ∑ b ∈ B'.filter (u ∣ ·), b.factorization u`
  have hsplit_u : ∀ u ∈ U,
      ∑ b ∈ B, b.factorization u = χ₀ + ∑ b ∈ B'.filter (fun b => u ∣ b), b.factorization u := by
    intro u hu
    rw [← sum_factorization_eq_filter B' u]
    dsimp only [B', χ₀]
    split_ifs with hmem
    · rw [← Finset.add_sum_erase B (fun b => b.factorization u) hmem, hv_b0_eq1 u hu]
    · rw [Finset.erase_eq_of_notMem hmem, zero_add]
  -- Upper bound on `∑ b ∈ B'.filter (u ∣ ·), b.factorization u`
  have hbound_Q : ∀ q ∈ Q,
      ∑ a ∈ A, a.factorization q ≤ χ₀ + (B'.filter (fun b => q ∣ b)).card := by
    intro q hq
    have hcov_q := sum_factorization_le_of_isCover hA0 hB0 hcov q
    rw [hsplit_u q (Finset.mem_union_right _ hq)] at hcov_q
    have hle : ∑ b ∈ B'.filter (fun b => q ∣ b), b.factorization q ≤
        (B'.filter (fun b => q ∣ b)).card := by
      calc ∑ b ∈ B'.filter (fun b => q ∣ b), b.factorization q
          ≤ ∑ _b ∈ B'.filter (fun b => q ∣ b), 1 :=
            Finset.sum_le_sum fun b hb =>
              hQ_val_le1 q hq b (hBI (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2)
        _ = (B'.filter (fun b => q ∣ b)).card := by simp
    omega
  have hbound_P : ∀ p ∈ P,
      ∑ a ∈ A, a.factorization p ≤ χ₀ + (B'.filter (fun b => p ∣ b)).card + 1 := by
    intro p hp
    have hcov_p := sum_factorization_le_of_isCover hA0 hB0 hcov p
    rw [hsplit_u p (Finset.mem_union_left _ hp)] at hcov_p
    have hle : ∑ b ∈ B'.filter (fun b => p ∣ b), b.factorization p ≤
        (B'.filter (fun b => p ∣ b)).card + 1 := by
      calc ∑ b ∈ B'.filter (fun b => p ∣ b), b.factorization p
          ≤ ∑ b ∈ B'.filter (fun b => p ∣ b), (1 + if b = b₀ - p then 1 else 0) :=
            Finset.sum_le_sum fun b hb =>
              hP_val_le p hp b (hBI (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2)
        _ = (B'.filter (fun b => p ∣ b)).card +
              ∑ b ∈ B'.filter (fun b => p ∣ b), (if b = b₀ - p then 1 else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ (B'.filter (fun b => p ∣ b)).card + 1 := by
            gcongr
            rw [Finset.sum_ite_eq']
            split_ifs <;> omega
    omega
  -- Sum over `U = P ∪ Q`: LHS = `2 * n`
  have hlhs : ∑ u ∈ U, ∑ a ∈ A, a.factorization u = 2 * n := by
    rw [Finset.sum_comm]
    calc ∑ a ∈ A, ∑ u ∈ U, a.factorization u
        = ∑ _a ∈ A, 2 := Finset.sum_congr rfl fun a ha => (hAfull_props a (hA_sub ha)).2.2
      _ = 2 * n := by rw [Finset.sum_const, hA_card, smul_eq_mul, mul_comm]
  have hsum_U :
      2 * n ≤ (r + s) * χ₀ + r + ∑ u ∈ U, (B'.filter (fun b => u ∣ b)).card := by
    rw [← hlhs, Finset.sum_union hdisjPQ, Finset.sum_union hdisjPQ]
    have hsp : ∑ p ∈ P, ∑ a ∈ A, a.factorization p ≤
        ∑ p ∈ P, (χ₀ + (B'.filter (fun b => p ∣ b)).card + 1) :=
      Finset.sum_le_sum hbound_P
    have hsq : ∑ q ∈ Q, ∑ a ∈ A, a.factorization q ≤
        ∑ q ∈ Q, (χ₀ + (B'.filter (fun b => q ∣ b)).card) :=
      Finset.sum_le_sum hbound_Q
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      hPcard, hQcard] at hsp hsq
    linarith
  have hdisj_sum := sum_card_filter_le_of_no_two_primes U B' hsep_B
  have hχ_le1 : χ₀ ≤ 1 := by dsimp only [χ₀]; split_ifs <;> omega
  -- Combine: `2 * n ≤ (r + s) * χ₀ + r + B'.card = (r + s - 1) * χ₀ + r + B.card ≤ 2 * r + s - 1 + B.card`
  have hfinal : 2 * n ≤ B.card + (2 * r + s - 1) := by
    have h1 : (r + s) * χ₀ + B'.card = (r + s - 1) * χ₀ + B.card := by
      have : r + s = (r + s - 1) + 1 := by omega
      nlinarith
    have h2 : (r + s - 1) * χ₀ ≤ r + s - 1 := by
      calc (r + s - 1) * χ₀ ≤ (r + s - 1) * 1 := Nat.mul_le_mul_left _ hχ_le1
        _ = r + s - 1 := mul_one _
    omega
  omega

/-! ## Section 7: Sharp Small Lower Bounds (g(5) ≥ 6, g(6) ≥ 7, g(7) ≥ 9) -/

theorem erdos708_lower_five : ¬ SatisfiesBound 5 5 := by
  refine splitClique_lower_bound_of_clusters 2 1 (by norm_num) (by norm_num)
    {17, 19} {23} 17 19 23 23 (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    5 (by norm_num) (by norm_num) 5 (by norm_num)
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro q hq
    simp only [Finset.mem_singleton] at hq
    rcases hq with rfl
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem erdos708_lower_six : ¬ SatisfiesBound 6 6 := by
  refine splitClique_lower_bound_of_clusters 2 2 (by norm_num) (by norm_num)
    {29, 31} {37, 41} 29 31 37 41 (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    6 (by norm_num) (by norm_num) 6 (by norm_num)
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem erdos708_lower_seven : ¬ SatisfiesBound 7 8 := by
  refine splitClique_lower_bound_of_clusters 2 2 (by norm_num) (by norm_num)
    {29, 31} {37, 41} 29 31 37 41 (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
    7 (by norm_num) (by norm_num) 8 (by norm_num)
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Section 9: Structural Valuation Barrier (`|B|_min ≤ ∑ Ω(a)`)

This structural theorem explains why no set of primes and semiprimes can ever beat `2n`:
every valid `(A, I)` admits a cover of size at most `∑ a ∈ A, Ω(a)`. Consequently, any
counterexample to Erdős's `g(n) ≤ 2n` question must have average prime-factor count `> 2`. -/

/-- Total number of prime factors counted with multiplicity: `Ω(m) = ∑ p, m.factorization p`. -/
def bigOmega (m : ℕ) : ℕ :=
  m.factorization.sum (fun _ e => e)

lemma bigOmega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  unfold bigOmega
  rw [Nat.factorization_mul ha hb, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]

lemma bigOmega_pos_of_gt_one {m : ℕ} (hm : 1 < m) : 0 < bigOmega m := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hmem : p ∈ m.factorization.support :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
  have hpos : 0 < m.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
  unfold bigOmega
  rw [Finsupp.sum]
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun q => m.factorization q)
    (fun _ _ => Nat.zero_le _) hmem)

lemma bigOmega_finset_prod (S : Finset ℕ) (hpos : ∀ a ∈ S, a ≠ 0) :
    bigOmega (∏ a ∈ S, a) = ∑ a ∈ S, bigOmega a := by
  induction S using Finset.induction_on with
  | empty => simp [bigOmega]
  | @insert a s ha ih =>
    have ha0 : a ≠ 0 := hpos a (Finset.mem_insert_self a s)
    have hs0 : ∀ b ∈ s, b ≠ 0 := fun b hb => hpos b (Finset.mem_insert_of_mem hb)
    have hprod0 : (∏ b ∈ s, b) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, Finset.sum_insert ha, bigOmega_mul ha0 hprod0, ih hs0]

/-- Factorial product identity: `x! * ∏_{b ∈ [x+1, x+M]} b = (x + M)!`. -/
private lemma factorial_mul_prod_consecInterval (x M : ℕ) :
    x.factorial * ∏ b ∈ consecInterval x M, b = (x + M).factorial := by
  induction M with
  | zero =>
    have hemp : consecInterval x 0 = ∅ := by
      ext b; simp [consecInterval]
    rw [hemp, Finset.prod_empty, mul_one, add_zero]
  | succ M ih =>
    have hins : consecInterval x (M + 1) = insert (x + M + 1) (consecInterval x M) := by
      ext b
      simp only [consecInterval, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : x + M + 1 ∉ consecInterval x M := by
      simp [consecInterval]
    rw [hins, Finset.prod_insert hnot, ← mul_assoc, mul_comm x.factorial (x + M + 1),
        mul_assoc, ih, ← add_assoc, Nat.factorial_succ]

/-- Every interval `consecInterval x M` has product divisible by `M!`. -/
lemma factorial_dvd_prod_consecInterval (x M : ℕ) :
    M.factorial ∣ ∏ b ∈ consecInterval x M, b := by
  have hch := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left M x)
  rw [Nat.add_sub_cancel_right] at hch
  rw [← factorial_mul_prod_consecInterval x M] at hch
  have hfac_pos : 0 < x.factorial := Nat.factorial_pos x
  refine ⟨(x + M).choose M, ?_⟩
  have heq : x.factorial * (M.factorial * (x + M).choose M) =
      x.factorial * ∏ b ∈ consecInterval x M, b := by
    linarith
  exact (Nat.eq_of_mul_eq_mul_left hfac_pos heq).symm

/-- Every valid set `A` with maximum `M` is covered by the full interval `consecInterval x M`. -/
lemma isCover_consecInterval {A : Finset ℕ} (hA : A.Nonempty) (hge2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ) :
    IsCover A (consecInterval x (A.max' hA)) := by
  unfold IsCover
  set M := A.max' hA
  have hsub : A ⊆ consecInterval 0 M := by
    intro a ha
    unfold consecInterval
    rw [Finset.mem_Icc]
    exact ⟨by have := hge2 a ha; omega, by have := Finset.le_max' A a ha; omega⟩
  have hdvd1 : (∏ a ∈ A, a) ∣ ∏ m ∈ consecInterval 0 M, m :=
    Finset.prod_dvd_prod_of_subset A (consecInterval 0 M) id hsub
  have hfac_eq : ∏ m ∈ consecInterval 0 M, m = M.factorial := by
    have h := factorial_mul_prod_consecInterval 0 M
    simpa using h
  rw [hfac_eq] at hdvd1
  exact dvd_trans hdvd1 (factorial_dvd_prod_consecInterval x M)

/-- Core greedy/inductive shrinking lemma: if `D ≠ 0` divides `∏ b ∈ I, b` (all `b ≠ 0`),
then some subset `B ⊆ I` of cardinality `≤ Ω(D)` already has `D ∣ ∏ b ∈ B, b`. -/
theorem exists_subset_dvd_card_le_bigOmega :
    ∀ (k : ℕ) (D : ℕ) (I : Finset ℕ),
      D ≠ 0 → bigOmega D ≤ k → (∀ b ∈ I, b ≠ 0) → D ∣ ∏ b ∈ I, b →
      ∃ B ⊆ I, B.card ≤ k ∧ D ∣ ∏ b ∈ B, b := by
  intro k
  induction k with
  | zero =>
    intro D I hD0 hOm _ _
    have hD1 : D = 1 := by
      by_contra hne1
      have hgt1 : 1 < D := by omega
      have := bigOmega_pos_of_gt_one hgt1
      omega
    subst hD1
    exact ⟨∅, Finset.empty_subset I, by simp, one_dvd _⟩
  | succ k ih =>
    intro D I hD0 hOm hI0 hdvd
    by_cases hD1 : D = 1
    · subst hD1
      exact ⟨∅, Finset.empty_subset I, by simp, one_dvd _⟩
    · obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD1
      have hpI : p ∣ ∏ b ∈ I, b := dvd_trans hpD hdvd
      obtain ⟨b, hbI, hpb⟩ := (hp.prime.dvd_finsetProd_iff (fun b : ℕ => b)).mp hpI
      set d := Nat.gcd D b
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero hD0)
      have hpd : p ∣ d := Nat.dvd_gcd hpD hpb
      have hd_gt1 : 1 < d := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hd_pos hpd)
      have hd_D : d ∣ D := Nat.gcd_dvd_left D b
      have hd_b : d ∣ b := Nat.gcd_dvd_right D b
      set D' := D / d
      set b' := b / d
      have hD_eq : d * D' = D := Nat.mul_div_cancel' hd_D
      have hb_eq : d * b' = b := Nat.mul_div_cancel' hd_b
      have hD'0 : D' ≠ 0 := by intro h0; rw [h0, mul_zero] at hD_eq; exact hD0 hD_eq.symm
      have hcop : Nat.Coprime D' b' := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have h1 : d * Nat.gcd D' b' = d * 1 := by
          rw [← Nat.gcd_mul_left, hD_eq, hb_eq, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hd_pos h1
      have hdvd' : D' ∣ ∏ c ∈ I.erase b, c := by
        have hb_prod : b * ∏ c ∈ I.erase b, c = d * (b' * ∏ c ∈ I.erase b, c) := by
          rw [← mul_assoc, hb_eq]
        rw [← Finset.mul_prod_erase I (fun c => c) hbI, hb_prod, ← hD_eq] at hdvd
        have hcancel : D' ∣ b' * ∏ c ∈ I.erase b, c :=
          (mul_dvd_mul_iff_left hd_pos.ne').mp hdvd
        exact hcop.dvd_of_dvd_mul_left hcancel
      have hOm' : bigOmega D' ≤ k := by
        have hmul := bigOmega_mul hd_pos.ne' hD'0
        rw [hD_eq] at hmul
        have hd_om := bigOmega_pos_of_gt_one hd_gt1
        omega
      obtain ⟨B', hB'sub, hB'card, hB'dvd⟩ :=
        ih D' (I.erase b) hD'0 hOm' (fun c hc => hI0 c (Finset.mem_of_mem_erase hc)) hdvd'
      have hb_notB' : b ∉ B' := fun h => (Finset.mem_erase.mp (hB'sub h)).1 rfl
      refine ⟨insert b B', Finset.insert_subset hbI (Finset.Subset.trans hB'sub (Finset.erase_subset _ _)),
        ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hb_notB']; omega
      · rw [Finset.prod_insert hb_notB', ← hD_eq]
        exact mul_dvd_mul hd_b hB'dvd

/-- **Structural Valuation Barrier:** Every valid `(A, I)` admits a cover `B ⊆ I` of size
at most `∑ a ∈ A, Ω(a)`. Hence any counterexample to `g(n) ≤ 2n` MUST satisfy `2n < ∑ a ∈ A, Ω(a)`. -/
theorem exists_cover_card_le_sum_bigOmega {A : Finset ℕ} (hA : A.Nonempty)
    (hge2 : ∀ a ∈ A, 2 ≤ a) (x : ℕ) :
    ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ (∑ a ∈ A, bigOmega a) ∧ IsCover A B := by
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => by have := hge2 a ha; omega
  have hD0 : (∏ a ∈ A, a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hA0
  have hI0 : ∀ b ∈ consecInterval x (A.max' hA), b ≠ 0 :=
    fun b hb => (pos_of_mem_consecInterval hb).ne'
  have hcov_all := isCover_consecInterval hA hge2 x
  have hOm := bigOmega_finset_prod A hA0
  exact exists_subset_dvd_card_le_bigOmega (∑ a ∈ A, bigOmega a) (∏ a ∈ A, a)
    (consecInterval x (A.max' hA)) hD0 hOm.le hI0 hcov_all

/-- **Corollary:** No set of primes and semiprimes (`∀ a ∈ A, Ω(a) ≤ 2`) can EVER force `|B| > 2|A|`. -/
theorem exists_cover_le_two_mul_of_semiprimes {A : Finset ℕ} (hA : A.Nonempty)
    (hge2 : ∀ a ∈ A, 2 ≤ a) (hsemi : ∀ a ∈ A, bigOmega a ≤ 2) (x : ℕ) :
    ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ 2 * A.card ∧ IsCover A B := by
  obtain ⟨B, hBI, hBcard, hcov⟩ := exists_cover_card_le_sum_bigOmega hA hge2 x
  refine ⟨B, hBI, ?_, hcov⟩
  calc B.card ≤ ∑ a ∈ A, bigOmega a := hBcard
    _ ≤ ∑ _a ∈ A, 2 := Finset.sum_le_sum hsemi
    _ = 2 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

#print axioms erdos708_exact_one
#print axioms erdos708_exact_two
#print axioms erdos708_lower_three
#print axioms erdos708_lower_four
#print axioms splitClique_lower_bound_of_clusters
#print axioms erdos708_lower_five
#print axioms erdos708_lower_six
#print axioms erdos708_lower_seven
#print axioms exists_cover_card_le_sum_bigOmega
#print axioms exists_cover_le_two_mul_of_semiprimes

end Erdos708
