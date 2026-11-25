import Erdos708.G4
import Erdos708.G5Core

/-!
# PPL 176 (Erdős Problem #708) — Exact Settlement `g(5) = 6`

This module completes the `n = 5` case of **Erdős Problem #708**:
1. `erdos708_upper_five_of_matching_three`: closes the `r = 3` matching branch (`|S| = 3`,
   `|B| ≤ 6`), via Case B (shared unique multiple in `consecInterval x M`) and Case A
   (two-slot configuration `u₁ ∣ b₁`, `u₂ ∣ b₂`, `sᵢ ∣ bᵢ`).
2. `erdos708_upper_five : SatisfiesBound 5 6`: unconditional upper bound `g(5) ≤ 6` by strong
   induction on `M`, GCD reduction to `g = 1` (invoking `erdos708_upper_four` when `1 ∈ C`),
   base `M ≤ 6` via `erdos708_trivial_max_bound`, and matching sizes `r = 1..5`.
3. `erdos708_exact_five : SatisfiesBound 5 6 ∧ ¬ SatisfiesBound 5 5`: settles `g(5) = 6`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Elementary Helpers for `r = 3` -/

private lemma sup_id_eq_max'_5 {A : Finset ℕ} (hA : A.Nonempty) :
    A.sup id = A.max' hA := by
  apply le_antisymm
  · exact Finset.sup_le fun a ha => Finset.le_max' A a ha
  · exact Finset.le_sup (f := id) (Finset.max'_mem A hA)

private lemma erdos708_upper_of_max_le_5 {A : Finset ℕ} (hA : A.Nonempty)
    (hA_pos : ∀ a ∈ A, 0 < a) {k : ℕ} (hle : A.max' hA ≤ k) (x : ℕ) :
    ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ k ∧ IsCover A B := by
  obtain ⟨B, hBI, hBcard, hcov⟩ := erdos708_trivial_max_bound (fun a ha => hA_pos a ha) x
  have hsup : A.sup id = A.max' hA := sup_id_eq_max'_5 hA
  rw [hsup] at hBI hBcard
  exact ⟨B, hBI, le_trans hBcard hle, hcov⟩

private lemma card_finset_le_five_5 (a b c d e : ℕ) :
    ({a, b, c, d, e} : Finset ℕ).card ≤ 5 := by
  have h1 := Finset.card_insert_le a {b, c, d, e}
  have h2 := card_finset_le_four_5 b c d e
  omega

private lemma card_finset_le_six_5 (a b c d e f : ℕ) :
    ({a, b, c, d, e, f} : Finset ℕ).card ≤ 6 := by
  have h1 := Finset.card_insert_le a {b, c, d, e, f}
  have h2 := card_finset_le_five_5 b c d e f
  omega

private lemma two_mul_gcd_le_of_distinct_5 {a₁ a₂ M : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hle₁ : a₁ ≤ M) (hle₂ : a₂ ≤ M) (hne : a₁ ≠ a₂) :
    2 * Nat.gcd a₁ a₂ ≤ M := by
  set d := Nat.gcd a₁ a₂
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left a₂ ha₁
  have hd1 : d ∣ a₁ := Nat.gcd_dvd_left a₁ a₂
  have hd2 : d ∣ a₂ := Nat.gcd_dvd_right a₁ a₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q₁, hq1⟩ := hd1
    obtain ⟨q₂, hq2⟩ := hd2
    have hq1_pos : 1 ≤ q₁ := by
      by_contra h0; have : q₁ = 0 := by omega
      rw [this, mul_zero] at hq1; omega
    have hq12 : q₁ < q₂ := by
      by_contra hle
      have : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega)
      omega
    have h2d : 2 * d ≤ d * q₂ := by rw [mul_comm 2 d]; exact Nat.mul_le_mul_left d (by omega)
    omega
  · obtain ⟨q₁, hq1⟩ := hd1
    obtain ⟨q₂, hq2⟩ := hd2
    have hq2_pos : 1 ≤ q₂ := by
      by_contra h0; have : q₂ = 0 := by omega
      rw [this, mul_zero] at hq2; omega
    have hq21 : q₂ < q₁ := by
      by_contra hle
      have : d * q₁ ≤ d * q₂ := Nat.mul_le_mul_left d (by omega)
      omega
    have h2d : 2 * d ≤ d * q₁ := by rw [mul_comm 2 d]; exact Nat.mul_le_mul_left d (by omega)
    omega

private lemma five_mul_le_of_three_gt_half_5 {d a₁ a₂ a₃ M : ℕ}
    (_hd : 0 < d) (h12 : a₁ < a₂) (h23 : a₂ < a₃) (ha₃M : a₃ ≤ M) (hM2 : M < 2 * a₁)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) :
    5 * d ≤ M := by
  obtain ⟨q₁, hq1⟩ := hd1
  obtain ⟨q₂, hq2⟩ := hd2
  obtain ⟨q₃, hq3⟩ := hd3
  have hq12 : q₁ < q₂ := by
    by_contra hle
    have : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega)
    omega
  have hq23 : q₂ < q₃ := by
    by_contra hle
    have : d * q₃ ≤ d * q₂ := Nat.mul_le_mul_left d (by omega)
    omega
  have hq3_lt : q₃ < 2 * q₁ := by
    by_contra hge
    have h1 : 2 * (d * q₁) = d * (2 * q₁) := by ring
    have h2 : d * (2 * q₁) ≤ d * q₃ := Nat.mul_le_mul_left d (by omega)
    omega
  have hq3_ge5 : 5 ≤ q₃ := by omega
  have h5d : 5 * d ≤ d * q₃ := by rw [mul_comm 5]; exact Nat.mul_le_mul_left d hq3_ge5
  omega

private lemma five_mul_le_of_three_distinct_gt_half_5 {d a₁ a₂ a₃ M : ℕ}
    (hd : 0 < d) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (h1M : a₁ ≤ M) (h2M : a₂ ≤ M) (h3M : a₃ ≤ M)
    (hM1 : M < 2 * a₁) (hM2 : M < 2 * a₂) (hM3 : M < 2 * a₃)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) :
    5 * d ≤ M := by
  rcases lt_or_gt_of_ne h12 with h | h <;>
  rcases lt_or_gt_of_ne h13 with h' | h' <;>
  rcases lt_or_gt_of_ne h23 with h'' | h''
  · exact five_mul_le_of_three_gt_half_5 hd h h'' h3M hM1 hd1 hd2 hd3
  · exact five_mul_le_of_three_gt_half_5 hd h' h'' h2M hM1 hd1 hd3 hd2
  · omega
  · exact five_mul_le_of_three_gt_half_5 hd h' h h2M hM3 hd3 hd1 hd2
  · exact five_mul_le_of_three_gt_half_5 hd h h' h3M hM2 hd2 hd1 hd3
  · omega
  · exact five_mul_le_of_three_gt_half_5 hd h'' h' h1M hM2 hd2 hd3 hd1
  · exact five_mul_le_of_three_gt_half_5 hd h'' h h1M hM3 hd3 hd2 hd1

private lemma eq_pair_of_two_dvd_lt_three_mul_5 {d a₁ a₂ M : ℕ}
    (_hd : 0 < d) (ha₁ : 0 < a₁) (h12 : a₁ < a₂) (ha₂M : a₂ ≤ M) (hM3 : M < 3 * d)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) :
    a₁ = d ∧ a₂ = 2 * d := by
  obtain ⟨q₁, hq1⟩ := hd1
  obtain ⟨q₂, hq2⟩ := hd2
  have hq1_pos : 1 ≤ q₁ := by
    by_contra h0; have : q₁ = 0 := by omega
    rw [this, mul_zero] at hq1; omega
  have hq12 : q₁ < q₂ := by
    by_contra hle
    have : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega)
    omega
  have hq2_lt3 : q₂ < 3 := by
    by_contra hge
    have h1 : 3 * d ≤ d * q₂ := by rw [mul_comm 3]; exact Nat.mul_le_mul_left d (by omega)
    omega
  have hq1_eq : q₁ = 1 := by omega
  have hq2_eq : q₂ = 2 := by omega
  exact ⟨by rw [hq1, hq1_eq, mul_one], by rw [hq2, hq2_eq, mul_comm]⟩

private lemma exists_avoiding_of_not_subset_triple_5 {x M d b₁ b₂ b₃ : ℕ}
    (hnot : ¬ ((consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, b₃})) :
    ∃ w ∈ consecInterval x M, w ≠ b₁ ∧ w ≠ b₂ ∧ w ≠ b₃ ∧ d ∣ w := by
  obtain ⟨w, hw_flt, hw_not⟩ := Finset.not_subset.mp hnot
  rw [Finset.mem_filter] at hw_flt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw_not
  exact ⟨w, hw_flt.1, hw_not.1, hw_not.2.1, hw_not.2.2, hw_flt.2⟩

private lemma dvd_pair_of_filter_subset_pair_5 {x M d b₁ b₂ : ℕ}
    (hd : 0 < d) (h2d : 2 * d ≤ M) (hb12 : b₁ ≠ b₂)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂}) :
    d ∣ b₁ ∧ d ∣ b₂ ∧ M < 3 * d := by
  have hcard_ge2 : 2 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 2 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h2d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  have hpair_card : ({b₁, b₂} : Finset ℕ).card = 2 := Finset.card_pair hb12
  have hle : ((consecInterval x M).filter (fun b => d ∣ b)).card ≤ ({b₁, b₂} : Finset ℕ).card :=
    Finset.card_le_card hsub
  have heq : (consecInterval x M).filter (fun b => d ∣ b) = {b₁, b₂} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm1 : b₁ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by
    rw [heq]; exact Finset.mem_insert_self b₁ {b₂}
  have hm2 : b₂ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by
    rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b₂)
  have hM3 : M < 3 * d := by
    by_contra hge
    have h3d : 3 * d ≤ M := Nat.le_of_not_lt hge
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 3 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h3d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  exact ⟨(Finset.mem_filter.mp hm1).2, (Finset.mem_filter.mp hm2).2, hM3⟩

private lemma dvd_triple_of_filter_subset_triple_5 {x M d b₁ b₂ b₃ : ℕ}
    (hd : 0 < d) (h3d : 3 * d ≤ M) (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, b₃}) :
    d ∣ b₁ ∧ d ∣ b₂ ∧ d ∣ b₃ ∧ M < 4 * d := by
  have hcard_ge3 : 3 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 3 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h3d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  have h3_card : ({b₁, b₂, b₃} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hb12, hb13]),
        Finset.card_insert_of_notMem (by simp [hb23]), Finset.card_singleton]
  have hle : ((consecInterval x M).filter (fun b => d ∣ b)).card ≤ ({b₁, b₂, b₃} : Finset ℕ).card :=
    Finset.card_le_card hsub
  have heq : (consecInterval x M).filter (fun b => d ∣ b) = {b₁, b₂, b₃} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm1 : b₁ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by rw [heq]; simp
  have hm2 : b₂ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by rw [heq]; simp
  have hm3 : b₃ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by rw [heq]; simp
  have hM4 : M < 4 * d := by
    by_contra hge
    have h4d : 4 * d ≤ M := Nat.le_of_not_lt hge
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 4 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h4d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  exact ⟨(Finset.mem_filter.mp hm1).2, (Finset.mem_filter.mp hm2).2, (Finset.mem_filter.mp hm3).2, hM4⟩

private lemma dvd_b3_of_filter_subset_quad_5 {x M d b₁ b₂ b₃ w₁ : ℕ}
    (hd : 0 < d) (h4d : 4 * d ≤ M)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, b₃, w₁}) :
    d ∣ b₃ := by
  have hcard_ge4 : 4 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 4 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h4d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  have hle4 : ({b₁, b₂, b₃, w₁} : Finset ℕ).card ≤ 4 := card_finset_le_four_5 b₁ b₂ b₃ w₁
  have heq : (consecInterval x M).filter (fun b => d ∣ b) = {b₁, b₂, b₃, w₁} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm3 : b₃ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by rw [heq]; simp
  exact (Finset.mem_filter.mp hm3).2

private lemma adjacent_multiple_of_lt {x M d lo hi : ℕ}
    (_hd : 0 < d) (hlo : lo ∈ consecInterval x M) (hhi : hi ∈ consecInterval x M)
    (hlt : lo < hi) (hdlo : d ∣ lo) (hdhi : d ∣ hi)
    (hnone : ∀ m ∈ consecInterval x M, d ∣ m → m = lo ∨ m = hi) :
    hi = lo + d := by
  obtain ⟨q₁, hq1⟩ := hdlo
  obtain ⟨q₂, hq2⟩ := hdhi
  have hq12 : q₁ < q₂ := by
    by_contra hle; have : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega); omega
  have hq2_eq : q₂ = q₁ + 1 := by
    by_contra hne
    have hge : q₁ + 2 ≤ q₂ := by omega
    let m := d * (q₁ + 1)
    have hm_gt : lo < m := by rw [hq1]; dsimp [m]; nlinarith
    have hm_lt : m < hi := by rw [hq2]; dsimp [m]; exact Nat.mul_lt_mul_of_pos_left (by omega) _hd
    have hm_I : m ∈ consecInterval x M := by
      simp only [consecInterval, Finset.mem_Icc] at hlo hhi ⊢
      exact ⟨by omega, by omega⟩
    have hm_dvd : d ∣ m := ⟨q₁ + 1, rfl⟩
    rcases hnone m hm_I hm_dvd with heq | heq <;> omega
  rw [hq1, hq2, hq2_eq, mul_add, mul_one]

private lemma diff_eq_of_two_multiples_5 {x M d b₁ b₂ : ℕ}
    (hd : 0 < d) (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb1 : d ∣ b₁) (hb2 : d ∣ b₂)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂}) :
    b₁ + d = b₂ ∨ b₂ + d = b₁ := by
  have hnone : ∀ m ∈ consecInterval x M, d ∣ m → m = b₁ ∨ m = b₂ := fun m hm hdm => by
    have := hsub (Finset.mem_filter.mpr ⟨hm, hdm⟩)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases lt_or_gt_of_ne hb12 with hlt | hgt
  · left
    exact (adjacent_multiple_of_lt hd hb₁_I hb₂_I hlt hb1 hb2 hnone).symm
  · right
    exact (adjacent_multiple_of_lt hd hb₂_I hb₁_I hgt hb2 hb1
      (fun m hm hdm => (hnone m hm hdm).symm)).symm

private lemma span_three_sorted_5 {x M d lo mid hi : ℕ}
    (hd : 0 < d) (hlo : lo ∈ consecInterval x M) (hhi : hi ∈ consecInterval x M)
    (h12 : lo < mid) (h23 : mid < hi) (h1 : d ∣ lo) (h2 : d ∣ mid) (h3 : d ∣ hi)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {lo, mid, hi}) :
    mid = lo + d ∧ hi = lo + 2 * d := by
  obtain ⟨q₁, hq1⟩ := h1
  obtain ⟨q₂, hq2⟩ := h2
  obtain ⟨q₃, hq3⟩ := h3
  have hq12 : q₁ < q₂ := by
    by_contra hle; have : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega); omega
  have hq23 : q₂ < q₃ := by
    by_contra hle; have : d * q₃ ≤ d * q₂ := Nat.mul_le_mul_left d (by omega); omega
  have hq3_le : q₃ ≤ q₁ + 2 := by
    by_contra hge
    have hge3 : q₁ + 3 ≤ q₃ := by omega
    let m₁ := d * (q₁ + 1)
    let m₂ := d * (q₁ + 2)
    have hm1_gt : lo < m₁ := by rw [hq1]; dsimp [m₁]; exact Nat.mul_lt_mul_of_pos_left (by omega) hd
    have hm12 : m₁ < m₂ := by dsimp [m₁, m₂]; exact Nat.mul_lt_mul_of_pos_left (by omega) hd
    have hm2_lt : m₂ < hi := by rw [hq3]; dsimp [m₂]; exact Nat.mul_lt_mul_of_pos_left (by omega) hd
    have hm1_I : m₁ ∈ consecInterval x M := by
      simp only [consecInterval, Finset.mem_Icc] at hlo hhi ⊢; exact ⟨by omega, by omega⟩
    have hm2_I : m₂ ∈ consecInterval x M := by
      simp only [consecInterval, Finset.mem_Icc] at hlo hhi ⊢; exact ⟨by omega, by omega⟩
    have h4sub : ({lo, m₁, m₂, hi} : Finset ℕ) ⊆ (consecInterval x M).filter (fun b => d ∣ b) := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hlo, hq1 ▸ ⟨q₁, rfl⟩⟩
      · exact Finset.mem_filter.mpr ⟨hm1_I, ⟨q₁ + 1, rfl⟩⟩
      · exact Finset.mem_filter.mpr ⟨hm2_I, ⟨q₁ + 2, rfl⟩⟩
      · exact Finset.mem_filter.mpr ⟨hhi, hq3 ▸ ⟨q₃, rfl⟩⟩
    have h4card : ({lo, m₁, m₂, hi} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hle := Finset.card_le_card (Finset.Subset.trans h4sub hsub)
    have hle3 := card_finset_le_three_5 lo mid hi
    omega
  have hq2_eq : q₂ = q₁ + 1 := by omega
  have hq3_eq : q₃ = q₁ + 2 := by omega
  exact ⟨by rw [hq2, hq1, hq2_eq, mul_add, mul_one], by rw [hq3, hq1, hq3_eq]; ring⟩

private lemma span_three_props_5 {x M d b₁ b₂ b₃ : ℕ}
    (hd : 0 < d) (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M)
    (hb₃_I : b₃ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hb1 : d ∣ b₁) (hb2 : d ∣ b₂) (hb3 : d ∣ b₃)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, b₃}) :
    (∀ d' : ℕ, d' ∣ b₁ → d' ∣ b₂ → d' ∣ b₃ → d' ∣ d) ∧
    (∀ d' : ℕ, d' ∣ b₂ → d' ∣ b₃ → d' ∣ 2 * d) := by
  have hwrap : ∀ (lo mid hi : ℕ), lo ∈ consecInterval x M → hi ∈ consecInterval x M →
      lo < mid → mid < hi → d ∣ lo → d ∣ mid → d ∣ hi →
      ({lo, mid, hi} : Finset ℕ) = {b₁, b₂, b₃} →
      (∀ d' : ℕ, d' ∣ lo → d' ∣ mid → d' ∣ d) ∧
      (∀ d' : ℕ, d' ∣ b₂ → d' ∣ b₃ → d' ∣ 2 * d) := by
    intro lo mid hi hlo hhi h12 h23 hd1 hd2 hd3 hset
    obtain ⟨hmid_eq, hhi_eq⟩ := span_three_sorted_5 hd hlo hhi h12 h23 hd1 hd2 hd3 (by rw [hset]; exact hsub)
    refine ⟨fun d' hdl hdm => ?_, fun d' hd_b2 hd_b3 => ?_⟩
    · rw [hmid_eq] at hdm; exact (Nat.dvd_add_right hdl).mp hdm
    · have hb2_in : b₂ ∈ ({lo, mid, hi} : Finset ℕ) := by rw [hset]; simp
      have hb3_in : b₃ ∈ ({lo, mid, hi} : Finset ℕ) := by rw [hset]; simp
      have step_case : ∀ x y : ℕ, x < y → d' ∣ x → d' ∣ y →
          x ∈ ({lo, mid, hi} : Finset ℕ) → y ∈ ({lo, mid, hi} : Finset ℕ) → d' ∣ 2 * d := by
        intro u v huv hdu hdv hu hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        · omega
        · rw [hmid_eq] at hdv; exact dvd_mul_of_dvd_right ((Nat.dvd_add_right hdu).mp hdv) 2
        · rw [hhi_eq] at hdv; exact (Nat.dvd_add_right hdu).mp hdv
        · rw [hmid_eq] at hdu; omega
        · omega
        · rw [hmid_eq] at hdu; rw [hhi_eq] at hdv
          have h2eq : lo + 2 * d = (lo + d) + d := by ring
          rw [h2eq] at hdv; exact dvd_mul_of_dvd_right ((Nat.dvd_add_right hdu).mp hdv) 2
        · omega
        · omega
        · omega
      rcases lt_or_gt_of_ne hb23 with hlt | hgt
      · exact step_case b₂ b₃ hlt hd_b2 hd_b3 hb2_in hb3_in
      · exact step_case b₃ b₂ hgt hd_b3 hd_b2 hb3_in hb2_in
  rcases lt_or_gt_of_ne hb12 with h12 | h21 <;>
  rcases lt_or_gt_of_ne hb13 with h13 | h31 <;>
  rcases lt_or_gt_of_ne hb23 with h23 | h32
  · have heq : ({b₁, b₂, b₃} : Finset ℕ) = {b₁, b₂, b₃} := rfl
    have ⟨p1, p2⟩ := hwrap b₁ b₂ b₃ hb₁_I hb₃_I h12 h23 hb1 hb2 hb3 heq
    exact ⟨fun d' hd1 hd2 _ => p1 d' hd1 hd2, p2⟩
  · have heq : ({b₁, b₃, b₂} : Finset ℕ) = {b₁, b₂, b₃} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have ⟨p1, p2⟩ := hwrap b₁ b₃ b₂ hb₁_I hb₂_I h13 h32 hb1 hb3 hb2 heq
    exact ⟨fun d' hd1 _ hd3 => p1 d' hd1 hd3, p2⟩
  · omega
  · have heq : ({b₃, b₁, b₂} : Finset ℕ) = {b₁, b₂, b₃} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have ⟨p1, p2⟩ := hwrap b₃ b₁ b₂ hb₃_I hb₂_I h31 h12 hb3 hb1 hb2 heq
    exact ⟨fun d' hd1 _ hd3 => p1 d' hd3 hd1, p2⟩
  · have heq : ({b₂, b₁, b₃} : Finset ℕ) = {b₁, b₂, b₃} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have ⟨p1, p2⟩ := hwrap b₂ b₁ b₃ hb₂_I hb₃_I h21 h13 hb2 hb1 hb3 heq
    exact ⟨fun d' hd1 hd2 _ => p1 d' hd2 hd1, p2⟩
  · omega
  · have heq : ({b₂, b₃, b₁} : Finset ℕ) = {b₁, b₂, b₃} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have ⟨p1, p2⟩ := hwrap b₂ b₃ b₁ hb₂_I hb₁_I h23 h31 hb2 hb3 hb1 heq
    exact ⟨fun d' _ hd2 hd3 => p1 d' hd2 hd3, p2⟩
  · have heq : ({b₃, b₂, b₁} : Finset ℕ) = {b₁, b₂, b₃} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have ⟨p1, p2⟩ := hwrap b₃ b₂ b₁ hb₃_I hb₁_I h32 h21 hb3 hb2 hb1 heq
    exact ⟨fun d' _ hd2 hd3 => p1 d' hd3 hd2, p2⟩

private lemma gcd_five_eq_one_5 {A : Finset ℕ} {a₁ a₂ a₃ a₄ a₅ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄, a₅}) (hAgcd : A.gcd id = 1)
    {d : ℕ} (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) (hd4 : d ∣ a₄) (hd5 : d ∣ a₅) :
    d = 1 := by
  have hdvd : d ∣ A.gcd id := by
    refine Finset.dvd_gcd fun a ha => ?_
    rw [hA_eq] at ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [hAgcd] at hdvd
  exact Nat.eq_one_of_dvd_one hdvd

/-! ## Part 2: `r = 3` Case B (Three Elements Share Unique Multiple `b₁`) -/

private lemma cover_six_of_r3_same_slot {A : Finset ℕ} {x M u₁ u₂ s₁ s₂ s₃ b₁ b₂ b₃ : ℕ}
    (hA_eq : A = {u₁, u₂, s₁, s₂, s₃})
    (h12 : u₁ ≠ u₂) (h1s1 : u₁ ≠ s₁) (h1s2 : u₁ ≠ s₂) (h1s3 : u₁ ≠ s₃)
    (h2s1 : u₂ ≠ s₁) (h2s2 : u₂ ≠ s₂) (h2s3 : u₂ ≠ s₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb₃_I : b₃ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hu1_b1 : u₁ ∣ b₁) (hu2_b1 : u₂ ∣ b₁) (hs1_b1 : s₁ ∣ b₁) (hs2_b2 : s₂ ∣ b₂) (hs3_b3 : s₃ ∣ b₃)
    (hu1_h : M < 2 * u₁) (hu2_h : M < 2 * u₂) (hs1_h : M < 2 * s₁) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hu1_p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu2_p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs1_p : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hs2_p : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hs3_p : 0 < s₃ := hA_pos s₃ (by rw [hA_eq]; simp)
  have hu1_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hu2_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hs1_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hs2_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  have hs3_M : s₃ ≤ M := hA_le s₃ (by rw [hA_eq]; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb1_0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb2_0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hb3_0 : b₃ ≠ 0 := (pos_of_mem_consecInterval hb₃_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      u₁.factorization p + u₂.factorization p + s₁.factorization p +
        s₂.factorization p + s₃.factorization p := fun p => by
    rw [hA_eq,
        Finset.sum_insert (by simp [h12, h1s1, h1s2, h1s3]),
        Finset.sum_insert (by simp [h2s1, h2s2, h2s3]),
        Finset.sum_insert (by simp [hs12, hs13]),
        Finset.sum_insert (by simp [hs23]),
        Finset.sum_singleton]
    ring
  let g₁₂ := Nat.gcd u₁ u₂
  let g₁₃ := Nat.gcd u₁ s₁
  let g₂₃ := Nat.gcd u₂ s₁
  let D := Nat.gcd g₁₂ s₁
  have hg12_p : 0 < g₁₂ := Nat.gcd_pos_of_pos_left u₂ hu1_p
  have hg13_p : 0 < g₁₃ := Nat.gcd_pos_of_pos_left s₁ hu1_p
  have hg23_p : 0 < g₂₃ := Nat.gcd_pos_of_pos_left s₁ hu2_p
  have hD_p : 0 < D := Nat.gcd_pos_of_pos_left s₁ hg12_p
  have h3g12 : 3 * g₁₂ ≤ M := three_mul_le_of_two_gt_half_5 hg12_p h12 hu1_M hu2_M hu1_h hu2_h
    (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
  have h3g13 : 3 * g₁₃ ≤ M := three_mul_le_of_two_gt_half_5 hg13_p h1s1 hu1_M hs1_M hu1_h hs1_h
    (Nat.gcd_dvd_left u₁ s₁) (Nat.gcd_dvd_right u₁ s₁)
  have h3g23 : 3 * g₂₃ ≤ M := three_mul_le_of_two_gt_half_5 hg23_p h2s1 hu2_M hs1_M hu2_h hs1_h
    (Nat.gcd_dvd_left u₂ s₁) (Nat.gcd_dvd_right u₂ s₁)
  have h5D : 5 * D ≤ M := five_mul_le_of_three_distinct_gt_half_5 hD_p h12 h1s1 h2s1
    hu1_M hu2_M hs1_M hu1_h hu2_h hs1_h
    (dvd_trans (Nat.gcd_dvd_left g₁₂ s₁) (Nat.gcd_dvd_left u₁ u₂))
    (dvd_trans (Nat.gcd_dvd_left g₁₂ s₁) (Nat.gcd_dvd_right u₁ u₂))
    (Nat.gcd_dvd_right g₁₂ s₁)
  -- Cleanly handle the 3 subcases of `g₁₂, g₁₃, g₂₃`:
  have finish_all_three : ∀ w₁ w₂ w₃ : ℕ,
      w₁ ∈ consecInterval x M → w₂ ∈ consecInterval x M → w₃ ∈ consecInterval x M →
      w₁ ≠ b₁ → w₁ ≠ b₂ → w₁ ≠ b₃ → g₁₂ ∣ w₁ →
      w₂ ≠ b₁ → w₂ ≠ b₂ → w₂ ≠ b₃ → g₁₃ ∣ w₂ →
      w₃ ≠ b₁ → w₃ ≠ b₂ → w₃ ≠ b₃ → g₂₃ ∣ w₃ →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro w₁ w₂ w₃ hw1_I hw2_I hw3_I hw1_1 hw1_2 hw1_3 hg12_w1
      hw2_1 hw2_2 hw2_3 hg13_w2 hw3_1 hw3_2 hw3_3 hg23_w3
    have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
    have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw2_I).ne'
    have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
    by_cases h123 : w₁ = w₂ ∧ w₂ = w₃
    · rcases h123 with ⟨rfl, rfl⟩
      have h4_card : ({b₁, b₂, b₃, w₁} : Finset ℕ).card + 1 ≤ 5 := by
        have := card_finset_le_four_5 b₁ b₂ b₃ w₁; omega
      obtain ⟨w', hw'_I, hw'_not, hD_w'⟩ := exists_avoiding_multiple_in_consecInterval x M D
        {b₁, b₂, b₃, w₁} hD_p (le_trans (Nat.mul_le_mul_right D h4_card) h5D)
      have hw'_b1 : w' ≠ b₁ := fun h => hw'_not (by simp [h])
      have hw'_b2 : w' ≠ b₂ := fun h => hw'_not (by simp [h])
      have hw'_b3 : w' ≠ b₃ := fun h => hw'_not (by simp [h])
      have hw'_w1 : w' ≠ w₁ := fun h => hw'_not (by simp [h])
      have hw'_0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
      let B : Finset ℕ := {b₁, b₂, b₃, w₁, w'}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, le_trans (card_finset_le_five_5 b₁ b₂ b₃ w₁ w') (by omega),
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsumA_eq p,
          Finset.sum_insert (by simp [hb12, hb13, hw1_1.symm, hw'_b1.symm]),
          Finset.sum_insert (by simp [hb23, hw1_2.symm, hw'_b2.symm]),
          Finset.sum_insert (by simp [hw1_3.symm, hw'_b3.symm]),
          Finset.sum_insert (by simp [hw'_w1.symm]),
          Finset.sum_singleton]
      have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
      have hb1_u2 := fac_le_of_dvd_5 hb1_0 hu2_b1 (p := p)
      have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
      have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hw1_12 := fac_le_of_dvd_5 hw1_0 hg12_w1 (p := p)
      have hw1_13 := fac_le_of_dvd_5 hw1_0 hg13_w2 (p := p)
      have hw1_23 := fac_le_of_dvd_5 hw1_0 hg23_w3 (p := p)
      have hw'_D := fac_le_of_dvd_5 hw'_0 hD_w' (p := p)
      rw [fac_gcd_eq_min_5 hu1_p.ne' hu2_p.ne'] at hw1_12
      rw [fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'] at hw1_13
      rw [fac_gcd_eq_min_5 hu2_p.ne' hs1_p.ne'] at hw1_23
      rw [fac_gcd_eq_min_5 hg12_p.ne' hs1_p.ne', fac_gcd_eq_min_5 hu1_p.ne' hu2_p.ne'] at hw'_D
      omega
    · let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂, w₃}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₂ w₃,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsumA_eq p]
      have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
      have hb1_u2 := fac_le_of_dvd_5 hb1_0 hu2_b1 (p := p)
      have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
      have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hw1_12 := fac_le_of_dvd_5 hw1_0 hg12_w1 (p := p)
      have hw2_13 := fac_le_of_dvd_5 hw2_0 hg13_w2 (p := p)
      have hw3_23 := fac_le_of_dvd_5 hw3_0 hg23_w3 (p := p)
      rw [fac_gcd_eq_min_5 hu1_p.ne' hu2_p.ne'] at hw1_12
      rw [fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'] at hw2_13
      rw [fac_gcd_eq_min_5 hu2_p.ne' hs1_p.ne'] at hw3_23
      by_cases hw12 : w₁ = w₂
      · have hw23 : w₂ ≠ w₃ := fun h => h123 ⟨hw12, h⟩
        have hw13 : w₁ ≠ w₃ := hw12 ▸ hw23
        have hsub5 : ({b₁, b₂, b₃, w₁, w₃} : Finset ℕ) ⊆ B := fun b hb => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb12, hb13, hw1_1.symm, hw3_1.symm]),
            Finset.sum_insert (by simp [hb23, hw1_2.symm, hw3_2.symm]),
            Finset.sum_insert (by simp [hw1_3.symm, hw3_3.symm]),
            Finset.sum_insert (by simp [hw13]), Finset.sum_singleton] at hleB
        rw [← hw12] at hw2_13
        omega
      · by_cases hw13 : w₁ = w₃
        · have hsub5 : ({b₁, b₂, b₃, w₁, w₂} : Finset ℕ) ⊆ B := fun b hb => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
          have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
          rw [Finset.sum_insert (by simp [hb12, hb13, hw1_1.symm, hw2_1.symm]),
              Finset.sum_insert (by simp [hb23, hw1_2.symm, hw2_2.symm]),
              Finset.sum_insert (by simp [hw1_3.symm, hw2_3.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
          rw [← hw13] at hw3_23
          omega
        · by_cases hw23 : w₂ = w₃
          · have hsub5 : ({b₁, b₂, b₃, w₁, w₂} : Finset ℕ) ⊆ B := fun b hb => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
            have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
            rw [Finset.sum_insert (by simp [hb12, hb13, hw1_1.symm, hw2_1.symm]),
                Finset.sum_insert (by simp [hb23, hw1_2.symm, hw2_2.symm]),
                Finset.sum_insert (by simp [hw1_3.symm, hw2_3.symm]),
                Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
            rw [← hw23] at hw3_23
            omega
          · dsimp [B]
            rw [Finset.sum_insert (by simp [hb12, hb13, hw1_1.symm, hw2_1.symm, hw3_1.symm]),
                Finset.sum_insert (by simp [hb23, hw1_2.symm, hw2_2.symm, hw3_2.symm]),
                Finset.sum_insert (by simp [hw1_3.symm, hw2_3.symm, hw3_3.symm]),
                Finset.sum_insert (by simp [hw12, hw13]),
                Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
            omega
  -- Helper when one of the three pairwise GCDs stays inside `{b₁, b₂, b₃}`:
  have one_stays : ∀ x₁ x₂ x₃ : ℕ,
      A = {x₁, x₂, x₃, s₂, s₃} →
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
      x₁ ≠ s₂ → x₁ ≠ s₃ → x₂ ≠ s₂ → x₂ ≠ s₃ → x₃ ≠ s₂ → x₃ ≠ s₃ →
      0 < x₁ → 0 < x₂ → 0 < x₃ →
      x₁ ≤ M → x₂ ≤ M → x₃ ≤ M →
      M < 2 * x₁ → M < 2 * x₂ → M < 2 * x₃ →
      x₁ ∣ b₁ → x₂ ∣ b₁ → x₃ ∣ b₁ →
      (consecInterval x M).filter (fun b => Nat.gcd x₁ x₂ ∣ b) ⊆ {b₁, b₂, b₃} →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro x₁ x₂ x₃ hA' h_12 h_13 h_23 h_1s2 h_1s3 h_2s2 h_2s3 h_3s2 h_3s3
      hx1p hx2p hx3p hx1M hx2M hx3M hx1h hx2h hx3h hx1b1 hx2b1 hx3b1 hsub_12
    set g := Nat.gcd x₁ x₂
    have hg_p : 0 < g := Nat.gcd_pos_of_pos_left x₂ hx1p
    have h3g : 3 * g ≤ M := three_mul_le_of_two_gt_half_5 hg_p h_12 hx1M hx2M hx1h hx2h
      (Nat.gcd_dvd_left x₁ x₂) (Nat.gcd_dvd_right x₁ x₂)
    obtain ⟨hgb1, hgb2, hgb3, hM4g⟩ := dvd_triple_of_filter_subset_triple_5 hg_p h3g hb12 hb13 hb23 hsub_12
    have hspan_g := (span_three_props_5 hg_p hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hgb1 hgb2 hgb3 hsub_12).1
    have check_other : ∀ y : ℕ, x₁ ≠ y → x₂ ≠ y → 0 < y → y ≤ M → M < 2 * y → y ∣ b₁ →
        (consecInterval x M).filter (fun b => Nat.gcd x₁ y ∣ b) ⊆ {b₁, b₂, b₃} → False := by
      intro y hx1y hx2y hyp hyM hyh _ hsub_1y
      set g' := Nat.gcd x₁ y
      have hg'_p : 0 < g' := Nat.gcd_pos_of_pos_left y hx1p
      have h3g' : 3 * g' ≤ M := three_mul_le_of_two_gt_half_5 hg'_p hx1y hx1M hyM hx1h hyh
        (Nat.gcd_dvd_left x₁ y) (Nat.gcd_dvd_right x₁ y)
      obtain ⟨hg'b1, hg'b2, hg'b3, _⟩ := dvd_triple_of_filter_subset_triple_5 hg'_p h3g' hb12 hb13 hb23 hsub_1y
      have hspan_g' := (span_three_props_5 hg'_p hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hg'b1 hg'b2 hg'b3 hsub_1y).1
      have hgg' : g = g' := Nat.dvd_antisymm (hspan_g' g hgb1 hgb2 hgb3) (hspan_g g' hg'b1 hg'b2 hg'b3)
      have h5g : 5 * g ≤ M := five_mul_le_of_three_distinct_gt_half_5 hg_p h_12 hx1y hx2y
        hx1M hx2M hyM hx1h hx2h hyh
        (Nat.gcd_dvd_left x₁ x₂) (Nat.gcd_dvd_right x₁ x₂) (hgg' ▸ Nat.gcd_dvd_right x₁ y)
      omega
    have hnot_13 : ¬ ((consecInterval x M).filter (fun b => Nat.gcd x₁ x₃ ∣ b) ⊆ {b₁, b₂, b₃}) :=
      fun hs => check_other x₃ h_13 h_23 hx3p hx3M hx3h hx3b1 hs
    have hnot_23 : ¬ ((consecInterval x M).filter (fun b => Nat.gcd x₂ x₃ ∣ b) ⊆ {b₁, b₂, b₃}) := fun hs => by
      have hs' : (consecInterval x M).filter (fun b => Nat.gcd x₂ x₁ ∣ b) ⊆ {b₁, b₂, b₃} := by
        simpa [Nat.gcd_comm] using hsub_12
      set g₂₁ := Nat.gcd x₂ x₁
      have hg21_p : 0 < g₂₁ := Nat.gcd_pos_of_pos_left x₁ hx2p
      have h3g21 : 3 * g₂₁ ≤ M := three_mul_le_of_two_gt_half_5 hg21_p h_12.symm hx2M hx1M hx2h hx1h
        (Nat.gcd_dvd_left x₂ x₁) (Nat.gcd_dvd_right x₂ x₁)
      obtain ⟨h21b1, h21b2, h21b3, hM4g21⟩ := dvd_triple_of_filter_subset_triple_5 hg21_p h3g21 hb12 hb13 hb23 hs'
      have hspan_21 := (span_three_props_5 hg21_p hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 h21b1 h21b2 h21b3 hs').1
      set g' := Nat.gcd x₂ x₃
      have hg'_p : 0 < g' := Nat.gcd_pos_of_pos_left x₃ hx2p
      have h3g' : 3 * g' ≤ M := three_mul_le_of_two_gt_half_5 hg'_p h_23 hx2M hx3M hx2h hx3h
        (Nat.gcd_dvd_left x₂ x₃) (Nat.gcd_dvd_right x₂ x₃)
      obtain ⟨hg'b1, hg'b2, hg'b3, _⟩ := dvd_triple_of_filter_subset_triple_5 hg'_p h3g' hb12 hb13 hb23 hs
      have hspan_g' := (span_three_props_5 hg'_p hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hg'b1 hg'b2 hg'b3 hs).1
      have hgg' : g₂₁ = g' := Nat.dvd_antisymm (hspan_g' g₂₁ h21b1 h21b2 h21b3) (hspan_21 g' hg'b1 hg'b2 hg'b3)
      have h5g21 : 5 * g₂₁ ≤ M := five_mul_le_of_three_distinct_gt_half_5 hg21_p h_12.symm h_23 h_13
        hx2M hx1M hx3M hx2h hx1h hx3h
        (Nat.gcd_dvd_left x₂ x₁) (Nat.gcd_dvd_right x₂ x₁) (hgg' ▸ Nat.gcd_dvd_right x₂ x₃)
      omega
    obtain ⟨w₂, hw2_I, hw2_b1, hw2_b2, hw2_b3, hg13_w2⟩ := exists_avoiding_of_not_subset_triple_5 hnot_13
    obtain ⟨w₃, hw3_I, hw3_b1, hw3_b2, hw3_b3, hg23_w3⟩ := exists_avoiding_of_not_subset_triple_5 hnot_23
    have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw2_I).ne'
    have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
    have hnot_both_s : ¬ (g ∣ s₂ ∧ g ∣ s₃) := by
      rintro ⟨hgs2, hgs3⟩
      obtain ⟨q₁, hq1⟩ := Nat.gcd_dvd_left x₁ x₂
      obtain ⟨q₂, hq2⟩ := Nat.gcd_dvd_right x₁ x₂
      obtain ⟨k₂, hk2⟩ := hgs2
      obtain ⟨k₃, hk3⟩ := hgs3
      have hq1_r : q₁ = 2 ∨ q₁ = 3 := by
        have : 2 * g < 2 * (g * q₁) := by rw [← hq1]; omega
        have : g * q₁ < 4 * g := by rw [← hq1]; omega
        have : 1 < q₁ := by by_contra hle; have := Nat.mul_le_mul_left g (by omega : q₁ ≤ 1); omega
        have : q₁ < 4 := by by_contra hge; have := Nat.mul_le_mul_left g (by omega : 4 ≤ q₁); omega
        omega
      have hq2_r : q₂ = 2 ∨ q₂ = 3 := by
        have : 2 * g < 2 * (g * q₂) := by rw [← hq2]; omega
        have : g * q₂ < 4 * g := by rw [← hq2]; omega
        have : 1 < q₂ := by by_contra hle; have := Nat.mul_le_mul_left g (by omega : q₂ ≤ 1); omega
        have : q₂ < 4 := by by_contra hge; have := Nat.mul_le_mul_left g (by omega : 4 ≤ q₂); omega
        omega
      have hq12 : q₁ ≠ q₂ := fun h => h_12 ((hq1.trans (congrArg (g * ·) h)).trans hq2.symm)
      have hk2_r : k₂ = 1 := by
        have hk2_pos : 1 ≤ k₂ := by
          by_contra h0; have : k₂ = 0 := by omega
          rw [this, mul_zero] at hk2; omega
        have hk2_lt : k₂ < 4 := by
          by_contra hge; have := Nat.mul_le_mul_left g (by omega : 4 ≤ k₂); omega
        have hk2_nq1 : k₂ ≠ q₁ := fun h => h_1s2 (by rw [hq1, hk2, h])
        have hk2_nq2 : k₂ ≠ q₂ := fun h => h_2s2 (by rw [hq2, hk2, h])
        omega
      have hk3_r : k₃ = 1 := by
        have hk3_pos : 1 ≤ k₃ := by
          by_contra h0; have : k₃ = 0 := by omega
          rw [this, mul_zero] at hk3; omega
        have hk3_lt : k₃ < 4 := by
          by_contra hge; have := Nat.mul_le_mul_left g (by omega : 4 ≤ k₃); omega
        have hk3_nq1 : k₃ ≠ q₁ := fun h => h_1s3 (by rw [hq1, hk3, h])
        have hk3_nq2 : k₃ ≠ q₂ := fun h => h_2s3 (by rw [hq2, hk3, h])
        omega
      exact hs23 (by rw [hk2, hk3, hk2_r, hk3_r])
    have handle_nd : ∀ y₂ y₃ b_y2 b_y3 : ℕ,
        A = {x₁, x₂, x₃, y₂, y₃} →
        b_y2 ∈ consecInterval x M → b_y3 ∈ consecInterval x M →
        b₁ ≠ b_y2 → b₁ ≠ b_y3 → b_y2 ≠ b_y3 →
        {b₁, b_y2, b_y3} = ({b₁, b₂, b₃} : Finset ℕ) →
        y₂ ≠ y₃ → x₁ ≠ y₂ → x₁ ≠ y₃ → x₂ ≠ y₂ → x₂ ≠ y₃ → x₃ ≠ y₂ → x₃ ≠ y₃ →
        y₂ ∣ b_y2 → y₃ ∣ b_y3 → g ∣ b_y2 → g ∣ b_y3 →
        w₂ ≠ b_y2 → w₂ ≠ b_y3 → w₃ ≠ b_y2 → w₃ ≠ b_y3 → ¬ (g ∣ y₃) →
        ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
      intro y₂ y₃ b_y2 b_y3 hA'' hby2_I hby3_I hb1y2 hb1y3 hby23 _ hy23
        hx1y2 hx1y3 hx2y2 hx2y3 hx3y2 hx3y3 hy2_d hy3_d hgy2 hgy3 hw2y2 hw2y3 hw3y2 hw3y3 hnd
      have hy2_0 : y₂ ≠ 0 := (hA_pos y₂ (by rw [hA'']; simp)).ne'
      have hy3_0 : y₃ ≠ 0 := (hA_pos y₃ (by rw [hA'']; simp)).ne'
      have hby2_0 : b_y2 ≠ 0 := (pos_of_mem_consecInterval hby2_I).ne'
      have hby3_0 : b_y3 ≠ 0 := (pos_of_mem_consecInterval hby3_I).ne'
      let d₃ := Nat.gcd g y₃
      have hd3_p : 0 < d₃ := Nat.gcd_pos_of_pos_left y₃ hg_p
      have h2d3 : 2 * d₃ ≤ g := by
        obtain ⟨q, hq⟩ := Nat.gcd_dvd_left g y₃
        have hq2 : 2 ≤ q := by
          by_contra hlt; have hq1 : q = 0 ∨ q = 1 := by omega
          rcases hq1 with rfl | rfl
          · simp at hq; omega
          · rw [mul_one] at hq; exact hnd (hq ▸ Nat.gcd_dvd_right g y₃)
        rw [hq]; rw [mul_comm 2]; exact Nat.mul_le_mul_left d₃ hq2
      have h6d3 : 6 * d₃ ≤ M := by omega
      have h5_card : ({b₁, b_y2, b_y3, w₂, w₃} : Finset ℕ).card + 1 ≤ 6 := by
        have := card_finset_le_five_5 b₁ b_y2 b_y3 w₂ w₃; omega
      obtain ⟨w₁, hw1_I, hw1_not, hd3_w1⟩ := exists_avoiding_multiple_in_consecInterval x M d₃
        {b₁, b_y2, b_y3, w₂, w₃} hd3_p (le_trans (Nat.mul_le_mul_right d₃ h5_card) h6d3)
      have hw1_b1 : w₁ ≠ b₁ := fun h => hw1_not (by simp [h])
      have hw1_by2 : w₁ ≠ b_y2 := fun h => hw1_not (by simp [h])
      have hw1_by3 : w₁ ≠ b_y3 := fun h => hw1_not (by simp [h])
      have hw1_w2 : w₁ ≠ w₂ := fun h => hw1_not (by simp [h])
      have hw1_w3 : w₁ ≠ w₃ := fun h => hw1_not (by simp [h])
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      let B : Finset ℕ := {b₁, b_y2, b_y3, w₁, w₂, w₃}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 b₁ b_y2 b_y3 w₁ w₂ w₃,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      have hsum' : ∑ a ∈ A, a.factorization p =
          x₁.factorization p + x₂.factorization p + x₃.factorization p +
            y₂.factorization p + y₃.factorization p := by
        rw [hA'', Finset.sum_insert (by simp [h_12, h_13, hx1y2, hx1y3]),
            Finset.sum_insert (by simp [h_23, hx2y2, hx2y3]),
            Finset.sum_insert (by simp [hx3y2, hx3y3]),
            Finset.sum_insert (by simp [hy23]), Finset.sum_singleton]
        ring
      rw [hsum']
      have hb1_x1 := fac_le_of_dvd_5 hb1_0 hx1b1 (p := p)
      have hb1_x2 := fac_le_of_dvd_5 hb1_0 hx2b1 (p := p)
      have hb1_x3 := fac_le_of_dvd_5 hb1_0 hx3b1 (p := p)
      have hby2_y2 := fac_le_of_dvd_5 hby2_0 hy2_d (p := p)
      have hby2_g := fac_le_of_dvd_5 hby2_0 hgy2 (p := p)
      have hby3_y3 := fac_le_of_dvd_5 hby3_0 hy3_d (p := p)
      have hby3_g := fac_le_of_dvd_5 hby3_0 hgy3 (p := p)
      have hw1_d3 := fac_le_of_dvd_5 hw1_0 hd3_w1 (p := p)
      have hw2_13 := fac_le_of_dvd_5 hw2_0 hg13_w2 (p := p)
      have hw3_23 := fac_le_of_dvd_5 hw3_0 hg23_w3 (p := p)
      have hg_fac : g.factorization p = min (x₁.factorization p) (x₂.factorization p) :=
        fac_gcd_eq_min_5 hx1p.ne' hx2p.ne'
      rw [fac_gcd_eq_min_5 hg_p.ne' hy3_0, hg_fac] at hw1_d3
      rw [hg_fac] at hby2_g hby3_g
      rw [fac_gcd_eq_min_5 hx1p.ne' hx3p.ne'] at hw2_13
      rw [fac_gcd_eq_min_5 hx2p.ne' hx3p.ne'] at hw3_23
      by_cases hw23 : w₂ = w₃
      · have hsub5 : ({b₁, b_y2, b_y3, w₁, w₂} : Finset ℕ) ⊆ B := fun b hb => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb1y2, hb1y3, hw1_b1.symm, hw2_b1.symm]),
            Finset.sum_insert (by simp [hby23, hw1_by2.symm, hw2y2.symm]),
            Finset.sum_insert (by simp [hw1_by3.symm, hw2y3.symm]),
            Finset.sum_insert (by simp [hw1_w2]), Finset.sum_singleton] at hleB
        rw [← hw23] at hw3_23
        omega
      · dsimp [B]
        rw [Finset.sum_insert (by simp [hb1y2, hb1y3, hw1_b1.symm, hw2_b1.symm, hw3_b1.symm]),
            Finset.sum_insert (by simp [hby23, hw1_by2.symm, hw2y2.symm, hw3y2.symm]),
            Finset.sum_insert (by simp [hw1_by3.symm, hw2y3.symm, hw3y3.symm]),
            Finset.sum_insert (by simp [hw1_w2, hw1_w3]),
            Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
        omega
    by_cases hgs3 : g ∣ s₃
    · have hnds2 : ¬ (g ∣ s₂) := fun h => hnot_both_s ⟨h, hgs3⟩
      have hA_sw : A = {x₁, x₂, x₃, s₃, s₂} := by
        rw [hA']; exact congrArg (insert x₁) (congrArg (insert x₂) (congrArg (insert x₃) (Finset.pair_comm s₂ s₃)))
      have hset_sw : ({b₁, b₃, b₂} : Finset ℕ) = {b₁, b₂, b₃} := by rw [Finset.pair_comm b₂ b₃]
      exact handle_nd s₃ s₂ b₃ b₂ hA_sw hb₃_I hb₂_I hb13 hb12 hb23.symm hset_sw
        hs23.symm h_1s3 h_1s2 h_2s3 h_2s2 h_3s3 h_3s2 hs3_b3 hs2_b2 hgb3 hgb2
        hw2_b3 hw2_b2 hw3_b3 hw3_b2 hnds2
    · exact handle_nd s₂ s₃ b₂ b₃ hA' hb₂_I hb₃_I hb12 hb13 hb23 rfl
        hs23 h_1s2 h_1s3 h_2s2 h_2s3 h_3s2 h_3s3 hs2_b2 hs3_b3 hgb2 hgb3
        hw2_b2 hw2_b3 hw3_b2 hw3_b3 hgs3
  by_cases hs12_sub : (consecInterval x M).filter (fun b => g₁₂ ∣ b) ⊆ {b₁, b₂, b₃}
  · exact one_stays u₁ u₂ s₁ hA_eq h12 h1s1 h2s1 h1s2 h1s3 h2s2 h2s3 hs12 hs13
      hu1_p hu2_p hs1_p hu1_M hu2_M hs1_M hu1_h hu2_h hs1_h hu1_b1 hu2_b1 hs1_b1 hs12_sub
  · by_cases hs13_sub : (consecInterval x M).filter (fun b => g₁₃ ∣ b) ⊆ {b₁, b₂, b₃}
    · have hA_sw : A = {u₁, s₁, u₂, s₂, s₃} := by
        rw [hA_eq]; apply Finset.Subset.antisymm
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      exact one_stays u₁ s₁ u₂ hA_sw h1s1 h12 h2s1.symm h1s2 h1s3 hs12 hs13 h2s2 h2s3
        hu1_p hs1_p hu2_p hu1_M hs1_M hu2_M hu1_h hs1_h hu2_h hu1_b1 hs1_b1 hu2_b1 hs13_sub
    · by_cases hs23_sub : (consecInterval x M).filter (fun b => g₂₃ ∣ b) ⊆ {b₁, b₂, b₃}
      · have hA_sw : A = {u₂, s₁, u₁, s₂, s₃} := by
          rw [hA_eq]; apply Finset.Subset.antisymm
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        exact one_stays u₂ s₁ u₁ hA_sw h2s1 h12.symm h1s1.symm h2s2 h2s3 hs12 hs13 h1s2 h1s3
          hu2_p hs1_p hu1_p hu2_M hs1_M hu1_M hu2_h hs1_h hu1_h hu2_b1 hs1_b1 hu1_b1 hs23_sub
      · obtain ⟨w₁, hw1_I, hw1_1, hw1_2, hw1_3, hg12_w1⟩ := exists_avoiding_of_not_subset_triple_5 hs12_sub
        obtain ⟨w₂, hw2_I, hw2_1, hw2_2, hw2_3, hg13_w2⟩ := exists_avoiding_of_not_subset_triple_5 hs13_sub
        obtain ⟨w₃, hw3_I, hw3_1, hw3_2, hw3_3, hg23_w3⟩ := exists_avoiding_of_not_subset_triple_5 hs23_sub
        exact finish_all_three w₁ w₂ w₃ hw1_I hw2_I hw3_I hw1_1 hw1_2 hw1_3 hg12_w1
          hw2_1 hw2_2 hw2_3 hg13_w2 hw3_1 hw3_2 hw3_3 hg23_w3

/-! ## Part 3: `r = 3` Case A (Two Slots `(u₁, s₁) ∣ b₁`, `(u₂, s₂) ∣ b₂`, `s₃ ∣ b₃`) -/

private lemma cover_six_of_r3_two_slots_A2 {A : Finset ℕ} {x M u₁ s₁ u₂ s₂ s₃ b₁ b₂ b₃ w₂ : ℕ}
    (hA_eq : A = {u₁, s₁, u₂, s₂, s₃})
    (h1s1 : u₁ ≠ s₁) (h12 : u₁ ≠ u₂) (h1s2 : u₁ ≠ s₂) (h1s3 : u₁ ≠ s₃)
    (hs12 : s₁ ≠ u₂) (hs1s2 : s₁ ≠ s₂) (hs1s3 : s₁ ≠ s₃)
    (h2s2 : u₂ ≠ s₂) (h2s3 : u₂ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (_hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb₃_I : b₃ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hu1_b1 : u₁ ∣ b₁) (hs1_b1 : s₁ ∣ b₁) (hu2_b2 : u₂ ∣ b₂) (hs2_b2 : s₂ ∣ b₂) (hs3_b3 : s₃ ∣ b₃)
    (hsub_g1 : (consecInterval x M).filter (fun b => Nat.gcd u₁ s₁ ∣ b) ⊆ {b₁, b₂, b₃})
    (hw₂_I : w₂ ∈ consecInterval x M) (hw2_b1 : w₂ ≠ b₁) (hw2_b2 : w₂ ≠ b₂) (hw2_b3 : w₂ ≠ b₃)
    (hg2_w2 : Nat.gcd u₂ s₂ ∣ w₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hu1_p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hs1_p : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hu2_p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs2_p : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hs3_p : 0 < s₃ := hA_pos s₃ (by rw [hA_eq]; simp)
  have hu1_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hs1_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hu2_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hs2_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  have hs3_M : s₃ ≤ M := hA_le s₃ (by rw [hA_eq]; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb1_0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb2_0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hb3_0 : b₃ ≠ 0 := (pos_of_mem_consecInterval hb₃_I).ne'
  have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      u₁.factorization p + s₁.factorization p + u₂.factorization p +
        s₂.factorization p + s₃.factorization p := fun p => by
    rw [hA_eq,
        Finset.sum_insert (by simp [h1s1, h12, h1s2, h1s3]),
        Finset.sum_insert (by simp [hs12, hs1s2, hs1s3]),
        Finset.sum_insert (by simp [h2s2, h2s3]),
        Finset.sum_insert (by simp [hs23]), Finset.sum_singleton]
    ring
  let g₁ := Nat.gcd u₁ s₁
  let g₂ := Nat.gcd u₂ s₂
  have hg1_p : 0 < g₁ := Nat.gcd_pos_of_pos_left s₁ hu1_p
  have hg2_p : 0 < g₂ := Nat.gcd_pos_of_pos_left s₂ hu2_p
  have h2g1 : 2 * g₁ ≤ M := two_mul_gcd_le_of_distinct_5 hu1_p hs1_p hu1_M hs1_M h1s1
  have hg1_b1 : g₁ ∣ b₁ := dvd_trans (Nat.gcd_dvd_left u₁ s₁) hu1_b1
  have hg2_u2 : g₂ ∣ u₂ := Nat.gcd_dvd_left u₂ s₂
  have hg2_s2 : g₂ ∣ s₂ := Nat.gcd_dvd_right u₂ s₂
  by_cases hg1_b3 : g₁ ∣ b₃
  · -- **Subcase A2.1:** `g₁ ∣ b₃` (as well as `g₁ ∣ b₁`).
    let d₁ := Nat.gcd g₁ s₃
    have hd1_p : 0 < d₁ := Nat.gcd_pos_of_pos_left s₃ hg1_p
    have h3d1 : 3 * d₁ ≤ M := by
      have hT : ({u₁, s₁, s₃} : Finset ℕ).card * d₁ ≤ M :=
        card_mul_le_of_forall_dvd hd1_p fun a ha => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with ha_eq | ha_eq | ha_eq
          · rw [ha_eq]; exact ⟨hu1_p, hu1_M, dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)⟩
          · rw [ha_eq]; exact ⟨hs1_p, hs1_M, dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)⟩
          · rw [ha_eq]; exact ⟨hs3_p, hs3_M, Nat.gcd_dvd_right g₁ s₃⟩
      have hc3 : ({u₁, s₁, s₃} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h1s1, h1s3]),
            Finset.card_insert_of_notMem (by simp [hs1s3]), Finset.card_singleton]
      rwa [hc3] at hT
    by_cases hsub_d1 : (consecInterval x M).filter (fun b => d₁ ∣ b) ⊆ {b₁, b₂, b₃}
    · -- `d₁ ∣ b₁, b₂, b₃` and `M < 4 * d₁`.
      obtain ⟨hd1_b1, hd1_b2, hd1_b3, hM4d1⟩ :=
        dvd_triple_of_filter_subset_triple_5 hd1_p h3d1 hb12 hb13 hb23 hsub_d1
      let e₁ := Nat.gcd d₁ u₂
      let e₂ := Nat.gcd d₁ s₂
      have he1_p : 0 < e₁ := Nat.gcd_pos_of_pos_left u₂ hd1_p
      have he2_p : 0 < e₂ := Nat.gcd_pos_of_pos_left s₂ hd1_p
      have h4e1 : 4 * e₁ ≤ M := by
        have hT : ({u₁, s₁, s₃, u₂} : Finset ℕ).card * e₁ ≤ M :=
          card_mul_le_of_forall_dvd he1_p fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with ha_eq | ha_eq | ha_eq | ha_eq
            · rw [ha_eq]; exact ⟨hu1_p, hu1_M, dvd_trans (Nat.gcd_dvd_left d₁ u₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁))⟩
            · rw [ha_eq]; exact ⟨hs1_p, hs1_M, dvd_trans (Nat.gcd_dvd_left d₁ u₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁))⟩
            · rw [ha_eq]; exact ⟨hs3_p, hs3_M, dvd_trans (Nat.gcd_dvd_left d₁ u₂) (Nat.gcd_dvd_right g₁ s₃)⟩
            · rw [ha_eq]; exact ⟨hu2_p, hu2_M, Nat.gcd_dvd_right d₁ u₂⟩
        have hc4 : ({u₁, s₁, s₃, u₂} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [h1s1, h1s3, h12]),
              Finset.card_insert_of_notMem (by simp [hs1s3, hs12]),
              Finset.card_insert_of_notMem (by simp [h2s3.symm]), Finset.card_singleton]
        rwa [hc4] at hT
      have h4e2 : 4 * e₂ ≤ M := by
        have hT : ({u₁, s₁, s₃, s₂} : Finset ℕ).card * e₂ ≤ M :=
          card_mul_le_of_forall_dvd he2_p fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with ha_eq | ha_eq | ha_eq | ha_eq
            · rw [ha_eq]; exact ⟨hu1_p, hu1_M, dvd_trans (Nat.gcd_dvd_left d₁ s₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁))⟩
            · rw [ha_eq]; exact ⟨hs1_p, hs1_M, dvd_trans (Nat.gcd_dvd_left d₁ s₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁))⟩
            · rw [ha_eq]; exact ⟨hs3_p, hs3_M, dvd_trans (Nat.gcd_dvd_left d₁ s₂) (Nat.gcd_dvd_right g₁ s₃)⟩
            · rw [ha_eq]; exact ⟨hs2_p, hs2_M, Nat.gcd_dvd_right d₁ s₂⟩
        have hc4 : ({u₁, s₁, s₃, s₂} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [h1s1, h1s3, h1s2]),
              Finset.card_insert_of_notMem (by simp [hs1s3, hs1s2]),
              Finset.card_insert_of_notMem (by simp [hs23.symm]), Finset.card_singleton]
        rwa [hc4] at hT
      have h3_card : ({b₁, b₂, b₃} : Finset ℕ).card + 1 ≤ 4 := by
        have := card_finset_le_three_5 b₁ b₂ b₃; omega
      obtain ⟨w₁, hw1_I, hw1_not, he1_w1⟩ := exists_avoiding_multiple_in_consecInterval x M e₁
        {b₁, b₂, b₃} he1_p (le_trans (Nat.mul_le_mul_right e₁ h3_card) h4e1)
      obtain ⟨w₃, hw3_I, hw3_not, he2_w3⟩ := exists_avoiding_multiple_in_consecInterval x M e₂
        {b₁, b₂, b₃} he2_p (le_trans (Nat.mul_le_mul_right e₂ h3_card) h4e2)
      have hw1_b1 : w₁ ≠ b₁ := fun h => hw1_not (by simp [h])
      have hw1_b2 : w₁ ≠ b₂ := fun h => hw1_not (by simp [h])
      have hw1_b3 : w₁ ≠ b₃ := fun h => hw1_not (by simp [h])
      have hw3_b1 : w₃ ≠ b₁ := fun h => hw3_not (by simp [h])
      have hw3_b2 : w₃ ≠ b₂ := fun h => hw3_not (by simp [h])
      have hw3_b3 : w₃ ≠ b₃ := fun h => hw3_not (by simp [h])
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
      let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂, w₃}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₂ w₃,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsumA_eq p]
      have hgcd_d1_g2 : Nat.gcd d₁ g₂ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_right d₁ g₂) hg2_u2)
        (dvd_trans (Nat.gcd_dvd_right d₁ g₂) hg2_s2)
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (Nat.gcd_dvd_right g₁ s₃))
      have hfac_zero : min (d₁.factorization p) (min (u₂.factorization p) (s₂.factorization p)) = 0 := by
        have hz : (Nat.gcd d₁ g₂).factorization p = 0 := by rw [hgcd_d1_g2, Nat.factorization_one, Finsupp.zero_apply]
        rw [fac_gcd_eq_min_5 hd1_p.ne' hg2_p.ne', fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hz
        exact hz
      have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
      have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
      have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
      have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
      have hb2_d1 := fac_le_of_dvd_5 hb2_0 hd1_b2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hb3_g1 := fac_le_of_dvd_5 hb3_0 hg1_b3 (p := p)
      have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
      have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
      have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
      have hd1_eq : d₁.factorization p = min (g₁.factorization p) (s₃.factorization p) :=
        fac_gcd_eq_min_5 hg1_p.ne' hs3_p.ne'
      have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
        fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
      rw [fac_gcd_eq_min_5 hd1_p.ne' hu2_p.ne'] at hw1_e1
      rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
      rw [fac_gcd_eq_min_5 hd1_p.ne' hs2_p.ne'] at hw3_e2
      have hmem_w1 : w₁ ∈ B := by simp [B]
      have hmem_w2 : w₂ ∈ B := by simp [B]
      have hmem_w3 : w₃ ∈ B := by simp [B]
      have hle4 : ∀ w ∈ B, w ≠ b₁ → w ≠ b₂ → w ≠ b₃ →
          b₁.factorization p + b₂.factorization p + b₃.factorization p + w.factorization p ≤
            ∑ b ∈ B, b.factorization p := fun w hwB hwb1 hwb2 hwb3 => by
        have hsub4 : ({b₁, b₂, b₃, w} : Finset ℕ) ⊆ B := fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> simp [B, hwB]
        have := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb12, hb13, hwb1.symm]),
            Finset.sum_insert (by simp [hb23, hwb2.symm]),
            Finset.sum_insert (by simp [hwb3.symm]), Finset.sum_singleton] at this
        omega
      have h4_1 := hle4 w₁ hmem_w1 hw1_b1 hw1_b2 hw1_b3
      have h4_2 := hle4 w₂ hmem_w2 hw2_b1 hw2_b2 hw2_b3
      have h4_3 := hle4 w₃ hmem_w3 hw3_b1 hw3_b2 hw3_b3
      omega
    · -- `d₁` escapes `{b₁, b₂, b₃}` via `w₁`: `{b₁, b₂, b₃, w₁, w₂}` works!
      obtain ⟨w₁, hw1_I, hw1_b1, hw1_b2, hw1_b3, hd1_w1⟩ := exists_avoiding_of_not_subset_triple_5 hsub_d1
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, (card_finset_le_five_5 b₁ b₂ b₃ w₁ w₂).trans (by omega),
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsumA_eq p]
      have hgcd_d1_g2 : Nat.gcd d₁ g₂ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_right d₁ g₂) hg2_u2)
        (dvd_trans (Nat.gcd_dvd_right d₁ g₂) hg2_s2)
        (dvd_trans (Nat.gcd_dvd_left d₁ g₂) (Nat.gcd_dvd_right g₁ s₃))
      have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
      have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
      have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
      have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hb3_g1 := fac_le_of_dvd_5 hb3_0 hg1_b3 (p := p)
      have hw1_d1 := fac_le_of_dvd_5 hw1_0 hd1_w1 (p := p)
      have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
      rw [fac_gcd_eq_min_5 hg1_p.ne' hs3_p.ne', fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'] at hw1_d1
      rw [fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'] at hb3_g1
      rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
      by_cases hw12 : w₁ = w₂
      · have hzero : min (d₁.factorization p) (g₂.factorization p) = 0 := by
          have hz : (Nat.gcd d₁ g₂).factorization p = 0 := by rw [hgcd_d1_g2, Nat.factorization_one, Finsupp.zero_apply]
          rwa [fac_gcd_eq_min_5 hd1_p.ne' hg2_p.ne'] at hz
        rw [fac_gcd_eq_min_5 hg1_p.ne' hs3_p.ne', fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne',
            fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hzero
        have hsub4 : ({b₁, b₂, b₃, w₁} : Finset ℕ) ⊆ B := fun b hb => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm]),
            Finset.sum_insert (by simp [hb23, hw1_b2.symm]),
            Finset.sum_insert (by simp [hw1_b3.symm]), Finset.sum_singleton] at hleB
        rw [← hw12] at hw2_g2
        omega
      · have hleB : b₁.factorization p + b₂.factorization p + b₃.factorization p +
            w₁.factorization p + w₂.factorization p ≤ ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw2_b1.symm]),
              Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw2_b2.symm]),
              Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
          omega
        omega
  · -- **Subcase A2.2:** `¬ (g₁ ∣ b₃)`, so `(I.filter (g₁ ∣ ·)) ⊆ {b₁, b₂}`, `g₁ ∣ b₂`, `M < 3 * g₁`.
    have hsub_pair : (consecInterval x M).filter (fun b => g₁ ∣ b) ⊆ {b₁, b₂} := fun b hb => by
      have hmem := hsub_g1 hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (Finset.mem_filter.mp hb).2 hg1_b3
    obtain ⟨_, hg1_b2, hM3g1⟩ := dvd_pair_of_filter_subset_pair_5 hg1_p h2g1 hb12 hsub_pair
    have hu1s1_pair : (u₁ = g₁ ∧ s₁ = 2 * g₁) ∨ (s₁ = g₁ ∧ u₁ = 2 * g₁) := by
      rcases lt_or_gt_of_ne h1s1 with hlt | hgt
      · left; exact eq_pair_of_two_dvd_lt_three_mul_5 hg1_p hu1_p hlt hs1_M hM3g1
          (Nat.gcd_dvd_left u₁ s₁) (Nat.gcd_dvd_right u₁ s₁)
      · right; exact eq_pair_of_two_dvd_lt_three_mul_5 hg1_p hs1_p hgt hu1_M hM3g1
          (Nat.gcd_dvd_right u₁ s₁) (Nat.gcd_dvd_left u₁ s₁)
    have h2g1_b1 : 2 * g₁ ∣ b₁ := by
      rcases hu1s1_pair with ⟨_, hEq⟩ | ⟨_, hEq⟩
      · exact hEq ▸ hs1_b1
      · exact hEq ▸ hu1_b1
    let e₁ := Nat.gcd g₁ u₂
    let e₂ := Nat.gcd g₁ s₂
    let e := Nat.gcd g₁ g₂
    have he1_p : 0 < e₁ := Nat.gcd_pos_of_pos_left u₂ hg1_p
    have he2_p : 0 < e₂ := Nat.gcd_pos_of_pos_left s₂ hg1_p
    have he_p : 0 < e := Nat.gcd_pos_of_pos_left g₂ hg1_p
    have hg1_ne_u2 : g₁ ≠ u₂ := by
      rintro rfl
      rcases hu1s1_pair with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact h12 h; exact hs12 h]
    have hg1_ne_s2 : g₁ ≠ s₂ := by
      rintro rfl
      rcases hu1s1_pair with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact h1s2 h; exact hs1s2 h]
    have hnot_g1_u2 : ¬ (g₁ ∣ u₂) := fun hd => by
      obtain ⟨q, hq⟩ := hd
      have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq; omega
      have hq_lt3 : q < 3 := by by_contra h3; have := Nat.mul_le_mul_left g₁ (by omega : 3 ≤ q); omega
      have hq_12 : q = 1 ∨ q = 2 := by omega
      rcases hq_12 with rfl | rfl
      · exact hg1_ne_u2 (by rw [hq, mul_one])
      · rcases hu1s1_pair with ⟨_, hEq⟩ | ⟨_, hEq⟩
        · exact hs12 (by rw [hEq, hq, mul_comm 2 g₁])
        · exact h12.symm (by rw [hEq, hq, mul_comm 2 g₁])
    have hnot_g1_s2 : ¬ (g₁ ∣ s₂) := fun hd => by
      obtain ⟨q, hq⟩ := hd
      have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq; omega
      have hq_lt3 : q < 3 := by by_contra h3; have := Nat.mul_le_mul_left g₁ (by omega : 3 ≤ q); omega
      have hq_12 : q = 1 ∨ q = 2 := by omega
      rcases hq_12 with rfl | rfl
      · exact hg1_ne_s2 (by rw [hq, mul_one])
      · rcases hu1s1_pair with ⟨_, hEq⟩ | ⟨_, hEq⟩
        · exact hs1s2 (by rw [hEq, hq, mul_comm 2 g₁])
        · exact h1s2.symm (by rw [hEq, hq, mul_comm 2 g₁])
    have hnot_g1_g2 : ¬ (g₁ ∣ g₂) := fun h => hnot_g1_u2 (dvd_trans h hg2_u2)
    have h2e1_le : 2 * e₁ ≤ g₁ := by
      obtain ⟨q, hq⟩ := Nat.gcd_dvd_left g₁ u₂
      have hq2 : 2 ≤ q := by
        by_contra hlt; have : q = 0 ∨ q = 1 := by omega
        rcases this with rfl | rfl; simp at hq; omega; rw [mul_one] at hq; exact hnot_g1_u2 (hq ▸ Nat.gcd_dvd_right g₁ u₂)
      rw [hq, mul_comm 2]; exact Nat.mul_le_mul_left e₁ hq2
    have h2e2_le : 2 * e₂ ≤ g₁ := by
      obtain ⟨q, hq⟩ := Nat.gcd_dvd_left g₁ s₂
      have hq2 : 2 ≤ q := by
        by_contra hlt; have : q = 0 ∨ q = 1 := by omega
        rcases this with rfl | rfl; simp at hq; omega; rw [mul_one] at hq; exact hnot_g1_s2 (hq ▸ Nat.gcd_dvd_right g₁ s₂)
      rw [hq, mul_comm 2]; exact Nat.mul_le_mul_left e₂ hq2
    have h4e1 : 4 * e₁ ≤ M := by omega
    have h4e2 : 4 * e₂ ≤ M := by omega
    obtain ⟨q_e, hq_e⟩ := Nat.gcd_dvd_left g₁ g₂
    have hq_e_ge2 : 2 ≤ q_e := by
      by_contra hlt; have : q_e = 0 ∨ q_e = 1 := by omega
      rcases this with rfl | rfl; simp at hq_e; omega; rw [mul_one] at hq_e; exact hnot_g1_g2 (hq_e ▸ Nat.gcd_dvd_right g₁ g₂)
    by_cases hqe2 : q_e = 2
    · -- **Subcase A2.2a:** `g₁ = 2 * e`!
      have hg1_2e : g₁ = 2 * e := by rw [hq_e, hqe2, mul_comm]
      have h4e : 4 * e ≤ M := by omega
      have he_u2 : e ∣ u₂ := dvd_trans (Nat.gcd_dvd_right g₁ g₂) hg2_u2
      have he_s2 : e ∣ s₂ := dvd_trans (Nat.gcd_dvd_right g₁ g₂) hg2_s2
      have hn2_u2 : ¬ (2 ∣ u₂ / e) := fun h2 => hnot_g1_u2 (by
        obtain ⟨k, hk⟩ := h2
        have hu2e := Nat.mul_div_cancel' he_u2
        rw [hk] at hu2e
        exact ⟨k, by rw [hg1_2e]; linarith⟩)
      have hn2_s2 : ¬ (2 ∣ s₂ / e) := fun h2 => hnot_g1_s2 (by
        obtain ⟨k, hk⟩ := h2
        have hs2e := Nat.mul_div_cancel' he_s2
        rw [hk] at hs2e
        exact ⟨k, by rw [hg1_2e]; linarith⟩)
      have h_deficit_le_e : ∀ p : ℕ, p.Prime →
          u₁.factorization p + s₁.factorization p + u₂.factorization p + s₂.factorization p ≤
            b₁.factorization p + b₂.factorization p + w₂.factorization p + e.factorization p := by
        intro p hp
        have hb1_2g1 := fac_le_of_dvd_5 hb1_0 h2g1_b1 (p := p)
        have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
        have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
        have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
        have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
        have hw2_e : e.factorization p ≤ w₂.factorization p :=
          fac_le_of_dvd_5 hw2_0 (dvd_trans (Nat.gcd_dvd_right g₁ g₂) hg2_w2) (p := p)
        rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
        have h2e_eq : (2 * e).factorization p = (2 : ℕ).factorization p + e.factorization p := by
          rw [Nat.factorization_mul (by decide) he_p.ne', Finsupp.coe_add, Pi.add_apply]
        have h4e_eq : (2 * g₁).factorization p = 2 * (2 : ℕ).factorization p + e.factorization p := by
          rw [Nat.factorization_mul (by decide) hg1_p.ne', Finsupp.coe_add, Pi.add_apply, hg1_2e, h2e_eq]; omega
        have hu1s1_fac : u₁.factorization p + s₁.factorization p =
            3 * (2 : ℕ).factorization p + 2 * e.factorization p := by
          rcases hu1s1_pair with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;>
          · rw [hA, hB, hg1_2e, h2e_eq]
            have h4eq : (2 * (2 * e)).factorization p = 2 * (2 : ℕ).factorization p + e.factorization p := by
              rw [Nat.factorization_mul (by decide) (by omega), Finsupp.coe_add, Pi.add_apply, h2e_eq]; omega
            rw [h4eq]; omega
        by_cases hp2 : p = 2
        · subst hp2
          have h22 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
          have hu2_2 : u₂.factorization 2 = e.factorization 2 := by
            have hd := Nat.mul_div_cancel' he_u2
            have hq0 : (u₂ / e).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2_u2
            have hdiv_pos : u₂ / e ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact hu2_p.ne' hd.symm
            conv_lhs => rw [← hd, Nat.factorization_mul he_p.ne' hdiv_pos]
            simp [hq0]
          have hs2_2 : s₂.factorization 2 = e.factorization 2 := by
            have hd := Nat.mul_div_cancel' he_s2
            have hq0 : (s₂ / e).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2_s2
            have hdiv_pos : s₂ / e ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact hs2_p.ne' hd.symm
            conv_lhs => rw [← hd, Nat.factorization_mul he_p.ne' hdiv_pos]
            simp [hq0]
          rw [hg1_2e, h2e_eq, h22] at hb2_g1
          rw [h4e_eq, h22] at hb1_2g1
          rw [hu1s1_fac, h22, hu2_2, hs2_2]
          omega
        · have h20 : (2 : ℕ).factorization p = 0 :=
            Nat.factorization_eq_zero_of_not_dvd fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
          rw [hg1_2e, h2e_eq, h20, zero_add] at hb2_g1
          rw [h4e_eq, h20, mul_zero, zero_add] at hb1_2g1
          rw [hu1s1_fac, h20, mul_zero, zero_add]
          omega
      by_cases hsub_e : (consecInterval x M).filter (fun b => e ∣ b) ⊆ {b₁, b₂, b₃, w₂}
      · have he_b3 : e ∣ b₃ := dvd_b3_of_filter_subset_quad_5 he_p h4e hsub_e
        have hgcd_e_s3 : Nat.gcd e s₃ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
          (dvd_trans (Nat.gcd_dvd_left e s₃) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left u₁ s₁)))
          (dvd_trans (Nat.gcd_dvd_left e s₃) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right u₁ s₁)))
          (dvd_trans (Nat.gcd_dvd_left e s₃) he_u2)
          (dvd_trans (Nat.gcd_dvd_left e s₃) he_s2)
          (Nat.gcd_dvd_right e s₃)
        let B : Finset ℕ := {b₁, b₂, b₃, w₂}
        have hBI : B ⊆ consecInterval x M := fun b hb => by
          simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, le_trans (card_finset_le_four_5 b₁ b₂ b₃ w₂) (by omega),
          isCover_of_prime_factorization_5 hA0 hB0 fun p hp => ?_⟩
        rw [hsumA_eq p,
            Finset.sum_insert (by simp [hb12, hb13, hw2_b1.symm]),
            Finset.sum_insert (by simp [hb23, hw2_b2.symm]),
            Finset.sum_insert (by simp [hw2_b3.symm]), Finset.sum_singleton]
        have hdef := h_deficit_le_e p hp
        have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
        have hb3_e := fac_le_of_dvd_5 hb3_0 he_b3 (p := p)
        have hzero : min (e.factorization p) (s₃.factorization p) = 0 := by
          have hz : (Nat.gcd e s₃).factorization p = 0 := by rw [hgcd_e_s3, Nat.factorization_one, Finsupp.zero_apply]
          rwa [fac_gcd_eq_min_5 he_p.ne' hs3_p.ne'] at hz
        omega
      · obtain ⟨w₁, hw1_I, hw1_not⟩ := Finset.not_subset.mp hsub_e
        rw [Finset.mem_filter] at hw1_I
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw1_not
        rcases hw1_not with ⟨hw1_b1, hw1_b2, hw1_b3, hw1_w2⟩
        have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I.1).ne'
        let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂}
        have hBI : B ⊆ consecInterval x M := fun b hb => by
          simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> [exact hb₁_I; exact hb₂_I; exact hb₃_I; exact hw1_I.1; exact hw₂_I]
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, (card_finset_le_five_5 b₁ b₂ b₃ w₁ w₂).trans (by omega),
          isCover_of_prime_factorization_5 hA0 hB0 fun p hp => ?_⟩
        rw [hsumA_eq p,
            Finset.sum_insert (by simp [hb12, hb13, Ne.symm hw1_b1, hw2_b1.symm]),
            Finset.sum_insert (by simp [hb23, Ne.symm hw1_b2, hw2_b2.symm]),
            Finset.sum_insert (by simp [Ne.symm hw1_b3, hw2_b3.symm]),
            Finset.sum_insert (by simp [hw1_w2]), Finset.sum_singleton]
        have hdef := h_deficit_le_e p hp
        have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
        have hw1_e := fac_le_of_dvd_5 hw1_0 hw1_I.2 (p := p)
        omega
    · -- **Subcase A2.2b:** `3 * e ≤ g₁`, so `6 * e ≤ 2 * g₁ ≤ M`!
      have h3e_le : 3 * e ≤ g₁ := by
        rw [hq_e, mul_comm 3]; exact Nat.mul_le_mul_left e (by omega)
      have h6e : 6 * e ≤ M := by omega
      have h3_card : ({b₁, b₂, b₃} : Finset ℕ).card + 1 ≤ 4 := by
        have := card_finset_le_three_5 b₁ b₂ b₃; omega
      obtain ⟨w₁, hw1_I, hw1_not, he1_w1⟩ := exists_avoiding_multiple_in_consecInterval x M e₁
        {b₁, b₂, b₃} he1_p (le_trans (Nat.mul_le_mul_right e₁ h3_card) h4e1)
      obtain ⟨w₃, hw3_I, hw3_not, he2_w3⟩ := exists_avoiding_multiple_in_consecInterval x M e₂
        {b₁, b₂, b₃} he2_p (le_trans (Nat.mul_le_mul_right e₂ h3_card) h4e2)
      have hw1_b1 : w₁ ≠ b₁ := fun h => hw1_not (by simp [h])
      have hw1_b2 : w₁ ≠ b₂ := fun h => hw1_not (by simp [h])
      have hw1_b3 : w₁ ≠ b₃ := fun h => hw1_not (by simp [h])
      have hw3_b1 : w₃ ≠ b₁ := fun h => hw3_not (by simp [h])
      have hw3_b2 : w₃ ≠ b₂ := fun h => hw3_not (by simp [h])
      have hw3_b3 : w₃ ≠ b₃ := fun h => hw3_not (by simp [h])
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
      have try_five : ∀ v₁ v₂ : ℕ, v₁ ∈ consecInterval x M → v₂ ∈ consecInterval x M →
          v₁ ≠ b₁ → v₁ ≠ b₂ → v₁ ≠ b₃ → v₂ ≠ b₁ → v₂ ≠ b₂ → v₂ ≠ b₃ → v₁ ≠ v₂ →
          (∀ p : ℕ, u₁.factorization p + s₁.factorization p + u₂.factorization p +
              s₂.factorization p ≤
              b₁.factorization p + b₂.factorization p + v₁.factorization p + v₂.factorization p) →
          ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
        intro v₁ v₂ hv1I hv2I hv11 hv12 hv13 hv21 hv22 hv23 hv12_ne hcov4
        let B : Finset ℕ := {b₁, b₂, b₃, v₁, v₂}
        have hBI : B ⊆ consecInterval x M := fun b hb => by
          simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, (card_finset_le_five_5 b₁ b₂ b₃ v₁ v₂).trans (by omega),
          isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
        rw [hsumA_eq p,
            Finset.sum_insert (by simp [hb12, hb13, hv11.symm, hv21.symm]),
            Finset.sum_insert (by simp [hb23, hv12.symm, hv22.symm]),
            Finset.sum_insert (by simp [hv13.symm, hv23.symm]),
            Finset.sum_insert (by simp [hv12_ne]), Finset.sum_singleton]
        have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
        have := hcov4 p
        omega
      by_cases h123 : w₁ = w₂ ∧ w₂ = w₃
      · rcases h123 with ⟨rfl, rfl⟩
        have h4_card : ({b₁, b₂, b₃, w₁} : Finset ℕ).card + 1 ≤ 6 := by
          have := card_finset_le_four_5 b₁ b₂ b₃ w₁; omega
        obtain ⟨w₄, hw4_I, hw4_not, he_w4⟩ := exists_avoiding_multiple_in_consecInterval x M e
          {b₁, b₂, b₃, w₁} he_p (le_trans (Nat.mul_le_mul_right e h4_card) h6e)
        have hw4_b1 : w₄ ≠ b₁ := fun h => hw4_not (by simp [h])
        have hw4_b2 : w₄ ≠ b₂ := fun h => hw4_not (by simp [h])
        have hw4_b3 : w₄ ≠ b₃ := fun h => hw4_not (by simp [h])
        have hw4_w1 : w₄ ≠ w₁ := fun h => hw4_not (by simp [h])
        have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw4_I).ne'
        refine try_five w₁ w₄ hw1_I hw4_I hw1_b1 hw1_b2 hw1_b3 hw4_b1 hw4_b2 hw4_b3 hw4_w1.symm fun p => ?_
        have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
        have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
        have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
        have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
        have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
        have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
        have hw1_g2 := fac_le_of_dvd_5 hw1_0 hg2_w2 (p := p)
        have hw1_e2 := fac_le_of_dvd_5 hw1_0 he2_w3 (p := p)
        have hw4_e := fac_le_of_dvd_5 hw4_0 he_w4 (p := p)
        have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
          fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
        rw [hg1_eq] at hb2_g1
        rw [fac_gcd_eq_min_5 hg1_p.ne' hu2_p.ne', hg1_eq] at hw1_e1
        rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw1_g2
        rw [fac_gcd_eq_min_5 hg1_p.ne' hs2_p.ne', hg1_eq] at hw1_e2
        rw [fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne', hg1_eq, fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw4_e
        omega
      · by_cases hw12 : w₁ = w₂
        · have hw13 : w₁ ≠ w₃ := fun h => h123 ⟨hw12, hw12 ▸ h⟩
          have h5_card : ({b₁, b₂, b₃, w₁, w₃} : Finset ℕ).card + 1 ≤ 6 := by
            have := card_finset_le_five_5 b₁ b₂ b₃ w₁ w₃; omega
          obtain ⟨w₄, hw4_I, hw4_not, he_w4⟩ := exists_avoiding_multiple_in_consecInterval x M e
            {b₁, b₂, b₃, w₁, w₃} he_p (le_trans (Nat.mul_le_mul_right e h5_card) h6e)
          have hw4_b1 : w₄ ≠ b₁ := fun h => hw4_not (by simp [h])
          have hw4_b2 : w₄ ≠ b₂ := fun h => hw4_not (by simp [h])
          have hw4_b3 : w₄ ≠ b₃ := fun h => hw4_not (by simp [h])
          have hw4_w1 : w₄ ≠ w₁ := fun h => hw4_not (by simp [h])
          have hw4_w3 : w₄ ≠ w₃ := fun h => hw4_not (by simp [h])
          have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw4_I).ne'
          let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₃, w₄}
          have hBI : B ⊆ consecInterval x M := fun b hb => by
            simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
          have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
          refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₃ w₄,
            isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
          rw [hsumA_eq p,
              Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw3_b1.symm, hw4_b1.symm]),
              Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw3_b2.symm, hw4_b2.symm]),
              Finset.sum_insert (by simp [hw1_b3.symm, hw3_b3.symm, hw4_b3.symm]),
              Finset.sum_insert (by simp [hw13, hw4_w1.symm]),
              Finset.sum_insert (by simp [hw4_w3.symm]), Finset.sum_singleton]
          have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
          have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
          have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
          have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
          have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
          have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
          have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
          have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
          have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
          have hw4_e := fac_le_of_dvd_5 hw4_0 he_w4 (p := p)
          have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
            fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
          rw [hg1_eq] at hb2_g1
          rw [fac_gcd_eq_min_5 hg1_p.ne' hu2_p.ne', hg1_eq] at hw1_e1
          rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
          rw [fac_gcd_eq_min_5 hg1_p.ne' hs2_p.ne', hg1_eq] at hw3_e2
          rw [fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne', hg1_eq, fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw4_e
          rw [← hw12] at hw2_g2
          omega
        · by_cases hw13 : w₁ = w₃
          · have h5_card : ({b₁, b₂, b₃, w₁, w₂} : Finset ℕ).card + 1 ≤ 6 := by
              have := card_finset_le_five_5 b₁ b₂ b₃ w₁ w₂; omega
            obtain ⟨w₄, hw4_I, hw4_not, he_w4⟩ := exists_avoiding_multiple_in_consecInterval x M e
              {b₁, b₂, b₃, w₁, w₂} he_p (le_trans (Nat.mul_le_mul_right e h5_card) h6e)
            have hw4_b1 : w₄ ≠ b₁ := fun h => hw4_not (by simp [h])
            have hw4_b2 : w₄ ≠ b₂ := fun h => hw4_not (by simp [h])
            have hw4_b3 : w₄ ≠ b₃ := fun h => hw4_not (by simp [h])
            have hw4_w1 : w₄ ≠ w₁ := fun h => hw4_not (by simp [h])
            have hw4_w2 : w₄ ≠ w₂ := fun h => hw4_not (by simp [h])
            have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw4_I).ne'
            let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂, w₄}
            have hBI : B ⊆ consecInterval x M := fun b hb => by
              simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
            have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
            refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₂ w₄,
              isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
            rw [hsumA_eq p,
                Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw2_b1.symm, hw4_b1.symm]),
                Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw2_b2.symm, hw4_b2.symm]),
                Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm, hw4_b3.symm]),
                Finset.sum_insert (by simp [hw12, hw4_w1.symm]),
                Finset.sum_insert (by simp [hw4_w2.symm]), Finset.sum_singleton]
            have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
            have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
            have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
            have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
            have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
            have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
            have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
            have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
            have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
            have hw4_e := fac_le_of_dvd_5 hw4_0 he_w4 (p := p)
            have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
              fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
            rw [hg1_eq] at hb2_g1
            rw [fac_gcd_eq_min_5 hg1_p.ne' hu2_p.ne', hg1_eq] at hw1_e1
            rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
            rw [fac_gcd_eq_min_5 hg1_p.ne' hs2_p.ne', hg1_eq] at hw3_e2
            rw [fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne', hg1_eq, fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw4_e
            rw [← hw13] at hw3_e2
            omega
          · by_cases hw23 : w₂ = w₃
            · have h5_card : ({b₁, b₂, b₃, w₁, w₂} : Finset ℕ).card + 1 ≤ 6 := by
                have := card_finset_le_five_5 b₁ b₂ b₃ w₁ w₂; omega
              obtain ⟨w₄, hw4_I, hw4_not, he_w4⟩ := exists_avoiding_multiple_in_consecInterval x M e
                {b₁, b₂, b₃, w₁, w₂} he_p (le_trans (Nat.mul_le_mul_right e h5_card) h6e)
              have hw4_b1 : w₄ ≠ b₁ := fun h => hw4_not (by simp [h])
              have hw4_b2 : w₄ ≠ b₂ := fun h => hw4_not (by simp [h])
              have hw4_b3 : w₄ ≠ b₃ := fun h => hw4_not (by simp [h])
              have hw4_w1 : w₄ ≠ w₁ := fun h => hw4_not (by simp [h])
              have hw4_w2 : w₄ ≠ w₂ := fun h => hw4_not (by simp [h])
              have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw4_I).ne'
              let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂, w₄}
              have hBI : B ⊆ consecInterval x M := fun b hb => by
                simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
                rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
              have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
              refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₂ w₄,
                isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
              rw [hsumA_eq p,
                  Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw2_b1.symm, hw4_b1.symm]),
                  Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw2_b2.symm, hw4_b2.symm]),
                  Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm, hw4_b3.symm]),
                  Finset.sum_insert (by simp [hw12, hw4_w1.symm]),
                  Finset.sum_insert (by simp [hw4_w2.symm]), Finset.sum_singleton]
              have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
              have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
              have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
              have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
              have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
              have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
              have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
              have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
              have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
              have hw4_e := fac_le_of_dvd_5 hw4_0 he_w4 (p := p)
              have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
                fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
              rw [hg1_eq] at hb2_g1
              rw [fac_gcd_eq_min_5 hg1_p.ne' hu2_p.ne', hg1_eq] at hw1_e1
              rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
              rw [fac_gcd_eq_min_5 hg1_p.ne' hs2_p.ne', hg1_eq] at hw3_e2
              rw [fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne', hg1_eq, fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw4_e
              rw [← hw23] at hw3_e2
              omega
            · let B : Finset ℕ := {b₁, b₂, b₃, w₁, w₂, w₃}
              have hBI : B ⊆ consecInterval x M := fun b hb => by
                simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
                rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
              have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
              refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₁ w₂ w₃,
                isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
              rw [hsumA_eq p,
                  Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw2_b1.symm, hw3_b1.symm]),
                  Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw2_b2.symm, hw3_b2.symm]),
                  Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm, hw3_b3.symm]),
                  Finset.sum_insert (by simp [hw12, hw13]),
                  Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
              have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
              have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
              have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
              have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
              have hb2_g1 := fac_le_of_dvd_5 hb2_0 hg1_b2 (p := p)
              have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
              have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
              have hw2_g2 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
              have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
              have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
                fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
              rw [hg1_eq] at hb2_g1
              rw [fac_gcd_eq_min_5 hg1_p.ne' hu2_p.ne', hg1_eq] at hw1_e1
              rw [fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'] at hw2_g2
              rw [fac_gcd_eq_min_5 hg1_p.ne' hs2_p.ne', hg1_eq] at hw3_e2
              omega

private lemma a32_arith_5 {x1 y1 x2 y2 s c1 c2 b3 v1 v2 : ℕ}
    (hx1c : x1 ≤ c1) (hy1c : y1 ≤ c1)
    (hx2c : x2 ≤ c2) (hy2c : y2 ≤ c2) (hm1c : min x1 y1 ≤ c2)
    (hsb3 : s ≤ b3) (hm2b : min x2 y2 ≤ b3)
    (h1 : min (min x1 y1) x2 ≤ v1) (h2 : min (min x1 y1) y2 ≤ v2)
    (hd : min (min x2 y2) s ≤ v1)
    (hor : min (min x2 y2) s = 0 ∨ (min (min x1 y1) x2 = 0 ∧ min (min x1 y1) y2 = 0)) :
    x1 + y1 + x2 + y2 + s ≤ c1 + (c2 + (b3 + (v1 + v2))) := by
  rcases Nat.le_total x1 y1 with h1le | h1le <;> rcases Nat.le_total x2 y2 with h2le | h2le
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega

private lemma a32_arith_5b {x1 y1 x2 y2 s c1 c2 b3 w1 w2 : ℕ}
    (hx1c : x1 ≤ c1) (hy1c : y1 ≤ c1)
    (hx2c : x2 ≤ c2) (hy2c : y2 ≤ c2) (hm1c : min x1 y1 ≤ c2)
    (hsb3 : s ≤ b3) (hm2b : min x2 y2 ≤ b3)
    (h1 : min (min x1 y1) x2 ≤ w1) (h2 : min (min x1 y1) y2 ≤ w2)
    (hd : min (min x2 y2) s ≤ w2)
    (hor : min (min x2 y2) s = 0 ∨ (min (min x1 y1) x2 = 0 ∧ min (min x1 y1) y2 = 0)) :
    x1 + y1 + x2 + y2 + s ≤ c1 + (c2 + (b3 + (w1 + w2))) := by
  rcases Nat.le_total x1 y1 with h1le | h1le <;> rcases Nat.le_total x2 y2 with h2le | h2le
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega

private lemma a32_arith_6 {x1 y1 x2 y2 s c1 c2 b3 w1 w2 w3 : ℕ}
    (hx1c : x1 ≤ c1) (hy1c : y1 ≤ c1)
    (hx2c : x2 ≤ c2) (hy2c : y2 ≤ c2) (hm1c : min x1 y1 ≤ c2)
    (hsb3 : s ≤ b3) (hm2b : min x2 y2 ≤ b3)
    (h1 : min (min x1 y1) x2 ≤ w1) (h2 : min (min x1 y1) y2 ≤ w3)
    (hd : min (min x2 y2) s ≤ w2)
    (hor : min (min x2 y2) s = 0 ∨ (min (min x1 y1) x2 = 0 ∧ min (min x1 y1) y2 = 0)) :
    x1 + y1 + x2 + y2 + s ≤ c1 + (c2 + (b3 + (w1 + (w2 + w3)))) := by
  rcases Nat.le_total x1 y1 with h1le | h1le <;> rcases Nat.le_total x2 y2 with h2le | h2le
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_left h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_left h2le] at hm2b hd hor; omega
  · rw [min_eq_right h1le] at hm1c h1 h2 hor; rw [min_eq_right h2le] at hm2b hd hor; omega

private lemma cover_six_of_r3_two_slots_A3_one_not_b3
    {A : Finset ℕ} {x M x₁ y₁ x₂ y₂ s₃ c₁ c₂ b₃ : ℕ}
    (hA' : A = {x₁, y₁, x₂, y₂, s₃})
    (hx1y1 : x₁ ≠ y₁) (hx12 : x₁ ≠ x₂) (hx1y2 : x₁ ≠ y₂) (hx1s3 : x₁ ≠ s₃)
    (hy12 : y₁ ≠ x₂) (hy1y2 : y₁ ≠ y₂) (hy1s3 : y₁ ≠ s₃)
    (hx2y2 : x₂ ≠ y₂) (hx2s3 : x₂ ≠ s₃) (hy2s3 : y₂ ≠ s₃)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hc1_I : c₁ ∈ consecInterval x M) (hc2_I : c₂ ∈ consecInterval x M) (hb₃_I : b₃ ∈ consecInterval x M)
    (hc12 : c₁ ≠ c₂) (hc1b3 : c₁ ≠ b₃) (hc2b3 : c₂ ≠ b₃)
    (hx1_c1 : x₁ ∣ c₁) (hy1_c1 : y₁ ∣ c₁) (hx2_c2 : x₂ ∣ c₂) (hy2_c2 : y₂ ∣ c₂) (hs3_b3 : s₃ ∣ b₃)
    (hsub1 : (consecInterval x M).filter (fun b => Nat.gcd x₁ y₁ ∣ b) ⊆ {c₁, c₂, b₃})
    (hsub2 : (consecInterval x M).filter (fun b => Nat.gcd x₂ y₂ ∣ b) ⊆ {c₁, c₂, b₃})
    (hnd1 : ¬ (Nat.gcd x₁ y₁ ∣ b₃)) (hb3_2 : Nat.gcd x₂ y₂ ∣ b₃) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hx1p : 0 < x₁ := hA_pos x₁ (by rw [hA']; simp)
  have hy1p : 0 < y₁ := hA_pos y₁ (by rw [hA']; simp)
  have hx2p : 0 < x₂ := hA_pos x₂ (by rw [hA']; simp)
  have hy2p : 0 < y₂ := hA_pos y₂ (by rw [hA']; simp)
  have hs3_p : 0 < s₃ := hA_pos s₃ (by rw [hA']; simp)
  have hx1M : x₁ ≤ M := hA_le x₁ (by rw [hA']; simp)
  have hy1M : y₁ ≤ M := hA_le y₁ (by rw [hA']; simp)
  have hx2M : x₂ ≤ M := hA_le x₂ (by rw [hA']; simp)
  have hy2M : y₂ ≤ M := hA_le y₂ (by rw [hA']; simp)
  have hs3_M : s₃ ≤ M := hA_le s₃ (by rw [hA']; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hc1_0 : c₁ ≠ 0 := (pos_of_mem_consecInterval hc1_I).ne'
  have hc2_0 : c₂ ≠ 0 := (pos_of_mem_consecInterval hc2_I).ne'
  have hb3_0 : b₃ ≠ 0 := (pos_of_mem_consecInterval hb₃_I).ne'
  set G₁ := Nat.gcd x₁ y₁
  set G₂ := Nat.gcd x₂ y₂
  have hG1_p : 0 < G₁ := Nat.gcd_pos_of_pos_left y₁ hx1p
  have hG2_p : 0 < G₂ := Nat.gcd_pos_of_pos_left y₂ hx2p
  have h2G1 : 2 * G₁ ≤ M := two_mul_gcd_le_of_distinct_5 hx1p hy1p hx1M hy1M hx1y1
  have hG1_c1 : G₁ ∣ c₁ := dvd_trans (Nat.gcd_dvd_left x₁ y₁) hx1_c1
  have hG2_c2 : G₂ ∣ c₂ := dvd_trans (Nat.gcd_dvd_left x₂ y₂) hx2_c2
  have hsub1_pair : (consecInterval x M).filter (fun b => G₁ ∣ b) ⊆ {c₁, c₂} := fun b hb => by
    have hmem := hsub1 hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with rfl | rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl; exact absurd (Finset.mem_filter.mp hb).2 hnd1]
  obtain ⟨_, hG1_c2, hM3G1⟩ := dvd_pair_of_filter_subset_pair_5 hG1_p h2G1 hc12 hsub1_pair
  have hpair1 : (x₁ = G₁ ∧ y₁ = 2 * G₁) ∨ (y₁ = G₁ ∧ x₁ = 2 * G₁) := by
    rcases lt_or_gt_of_ne hx1y1 with hlt | hgt
    · left; exact eq_pair_of_two_dvd_lt_three_mul_5 hG1_p hx1p hlt hy1M hM3G1
        (Nat.gcd_dvd_left x₁ y₁) (Nat.gcd_dvd_right x₁ y₁)
    · right; exact eq_pair_of_two_dvd_lt_three_mul_5 hG1_p hy1p hgt hx1M hM3G1
        (Nat.gcd_dvd_right x₁ y₁) (Nat.gcd_dvd_left x₁ y₁)
  have h2G1_c1 : 2 * G₁ ∣ c₁ := by rcases hpair1 with ⟨_, hE⟩ | ⟨_, hE⟩ <;> [exact hE ▸ hy1_c1; exact hE ▸ hx1_c1]
  set d₂ := Nat.gcd G₂ s₃
  have hd2_p : 0 < d₂ := Nat.gcd_pos_of_pos_left s₃ hG2_p
  have h3d2 : 3 * d₂ ≤ M := by
    have hT : ({x₂, y₂, s₃} : Finset ℕ).card * d₂ ≤ M :=
      card_mul_le_of_forall_dvd hd2_p fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with ha_eq | ha_eq | ha_eq
        · rw [ha_eq]; exact ⟨hx2p, hx2M, dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_left x₂ y₂)⟩
        · rw [ha_eq]; exact ⟨hy2p, hy2M, dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_right x₂ y₂)⟩
        · rw [ha_eq]; exact ⟨hs3_p, hs3_M, Nat.gcd_dvd_right G₂ s₃⟩
    have hc3 : ({x₂, y₂, s₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hx2y2, hx2s3]),
          Finset.card_insert_of_notMem (by simp [hy2s3]), Finset.card_singleton]
    rwa [hc3] at hT
  have hnot_d2 : ¬ ((consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {c₁, c₂, b₃}) := by
    intro hs
    obtain ⟨hd2_c1, hd2_c2, _, hM4d2⟩ := dvd_triple_of_filter_subset_triple_5 hd2_p h3d2 hc12 hc1b3 hc2b3 hs
    have hsub_d2_pair : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {c₁, c₂, b₃} := hs
    have hspan_d2 := (span_three_props_5 hd2_p hc1_I hc2_I hb₃_I hc12 hc1b3 hc2b3 hd2_c1 hd2_c2
      (dvd_trans (Nat.gcd_dvd_left G₂ s₃) hb3_2) hsub_d2_pair).2
    have hsub_perm : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {b₃, c₁, c₂} := by
      intro z hz; have := hs hz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl <;> simp
    have hG1_dvd_2d2 : G₁ ∣ 2 * d₂ :=
      (span_three_props_5 hd2_p hb₃_I hc1_I hc2_I hc1b3.symm hc2b3.symm hc12
        (dvd_trans (Nat.gcd_dvd_left G₂ s₃) hb3_2) hd2_c1 hd2_c2 hsub_perm).2 G₁ hG1_c1 hG1_c2
    have hcop : Nat.Coprime G₁ d₂ := by
      have hg1 := gcd_five_eq_one_5 hA' hAgcd
        (dvd_trans (Nat.gcd_dvd_left G₁ d₂) (Nat.gcd_dvd_left x₁ y₁))
        (dvd_trans (Nat.gcd_dvd_left G₁ d₂) (Nat.gcd_dvd_right x₁ y₁))
        (dvd_trans (Nat.gcd_dvd_right G₁ d₂) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_left x₂ y₂)))
        (dvd_trans (Nat.gcd_dvd_right G₁ d₂) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_right x₂ y₂)))
        (dvd_trans (Nat.gcd_dvd_right G₁ d₂) (Nat.gcd_dvd_right G₂ s₃))
      exact hg1
    have hG1_dvd2 : G₁ ∣ 2 := hcop.dvd_of_dvd_mul_right hG1_dvd_2d2
    have hG1_le2 : G₁ ≤ 2 := Nat.le_of_dvd (by decide) hG1_dvd2
    omega
  obtain ⟨w₂, hw2_I, hw2_c1, hw2_c2, hw2_b3, hd2_w2⟩ := exists_avoiding_of_not_subset_triple_5 hnot_d2
  have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw2_I).ne'
  have hnot_G1_x2 : ¬ (G₁ ∣ x₂) := fun hd => by
    obtain ⟨q, hq⟩ := hd
    have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq; omega
    have hq_lt3 : q < 3 := by by_contra h3; have := Nat.mul_le_mul_left G₁ (by omega : 3 ≤ q); omega
    rcases (by omega : q = 1 ∨ q = 2) with rfl | rfl
    · rcases hpair1 with ⟨hE, _⟩ | ⟨hE, _⟩ <;> [exact hx12 (by rw [hE, hq, mul_one]); exact hy12 (by rw [hE, hq, mul_one])]
    · rcases hpair1 with ⟨_, hE⟩ | ⟨_, hE⟩ <;> [exact hy12 (by rw [hE, hq, mul_comm 2 G₁]); exact hx12 (by rw [hE, hq, mul_comm 2 G₁])]
  have hnot_G1_y2 : ¬ (G₁ ∣ y₂) := fun hd => by
    obtain ⟨q, hq⟩ := hd
    have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq; omega
    have hq_lt3 : q < 3 := by by_contra h3; have := Nat.mul_le_mul_left G₁ (by omega : 3 ≤ q); omega
    rcases (by omega : q = 1 ∨ q = 2) with rfl | rfl
    · rcases hpair1 with ⟨hE, _⟩ | ⟨hE, _⟩ <;> [exact hx1y2 (by rw [hE, hq, mul_one]); exact hy1y2 (by rw [hE, hq, mul_one])]
    · rcases hpair1 with ⟨_, hE⟩ | ⟨_, hE⟩ <;> [exact hy1y2 (by rw [hE, hq, mul_comm 2 G₁]); exact hx1y2 (by rw [hE, hq, mul_comm 2 G₁])]
  have hnot_G1_G2 : ¬ (G₁ ∣ G₂) := fun h => hnot_G1_x2 (dvd_trans h (Nat.gcd_dvd_left x₂ y₂))
  let e₁ := Nat.gcd G₁ x₂
  let e₂ := Nat.gcd G₁ y₂
  let e := Nat.gcd G₁ G₂
  have he1_p : 0 < e₁ := Nat.gcd_pos_of_pos_left x₂ hG1_p
  have he2_p : 0 < e₂ := Nat.gcd_pos_of_pos_left y₂ hG1_p
  have he_p : 0 < e := Nat.gcd_pos_of_pos_left G₂ hG1_p
  have h2e1_le : 2 * e₁ ≤ G₁ := by
    obtain ⟨q, hq⟩ := Nat.gcd_dvd_left G₁ x₂
    have hq2 : 2 ≤ q := by by_contra hlt; rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> [simp at hq; rw [mul_one] at hq] <;> [omega; exact hnot_G1_x2 (hq ▸ Nat.gcd_dvd_right G₁ x₂)]
    rw [hq, mul_comm 2]; exact Nat.mul_le_mul_left e₁ hq2
  have h2e2_le : 2 * e₂ ≤ G₁ := by
    obtain ⟨q, hq⟩ := Nat.gcd_dvd_left G₁ y₂
    have hq2 : 2 ≤ q := by by_contra hlt; rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> [simp at hq; rw [mul_one] at hq] <;> [omega; exact hnot_G1_y2 (hq ▸ Nat.gcd_dvd_right G₁ y₂)]
    rw [hq, mul_comm 2]; exact Nat.mul_le_mul_left e₂ hq2
  have h4e1 : 4 * e₁ ≤ M := by omega
  have h4e2 : 4 * e₂ ≤ M := by omega
  obtain ⟨q_e, hq_e⟩ := Nat.gcd_dvd_left G₁ G₂
  have hq_e_ge2 : 2 ≤ q_e := by
    by_contra hlt; rcases (by omega : q_e = 0 ∨ q_e = 1) with rfl | rfl <;> [simp at hq_e; rw [mul_one] at hq_e] <;> [omega; exact hnot_G1_G2 (hq_e ▸ Nat.gcd_dvd_right G₁ G₂)]
  have hsum' : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      x₁.factorization p + y₁.factorization p + x₂.factorization p +
        y₂.factorization p + s₃.factorization p := fun p => by
    rw [hA', Finset.sum_insert (by simp [hx1y1, hx12, hx1y2, hx1s3]),
        Finset.sum_insert (by simp [hy12, hy1y2, hy1s3]),
        Finset.sum_insert (by simp [hx2y2, hx2s3]),
        Finset.sum_insert (by simp [hy2s3]), Finset.sum_singleton]
    ring
  by_cases hqe2 : q_e = 2
  · have hG1_2e : G₁ = 2 * e := by rw [hq_e, hqe2, mul_comm]
    have h4e : 4 * e ≤ M := by omega
    have h3_card : ({c₁, c₂, b₃} : Finset ℕ).card + 1 ≤ 4 := by
      have := card_finset_le_three_5 c₁ c₂ b₃; omega
    obtain ⟨w₁, hw1_I, hw1_not, he_w1⟩ := exists_avoiding_multiple_in_consecInterval x M e
      {c₁, c₂, b₃} he_p (le_trans (Nat.mul_le_mul_right e h3_card) h4e)
    have hw1_c1 : w₁ ≠ c₁ := fun h => hw1_not (by simp [h])
    have hw1_c2 : w₁ ≠ c₂ := fun h => hw1_not (by simp [h])
    have hw1_b3 : w₁ ≠ b₃ := fun h => hw1_not (by simp [h])
    have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
    have he_x2 : e ∣ x₂ := dvd_trans (Nat.gcd_dvd_right G₁ G₂) (Nat.gcd_dvd_left x₂ y₂)
    have he_y2 : e ∣ y₂ := dvd_trans (Nat.gcd_dvd_right G₁ G₂) (Nat.gcd_dvd_right x₂ y₂)
    have hn2_x2 : ¬ (2 ∣ x₂ / e) := fun h2 => hnot_G1_x2 (by
      obtain ⟨k, hk⟩ := h2; have h := Nat.mul_div_cancel' he_x2; rw [hk] at h
      exact ⟨k, by rw [hG1_2e]; linarith⟩)
    have hn2_y2 : ¬ (2 ∣ y₂ / e) := fun h2 => hnot_G1_y2 (by
      obtain ⟨k, hk⟩ := h2; have h := Nat.mul_div_cancel' he_y2; rw [hk] at h
      exact ⟨k, by rw [hG1_2e]; linarith⟩)
    have hgcd_e_s3 : Nat.gcd e s₃ = 1 := gcd_five_eq_one_5 hA' hAgcd
      (dvd_trans (Nat.gcd_dvd_left e s₃) (dvd_trans (Nat.gcd_dvd_left G₁ G₂) (Nat.gcd_dvd_left x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_left e s₃) (dvd_trans (Nat.gcd_dvd_left G₁ G₂) (Nat.gcd_dvd_right x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_left e s₃) he_x2)
      (dvd_trans (Nat.gcd_dvd_left e s₃) he_y2)
      (Nat.gcd_dvd_right e s₃)
    let B : Finset ℕ := {c₁, c₂, b₃, w₁, w₂}
    have hBI : B ⊆ consecInterval x M := fun b hb => by
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, (card_finset_le_five_5 c₁ c₂ b₃ w₁ w₂).trans (by omega),
      isCover_of_prime_factorization_5 hA0 hB0 fun p hp => ?_⟩
    rw [hsum' p]
    have hle4 : ∀ w ∈ B, w ≠ c₁ → w ≠ c₂ → w ≠ b₃ →
        c₁.factorization p + c₂.factorization p + b₃.factorization p + w.factorization p ≤
          ∑ b ∈ B, b.factorization p := fun w hwB hwc1 hwc2 hwb3 => by
      have hsub4 : ({c₁, c₂, b₃, w} : Finset ℕ) ⊆ B := fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> simp [B, hwB]
      have := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
      rw [Finset.sum_insert (by simp [hc12, hc1b3, hwc1.symm]),
          Finset.sum_insert (by simp [hc2b3, hwc2.symm]),
          Finset.sum_insert (by simp [hwb3.symm]), Finset.sum_singleton] at this
      omega
    have h4_1 := hle4 w₁ (by simp [B]) hw1_c1 hw1_c2 hw1_b3
    have h4_2 := hle4 w₂ (by simp [B]) hw2_c1 hw2_c2 hw2_b3
    have hc1_2G1 := fac_le_of_dvd_5 hc1_0 h2G1_c1 (p := p)
    have hc2_x2 := fac_le_of_dvd_5 hc2_0 hx2_c2 (p := p)
    have hc2_y2 := fac_le_of_dvd_5 hc2_0 hy2_c2 (p := p)
    have hc2_G1 := fac_le_of_dvd_5 hc2_0 hG1_c2 (p := p)
    have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
    have hb3_G2 := fac_le_of_dvd_5 hb3_0 hb3_2 (p := p)
    have hw1_e := fac_le_of_dvd_5 hw1_0 he_w1 (p := p)
    have hw2_d2 := fac_le_of_dvd_5 hw2_0 hd2_w2 (p := p)
    have hG2_eq : G₂.factorization p = min (x₂.factorization p) (y₂.factorization p) :=
      fac_gcd_eq_min_5 hx2p.ne' hy2p.ne'
    have hd2_eq : d₂.factorization p = min (G₂.factorization p) (s₃.factorization p) :=
      fac_gcd_eq_min_5 hG2_p.ne' hs3_p.ne'
    rw [hd2_eq, hG2_eq] at hw2_d2
    rw [hG2_eq] at hb3_G2
    have hzero : min (e.factorization p) (s₃.factorization p) = 0 := by
      have hz : (Nat.gcd e s₃).factorization p = 0 := by rw [hgcd_e_s3, Nat.factorization_one, Finsupp.zero_apply]
      rwa [fac_gcd_eq_min_5 he_p.ne' hs3_p.ne'] at hz
    have h2e_eq : (2 * e).factorization p = (2 : ℕ).factorization p + e.factorization p := by
      rw [Nat.factorization_mul (by decide) he_p.ne', Finsupp.coe_add, Pi.add_apply]
    have h4e_eq : (2 * G₁).factorization p = 2 * (2 : ℕ).factorization p + e.factorization p := by
      rw [Nat.factorization_mul (by decide) hG1_p.ne', Finsupp.coe_add, Pi.add_apply, hG1_2e, h2e_eq]; omega
    have hxy1_fac : x₁.factorization p + y₁.factorization p =
        3 * (2 : ℕ).factorization p + 2 * e.factorization p := by
      rcases hpair1 with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;>
      · rw [hA, hB, hG1_2e, h2e_eq]
        have h4eq : (2 * (2 * e)).factorization p = 2 * (2 : ℕ).factorization p + e.factorization p := by
          rw [Nat.factorization_mul (by decide) (by omega), Finsupp.coe_add, Pi.add_apply, h2e_eq]; omega
        rw [h4eq]; omega
    by_cases hp2 : p = 2
    · subst hp2
      have h22 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
      have hx2_2 : x₂.factorization 2 = e.factorization 2 := by
        have hd := Nat.mul_div_cancel' he_x2
        have hq0 : (x₂ / e).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2_x2
        have hdp : x₂ / e ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact hx2p.ne' hd.symm
        conv_lhs => rw [← hd, Nat.factorization_mul he_p.ne' hdp]
        simp [hq0]
      have hy2_2 : y₂.factorization 2 = e.factorization 2 := by
        have hd := Nat.mul_div_cancel' he_y2
        have hq0 : (y₂ / e).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2_y2
        have hdp : y₂ / e ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact hy2p.ne' hd.symm
        conv_lhs => rw [← hd, Nat.factorization_mul he_p.ne' hdp]
        simp [hq0]
      rw [hG1_2e, h2e_eq, h22] at hc2_G1
      rw [h4e_eq, h22] at hc1_2G1
      rw [hxy1_fac, h22, hx2_2, hy2_2]
      omega
    · have h20 : (2 : ℕ).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      have hc2_e : e.factorization p ≤ c₂.factorization p := by
        rwa [hG1_2e, h2e_eq, h20, zero_add] at hc2_G1
      rw [h4e_eq, h20, mul_zero, zero_add] at hc1_2G1
      rw [hxy1_fac, h20, mul_zero, zero_add]
      have he_x2p := fac_le_of_dvd_5 hx2p.ne' he_x2 (p := p)
      have he_y2p := fac_le_of_dvd_5 hy2p.ne' he_y2 (p := p)
      omega
  · have h3e_le : 3 * e ≤ G₁ := by rw [hq_e, mul_comm 3]; exact Nat.mul_le_mul_left e (by omega)
    have h6e : 6 * e ≤ M := by omega
    have h3_card : ({c₁, c₂, b₃} : Finset ℕ).card + 1 ≤ 4 := by
      have := card_finset_le_three_5 c₁ c₂ b₃; omega
    obtain ⟨w₁, hw1_I, hw1_not, he1_w1⟩ := exists_avoiding_multiple_in_consecInterval x M e₁
      {c₁, c₂, b₃} he1_p (le_trans (Nat.mul_le_mul_right e₁ h3_card) h4e1)
    obtain ⟨w₃, hw3_I, hw3_not, he2_w3⟩ := exists_avoiding_multiple_in_consecInterval x M e₂
      {c₁, c₂, b₃} he2_p (le_trans (Nat.mul_le_mul_right e₂ h3_card) h4e2)
    have hw1_c1 : w₁ ≠ c₁ := fun h => hw1_not (by simp [h])
    have hw1_c2 : w₁ ≠ c₂ := fun h => hw1_not (by simp [h])
    have hw1_b3 : w₁ ≠ b₃ := fun h => hw1_not (by simp [h])
    have hw3_c1 : w₃ ≠ c₁ := fun h => hw3_not (by simp [h])
    have hw3_c2 : w₃ ≠ c₂ := fun h => hw3_not (by simp [h])
    have hw3_b3 : w₃ ≠ b₃ := fun h => hw3_not (by simp [h])
    have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
    have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
    have hgcd_1 : Nat.gcd d₂ e₁ = 1 := gcd_five_eq_one_5 hA' hAgcd
      (dvd_trans (Nat.gcd_dvd_right d₂ e₁) (dvd_trans (Nat.gcd_dvd_left G₁ x₂) (Nat.gcd_dvd_left x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_right d₂ e₁) (dvd_trans (Nat.gcd_dvd_left G₁ x₂) (Nat.gcd_dvd_right x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_right d₂ e₁) (Nat.gcd_dvd_right G₁ x₂))
      (dvd_trans (Nat.gcd_dvd_left d₂ e₁) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_right x₂ y₂)))
      (dvd_trans (Nat.gcd_dvd_left d₂ e₁) (Nat.gcd_dvd_right G₂ s₃))
    have hgcd_2 : Nat.gcd d₂ e₂ = 1 := gcd_five_eq_one_5 hA' hAgcd
      (dvd_trans (Nat.gcd_dvd_right d₂ e₂) (dvd_trans (Nat.gcd_dvd_left G₁ y₂) (Nat.gcd_dvd_left x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_right d₂ e₂) (dvd_trans (Nat.gcd_dvd_left G₁ y₂) (Nat.gcd_dvd_right x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_left d₂ e₂) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_left x₂ y₂)))
      (dvd_trans (Nat.gcd_dvd_right d₂ e₂) (Nat.gcd_dvd_right G₁ y₂))
      (dvd_trans (Nat.gcd_dvd_left d₂ e₂) (Nat.gcd_dvd_right G₂ s₃))
    have hgcd_3 : Nat.gcd d₂ e = 1 := gcd_five_eq_one_5 hA' hAgcd
      (dvd_trans (Nat.gcd_dvd_right d₂ e) (dvd_trans (Nat.gcd_dvd_left G₁ G₂) (Nat.gcd_dvd_left x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_right d₂ e) (dvd_trans (Nat.gcd_dvd_left G₁ G₂) (Nat.gcd_dvd_right x₁ y₁)))
      (dvd_trans (Nat.gcd_dvd_left d₂ e) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_left x₂ y₂)))
      (dvd_trans (Nat.gcd_dvd_left d₂ e) (dvd_trans (Nat.gcd_dvd_left G₂ s₃) (Nat.gcd_dvd_right x₂ y₂)))
      (dvd_trans (Nat.gcd_dvd_left d₂ e) (Nat.gcd_dvd_right G₂ s₃))
    by_cases hw13 : w₁ = w₃
    · have h5_card : ({c₁, c₂, b₃, w₁, w₂} : Finset ℕ).card + 1 ≤ 6 := by
        have := card_finset_le_five_5 c₁ c₂ b₃ w₁ w₂; omega
      obtain ⟨w₄, hw4_I, hw4_not, he_w4⟩ := exists_avoiding_multiple_in_consecInterval x M e
        {c₁, c₂, b₃, w₁, w₂} he_p (le_trans (Nat.mul_le_mul_right e h5_card) h6e)
      have hw4_c1 : w₄ ≠ c₁ := fun h => hw4_not (by simp [h])
      have hw4_c2 : w₄ ≠ c₂ := fun h => hw4_not (by simp [h])
      have hw4_b3 : w₄ ≠ b₃ := fun h => hw4_not (by simp [h])
      have hw4_w1 : w₄ ≠ w₁ := fun h => hw4_not (by simp [h])
      have hw4_w2 : w₄ ≠ w₂ := fun h => hw4_not (by simp [h])
      have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw4_I).ne'
      let B : Finset ℕ := {c₁, c₂, b₃, w₁, w₂, w₄}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 c₁ c₂ b₃ w₁ w₂ w₄,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsum' p]
      have hz1 : (Nat.gcd d₂ e₁).factorization p = 0 := by rw [hgcd_1, Nat.factorization_one, Finsupp.zero_apply]
      have hz2 : (Nat.gcd d₂ e₂).factorization p = 0 := by rw [hgcd_2, Nat.factorization_one, Finsupp.zero_apply]
      have hz3 : (Nat.gcd d₂ e).factorization p = 0 := by rw [hgcd_3, Nat.factorization_one, Finsupp.zero_apply]
      rw [fac_gcd_eq_min_5 hd2_p.ne' he1_p.ne'] at hz1
      rw [fac_gcd_eq_min_5 hd2_p.ne' he2_p.ne'] at hz2
      rw [fac_gcd_eq_min_5 hd2_p.ne' he_p.ne'] at hz3
      have hc1_x1 := fac_le_of_dvd_5 hc1_0 hx1_c1 (p := p)
      have hc1_y1 := fac_le_of_dvd_5 hc1_0 hy1_c1 (p := p)
      have hc2_x2 := fac_le_of_dvd_5 hc2_0 hx2_c2 (p := p)
      have hc2_y2 := fac_le_of_dvd_5 hc2_0 hy2_c2 (p := p)
      have hc2_G1 := fac_le_of_dvd_5 hc2_0 hG1_c2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hb3_G2 := fac_le_of_dvd_5 hb3_0 hb3_2 (p := p)
      have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
      have hw1_e2 := fac_le_of_dvd_5 hw1_0 (hw13 ▸ he2_w3) (p := p)
      have hw2_d2 := fac_le_of_dvd_5 hw2_0 hd2_w2 (p := p)
      have hw4_e := fac_le_of_dvd_5 hw4_0 he_w4 (p := p)
      have hG1_eq : G₁.factorization p = min (x₁.factorization p) (y₁.factorization p) :=
        fac_gcd_eq_min_5 hx1p.ne' hy1p.ne'
      have hG2_eq : G₂.factorization p = min (x₂.factorization p) (y₂.factorization p) :=
        fac_gcd_eq_min_5 hx2p.ne' hy2p.ne'
      rw [hG1_eq] at hc2_G1
      rw [hG2_eq] at hb3_G2
      rw [fac_gcd_eq_min_5 hG1_p.ne' hx2p.ne', hG1_eq] at hw1_e1 hz1
      rw [fac_gcd_eq_min_5 hG1_p.ne' hy2p.ne', hG1_eq] at hw1_e2 hz2
      rw [fac_gcd_eq_min_5 hG2_p.ne' hs3_p.ne', hG2_eq] at hw2_d2 hz1 hz2 hz3
      rw [fac_gcd_eq_min_5 hG1_p.ne' hG2_p.ne', hG1_eq, hG2_eq] at hw4_e hz3
      by_cases hw12 : w₁ = w₂
      · have hsub5 : ({c₁, c₂, b₃, w₁, w₄} : Finset ℕ) ⊆ B := fun b hb => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hc12, hc1b3, hw1_c1.symm, hw4_c1.symm]),
            Finset.sum_insert (by simp [hc2b3, hw1_c2.symm, hw4_c2.symm]),
            Finset.sum_insert (by simp [hw1_b3.symm, hw4_b3.symm]),
            Finset.sum_insert (by simp [hw4_w1.symm]), Finset.sum_singleton] at hleB
        rw [← hw12] at hw2_d2
        omega
      · dsimp [B]
        rw [Finset.sum_insert (by simp [hc12, hc1b3, hw1_c1.symm, hw2_c1.symm, hw4_c1.symm]),
            Finset.sum_insert (by simp [hc2b3, hw1_c2.symm, hw2_c2.symm, hw4_c2.symm]),
            Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm, hw4_b3.symm]),
            Finset.sum_insert (by simp [hw12, hw4_w1.symm]),
            Finset.sum_insert (by simp [hw4_w2.symm]), Finset.sum_singleton]
        omega
    · let B : Finset ℕ := {c₁, c₂, b₃, w₁, w₂, w₃}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 c₁ c₂ b₃ w₁ w₂ w₃,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsum' p]
      have hz1 : (Nat.gcd d₂ e₁).factorization p = 0 := by rw [hgcd_1, Nat.factorization_one, Finsupp.zero_apply]
      have hz2 : (Nat.gcd d₂ e₂).factorization p = 0 := by rw [hgcd_2, Nat.factorization_one, Finsupp.zero_apply]
      rw [fac_gcd_eq_min_5 hd2_p.ne' he1_p.ne'] at hz1
      rw [fac_gcd_eq_min_5 hd2_p.ne' he2_p.ne'] at hz2
      have hd2_or : d₂.factorization p = 0 ∨ (e₁.factorization p = 0 ∧ e₂.factorization p = 0) := by omega
      have hc1_x1 := fac_le_of_dvd_5 hc1_0 hx1_c1 (p := p)
      have hc1_y1 := fac_le_of_dvd_5 hc1_0 hy1_c1 (p := p)
      have hc2_x2 := fac_le_of_dvd_5 hc2_0 hx2_c2 (p := p)
      have hc2_y2 := fac_le_of_dvd_5 hc2_0 hy2_c2 (p := p)
      have hc2_G1 := fac_le_of_dvd_5 hc2_0 hG1_c2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hb3_G2 := fac_le_of_dvd_5 hb3_0 hb3_2 (p := p)
      have hw1_e1 := fac_le_of_dvd_5 hw1_0 he1_w1 (p := p)
      have hw2_d2 := fac_le_of_dvd_5 hw2_0 hd2_w2 (p := p)
      have hw3_e2 := fac_le_of_dvd_5 hw3_0 he2_w3 (p := p)
      have hG1_eq : G₁.factorization p = min (x₁.factorization p) (y₁.factorization p) :=
        fac_gcd_eq_min_5 hx1p.ne' hy1p.ne'
      have hG2_eq : G₂.factorization p = min (x₂.factorization p) (y₂.factorization p) :=
        fac_gcd_eq_min_5 hx2p.ne' hy2p.ne'
      rw [hG1_eq] at hc2_G1
      rw [hG2_eq] at hb3_G2
      rw [fac_gcd_eq_min_5 hG1_p.ne' hx2p.ne', hG1_eq] at hw1_e1
      rw [fac_gcd_eq_min_5 hG1_p.ne' hy2p.ne', hG1_eq] at hw3_e2
      rw [fac_gcd_eq_min_5 hG2_p.ne' hs3_p.ne', hG2_eq] at hw2_d2
      rw [fac_gcd_eq_min_5 hG2_p.ne' hs3_p.ne', hG2_eq] at hd2_or
      rw [fac_gcd_eq_min_5 hG1_p.ne' hx2p.ne', hG1_eq] at hd2_or
      rw [fac_gcd_eq_min_5 hG1_p.ne' hy2p.ne', hG1_eq] at hd2_or
      by_cases hw12 : w₁ = w₂
      · have hw23 : w₂ ≠ w₃ := fun h => hw13 (hw12.trans h)
        have hsub5 : ({c₁, c₂, b₃, w₁, w₃} : Finset ℕ) ⊆ B := fun b hb => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hc12, hc1b3, hw1_c1.symm, hw3_c1.symm]),
            Finset.sum_insert (by simp [hc2b3, hw1_c2.symm, hw3_c2.symm]),
            Finset.sum_insert (by simp [hw1_b3.symm, hw3_b3.symm]),
            Finset.sum_insert (by simp [hw13]), Finset.sum_singleton] at hleB
        refine Nat.le_trans ?_ hleB
        rw [← hw12] at hw2_d2
        exact a32_arith_5 hc1_x1 hc1_y1 hc2_x2 hc2_y2 hc2_G1 hb3_s3 hb3_G2
          hw1_e1 hw3_e2 hw2_d2 hd2_or
      · by_cases hw23 : w₂ = w₃
        · have hsub5 : ({c₁, c₂, b₃, w₁, w₂} : Finset ℕ) ⊆ B := fun b hb => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [B]
          have hleB := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization p)
          rw [Finset.sum_insert (by simp [hc12, hc1b3, hw1_c1.symm, hw2_c1.symm]),
              Finset.sum_insert (by simp [hc2b3, hw1_c2.symm, hw2_c2.symm]),
              Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
          refine Nat.le_trans ?_ hleB
          rw [← hw23] at hw3_e2
          exact a32_arith_5b hc1_x1 hc1_y1 hc2_x2 hc2_y2 hc2_G1 hb3_s3 hb3_G2
            hw1_e1 hw3_e2 hw2_d2 hd2_or
        · dsimp [B]
          rw [Finset.sum_insert (by simp [hc12, hc1b3, hw1_c1.symm, hw2_c1.symm, hw3_c1.symm]),
              Finset.sum_insert (by simp [hc2b3, hw1_c2.symm, hw2_c2.symm, hw3_c2.symm]),
              Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm, hw3_b3.symm]),
              Finset.sum_insert (by simp [hw12, hw13]),
              Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
          exact a32_arith_6 hc1_x1 hc1_y1 hc2_x2 hc2_y2 hc2_G1 hb3_s3 hb3_G2
            hw1_e1 hw3_e2 hw2_d2 hd2_or

private lemma cover_six_of_r3_two_slots_A3 {A : Finset ℕ} {x M u₁ s₁ u₂ s₂ s₃ b₁ b₂ b₃ : ℕ}
    (hA_eq : A = {u₁, s₁, u₂, s₂, s₃})
    (h1s1 : u₁ ≠ s₁) (h12 : u₁ ≠ u₂) (h1s2 : u₁ ≠ s₂) (h1s3 : u₁ ≠ s₃)
    (hs12 : s₁ ≠ u₂) (hs1s2 : s₁ ≠ s₂) (hs1s3 : s₁ ≠ s₃)
    (h2s2 : u₂ ≠ s₂) (h2s3 : u₂ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (_hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb₃_I : b₃ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hu1_b1 : u₁ ∣ b₁) (hs1_b1 : s₁ ∣ b₁) (hu2_b2 : u₂ ∣ b₂) (hs2_b2 : s₂ ∣ b₂) (hs3_b3 : s₃ ∣ b₃)
    (hsub_g1 : (consecInterval x M).filter (fun b => Nat.gcd u₁ s₁ ∣ b) ⊆ {b₁, b₂, b₃})
    (hsub_g2 : (consecInterval x M).filter (fun b => Nat.gcd u₂ s₂ ∣ b) ⊆ {b₁, b₂, b₃}) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hu1_p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hs1_p : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hu2_p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs2_p : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hs3_p : 0 < s₃ := hA_pos s₃ (by rw [hA_eq]; simp)
  have hu1_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hs1_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hu2_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hs2_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  have hs3_M : s₃ ≤ M := hA_le s₃ (by rw [hA_eq]; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb1_0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb2_0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hb3_0 : b₃ ≠ 0 := (pos_of_mem_consecInterval hb₃_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      u₁.factorization p + s₁.factorization p + u₂.factorization p +
        s₂.factorization p + s₃.factorization p := fun p => by
    rw [hA_eq,
        Finset.sum_insert (by simp [h1s1, h12, h1s2, h1s3]),
        Finset.sum_insert (by simp [hs12, hs1s2, hs1s3]),
        Finset.sum_insert (by simp [h2s2, h2s3]),
        Finset.sum_insert (by simp [hs23]), Finset.sum_singleton]
    ring
  let g₁ := Nat.gcd u₁ s₁
  let g₂ := Nat.gcd u₂ s₂
  have hg1_p : 0 < g₁ := Nat.gcd_pos_of_pos_left s₁ hu1_p
  have hg2_p : 0 < g₂ := Nat.gcd_pos_of_pos_left s₂ hu2_p
  have h2g1 : 2 * g₁ ≤ M := two_mul_gcd_le_of_distinct_5 hu1_p hs1_p hu1_M hs1_M h1s1
  have h2g2 : 2 * g₂ ≤ M := two_mul_gcd_le_of_distinct_5 hu2_p hs2_p hu2_M hs2_M h2s2
  have hg1_b1 : g₁ ∣ b₁ := dvd_trans (Nat.gcd_dvd_left u₁ s₁) hu1_b1
  have hg2_b2 : g₂ ∣ b₂ := dvd_trans (Nat.gcd_dvd_left u₂ s₂) hu2_b2
  by_cases hg1_b3 : g₁ ∣ b₃
  · by_cases hg2_b3 : g₂ ∣ b₃
    · -- **Subcase A3.1:** `g₁ ∣ b₃` and `g₂ ∣ b₃` (`g₁ ∣ b₁, b₃`, `g₂ ∣ b₂, b₃`).
      let e := Nat.gcd g₁ g₂
      let d₁ := Nat.gcd g₁ s₃
      let d₂ := Nat.gcd g₂ s₃
      have he_p : 0 < e := Nat.gcd_pos_of_pos_left g₂ hg1_p
      have hd1_p : 0 < d₁ := Nat.gcd_pos_of_pos_left s₃ hg1_p
      have hd2_p : 0 < d₂ := Nat.gcd_pos_of_pos_left s₃ hg2_p
      have h4e : 4 * e ≤ M := by
        have hT : ({u₁, s₁, u₂, s₂} : Finset ℕ).card * e ≤ M :=
          card_mul_le_of_forall_dvd he_p fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with h | h | h | h <;> rw [h]
            · exact ⟨hu1_p, hu1_M, dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left u₁ s₁)⟩
            · exact ⟨hs1_p, hs1_M, dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right u₁ s₁)⟩
            · exact ⟨hu2_p, hu2_M, dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left u₂ s₂)⟩
            · exact ⟨hs2_p, hs2_M, dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right u₂ s₂)⟩
        have hc4 : ({u₁, s₁, u₂, s₂} : Finset ℕ).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [h1s1, h12, h1s2]),
              Finset.card_insert_of_notMem (by simp [hs12, hs1s2]),
              Finset.card_insert_of_notMem (by simp [h2s2]), Finset.card_singleton]
        rwa [hc4] at hT
      have h3d1 : 3 * d₁ ≤ M := by
        have hT : ({u₁, s₁, s₃} : Finset ℕ).card * d₁ ≤ M :=
          card_mul_le_of_forall_dvd hd1_p fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with h | h | h <;> rw [h]
            · exact ⟨hu1_p, hu1_M, dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)⟩
            · exact ⟨hs1_p, hs1_M, dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)⟩
            · exact ⟨hs3_p, hs3_M, Nat.gcd_dvd_right g₁ s₃⟩
        have hc3 : ({u₁, s₁, s₃} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [h1s1, h1s3]),
              Finset.card_insert_of_notMem (by simp [hs1s3]), Finset.card_singleton]
        rwa [hc3] at hT
      have h3d2 : 3 * d₂ ≤ M := by
        have hT : ({u₂, s₂, s₃} : Finset ℕ).card * d₂ ≤ M :=
          card_mul_le_of_forall_dvd hd2_p fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with h | h | h <;> rw [h]
            · exact ⟨hu2_p, hu2_M, dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_left u₂ s₂)⟩
            · exact ⟨hs2_p, hs2_M, dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_right u₂ s₂)⟩
            · exact ⟨hs3_p, hs3_M, Nat.gcd_dvd_right g₂ s₃⟩
        have hc3 : ({u₂, s₂, s₃} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [h2s2, h2s3]),
              Finset.card_insert_of_notMem (by simp [hs23]), Finset.card_singleton]
        rwa [hc3] at hT
      have h3_card : ({b₁, b₂, b₃} : Finset ℕ).card + 1 ≤ 4 := by
        have := card_finset_le_three_5 b₁ b₂ b₃; omega
      obtain ⟨w₀, hw0_I, hw0_not, he_w0⟩ := exists_avoiding_multiple_in_consecInterval x M e
        {b₁, b₂, b₃} he_p (le_trans (Nat.mul_le_mul_right e h3_card) h4e)
      have hnot_d1 : ¬ ((consecInterval x M).filter (fun b => d₁ ∣ b) ⊆ {b₁, b₂, b₃}) := by
        intro hs
        obtain ⟨hd1_1, hd1_2, hd1_3, hM4d1⟩ := dvd_triple_of_filter_subset_triple_5 hd1_p h3d1 hb12 hb13 hb23 hs
        have hg2_dvd_2d1 : g₂ ∣ 2 * d₁ :=
          (span_three_props_5 hd1_p hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hd1_1 hd1_2 hd1_3 hs).2 g₂ hg2_b2 hg2_b3
        have hcop : Nat.Coprime g₂ d₁ := gcd_five_eq_one_5 hA_eq hAgcd
          (dvd_trans (Nat.gcd_dvd_right g₂ d₁) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)))
          (dvd_trans (Nat.gcd_dvd_right g₂ d₁) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)))
          (dvd_trans (Nat.gcd_dvd_left g₂ d₁) (Nat.gcd_dvd_left u₂ s₂))
          (dvd_trans (Nat.gcd_dvd_left g₂ d₁) (Nat.gcd_dvd_right u₂ s₂))
          (dvd_trans (Nat.gcd_dvd_right g₂ d₁) (Nat.gcd_dvd_right g₁ s₃))
        have hg2_dvd2 : g₂ ∣ 2 := hcop.dvd_of_dvd_mul_right hg2_dvd_2d1
        have hM4g2 : M < 4 * g₂ := by
          by_contra hge
          have h4g2 : 4 * g₂ ≤ M := Nat.le_of_not_lt hge
          have h1 := card_multiples_Icc_ge x M g₂ hg2_p
          have h2 : 4 ≤ M / g₂ := (Nat.le_div_iff_mul_le hg2_p).mpr h4g2
          have hle := Finset.card_le_card hsub_g2
          have h3c := card_finset_le_three_5 b₁ b₂ b₃
          have hp : M / g₂ ≤ ({b₁, b₂, b₃} : Finset ℕ).card := le_trans h1 hle
          omega
        have hg2_2 : g₂ = 2 := by
          have hg2_le2 := Nat.le_of_dvd (by decide) hg2_dvd2
          omega
        have hd1_1 : d₁ = 1 := by
          have h2nd : ¬ (2 ∣ d₁) := fun h2 => by
            have := Nat.dvd_gcd (by rw [hg2_2] : 2 ∣ g₂) h2
            rw [hcop] at this
            omega
          have hd1_le2 : d₁ ≤ 2 := by omega
          have hd1_ne2 : d₁ ≠ 2 := fun h => h2nd (by rw [h])
          omega
        omega
      have hnot_d2 : ¬ ((consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {b₁, b₂, b₃}) := by
        intro hs
        obtain ⟨hd2_1, hd2_2, hd2_3, hM4d2⟩ := dvd_triple_of_filter_subset_triple_5 hd2_p h3d2 hb12 hb13 hb23 hs
        have hsub_perm : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {b₂, b₁, b₃} := by
          intro z hz; have := hs hz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
        have hg1_dvd_2d2 : g₁ ∣ 2 * d₂ :=
          (span_three_props_5 hd2_p hb₂_I hb₁_I hb₃_I hb12.symm hb23 hb13 hd2_2 hd2_1 hd2_3 hsub_perm).2 g₁ hg1_b1 hg1_b3
        have hcop : Nat.Coprime g₁ d₂ := gcd_five_eq_one_5 hA_eq hAgcd
          (dvd_trans (Nat.gcd_dvd_left g₁ d₂) (Nat.gcd_dvd_left u₁ s₁))
          (dvd_trans (Nat.gcd_dvd_left g₁ d₂) (Nat.gcd_dvd_right u₁ s₁))
          (dvd_trans (Nat.gcd_dvd_right g₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_left u₂ s₂)))
          (dvd_trans (Nat.gcd_dvd_right g₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_right u₂ s₂)))
          (dvd_trans (Nat.gcd_dvd_right g₁ d₂) (Nat.gcd_dvd_right g₂ s₃))
        have hg1_dvd2 : g₁ ∣ 2 := hcop.dvd_of_dvd_mul_right hg1_dvd_2d2
        have hM4g1 : M < 4 * g₁ := by
          by_contra hge
          have h4g1 : 4 * g₁ ≤ M := Nat.le_of_not_lt hge
          have h1 := card_multiples_Icc_ge x M g₁ hg1_p
          have h2 : 4 ≤ M / g₁ := (Nat.le_div_iff_mul_le hg1_p).mpr h4g1
          have hle := Finset.card_le_card hsub_g1
          have h3c := card_finset_le_three_5 b₁ b₂ b₃
          have hp : M / g₁ ≤ ({b₁, b₂, b₃} : Finset ℕ).card := le_trans h1 hle
          omega
        have hg1_2 : g₁ = 2 := by have := Nat.le_of_dvd (by decide) hg1_dvd2; omega
        have hd2_1 : d₂ = 1 := by
          have h2nd : ¬ (2 ∣ d₂) := fun h2 => by
            have := Nat.dvd_gcd (by rw [hg1_2] : 2 ∣ g₁) h2; rw [hcop] at this; omega
          have : d₂ ≠ 2 := fun h => h2nd (by rw [h])
          omega
        omega
      obtain ⟨w₁, hw1_I, hw1_b1, hw1_b2, hw1_b3, hd1_w1⟩ := exists_avoiding_of_not_subset_triple_5 hnot_d1
      obtain ⟨w₂, hw2_I, hw2_b1, hw2_b2, hw2_b3, hd2_w2⟩ := exists_avoiding_of_not_subset_triple_5 hnot_d2
      have hw0_b1 : w₀ ≠ b₁ := fun h => hw0_not (by simp [h])
      have hw0_b2 : w₀ ≠ b₂ := fun h => hw0_not (by simp [h])
      have hw0_b3 : w₀ ≠ b₃ := fun h => hw0_not (by simp [h])
      have hw0_0 : w₀ ≠ 0 := (pos_of_mem_consecInterval hw0_I).ne'
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw2_I).ne'
      let B : Finset ℕ := {b₁, b₂, b₃, w₀, w₁, w₂}
      have hBI : B ⊆ consecInterval x M := fun b hb => by
        simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_six_5 b₁ b₂ b₃ w₀ w₁ w₂,
        isCover_of_prime_factorization_5 hA0 hB0 fun p _ => ?_⟩
      rw [hsumA_eq p]
      have hgcd_e_d1 : Nat.gcd e d₁ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
        (dvd_trans (Nat.gcd_dvd_left e d₁) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left e d₁) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left e d₁) (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_left e d₁) (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_right e d₁) (Nat.gcd_dvd_right g₁ s₃))
      have hgcd_e_d2 : Nat.gcd e d₂ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
        (dvd_trans (Nat.gcd_dvd_left e d₂) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left e d₂) (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left e d₂) (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_left e d₂) (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_right e d₂) (Nat.gcd_dvd_right g₂ s₃))
      have hgcd_d1_d2 : Nat.gcd d₁ d₂ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
        (dvd_trans (Nat.gcd_dvd_left d₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_left u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_left d₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₁ s₃) (Nat.gcd_dvd_right u₁ s₁)))
        (dvd_trans (Nat.gcd_dvd_right d₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_left u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_right d₁ d₂) (dvd_trans (Nat.gcd_dvd_left g₂ s₃) (Nat.gcd_dvd_right u₂ s₂)))
        (dvd_trans (Nat.gcd_dvd_left d₁ d₂) (Nat.gcd_dvd_right g₁ s₃))
      have hz01 : (Nat.gcd e d₁).factorization p = 0 := by rw [hgcd_e_d1, Nat.factorization_one, Finsupp.zero_apply]
      have hz02 : (Nat.gcd e d₂).factorization p = 0 := by rw [hgcd_e_d2, Nat.factorization_one, Finsupp.zero_apply]
      have hz12 : (Nat.gcd d₁ d₂).factorization p = 0 := by rw [hgcd_d1_d2, Nat.factorization_one, Finsupp.zero_apply]
      rw [fac_gcd_eq_min_5 he_p.ne' hd1_p.ne'] at hz01
      rw [fac_gcd_eq_min_5 he_p.ne' hd2_p.ne'] at hz02
      rw [fac_gcd_eq_min_5 hd1_p.ne' hd2_p.ne'] at hz12
      have hb1_u1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
      have hb1_s1 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
      have hb2_u2 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
      have hb2_s2 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
      have hb3_s3 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
      have hb3_g1 := fac_le_of_dvd_5 hb3_0 hg1_b3 (p := p)
      have hb3_g2 := fac_le_of_dvd_5 hb3_0 hg2_b3 (p := p)
      have hw0_e := fac_le_of_dvd_5 hw0_0 he_w0 (p := p)
      have hw1_d1 := fac_le_of_dvd_5 hw1_0 hd1_w1 (p := p)
      have hw2_d2 := fac_le_of_dvd_5 hw2_0 hd2_w2 (p := p)
      have hg1_eq : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
        fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne'
      have hg2_eq : g₂.factorization p = min (u₂.factorization p) (s₂.factorization p) :=
        fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne'
      rw [hg1_eq] at hb3_g1
      rw [hg2_eq] at hb3_g2
      rw [fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne', hg1_eq, hg2_eq] at hw0_e hz01 hz02
      rw [fac_gcd_eq_min_5 hg1_p.ne' hs3_p.ne', hg1_eq] at hw1_d1 hz01 hz12
      rw [fac_gcd_eq_min_5 hg2_p.ne' hs3_p.ne', hg2_eq] at hw2_d2 hz02 hz12
      have hle4 : ∀ w ∈ B, w ≠ b₁ → w ≠ b₂ → w ≠ b₃ →
          b₁.factorization p + b₂.factorization p + b₃.factorization p + w.factorization p ≤
            ∑ b ∈ B, b.factorization p := fun w hwB hwb1 hwb2 hwb3 => by
        have hsub4 : ({b₁, b₂, b₃, w} : Finset ℕ) ⊆ B := fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> simp [B, hwB]
        have := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb12, hb13, hwb1.symm]),
            Finset.sum_insert (by simp [hb23, hwb2.symm]),
            Finset.sum_insert (by simp [hwb3.symm]), Finset.sum_singleton] at this
        omega
      have h4_0 := hle4 w₀ (by simp [B]) hw0_b1 hw0_b2 hw0_b3
      have h4_1 := hle4 w₁ (by simp [B]) hw1_b1 hw1_b2 hw1_b3
      have h4_2 := hle4 w₂ (by simp [B]) hw2_b1 hw2_b2 hw2_b3
      omega
    · have hA_sw : A = {u₂, s₂, u₁, s₁, s₃} := by
        rw [hA_eq]; apply Finset.Subset.antisymm
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      exact cover_six_of_r3_two_slots_A3_one_not_b3 hA_sw
        h2s2 h12.symm hs12.symm h2s3 h1s2.symm hs1s2.symm hs23 h1s1 h1s3 hs1s3
        hA_pos hA_le hAgcd hb₂_I hb₁_I hb₃_I hb12.symm hb23 hb13
        hu2_b2 hs2_b2 hu1_b1 hs1_b1 hs3_b3
        (fun z hz => by
          have := hsub_g2 hz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
          rcases this with rfl | rfl | rfl <;> simp)
        (fun z hz => by
          have := hsub_g1 hz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
          rcases this with rfl | rfl | rfl <;> simp)
        hg2_b3 hg1_b3
  · by_cases hg2_b3 : g₂ ∣ b₃
    · exact cover_six_of_r3_two_slots_A3_one_not_b3 hA_eq h1s1 h12 h1s2 h1s3 hs12 hs1s2 hs1s3
        h2s2 h2s3 hs23 hA_pos hA_le hAgcd hb₁_I hb₂_I hb₃_I hb12 hb13 hb23
        hu1_b1 hs1_b1 hu2_b2 hs2_b2 hs3_b3
        hsub_g1 hsub_g2 hg1_b3 hg2_b3
    · -- Both `¬ g₁ ∣ b₃` and `¬ g₂ ∣ b₃` ⇒ `g₁ = |b₁ - b₂| = g₂`, impossible!
      exfalso
      have hsub1_p : (consecInterval x M).filter (fun b => g₁ ∣ b) ⊆ {b₁, b₂} := fun b hb => by
        have hmem := hsub_g1 hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with rfl | rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl; exact absurd (Finset.mem_filter.mp hb).2 hg1_b3]
      have hsub2_p : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₁, b₂} := fun b hb => by
        have hmem := hsub_g2 hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
        rcases hmem with rfl | rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl; exact absurd (Finset.mem_filter.mp hb).2 hg2_b3]
      obtain ⟨_, hg1_b2, hM3g1⟩ := dvd_pair_of_filter_subset_pair_5 hg1_p h2g1 hb12 hsub1_p
      obtain ⟨hg2_b1, _, hM3g2⟩ := dvd_pair_of_filter_subset_pair_5 hg2_p h2g2 hb12 hsub2_p
      have hdiff1 := diff_eq_of_two_multiples_5 hg1_p hb₁_I hb₂_I hb12 hg1_b1 hg1_b2 hsub1_p
      have hdiff2 := diff_eq_of_two_multiples_5 hg2_p hb₁_I hb₂_I hb12 hg2_b1 hg2_b2 hsub2_p
      have hg12_eq : g₁ = g₂ := by rcases hdiff1 with h | h <;> rcases hdiff2 with h' | h' <;> omega
      have hpair1 : (u₁ = g₁ ∧ s₁ = 2 * g₁) ∨ (s₁ = g₁ ∧ u₁ = 2 * g₁) := by
        rcases lt_or_gt_of_ne h1s1 with hlt | hgt
        · left; exact eq_pair_of_two_dvd_lt_three_mul_5 hg1_p hu1_p hlt hs1_M hM3g1
            (Nat.gcd_dvd_left u₁ s₁) (Nat.gcd_dvd_right u₁ s₁)
        · right; exact eq_pair_of_two_dvd_lt_three_mul_5 hg1_p hs1_p hgt hu1_M hM3g1
            (Nat.gcd_dvd_right u₁ s₁) (Nat.gcd_dvd_left u₁ s₁)
      have hpair2 : (u₂ = g₂ ∧ s₂ = 2 * g₂) ∨ (s₂ = g₂ ∧ u₂ = 2 * g₂) := by
        rcases lt_or_gt_of_ne h2s2 with hlt | hgt
        · left; exact eq_pair_of_two_dvd_lt_three_mul_5 hg2_p hu2_p hlt hs2_M hM3g2
            (Nat.gcd_dvd_left u₂ s₂) (Nat.gcd_dvd_right u₂ s₂)
        · right; exact eq_pair_of_two_dvd_lt_three_mul_5 hg2_p hs2_p hgt hu2_M hM3g2
            (Nat.gcd_dvd_right u₂ s₂) (Nat.gcd_dvd_left u₂ s₂)
      rcases hpair1 with ⟨hu1e, _⟩ | ⟨hs1e, _⟩ <;> rcases hpair2 with ⟨hu2e, _⟩ | ⟨hs2e, _⟩ <;>
        [exact h12 (by rw [hu1e, hu2e, hg12_eq]); exact h1s2 (by rw [hu1e, hs2e, hg12_eq]);
         exact hs12 (by rw [hs1e, hu2e, hg12_eq]); exact hs1s2 (by rw [hs1e, hs2e, hg12_eq])]

private lemma cover_six_of_r3_two_slots {A : Finset ℕ} {x M u₁ s₁ u₂ s₂ s₃ b₁ b₂ b₃ : ℕ}
    (hA_eq : A = {u₁, s₁, u₂, s₂, s₃})
    (h1s1 : u₁ ≠ s₁) (h12 : u₁ ≠ u₂) (h1s2 : u₁ ≠ s₂) (h1s3 : u₁ ≠ s₃)
    (hs12 : s₁ ≠ u₂) (hs1s2 : s₁ ≠ s₂) (hs1s3 : s₁ ≠ s₃)
    (h2s2 : u₂ ≠ s₂) (h2s3 : u₂ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb₃_I : b₃ ∈ consecInterval x M)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃)
    (hu1_b1 : u₁ ∣ b₁) (hs1_b1 : s₁ ∣ b₁) (hu2_b2 : u₂ ∣ b₂) (hs2_b2 : s₂ ∣ b₂) (hs3_b3 : s₃ ∣ b₃) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hu1_p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hs1_p : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hu2_p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs2_p : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hs3_p : 0 < s₃ := hA_pos s₃ (by rw [hA_eq]; simp)
  have hu1_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hs1_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hu2_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hs2_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb1_0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb2_0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hb3_0 : b₃ ≠ 0 := (pos_of_mem_consecInterval hb₃_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      u₁.factorization p + s₁.factorization p + u₂.factorization p +
        s₂.factorization p + s₃.factorization p := fun p => by
    rw [hA_eq,
        Finset.sum_insert (by simp [h1s1, h12, h1s2, h1s3]),
        Finset.sum_insert (by simp [hs12, hs1s2, hs1s3]),
        Finset.sum_insert (by simp [h2s2, h2s3]),
        Finset.sum_insert (by simp [hs23]), Finset.sum_singleton]
    ring
  let g₁ := Nat.gcd u₁ s₁
  let g₂ := Nat.gcd u₂ s₂
  have hg1_p : 0 < g₁ := Nat.gcd_pos_of_pos_left s₁ hu1_p
  have hg2_p : 0 < g₂ := Nat.gcd_pos_of_pos_left s₂ hu2_p
  by_cases hsub1 : (consecInterval x M).filter (fun b => g₁ ∣ b) ⊆ {b₁, b₂, b₃}
  · by_cases hsub2 : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₁, b₂, b₃}
    · exact cover_six_of_r3_two_slots_A3 hA_eq h1s1 h12 h1s2 h1s3 hs12 hs1s2 hs1s3 h2s2 h2s3 hs23
        hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb₃_I hb12 hb13 hb23
        hu1_b1 hs1_b1 hu2_b2 hs2_b2 hs3_b3 hsub1 hsub2
    · obtain ⟨w₂, hw2_I, hw2_b1, hw2_b2, hw2_b3, hg2_w2⟩ := exists_avoiding_of_not_subset_triple_5 hsub2
      exact cover_six_of_r3_two_slots_A2 hA_eq h1s1 h12 h1s2 h1s3 hs12 hs1s2 hs1s3 h2s2 h2s3 hs23
        hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb₃_I hb12 hb13 hb23
        hu1_b1 hs1_b1 hu2_b2 hs2_b2 hs3_b3 hsub1 hw2_I hw2_b1 hw2_b2 hw2_b3 hg2_w2
  · by_cases hsub2 : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₁, b₂, b₃}
    · obtain ⟨w₁, hw1_I, hw1_b1, hw1_b2, hw1_b3, hg1_w1⟩ := exists_avoiding_of_not_subset_triple_5 hsub1
      have hA_sw : A = {u₂, s₂, u₁, s₁, s₃} := by
        rw [hA_eq]; apply Finset.Subset.antisymm
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      have hsub2' : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₂, b₁, b₃} := by
        intro z hz; have := hsub2 hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl <;> simp
      exact cover_six_of_r3_two_slots_A2 hA_sw h2s2 h12.symm hs12.symm h2s3 h1s2.symm hs1s2.symm hs23
        h1s1 h1s3 hs1s3 hA_pos hA_le hAgcd hM7 hb₂_I hb₁_I hb₃_I hb12.symm hb23 hb13
        hu2_b2 hs2_b2 hu1_b1 hs1_b1 hs3_b3 hsub2' hw1_I hw1_b2 hw1_b1 hw1_b3 hg1_w1
    · -- **Case A1:** Neither `g₁` nor `g₂` is restricted to `{b₁, b₂, b₃}`.
      obtain ⟨w₁, hw1_I, hw1_b1, hw1_b2, hw1_b3, hg1_w1⟩ := exists_avoiding_of_not_subset_triple_5 hsub1
      obtain ⟨w₂, hw2_I, hw2_b1, hw2_b2, hw2_b3, hg2_w2⟩ := exists_avoiding_of_not_subset_triple_5 hsub2
      have hs3_M : s₃ ≤ M := hA_le s₃ (by rw [hA_eq]; simp)
      have hw1_0 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw1_I).ne'
      have hw2_0 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw2_I).ne'
      have hg1_u1 : g₁ ∣ u₁ := Nat.gcd_dvd_left u₁ s₁
      have hg1_s1 : g₁ ∣ s₁ := Nat.gcd_dvd_right u₁ s₁
      have hg2_u2 : g₂ ∣ u₂ := Nat.gcd_dvd_left u₂ s₂
      have hg2_s2 : g₂ ∣ s₂ := Nat.gcd_dvd_right u₂ s₂
      by_cases hw12 : w₁ = w₂
      · subst hw12
        let d := Nat.gcd g₁ g₂
        have hd_p : 0 < d := Nat.gcd_pos_of_pos_left g₂ hg1_p
        have hd_g1 : d ∣ g₁ := Nat.gcd_dvd_left g₁ g₂
        have hd_g2 : d ∣ g₂ := Nat.gcd_dvd_right g₁ g₂
        have hd_u1 : d ∣ u₁ := dvd_trans hd_g1 hg1_u1
        have hd_s1 : d ∣ s₁ := dvd_trans hd_g1 hg1_s1
        have hd_u2 : d ∣ u₂ := dvd_trans hd_g2 hg2_u2
        have hd_s2 : d ∣ s₂ := dvd_trans hd_g2 hg2_s2
        by_cases hsub_d : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, b₃, w₁}
        · have h4d : 4 * d ≤ M := by
            have hT : ({u₁, s₁, u₂, s₂} : Finset ℕ).card * d ≤ M :=
              card_mul_le_of_forall_dvd hd_p fun a ha => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at ha
                rcases ha with h | h | h | h <;> rw [h]
                · exact ⟨hu1_p, hu1_M, hd_u1⟩
                · exact ⟨hs1_p, hs1_M, hd_s1⟩
                · exact ⟨hu2_p, hu2_M, hd_u2⟩
                · exact ⟨hs2_p, hs2_M, hd_s2⟩
            have hc4 : ({u₁, s₁, u₂, s₂} : Finset ℕ).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp [h1s1, h12, h1s2]),
                  Finset.card_insert_of_notMem (by simp [hs12, hs1s2]),
                  Finset.card_insert_of_notMem (by simp [h2s2]), Finset.card_singleton]
            rwa [hc4] at hT
          by_cases hd1 : d = 1
          · refine ⟨{b₁, b₂, b₃, w₁}, ?_, card_finset_le_four_5 b₁ b₂ b₃ w₁ |>.trans (by omega), ?_⟩
            · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl | rfl <;> assumption
            · refine isCover_of_prime_factorization_5 hA0 ?_ fun p hp => ?_
              · intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
                rcases hb with rfl | rfl | rfl | rfl <;> assumption
              · rw [hsumA_eq p,
                    Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm]),
                    Finset.sum_insert (by simp [hb23, hw1_b2.symm]),
                    Finset.sum_insert (by simp [hw1_b3.symm]), Finset.sum_singleton]
                have h1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
                have h2 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
                have h3 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
                have h4 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
                have h5 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
                have h6 := fac_le_of_dvd_5 hw1_0 hg1_w1 (p := p)
                have h7 := fac_le_of_dvd_5 hw1_0 hg2_w2 (p := p)
                have hm1 : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
                  fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne' (p := p)
                have hm2 : g₂.factorization p = min (u₂.factorization p) (s₂.factorization p) :=
                  fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne' (p := p)
                have hd0 : min (g₁.factorization p) (g₂.factorization p) = 0 := by
                  rw [← fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne' (p := p)]
                  change d.factorization p = 0; rw [hd1]; simp
                omega
          · -- `d ≥ 2`, `4 * d ≤ M` (hence `8 ≤ M`), and `{b₁, b₂, b₃, w₁} = {(x/d+1)*d, ..., (x/d+4)*d}`.
            have hM8 : 8 ≤ M := by omega
            have hgcd_d_s3 : Nat.gcd d s₃ = 1 := gcd_five_eq_one_5 hA_eq hAgcd
              (dvd_trans (Nat.gcd_dvd_left d s₃) hd_u1)
              (dvd_trans (Nat.gcd_dvd_left d s₃) hd_s1)
              (dvd_trans (Nat.gcd_dvd_left d s₃) hd_u2)
              (dvd_trans (Nat.gcd_dvd_left d s₃) hd_s2)
              (Nat.gcd_dvd_right d s₃)
            let k := x / d
            let m₁ := (k + 1) * d
            let m₂ := (k + 2) * d
            let m₃ := (k + 3) * d
            let m₄ := (k + 4) * d
            have hx_eq : k * d + x % d = x := by
              simpa [k, mul_comm] using Nat.div_add_mod x d
            have hx_mod : x % d < d := Nat.mod_lt x hd_p
            have hm_I : ∀ j, 1 ≤ j → j ≤ 4 → (k + j) * d ∈ consecInterval x M := by
              intro j hj1 hj4
              simp only [consecInterval, Finset.mem_Icc]
              have hk1 : k * d + d ≤ (k + j) * d := by nlinarith
              have hk4 : (k + j) * d ≤ k * d + 4 * d := by nlinarith
              exact ⟨by omega, by omega⟩
            have hm1_I := hm_I 1 (by omega) (by omega)
            have hm2_I := hm_I 2 (by omega) (by omega)
            have hm3_I := hm_I 3 (by omega) (by omega)
            have hm4_I := hm_I 4 (by omega) (by omega)
            have hS4_sub : ({m₁, m₂, m₃, m₄} : Finset ℕ) ⊆ {b₁, b₂, b₃, w₁} := by
              intro z hz
              apply hsub_d
              refine Finset.mem_filter.mpr ⟨?_, ?_⟩
              · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl | rfl | rfl <;> assumption
              · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl | rfl | rfl <;> exact dvd_mul_left d _
            have hm12 : m₁ < m₂ := by dsimp [m₁, m₂]; nlinarith
            have hm23 : m₂ < m₃ := by dsimp [m₂, m₃]; nlinarith
            have hm34 : m₃ < m₄ := by dsimp [m₃, m₄]; nlinarith
            have hS4_card : ({m₁, m₂, m₃, m₄} : Finset ℕ).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
            have hS4_eq : ({m₁, m₂, m₃, m₄} : Finset ℕ) = {b₁, b₂, b₃, w₁} :=
              Finset.eq_of_subset_of_card_le hS4_sub
                (by have := card_finset_le_four_5 b₁ b₂ b₃ w₁; omega)
            have hM5d : M < 5 * d := by
              by_contra hge
              have h5d : 5 * d ≤ M := Nat.le_of_not_lt hge
              have hcard_ge5 : 5 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
                have h1 := card_multiples_Icc_ge x M d hd_p
                have h2 : 5 ≤ M / d := (Nat.le_div_iff_mul_le hd_p).mpr h5d
                change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
                omega
              have hle := Finset.card_le_card hsub_d
              have hle4 := card_finset_le_four_5 b₁ b₂ b₃ w₁
              omega
            have h_sum_4d : ∀ p : ℕ, u₁.factorization p + s₁.factorization p +
                u₂.factorization p + s₂.factorization p =
                4 * d.factorization p + (24 : ℕ).factorization p := by
              intro p
              obtain ⟨q₁, hq1⟩ := hd_u1
              obtain ⟨q₂, hq2⟩ := hd_s1
              obtain ⟨q₃, hq3⟩ := hd_u2
              obtain ⟨q₄, hq4⟩ := hd_s2
              have hq1_r : 1 ≤ q₁ ∧ q₁ ≤ 4 := by
                have h0 : 0 < q₁ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq1; omega
                have h5 : q₁ ≤ 4 := by by_contra hgt; have := Nat.mul_le_mul_left d (by omega : 5 ≤ q₁); omega
                exact ⟨h0, h5⟩
              have hq2_r : 1 ≤ q₂ ∧ q₂ ≤ 4 := by
                have h0 : 0 < q₂ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq2; omega
                have h5 : q₂ ≤ 4 := by by_contra hgt; have := Nat.mul_le_mul_left d (by omega : 5 ≤ q₂); omega
                exact ⟨h0, h5⟩
              have hq3_r : 1 ≤ q₃ ∧ q₃ ≤ 4 := by
                have h0 : 0 < q₃ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq3; omega
                have h5 : q₃ ≤ 4 := by by_contra hgt; have := Nat.mul_le_mul_left d (by omega : 5 ≤ q₃); omega
                exact ⟨h0, h5⟩
              have hq4_r : 1 ≤ q₄ ∧ q₄ ≤ 4 := by
                have h0 : 0 < q₄ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq4; omega
                have h5 : q₄ ≤ 4 := by by_contra hgt; have := Nat.mul_le_mul_left d (by omega : 5 ≤ q₄); omega
                exact ⟨h0, h5⟩
              have hne12 : q₁ ≠ q₂ := fun h => h1s1 (by rw [hq1, hq2, h])
              have hne13 : q₁ ≠ q₃ := fun h => h12 (by rw [hq1, hq3, h])
              have hne14 : q₁ ≠ q₄ := fun h => h1s2 (by rw [hq1, hq4, h])
              have hne23 : q₂ ≠ q₃ := fun h => hs12 (by rw [hq2, hq3, h])
              have hne24 : q₂ ≠ q₄ := fun h => hs1s2 (by rw [hq2, hq4, h])
              have hne34 : q₃ ≠ q₄ := fun h => h2s2 (by rw [hq3, hq4, h])
              have hQ_sub : ({q₁, q₂, q₃, q₄} : Finset ℕ) ⊆ {1, 2, 3, 4} := by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
                rcases hz with rfl | rfl | rfl | rfl <;> omega
              have hQ_eq : ({q₁, q₂, q₃, q₄} : Finset ℕ) = {1, 2, 3, 4} := by
                have hcQ : ({q₁, q₂, q₃, q₄} : Finset ℕ).card = 4 := by
                  rw [Finset.card_insert_of_notMem (by simp [hne12, hne13, hne14]),
                      Finset.card_insert_of_notMem (by simp [hne23, hne24]),
                      Finset.card_insert_of_notMem (by simp [hne34]), Finset.card_singleton]
                have hc14 : ({1, 2, 3, 4} : Finset ℕ).card = 4 := by decide
                exact Finset.eq_of_subset_of_card_le hQ_sub (by omega)
              have hsumQ : ∑ q ∈ ({q₁, q₂, q₃, q₄} : Finset ℕ), q.factorization p =
                  (1 : ℕ).factorization p + (2 : ℕ).factorization p +
                  (3 : ℕ).factorization p + (4 : ℕ).factorization p := by
                rw [hQ_eq, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
                    Finset.sum_insert (by simp), Finset.sum_singleton]; ring
              rw [Finset.sum_insert (by simp [hne12, hne13, hne14]),
                  Finset.sum_insert (by simp [hne23, hne24]),
                  Finset.sum_insert (by simp [hne34]), Finset.sum_singleton] at hsumQ
              have hmul1 : u₁.factorization p = d.factorization p + q₁.factorization p := by
                rw [hq1, Nat.factorization_mul hd_p.ne' (by omega), Finsupp.coe_add, Pi.add_apply]
              have hmul2 : s₁.factorization p = d.factorization p + q₂.factorization p := by
                rw [hq2, Nat.factorization_mul hd_p.ne' (by omega), Finsupp.coe_add, Pi.add_apply]
              have hmul3 : u₂.factorization p = d.factorization p + q₃.factorization p := by
                rw [hq3, Nat.factorization_mul hd_p.ne' (by omega), Finsupp.coe_add, Pi.add_apply]
              have hmul4 : s₂.factorization p = d.factorization p + q₄.factorization p := by
                rw [hq4, Nat.factorization_mul hd_p.ne' (by omega), Finsupp.coe_add, Pi.add_apply]
              have h24 : (24 : ℕ).factorization p =
                  (1 : ℕ).factorization p + (2 : ℕ).factorization p +
                  (3 : ℕ).factorization p + (4 : ℕ).factorization p := by
                have heq24 : (24 : ℕ) = 1 * 2 * 3 * 4 := by norm_num
                rw [heq24, Nat.factorization_mul (by norm_num) (by norm_num),
                    Nat.factorization_mul (by norm_num) (by norm_num),
                    Nat.factorization_mul (by norm_num) (by norm_num)]
                simp [Finsupp.coe_add, Pi.add_apply]
              omega
            have hsum4b : ∀ p : ℕ, b₁.factorization p + b₂.factorization p + b₃.factorization p +
                w₁.factorization p =
                4 * d.factorization p + ((k + 1).factorization p + (k + 2).factorization p +
                  (k + 3).factorization p + (k + 4).factorization p) := by
              intro p
              have hsb : ∑ b ∈ ({b₁, b₂, b₃, w₁} : Finset ℕ), b.factorization p =
                  ∑ b ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ), b.factorization p := by rw [hS4_eq]
              rw [Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm]),
                  Finset.sum_insert (by simp [hb23, hw1_b2.symm]),
                  Finset.sum_insert (by simp [hw1_b3.symm]), Finset.sum_singleton,
                  Finset.sum_insert (by simp; omega),
                  Finset.sum_insert (by simp; omega),
                  Finset.sum_insert (by simp; omega), Finset.sum_singleton] at hsb
              have hfm1 : m₁.factorization p = (k + 1).factorization p + d.factorization p := by
                dsimp [m₁]; rw [Nat.factorization_mul (Nat.succ_ne_zero k) hd_p.ne', Finsupp.coe_add, Pi.add_apply]
              have hfm2 : m₂.factorization p = (k + 2).factorization p + d.factorization p := by
                dsimp [m₂]; rw [Nat.factorization_mul (Nat.succ_ne_zero (k + 1)) hd_p.ne', Finsupp.coe_add, Pi.add_apply]
              have hfm3 : m₃.factorization p = (k + 3).factorization p + d.factorization p := by
                dsimp [m₃]; rw [Nat.factorization_mul (Nat.succ_ne_zero (k + 2)) hd_p.ne', Finsupp.coe_add, Pi.add_apply]
              have hfm4 : m₄.factorization p = (k + 4).factorization p + d.factorization p := by
                dsimp [m₄]; rw [Nat.factorization_mul (Nat.succ_ne_zero (k + 3)) hd_p.ne', Finsupp.coe_add, Pi.add_apply]
              omega
            have h24_dvd_prod : 24 ∣ (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
              have h8 : 8 ∣ (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
                have hmod8 : ((k + 1) * (k + 2) * (k + 3) * (k + 4)) % 8 = 0 := by
                  have hk8 : k % 8 < 8 := Nat.mod_lt k (by omega)
                  have hrew : ((k + 1) * (k + 2) * (k + 3) * (k + 4)) % 8 =
                      (((k % 8 + 1) * (k % 8 + 2) * (k % 8 + 3) * (k % 8 + 4))) % 8 := by
                    simp [Nat.mul_mod, Nat.add_mod]
                  rw [hrew]; interval_cases (k % 8) <;> norm_num
                exact Nat.dvd_of_mod_eq_zero hmod8
              have h3 : 3 ∣ (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
                have hmod3 : ((k + 1) * (k + 2) * (k + 3) * (k + 4)) % 3 = 0 := by
                  have hk3 : k % 3 < 3 := Nat.mod_lt k (by omega)
                  have hrew : ((k + 1) * (k + 2) * (k + 3) * (k + 4)) % 3 =
                      (((k % 3 + 1) * (k % 3 + 2) * (k % 3 + 3) * (k % 3 + 4))) % 3 := by
                    simp [Nat.mul_mod, Nat.add_mod]
                  rw [hrew]; interval_cases (k % 3) <;> norm_num
                exact Nat.dvd_of_mod_eq_zero hmod3
              exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 8 3) h8 h3)
            have h24_fac_le : ∀ p : ℕ, (24 : ℕ).factorization p ≤
                (k + 1).factorization p + (k + 2).factorization p +
                  (k + 3).factorization p + (k + 4).factorization p := by
              intro p
              have hp := fac_le_of_dvd_5 (by positivity) h24_dvd_prod (p := p)
              rw [Nat.factorization_mul (by positivity) (by positivity),
                  Nat.factorization_mul (by positivity) (by positivity),
                  Nat.factorization_mul (by positivity) (by positivity)] at hp
              simpa [Finsupp.coe_add, Pi.add_apply, add_assoc] using hp
            -- Find optional extra `w₄` (multiple of 4 outside `S₄`, if `¬ 2 ∣ d`) and `w₅` (multiple of 3 outside `S₄`, if `¬ 3 ∣ d` and `b₁,b₂,w₁` miss 3).
            have hex_w4 : ¬ (2 ∣ d) → ∃ w₄ ∈ consecInterval x M,
                w₄ ≠ b₁ ∧ w₄ ≠ b₂ ∧ w₄ ≠ b₃ ∧ w₄ ≠ w₁ ∧ 4 ∣ w₄ := by
              intro hnd2
              let t₁ := (x / 4 + 1) * 4
              let t₂ := (x / 4 + 2) * 4
              have ht1_I : t₁ ∈ consecInterval x M := by
                simp only [consecInterval, Finset.mem_Icc]
                have := Nat.div_add_mod x 4; have := Nat.mod_lt x (by omega : 0 < 4)
                exact ⟨by omega, by omega⟩
              have ht2_I : t₂ ∈ consecInterval x M := by
                simp only [consecInterval, Finset.mem_Icc]
                have := Nat.div_add_mod x 4; have := Nat.mod_lt x (by omega : 0 < 4)
                exact ⟨by omega, by omega⟩
              have ht12 : t₁ ≠ t₂ := by dsimp [t₁, t₂]; omega
              have h4_t1 : 4 ∣ t₁ := dvd_mul_left 4 _
              have h4_t2 : 4 ∣ t₂ := dvd_mul_left 4 _
              have hnot_both : ¬ (t₁ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ) ∧ t₂ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ)) := by
                rintro ⟨hm_t1, hm_t2⟩
                have hcop4d : Nat.Coprime 4 d :=
                  (by decide : (4 : ℕ) = 2 ^ 2) ▸
                    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd2)
                have hm_dvd4 : ∀ t, t ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ) → 4 ∣ t →
                    ∃ j : ℕ, t = (k + j) * d ∧ 1 ≤ j ∧ j ≤ 4 ∧ 4 ∣ k + j := fun t ht h4t => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
                  rcases ht with rfl | rfl | rfl | rfl
                  · exact ⟨1, rfl, by omega, by omega, hcop4d.dvd_of_dvd_mul_right h4t⟩
                  · exact ⟨2, rfl, by omega, by omega, hcop4d.dvd_of_dvd_mul_right h4t⟩
                  · exact ⟨3, rfl, by omega, by omega, hcop4d.dvd_of_dvd_mul_right h4t⟩
                  · exact ⟨4, rfl, by omega, by omega, hcop4d.dvd_of_dvd_mul_right h4t⟩
                obtain ⟨i, hi_eq, hi1, hi4, h4i⟩ := hm_dvd4 t₁ hm_t1 h4_t1
                obtain ⟨j, hj_eq, hj1, hj4, h4j⟩ := hm_dvd4 t₂ hm_t2 h4_t2
                have hij : i ≠ j := fun h => ht12 (by rw [hi_eq, hj_eq, h])
                rcases lt_or_gt_of_ne hij with hlt | hgt
                · have hdv := Nat.dvd_sub h4j h4i
                  have hle := Nat.le_of_dvd (by omega) hdv
                  omega
                · have hdv := Nat.dvd_sub h4i h4j
                  have hle := Nat.le_of_dvd (by omega) hdv
                  omega
              rw [hS4_eq] at hnot_both
              by_cases ht1_in : t₁ ∈ ({b₁, b₂, b₃, w₁} : Finset ℕ)
              · have ht2_out : t₂ ∉ ({b₁, b₂, b₃, w₁} : Finset ℕ) := fun h => hnot_both ⟨ht1_in, h⟩
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht2_out
                exact ⟨t₂, ht2_I, ht2_out.1, ht2_out.2.1, ht2_out.2.2.1, ht2_out.2.2.2, h4_t2⟩
              · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht1_in
                exact ⟨t₁, ht1_I, ht1_in.1, ht1_in.2.1, ht1_in.2.2.1, ht1_in.2.2.2, h4_t1⟩
            have hex_w5 : ¬ (3 ∣ d) → ¬ (∃ b ∈ ({b₁, b₂, w₁} : Finset ℕ), 3 ∣ b) →
                ∃ w₅ ∈ consecInterval x M, w₅ ≠ b₁ ∧ w₅ ≠ b₂ ∧ w₅ ≠ b₃ ∧ w₅ ≠ w₁ ∧ 3 ∣ w₅ := by
              intro hnd3 hno3
              let t₁ := (x / 3 + 1) * 3
              let t₂ := (x / 3 + 2) * 3
              have ht1_I : t₁ ∈ consecInterval x M := by
                simp only [consecInterval, Finset.mem_Icc]
                have := Nat.div_add_mod x 3; have := Nat.mod_lt x (by omega : 0 < 3)
                exact ⟨by omega, by omega⟩
              have ht2_I : t₂ ∈ consecInterval x M := by
                simp only [consecInterval, Finset.mem_Icc]
                have := Nat.div_add_mod x 3; have := Nat.mod_lt x (by omega : 0 < 3)
                exact ⟨by omega, by omega⟩
              have ht12 : t₁ ≠ t₂ := by dsimp [t₁, t₂]; omega
              have h3_t1 : 3 ∣ t₁ := dvd_mul_left 3 _
              have h3_t2 : 3 ∣ t₂ := dvd_mul_left 3 _
              have hnot_both : ¬ (t₁ ∈ ({b₁, b₂, b₃, w₁} : Finset ℕ) ∧ t₂ ∈ ({b₁, b₂, b₃, w₁} : Finset ℕ)) := by
                rintro ⟨ht1, ht2⟩
                have h1_b3 : t₁ = b₃ := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at ht1
                  rcases ht1 with heq | heq | heq | heq
                  · exact absurd ⟨b₁, by simp, heq ▸ h3_t1⟩ hno3
                  · exact absurd ⟨b₂, by simp, heq ▸ h3_t1⟩ hno3
                  · exact heq
                  · exact absurd ⟨w₁, by simp, heq ▸ h3_t1⟩ hno3
                have h2_b3 : t₂ = b₃ := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at ht2
                  rcases ht2 with heq | heq | heq | heq
                  · exact absurd ⟨b₁, by simp, heq ▸ h3_t2⟩ hno3
                  · exact absurd ⟨b₂, by simp, heq ▸ h3_t2⟩ hno3
                  · exact heq
                  · exact absurd ⟨w₁, by simp, heq ▸ h3_t2⟩ hno3
                exact ht12 (h1_b3.trans h2_b3.symm)
              by_cases ht1_in : t₁ ∈ ({b₁, b₂, b₃, w₁} : Finset ℕ)
              · have ht2_out : t₂ ∉ ({b₁, b₂, b₃, w₁} : Finset ℕ) := fun h => hnot_both ⟨ht1_in, h⟩
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht2_out
                exact ⟨t₂, ht2_I, ht2_out.1, ht2_out.2.1, ht2_out.2.2.1, ht2_out.2.2.2, h3_t2⟩
              · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht1_in
                exact ⟨t₁, ht1_I, ht1_in.1, ht1_in.2.1, ht1_in.2.2.1, ht1_in.2.2.2, h3_t1⟩
            have hE2 : ∃ E₂ : Finset ℕ, E₂ ⊆ consecInterval x M ∧ E₂.card ≤ 1 ∧
                (∀ z ∈ E₂, z ≠ b₁ ∧ z ≠ b₂ ∧ z ≠ b₃ ∧ z ≠ w₁) ∧
                (¬ (2 ∣ d) → ∃ w₄ ∈ E₂, 4 ∣ w₄) := by
              by_cases h2d : 2 ∣ d
              · exact ⟨∅, Finset.empty_subset _, by simp, by simp, fun h => absurd h2d h⟩
              · obtain ⟨w₄, hw4_I, h41, h42, h43, h4w, h4_dvd⟩ := hex_w4 h2d
                exact ⟨{w₄}, by simpa, by simp, fun z hz => by simp at hz; subst hz; exact ⟨h41, h42, h43, h4w⟩,
                  fun _ => ⟨w₄, Finset.mem_singleton_self w₄, h4_dvd⟩⟩
            have hE3 : ∃ E₃ : Finset ℕ, E₃ ⊆ consecInterval x M ∧ E₃.card ≤ 1 ∧
                (∀ z ∈ E₃, z ≠ b₁ ∧ z ≠ b₂ ∧ z ≠ b₃ ∧ z ≠ w₁) ∧
                (¬ (3 ∣ d) → (∃ b ∈ ({b₁, b₂, w₁} : Finset ℕ), 3 ∣ b) ∨ ∃ w₅ ∈ E₃, 3 ∣ w₅) := by
              by_cases h3d : 3 ∣ d
              · exact ⟨∅, Finset.empty_subset _, by simp, by simp, fun h => absurd h3d h⟩
              · by_cases hex3 : ∃ b ∈ ({b₁, b₂, w₁} : Finset ℕ), 3 ∣ b
                · exact ⟨∅, Finset.empty_subset _, by simp, by simp, fun _ => Or.inl hex3⟩
                · obtain ⟨w₅, hw5_I, h51, h52, h53, h5w, h5_dvd⟩ := hex_w5 h3d hex3
                  exact ⟨{w₅}, by simpa, by simp, fun z hz => by simp at hz; subst hz; exact ⟨h51, h52, h53, h5w⟩,
                    fun _ => Or.inr ⟨w₅, Finset.mem_singleton_self w₅, h5_dvd⟩⟩
            obtain ⟨E₂, hE2_I, hE2_c, hE2_disj, hE2_prop⟩ := hE2
            obtain ⟨E₃, hE3_I, hE3_c, hE3_disj, hE3_prop⟩ := hE3
            let B0 : Finset ℕ := {b₁, b₂, b₃, w₁}
            let B : Finset ℕ := B0 ∪ (E₂ ∪ E₃)
            have hB_card : B.card ≤ 6 := by
              have h1 : B.card ≤ B0.card + (E₂ ∪ E₃).card := Finset.card_union_le B0 (E₂ ∪ E₃)
              have h2 : (E₂ ∪ E₃).card ≤ E₂.card + E₃.card := Finset.card_union_le E₂ E₃
              have h0 : B0.card ≤ 4 := card_finset_le_four_5 b₁ b₂ b₃ w₁
              omega
            refine ⟨B, ?_, hB_card, isCover_of_prime_factorization_5 hA0 ?_ fun p hp => ?_⟩
            · intro z hz; simp only [B, Finset.mem_union] at hz
              rcases hz with hz0 | hz2 | hz3
              · simp only [B0, Finset.mem_insert, Finset.mem_singleton] at hz0
                rcases hz0 with rfl | rfl | rfl | rfl <;> assumption
              · exact hE2_I hz2
              · exact hE3_I hz3
            · intro z hz; simp only [B, Finset.mem_union] at hz
              rcases hz with hz0 | hz2 | hz3
              · simp only [B0, Finset.mem_insert, Finset.mem_singleton] at hz0
                rcases hz0 with rfl | rfl | rfl | rfl <;> assumption
              · exact (pos_of_mem_consecInterval (hE2_I hz2)).ne'
              · exact (pos_of_mem_consecInterval (hE3_I hz3)).ne'
            · have hB0_sum : ∑ b ∈ B0, b.factorization p = b₁.factorization p + b₂.factorization p +
                  b₃.factorization p + w₁.factorization p := by
                dsimp [B0]
                rw [Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm]),
                    Finset.sum_insert (by simp [hb23, hw1_b2.symm]),
                    Finset.sum_insert (by simp [hw1_b3.symm]), Finset.sum_singleton]; ring
              have hB0_le_B : ∑ b ∈ B0, b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
                Finset.sum_le_sum_of_subset Finset.subset_union_left
              have hdisj : Disjoint B0 (E₂ ∪ E₃) := Finset.disjoint_left.mpr fun z hz0 hzE => by
                dsimp only [B0] at hz0
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz0
                simp only [Finset.mem_union] at hzE
                rcases hzE with h2 | h3
                · have ⟨a1, a2, a3, a4⟩ := hE2_disj z h2
                  rcases hz0 with rfl | rfl | rfl | rfl
                  · exact a1 rfl
                  · exact a2 rfl
                  · exact a3 rfl
                  · exact a4 rfl
                · have ⟨a1, a2, a3, a4⟩ := hE3_disj z h3
                  rcases hz0 with rfl | rfl | rfl | rfl
                  · exact a1 rfl
                  · exact a2 rfl
                  · exact a3 rfl
                  · exact a4 rfl
              rw [hsumA_eq p]
              by_cases hpd : p ∣ d
              · have hp_ns3 : ¬ (p ∣ s₃) := fun h => by
                  have := Nat.dvd_gcd hpd h
                  rw [hgcd_d_s3] at this
                  exact Nat.Prime.ne_one hp (Nat.eq_one_of_dvd_one this)
                have hs3_0 : s₃.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ns3
                have := h_sum_4d p
                have := hsum4b p
                have := h24_fac_le p
                omega
              · have hd_0 : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpd
                have hs3_le : s₃.factorization p ≤ b₃.factorization p := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
                by_cases hp2 : p = 2
                · subst hp2
                  obtain ⟨w₄, hw4_E2, h4_w4⟩ := hE2_prop hpd
                  have hw4_B : w₄ ∈ B := Finset.mem_union_right B0 (Finset.mem_union_left E₃ hw4_E2)
                  have hw4_0 : w₄ ≠ 0 := (pos_of_mem_consecInterval (hE2_I hw4_E2)).ne'
                  have hw4_fac : 2 ≤ w₄.factorization 2 := by
                    have h4_fac := fac_le_of_dvd_5 hw4_0 h4_w4 (p := 2)
                    have h2_4 : (4 : ℕ).factorization 2 = 2 := by
                      have : (4 : ℕ) = 2 ^ 2 := by norm_num
                      rw [this, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
                          Nat.Prime.factorization_self Nat.prime_two]
                    omega
                  -- Check `b₁, b₂, w₁`: since `{m₁, m₂, m₃, m₄} = {b₁, b₂, b₃, w₁}` and two of `mᵢ` are even, at least one of `{b₁, b₂, w₁}` is even.
                  have heven_in : ∃ b ∈ ({b₁, b₂, w₁} : Finset ℕ), 2 ∣ b := by
                    rcases Nat.even_or_odd (k + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
                    · have hm1_e : 2 ∣ m₁ := dvd_mul_of_dvd_left ⟨r, by omega⟩ d
                      have hm3_e : 2 ∣ m₃ := dvd_mul_of_dvd_left ⟨r + 1, by omega⟩ d
                      by_cases hmb1 : m₁ = b₃
                      · have hm3_ne : m₃ ≠ b₃ := by intro h; exact (hm12.trans hm23).ne (by omega : m₁ = m₃)
                        have hm3_in := hS4_eq ▸ (by simp : m₃ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ))
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hm3_in
                        rcases hm3_in with heq | heq | heq | heq
                        · exact ⟨b₁, by simp, heq ▸ hm3_e⟩
                        · exact ⟨b₂, by simp, heq ▸ hm3_e⟩
                        · exact absurd heq hm3_ne
                        · exact ⟨w₁, by simp, heq ▸ hm3_e⟩
                      · have hm1_in := hS4_eq ▸ (by simp : m₁ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ))
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hm1_in
                        rcases hm1_in with heq | heq | heq | heq
                        · exact ⟨b₁, by simp, heq ▸ hm1_e⟩
                        · exact ⟨b₂, by simp, heq ▸ hm1_e⟩
                        · exact absurd heq hmb1
                        · exact ⟨w₁, by simp, heq ▸ hm1_e⟩
                    · have hm2_e : 2 ∣ m₂ := dvd_mul_of_dvd_left ⟨r + 1, by omega⟩ d
                      have hm4_e : 2 ∣ m₄ := dvd_mul_of_dvd_left ⟨r + 2, by omega⟩ d
                      by_cases hmb2 : m₂ = b₃
                      · have hm4_ne : m₄ ≠ b₃ := by intro h; exact (hm23.trans hm34).ne (by omega : m₂ = m₄)
                        have hm4_in := hS4_eq ▸ (by simp : m₄ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ))
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hm4_in
                        rcases hm4_in with heq | heq | heq | heq
                        · exact ⟨b₁, by simp, heq ▸ hm4_e⟩
                        · exact ⟨b₂, by simp, heq ▸ hm4_e⟩
                        · exact absurd heq hm4_ne
                        · exact ⟨w₁, by simp, heq ▸ hm4_e⟩
                      · have hm2_in := hS4_eq ▸ (by simp : m₂ ∈ ({m₁, m₂, m₃, m₄} : Finset ℕ))
                        simp only [Finset.mem_insert, Finset.mem_singleton] at hm2_in
                        rcases hm2_in with heq | heq | heq | heq
                        · exact ⟨b₁, by simp, heq ▸ hm2_e⟩
                        · exact ⟨b₂, by simp, heq ▸ hm2_e⟩
                        · exact absurd heq hmb2
                        · exact ⟨w₁, by simp, heq ▸ hm2_e⟩
                  have h1_fac2 : 1 ≤ b₁.factorization 2 + b₂.factorization 2 + w₁.factorization 2 := by
                    obtain ⟨b, hb_in, h2b⟩ := heven_in
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hb_in
                    rcases hb_in with heq | heq | heq
                    · have := fac_le_of_dvd_5 hb1_0 (heq ▸ h2b) (p := 2)
                      rw [Nat.Prime.factorization_self Nat.prime_two] at this; omega
                    · have := fac_le_of_dvd_5 hb2_0 (heq ▸ h2b) (p := 2)
                      rw [Nat.Prime.factorization_self Nat.prime_two] at this; omega
                    · have := fac_le_of_dvd_5 hw1_0 (heq ▸ h2b) (p := 2)
                      rw [Nat.Prime.factorization_self Nat.prime_two] at this; omega
                  have hsub5 : ({b₁, b₂, b₃, w₁, w₄} : Finset ℕ) ⊆ B := by
                    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                    rcases hz with rfl | rfl | rfl | rfl | rfl
                    · exact Finset.mem_union_left _ (by simp [B0])
                    · exact Finset.mem_union_left _ (by simp [B0])
                    · exact Finset.mem_union_left _ (by simp [B0])
                    · exact Finset.mem_union_left _ (by simp [B0])
                    · exact hw4_B
                  have hw4_d := hE2_disj w₄ hw4_E2
                  have hsum5_le := Finset.sum_le_sum_of_subset hsub5 (f := fun b => b.factorization 2)
                  rw [Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw4_d.1.symm]),
                      Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw4_d.2.1.symm]),
                      Finset.sum_insert (by simp [hw1_b3.symm, hw4_d.2.2.1.symm]),
                      Finset.sum_insert (by simp [hw4_d.2.2.2.symm]), Finset.sum_singleton] at hsum5_le
                  have h24_2 : (24 : ℕ).factorization 2 = 3 := by
                    have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
                    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply,
                        Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
                        Nat.Prime.factorization_self Nat.prime_two]
                    have : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
                    omega
                  have := h_sum_4d 2
                  omega
                · by_cases hp3 : p = 3
                  · subst hp3
                    have h24_3 : (24 : ℕ).factorization 3 = 1 := by
                      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
                      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.coe_add, Pi.add_apply,
                          Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
                          Nat.Prime.factorization_self Nat.prime_three]
                      have : (2 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
                      omega
                    have hb3_extra3 : b₃.factorization 3 + 1 ≤ ∑ b ∈ B, b.factorization 3 := by
                      rcases hE3_prop hpd with ⟨b, hb_in, h3b⟩ | ⟨w₅, hw5_E3, h3_w5⟩
                      · have hfac1 : 1 ≤ b₁.factorization 3 + b₂.factorization 3 + w₁.factorization 3 := by
                          simp only [Finset.mem_insert, Finset.mem_singleton] at hb_in
                          rcases hb_in with heq | heq | heq
                          · have := fac_le_of_dvd_5 hb1_0 (heq ▸ h3b) (p := 3)
                            rw [Nat.Prime.factorization_self Nat.prime_three] at this; omega
                          · have := fac_le_of_dvd_5 hb2_0 (heq ▸ h3b) (p := 3)
                            rw [Nat.Prime.factorization_self Nat.prime_three] at this; omega
                          · have := fac_le_of_dvd_5 hw1_0 (heq ▸ h3b) (p := 3)
                            rw [Nat.Prime.factorization_self Nat.prime_three] at this; omega
                        omega
                      · have hw5_B : w₅ ∈ B := Finset.mem_union_right B0 (Finset.mem_union_right E₂ hw5_E3)
                        have hw5_0 : w₅ ≠ 0 := (pos_of_mem_consecInterval (hE3_I hw5_E3)).ne'
                        have hw5_fac : 1 ≤ w₅.factorization 3 := by
                          have := fac_le_of_dvd_5 hw5_0 h3_w5 (p := 3)
                          rwa [Nat.Prime.factorization_self Nat.prime_three] at this
                        have hsub2 : ({b₃, w₅} : Finset ℕ) ⊆ B := by
                          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                          rcases hz with rfl | rfl
                          · exact Finset.mem_union_left _ (by simp [B0])
                          · exact hw5_B
                        have hw5_d := hE3_disj w₅ hw5_E3
                        have hsum2 := Finset.sum_le_sum_of_subset hsub2 (f := fun b => b.factorization 3)
                        rw [Finset.sum_insert (by simp [hw5_d.2.2.1.symm]), Finset.sum_singleton] at hsum2
                        omega
                    have := h_sum_4d 3
                    omega
                  · have h24_0 : (24 : ℕ).factorization p = 0 :=
                      Nat.factorization_eq_zero_of_not_dvd fun h => by
                        have : p ∣ 2 ^ 3 * 3 := h
                        rcases hp.dvd_mul.mp this with h2 | h3
                        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
                        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
                    have := h_sum_4d p
                    have hsum4_pos : b₃.factorization p ≤ ∑ b ∈ B0, b.factorization p := by
                      rw [hB0_sum]; omega
                    omega
        · obtain ⟨w₃, hw3_flt, hw3_not⟩ := Finset.not_subset.mp hsub_d
          rw [Finset.mem_filter] at hw3_flt
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw3_not
          rcases hw3_not with ⟨hw3_1, hw3_2, hw3_3, hw3_w1⟩
          have hw3_I : w₃ ∈ consecInterval x M := hw3_flt.1
          have hd_w3 : d ∣ w₃ := hw3_flt.2
          have hw3_0 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw3_I).ne'
          refine ⟨{b₁, b₂, b₃, w₁, w₃}, ?_, card_finset_le_five_5 b₁ b₂ b₃ w₁ w₃ |>.trans (by omega), ?_⟩
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
          · refine isCover_of_prime_factorization_5 hA0 ?_ fun p _ => ?_
            · intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
            · rw [hsumA_eq p,
                  Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, Ne.symm hw3_1]),
                  Finset.sum_insert (by simp [hb23, hw1_b2.symm, Ne.symm hw3_2]),
                  Finset.sum_insert (by simp [hw1_b3.symm, Ne.symm hw3_3]),
                  Finset.sum_insert (by simp [Ne.symm hw3_w1]), Finset.sum_singleton]
              have h1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
              have h2 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
              have h3 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
              have h4 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
              have h5 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
              have h6 := fac_le_of_dvd_5 hw1_0 hg1_w1 (p := p)
              have h7 := fac_le_of_dvd_5 hw1_0 hg2_w2 (p := p)
              have h8 := fac_le_of_dvd_5 hw3_0 hd_w3 (p := p)
              have hm1 : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
                fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne' (p := p)
              have hm2 : g₂.factorization p = min (u₂.factorization p) (s₂.factorization p) :=
                fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne' (p := p)
              have hmd : d.factorization p = min (g₁.factorization p) (g₂.factorization p) :=
                fac_gcd_eq_min_5 hg1_p.ne' hg2_p.ne' (p := p)
              omega
      · refine ⟨{b₁, b₂, b₃, w₁, w₂}, ?_, card_finset_le_five_5 b₁ b₂ b₃ w₁ w₂ |>.trans (by omega), ?_⟩
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
        · refine isCover_of_prime_factorization_5 hA0 ?_ fun p _ => ?_
          · intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
          · rw [hsumA_eq p,
                Finset.sum_insert (by simp [hb12, hb13, hw1_b1.symm, hw2_b1.symm]),
                Finset.sum_insert (by simp [hb23, hw1_b2.symm, hw2_b2.symm]),
                Finset.sum_insert (by simp [hw1_b3.symm, hw2_b3.symm]),
                Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
            have h1 := fac_le_of_dvd_5 hb1_0 hu1_b1 (p := p)
            have h2 := fac_le_of_dvd_5 hb1_0 hs1_b1 (p := p)
            have h3 := fac_le_of_dvd_5 hb2_0 hu2_b2 (p := p)
            have h4 := fac_le_of_dvd_5 hb2_0 hs2_b2 (p := p)
            have h5 := fac_le_of_dvd_5 hb3_0 hs3_b3 (p := p)
            have h6 := fac_le_of_dvd_5 hw1_0 hg1_w1 (p := p)
            have h7 := fac_le_of_dvd_5 hw2_0 hg2_w2 (p := p)
            have hm1 : g₁.factorization p = min (u₁.factorization p) (s₁.factorization p) :=
              fac_gcd_eq_min_5 hu1_p.ne' hs1_p.ne' (p := p)
            have hm2 : g₂.factorization p = min (u₂.factorization p) (s₂.factorization p) :=
              fac_gcd_eq_min_5 hu2_p.ne' hs2_p.ne' (p := p)
            omega

/-! ## Part 4: `r = 3` Reduction and Unconditional Settlement `g(5) = 6` -/

lemma erdos708_upper_five_of_matching_three
    {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hS_sub : S ⊆ A) (hS_card : S.card = 3)
    (f : ℕ → ℕ)
    (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a)
    (hf_inj : Set.InjOn f S)
    (hnot4 : ¬ HasMatching A x M 4) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨s₁, s₂, s₃, hs12, hs13, hs23, hS_eq⟩ := Finset.card_eq_three.mp hS_card
  have hU_card : (A \ S).card = 2 := by
    have := Finset.card_sdiff_add_card_inter A S
    rw [Finset.inter_eq_right.mpr hS_sub, hA_card, hS_card] at this
    omega
  obtain ⟨u₁, u₂, h12, hU_eq⟩ := Finset.card_eq_two.mp hU_card
  have hu1_in : u₁ ∈ A \ S := by rw [hU_eq]; simp
  have hu2_in : u₂ ∈ A \ S := by rw [hU_eq]; simp
  have hs1_in : s₁ ∈ S := by rw [hS_eq]; simp
  have hs2_in : s₂ ∈ S := by rw [hS_eq]; simp
  have hs3_in : s₃ ∈ S := by rw [hS_eq]; simp
  have hu1_A : u₁ ∈ A := (Finset.mem_sdiff.mp hu1_in).1
  have hu2_A : u₂ ∈ A := (Finset.mem_sdiff.mp hu2_in).1
  have hu1_nS : u₁ ∉ S := (Finset.mem_sdiff.mp hu1_in).2
  have hu2_nS : u₂ ∉ S := (Finset.mem_sdiff.mp hu2_in).2
  have h1s1 : u₁ ≠ s₁ := fun h => hu1_nS (h ▸ hs1_in)
  have h1s2 : u₁ ≠ s₂ := fun h => hu1_nS (h ▸ hs2_in)
  have h1s3 : u₁ ≠ s₃ := fun h => hu1_nS (h ▸ hs3_in)
  have h2s1 : u₂ ≠ s₁ := fun h => hu2_nS (h ▸ hs1_in)
  have h2s2 : u₂ ≠ s₂ := fun h => hu2_nS (h ▸ hs2_in)
  have h2s3 : u₂ ≠ s₃ := fun h => hu2_nS (h ▸ hs3_in)
  have hA_eq : A = {u₁, u₂, s₁, s₂, s₃} := by
    apply Finset.Subset.antisymm
    · intro z hz
      by_cases hzS : z ∈ S
      · rw [hS_eq] at hzS; simp only [Finset.mem_insert, Finset.mem_singleton] at hzS ⊢
        rcases hzS with rfl | rfl | rfl <;> simp
      · have hzU : z ∈ A \ S := Finset.mem_sdiff.mpr ⟨hz, hzS⟩
        rw [hU_eq] at hzU; simp only [Finset.mem_insert, Finset.mem_singleton] at hzU ⊢
        rcases hzU with rfl | rfl <;> simp
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hu1_A
      · exact hu2_A
      · exact hS_sub hs1_in
      · exact hS_sub hs2_in
      · exact hS_sub hs3_in
  let b₁ := f s₁; let b₂ := f s₂; let b₃ := f s₃
  have hb₁_I : b₁ ∈ consecInterval x M := hf_mem s₁ hs1_in
  have hb₂_I : b₂ ∈ consecInterval x M := hf_mem s₂ hs2_in
  have hb₃_I : b₃ ∈ consecInterval x M := hf_mem s₃ hs3_in
  have hs1_b1 : s₁ ∣ b₁ := hf_dvd s₁ hs1_in
  have hs2_b2 : s₂ ∣ b₂ := hf_dvd s₂ hs2_in
  have hs3_b3 : s₃ ∣ b₃ := hf_dvd s₃ hs3_in
  have hb12 : b₁ ≠ b₂ := fun h => hs12 (hf_inj hs1_in hs2_in h)
  have hb13 : b₁ ≠ b₃ := fun h => hs13 (hf_inj hs1_in hs3_in h)
  have hb23 : b₂ ≠ b₃ := fun h => hs23 (hf_inj hs2_in hs3_in h)
  have hall_hit : ∀ u ∈ A \ S, ∀ m ∈ consecInterval x M, u ∣ m → m ∈ ({b₁, b₂, b₃} : Finset ℕ) := by
    intro u huU m hm_I hum
    by_contra hm_not
    have huA : u ∈ A := (Finset.mem_sdiff.mp huU).1
    have hu_nS : u ∉ S := (Finset.mem_sdiff.mp huU).2
    let S' := insert u S
    let f' : ℕ → ℕ := fun a => if a = u then m else f a
    have hS'_sub : S' ⊆ A := Finset.insert_subset_iff.mpr ⟨huA, hS_sub⟩
    have hS'_card : S'.card = 4 := by rw [Finset.card_insert_of_notMem hu_nS, hS_card]
    apply hnot4
    refine ⟨S', hS'_sub, hS'_card, f', ?_, ?_, ?_⟩
    · intro a ha; rw [Finset.mem_insert] at ha
      rcases ha with ha_eq | haS
      · rw [ha_eq]; simpa [f'] using hm_I
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        simpa [f', hne] using hf_mem a haS
    · intro a ha; rw [Finset.mem_insert] at ha
      rcases ha with ha_eq | haS
      · rw [ha_eq]; simpa [f'] using hum
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        simpa [f', hne] using hf_dvd a haS
    · intro a ha b hb hab
      simp only [Finset.mem_coe, S', Finset.mem_insert] at ha hb
      rcases ha with ha_eq | haS <;> rcases hb with hb_eq | hbS
      · exact ha_eq.trans hb_eq.symm
      · have hne : b ≠ u := fun h => hu_nS (h ▸ hbS)
        rw [ha_eq] at hab
        simp only [f', ite_true, if_neg hne] at hab
        have hfb_in : f b ∈ ({b₁, b₂, b₃} : Finset ℕ) := by
          rw [hS_eq] at hbS; simp only [Finset.mem_insert, Finset.mem_singleton] at hbS
          rcases hbS with rfl | rfl | rfl <;> simp [b₁, b₂, b₃]
        exact False.elim (hm_not (hab ▸ hfb_in))
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        rw [hb_eq] at hab
        simp only [f', ite_true, if_neg hne] at hab
        have hfa_in : f a ∈ ({b₁, b₂, b₃} : Finset ℕ) := by
          rw [hS_eq] at haS; simp only [Finset.mem_insert, Finset.mem_singleton] at haS
          rcases haS with rfl | rfl | rfl <;> simp [b₁, b₂, b₃]
        exact False.elim (hm_not (hab.symm ▸ hfa_in))
      · have hnea : a ≠ u := fun h => hu_nS (h ▸ haS)
        have hneb : b ≠ u := fun h => hu_nS (h ▸ hbS)
        simp only [f', if_neg hnea, if_neg hneb] at hab
        exact hf_inj haS hbS hab
  have hu1_p : 0 < u₁ := hA_pos u₁ hu1_A
  have hu2_p : 0 < u₂ := hA_pos u₂ hu2_A
  have hu1_M : u₁ ≤ M := hA_le u₁ hu1_A
  have hu2_M : u₂ ≤ M := hA_le u₂ hu2_A
  obtain ⟨m₁, hm1_I, hu1_m1⟩ := exists_multiple_in_consecInterval x u₁ M hu1_p hu1_M
  obtain ⟨m₂, hm2_I, hu2_m2⟩ := exists_multiple_in_consecInterval x u₂ M hu2_p hu2_M
  have hm1_hit := hall_hit u₁ hu1_in m₁ hm1_I hu1_m1
  have hm2_hit := hall_hit u₂ hu2_in m₂ hm2_I hu2_m2
  have run_two : ∀ x₁ y₁ x₂ y₂ y₃ c₁ c₂ c₃ : ℕ,
      A = {x₁, y₁, x₂, y₂, y₃} →
      x₁ ≠ y₁ → x₁ ≠ x₂ → x₁ ≠ y₂ → x₁ ≠ y₃ →
      y₁ ≠ x₂ → y₁ ≠ y₂ → y₁ ≠ y₃ →
      x₂ ≠ y₂ → x₂ ≠ y₃ → y₂ ≠ y₃ →
      c₁ ∈ consecInterval x M → c₂ ∈ consecInterval x M → c₃ ∈ consecInterval x M →
      c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      x₁ ∣ c₁ → y₁ ∣ c₁ → x₂ ∣ c₂ → y₂ ∣ c₂ → y₃ ∣ c₃ →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B :=
    fun x₁ y₁ x₂ y₂ y₃ c₁ c₂ c₃ hAe a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        hc1 hc2 hc3 hc12 hc13 hc23 hx1c hy1c hx2c hy2c hy3c =>
      cover_six_of_r3_two_slots hAe a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
        hA_pos hA_le hAgcd hM7 hc1 hc2 hc3 hc12 hc13 hc23 hx1c hy1c hx2c hy2c hy3c
  have h_all_same : ∀ c₁ c₂ c₃ q₁ q₂ q₃ : ℕ,
      A = {u₁, u₂, q₁, q₂, q₃} →
      u₁ ≠ u₂ → u₁ ≠ q₁ → u₁ ≠ q₂ → u₁ ≠ q₃ →
      u₂ ≠ q₁ → u₂ ≠ q₂ → u₂ ≠ q₃ →
      q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
      c₁ ∈ consecInterval x M → c₂ ∈ consecInterval x M → c₃ ∈ consecInterval x M →
      c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      u₁ ∣ c₁ → u₂ ∣ c₁ → q₁ ∣ c₁ → q₂ ∣ c₂ → q₃ ∣ c₃ →
      (consecInterval x M).filter (fun b => u₁ ∣ b) ⊆ {c₁} →
      (consecInterval x M).filter (fun b => u₂ ∣ b) ⊆ {c₁} →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro c₁ c₂ c₃ q₁ q₂ q₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
      hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1c hq2c hq3c hsubu1 hsubu2
    have hM2u1 : M < 2 * u₁ := lt_two_mul_of_unique_multiple_in_consecInterval hu1_p hc1 hu1c
      (fun b hb hdb => by simpa using hsubu1 (Finset.mem_filter.mpr ⟨hb, hdb⟩))
    have hM2u2 : M < 2 * u₂ := lt_two_mul_of_unique_multiple_in_consecInterval hu2_p hc1 hu2c
      (fun b hb hdb => by simpa using hsubu2 (Finset.mem_filter.mpr ⟨hb, hdb⟩))
    by_cases hsubq1 : (consecInterval x M).filter (fun b => q₁ ∣ b) ⊆ {c₁}
    · have hM2q1 : M < 2 * q₁ := lt_two_mul_of_unique_multiple_in_consecInterval
        (hA_pos q₁ (by rw [hAe]; simp)) hc1 hq1c
        (fun b hb hdb => by simpa using hsubq1 (Finset.mem_filter.mpr ⟨hb, hdb⟩))
      exact cover_six_of_r3_same_slot hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
        hA_pos hA_le hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1c hq2c hq3c hM2u1 hM2u2 hM2q1
    · obtain ⟨c₁', hflt, hc1'_not⟩ := Finset.not_subset.mp hsubq1
      rw [Finset.mem_filter] at hflt
      have hc1'_I : c₁' ∈ consecInterval x M := hflt.1
      have hq1_c1' : q₁ ∣ c₁' := hflt.2
      have hc1'_ne1 : c₁' ≠ c₁ := by simpa using hc1'_not
      by_cases hc1'_c2 : c₁' = c₂
      · rw [hc1'_c2] at hq1_c1'
        exact run_two u₁ u₂ q₁ q₂ q₃ c₁ c₂ c₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
          hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1_c1' hq2c hq3c
      · by_cases hc1'_c3 : c₁' = c₃
        · rw [hc1'_c3] at hq1_c1'
          have hAe_sw : A = {u₁, u₂, q₁, q₃, q₂} := by
            rw [hAe]; apply Finset.Subset.antisymm
            · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
              rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
            · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
              rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          exact run_two u₁ u₂ q₁ q₃ q₂ c₁ c₃ c₂ hAe_sw a12 a1q1 a1q3 a1q2 a2q1 a2q3 a2q2 aq13 aq12 aq23.symm
            hc1 hc3 hc2 hc13 hc12 hc23.symm hu1c hu2c hq1_c1' hq3c hq2c
        · -- `c₁' ∉ {c₁, c₂, c₃}`: extend `{q₁ ↦ c₁', q₂ ↦ c₂, q₃ ↦ c₃}` by `u₁ ↦ c₁` ⇒ 4-matching!
          have hq1_A : q₁ ∈ A := by rw [hAe]; simp
          have hq2_A : q₂ ∈ A := by rw [hAe]; simp
          have hq3_A : q₃ ∈ A := by rw [hAe]; simp
          let S' : Finset ℕ := {u₁, q₁, q₂, q₃}
          let f' : ℕ → ℕ := fun a =>
            if a = u₁ then c₁ else if a = q₁ then c₁' else if a = q₂ then c₂ else c₃
          exfalso; apply hnot4
          refine ⟨S', ?_, ?_, f', ?_, ?_, ?_⟩
          · intro z hz; simp only [S', Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption
          · dsimp [S']
            rw [Finset.card_insert_of_notMem (by simp [a1q1, a1q2, a1q3]),
                Finset.card_insert_of_notMem (by simp [aq12, aq13]),
                Finset.card_insert_of_notMem (by simp [aq23]), Finset.card_singleton]
          · intro a ha; simp only [S', Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · simpa [f'] using hc1
            · simpa [f', a1q1.symm] using hc1'_I
            · simpa [f', a1q2.symm, aq12.symm] using hc2
            · simpa [f', a1q3.symm, aq13.symm, aq23.symm] using hc3
          · intro a ha; simp only [S', Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · simpa [f'] using hu1c
            · simpa [f', a1q1.symm] using hq1_c1'
            · simpa [f', a1q2.symm, aq12.symm] using hq2c
            · simpa [f', a1q3.symm, aq13.symm, aq23.symm] using hq3c
          · intro a ha b hb hab; simp only [Finset.mem_coe, S', Finset.mem_insert, Finset.mem_singleton] at ha hb
            rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
              simp only [f', ite_true, if_neg a1q1.symm, if_neg a1q2.symm, if_neg a1q3.symm,
                if_neg aq12.symm, if_neg aq13.symm, if_neg aq23.symm] at hab
            all_goals first
              | rfl
              | exact absurd hab hc1'_ne1.symm
              | exact absurd hab hc12
              | exact absurd hab hc13
              | exact absurd hab hc1'_ne1
              | exact absurd hab hc1'_c2
              | exact absurd hab hc1'_c3
              | exact absurd hab hc12.symm
              | exact absurd hab (Ne.symm hc1'_c2)
              | exact absurd hab hc23
              | exact absurd hab hc13.symm
              | exact absurd hab (Ne.symm hc1'_c3)
              | exact absurd hab hc23.symm
  have h_one_diff : ∀ q₁ q₂ q₃ c₁ c₂ c₃ : ℕ,
      A = {u₁, u₂, q₁, q₂, q₃} →
      u₁ ≠ u₂ → u₁ ≠ q₁ → u₁ ≠ q₂ → u₁ ≠ q₃ →
      u₂ ≠ q₁ → u₂ ≠ q₂ → u₂ ≠ q₃ →
      q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
      c₁ ∈ consecInterval x M → c₂ ∈ consecInterval x M → c₃ ∈ consecInterval x M →
      c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      u₁ ∣ c₁ → u₂ ∣ c₂ → q₁ ∣ c₁ → q₂ ∣ c₂ → q₃ ∣ c₃ →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro q₁ q₂ q₃ c₁ c₂ c₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
      hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1c hq2c hq3c
    have hAe2 : A = {u₁, q₁, u₂, q₂, q₃} := by
      rw [hAe]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact run_two u₁ q₁ u₂ q₂ q₃ c₁ c₂ c₃ hAe2 a1q1 a12 a1q2 a1q3 a2q1.symm aq12 aq13
      a2q2 a2q3 aq23 hc1 hc2 hc3 hc12 hc13 hc23 hu1c hq1c hu2c hq2c hq3c
  have h_same_or_diff : ∀ q₁ q₂ q₃ c₁ c₂ c₃ : ℕ,
      A = {u₁, u₂, q₁, q₂, q₃} →
      u₁ ≠ u₂ → u₁ ≠ q₁ → u₁ ≠ q₂ → u₁ ≠ q₃ →
      u₂ ≠ q₁ → u₂ ≠ q₂ → u₂ ≠ q₃ →
      q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
      c₁ ∈ consecInterval x M → c₂ ∈ consecInterval x M → c₃ ∈ consecInterval x M →
      c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
      u₁ ∣ c₁ → u₂ ∣ c₁ → q₁ ∣ c₁ → q₂ ∣ c₂ → q₃ ∣ c₃ →
      (∀ z ∈ consecInterval x M, u₁ ∣ z → z ∈ ({c₁, c₂, c₃} : Finset ℕ)) →
      (∀ z ∈ consecInterval x M, u₂ ∣ z → z ∈ ({c₁, c₂, c₃} : Finset ℕ)) →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro q₁ q₂ q₃ c₁ c₂ c₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
      hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1c hq2c hq3c hhit1 hhit2
    by_cases hsubu1 : (consecInterval x M).filter (fun b => u₁ ∣ b) ⊆ {c₁}
    · by_cases hsubu2 : (consecInterval x M).filter (fun b => u₂ ∣ b) ⊆ {c₁}
      · exact h_all_same c₁ c₂ c₃ q₁ q₂ q₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
          hc1 hc2 hc3 hc12 hc13 hc23 hu1c hu2c hq1c hq2c hq3c hsubu1 hsubu2
      · obtain ⟨m', hflt, hm'_not⟩ := Finset.not_subset.mp hsubu2
        rw [Finset.mem_filter] at hflt
        have hm'_hit := hhit2 m' hflt.1 hflt.2
        have hm'_ne : m' ≠ c₁ := by simpa using hm'_not
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm'_hit
        rcases hm'_hit with hm'_c1 | hm'_c2 | hm'_c3
        · exact absurd hm'_c1 hm'_ne
        · rw [hm'_c2] at hflt
          exact h_one_diff q₁ q₂ q₃ c₁ c₂ c₃ hAe a12 a1q1 a1q2 a1q3 a2q1 a2q2 a2q3 aq12 aq13 aq23
            hc1 hc2 hc3 hc12 hc13 hc23 hu1c hflt.2 hq1c hq2c hq3c
        · rw [hm'_c3] at hflt
          have hAe_sw : A = {u₁, u₂, q₁, q₃, q₂} := by
            rw [hAe]; apply Finset.Subset.antisymm
            · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
              rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
            · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
              rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          exact h_one_diff q₁ q₃ q₂ c₁ c₃ c₂ hAe_sw a12 a1q1 a1q3 a1q2 a2q1 a2q3 a2q2 aq13 aq12 aq23.symm
            hc1 hc3 hc2 hc13 hc12 hc23.symm hu1c hflt.2 hq1c hq3c hq2c
    · obtain ⟨m', hflt, hm'_not⟩ := Finset.not_subset.mp hsubu1
      rw [Finset.mem_filter] at hflt
      have hm'_hit := hhit1 m' hflt.1 hflt.2
      have hm'_ne : m' ≠ c₁ := by simpa using hm'_not
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'_hit
      rcases hm'_hit with hm'_c1 | hm'_c2 | hm'_c3
      · exact absurd hm'_c1 hm'_ne
      · rw [hm'_c2] at hflt
        have hAe_sw : A = {u₁, u₂, q₂, q₁, q₃} := by
          rw [hAe]; apply Finset.Subset.antisymm
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        have hAe2 : A = {u₁, q₂, u₂, q₁, q₃} := by
          rw [hAe_sw]; apply Finset.Subset.antisymm
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        exact run_two u₁ q₂ u₂ q₁ q₃ c₂ c₁ c₃ hAe2 a1q2 a12 a1q1 a1q3 a2q2.symm aq12.symm aq23
          a2q1 a2q3 aq13 hc2 hc1 hc3 hc12.symm hc23 hc13 hflt.2 hq2c hu2c hq1c hq3c
      · rw [hm'_c3] at hflt
        have hAe2 : A = {u₁, q₃, u₂, q₁, q₂} := by
          rw [hAe]; apply Finset.Subset.antisymm
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
        exact run_two u₁ q₃ u₂ q₁ q₂ c₃ c₁ c₂ hAe2 a1q3 a12 a1q1 a1q2 a2q3.symm aq13.symm aq23.symm
          a2q1 a2q2 aq12 hc3 hc1 hc2 hc13.symm hc23.symm hc12 hflt.2 hq3c hu2c hq1c hq2c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm1_hit hm2_hit
  rcases hm1_hit with hm1_eq | hm1_eq | hm1_eq <;> rcases hm2_hit with hm2_eq | hm2_eq | hm2_eq
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    exact h_same_or_diff s₁ s₂ s₃ b₁ b₂ b₃ hA_eq h12 h1s1 h1s2 h1s3 h2s1 h2s2 h2s3 hs12 hs13 hs23
      hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hu1_m1 hu2_m2 hs1_b1 hs2_b2 hs3_b3
      (fun z hz hdz => hall_hit u₁ hu1_in z hz hdz)
      (fun z hz hdz => hall_hit u₂ hu2_in z hz hdz)
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    exact h_one_diff s₁ s₂ s₃ b₁ b₂ b₃ hA_eq h12 h1s1 h1s2 h1s3 h2s1 h2s2 h2s3 hs12 hs13 hs23
      hb₁_I hb₂_I hb₃_I hb12 hb13 hb23 hu1_m1 hu2_m2 hs1_b1 hs2_b2 hs3_b3
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₁, s₃, s₂} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_one_diff s₁ s₃ s₂ b₁ b₃ b₂ hA_sw h12 h1s1 h1s3 h1s2 h2s1 h2s3 h2s2 hs13 hs12 hs23.symm
      hb₁_I hb₃_I hb₂_I hb13 hb12 hb23.symm hu1_m1 hu2_m2 hs1_b1 hs3_b3 hs2_b2
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₂, s₁, s₃} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_one_diff s₂ s₁ s₃ b₂ b₁ b₃ hA_sw h12 h1s2 h1s1 h1s3 h2s2 h2s1 h2s3 hs12.symm hs23 hs13
      hb₂_I hb₁_I hb₃_I hb12.symm hb23 hb13 hu1_m1 hu2_m2 hs2_b2 hs1_b1 hs3_b3
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₂, s₁, s₃} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_same_or_diff s₂ s₁ s₃ b₂ b₁ b₃ hA_sw h12 h1s2 h1s1 h1s3 h2s2 h2s1 h2s3 hs12.symm hs23 hs13
      hb₂_I hb₁_I hb₃_I hb12.symm hb23 hb13 hu1_m1 hu2_m2 hs2_b2 hs1_b1 hs3_b3
      (fun z hz hdz => by have := hall_hit u₁ hu1_in z hz hdz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; rcases this with rfl | rfl | rfl <;> simp)
      (fun z hz hdz => by have := hall_hit u₂ hu2_in z hz hdz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; rcases this with rfl | rfl | rfl <;> simp)
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₂, s₃, s₁} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_one_diff s₂ s₃ s₁ b₂ b₃ b₁ hA_sw h12 h1s2 h1s3 h1s1 h2s2 h2s3 h2s1 hs23 hs12.symm hs13.symm
      hb₂_I hb₃_I hb₁_I hb23 hb12.symm hb13.symm hu1_m1 hu2_m2 hs2_b2 hs3_b3 hs1_b1
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₃, s₁, s₂} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_one_diff s₃ s₁ s₂ b₃ b₁ b₂ hA_sw h12 h1s3 h1s1 h1s2 h2s3 h2s1 h2s2 hs13.symm hs23.symm hs12
      hb₃_I hb₁_I hb₂_I hb13.symm hb23.symm hb12 hu1_m1 hu2_m2 hs3_b3 hs1_b1 hs2_b2
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₃, s₂, s₁} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_one_diff s₃ s₂ s₁ b₃ b₂ b₁ hA_sw h12 h1s3 h1s2 h1s1 h2s3 h2s2 h2s1 hs23.symm hs13.symm hs12.symm
      hb₃_I hb₂_I hb₁_I hb23.symm hb13.symm hb12.symm hu1_m1 hu2_m2 hs3_b3 hs2_b2 hs1_b1
  · rw [hm1_eq] at hu1_m1; rw [hm2_eq] at hu2_m2
    have hA_sw : A = {u₁, u₂, s₃, s₁, s₂} := by
      rw [hA_eq]; apply Finset.Subset.antisymm
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
    exact h_same_or_diff s₃ s₁ s₂ b₃ b₁ b₂ hA_sw h12 h1s3 h1s1 h1s2 h2s3 h2s1 h2s2 hs13.symm hs23.symm hs12
      hb₃_I hb₁_I hb₂_I hb13.symm hb23.symm hb12 hu1_m1 hu2_m2 hs3_b3 hs1_b1 hs2_b2
      (fun z hz hdz => by have := hall_hit u₁ hu1_in z hz hdz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; rcases this with rfl | rfl | rfl <;> simp)
      (fun z hz hdz => by have := hall_hit u₂ hu2_in z hz hdz; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; rcases this with rfl | rfl | rfl <;> simp)

private lemma erdos708_upper_five_strong :
    ∀ (M : ℕ) (A : Finset ℕ) (hA : A.Nonempty),
      A.max' hA = M → A.card = 5 → (∀ a ∈ A, 0 < a) →
      ∀ x : ℕ, ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro A hA hM_eq hA_card hA_pos x
    by_cases hM6 : M ≤ 6
    · subst hM_eq
      exact erdos708_upper_of_max_le_5 hA hA_pos hM6 x
    · have hM7 : 7 ≤ M := by omega
      have hM_sup : M = A.sup id := by rw [sup_id_eq_max'_5 hA, hM_eq]
      have hA_le : ∀ a ∈ A, a ≤ M := fun a ha => by
        rw [← hM_eq]; exact Finset.le_max' A a ha
      let g := A.gcd id
      have hg_dvd : ∀ a ∈ A, g ∣ a := fun a ha => Finset.gcd_dvd ha
      have hg_pos : 0 < g := by
        by_contra h0
        have hg0 : g = 0 := by omega
        obtain ⟨a₀, ha₀⟩ := hA
        have h1 : 0 ∣ a₀ := hg0 ▸ hg_dvd a₀ ha₀
        have := zero_dvd_iff.mp h1
        have := hA_pos a₀ ha₀
        omega
      by_cases hg1 : g = 1
      · obtain ⟨S, f, hSA, hS1, hS5, hf_mem, hf_dvd, hf_inj, hnot⟩ :=
          exists_max_matching_full (x := x) hA hA_pos hA_le
        have hS5' : S.card ≤ 5 := by omega
        rcases Nat.lt_or_eq_of_le hS5' with hlt5 | heq5
        · rcases Nat.lt_or_eq_of_le (by omega : S.card ≤ 4) with hlt4 | heq4
          · rcases Nat.lt_or_eq_of_le (by omega : S.card ≤ 3) with hlt3 | heq3
            · rcases Nat.lt_or_eq_of_le (by omega : S.card ≤ 2) with hlt2 | heq2
              · have heq1 : S.card = 1 := by omega
                have hnot2 : ¬ HasMatching A x M 2 := by simpa [heq1] using hnot
                exact erdos708_upper_five_of_matching_one hA_card hA_pos hA_le hg1 hM7
                  hSA heq1 hf_mem hf_dvd hnot2
              · have hnot3 : ¬ HasMatching A x M 3 := by simpa [heq2] using hnot
                exact erdos708_upper_five_of_matching_two hA_card hA_pos hA_le hg1 hM7
                  hSA heq2 f hf_mem hf_dvd hf_inj hnot3
            · have hnot4 : ¬ HasMatching A x M 4 := by simpa [heq3] using hnot
              exact erdos708_upper_five_of_matching_three hA_card hA_pos hA_le hg1 hM7
                hSA heq3 f hf_mem hf_dvd hf_inj hnot4
          · exact (erdos708_upper_n_of_matching_pred (by omega : 1 ≤ 5) hA_card hA_pos hA_le
              hSA (by omega : S.card = 5 - 1) f hf_mem hf_dvd hf_inj).imp fun B ⟨hBI, hBc, hBcov⟩ =>
                ⟨hBI, hBc.trans (by omega), hBcov⟩
        · have hSA_eq : S = A := Finset.eq_of_subset_of_card_le hSA (by omega)
          let B := S.image f
          refine ⟨B, ?_, ?_, ?_⟩
          · intro b hb; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb; exact hf_mem a ha
          · exact (Finset.card_image_le).trans (by omega)
          · refine isCover_of_prime_factorization_5 (fun a ha => (hA_pos a ha).ne') ?_ fun p _ => ?_
            · intro b hb; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
              exact (pos_of_mem_consecInterval (hf_mem a ha)).ne'
            · rw [← hSA_eq, Finset.sum_image (fun a ha b hb hab => hf_inj ha hb hab)]
              exact Finset.sum_le_sum fun a ha =>
                fac_le_of_dvd_5 (pos_of_mem_consecInterval (hf_mem a ha)).ne' (hf_dvd a ha) (p := p)
      · have hg_gt1 : 1 < g := by omega
        let A' := A.image (· / g)
        have hA'_ne : A'.Nonempty := hA.image _
        have hA'_pos : ∀ a' ∈ A', 0 < a' := by
          intro a' ha'
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
          have hga := hg_dvd a ha
          exact Nat.div_pos (Nat.le_of_dvd (hA_pos a ha) hga) hg_pos
        have hA'_card : A'.card = 5 := by
          rw [Finset.card_image_of_injOn]
          · exact hA_card
          · intro a ha b hb hab
            have h1 := Nat.mul_div_cancel' (hg_dvd a ha)
            have h2 := Nat.mul_div_cancel' (hg_dvd b hb)
            dsimp only at hab
            rw [hab] at h1
            omega
        have hA'_max : A'.max' hA'_ne = M / g := by
          apply le_antisymm
          · refine Finset.max'_le A' hA'_ne _ fun a' ha' => ?_
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
            exact Nat.div_le_div_right (hA_le a ha)
          · have hM_in : M ∈ A := hM_eq ▸ Finset.max'_mem A hA
            exact Finset.le_max' A' (M / g) (Finset.mem_image.mpr ⟨M, hM_in, rfl⟩)
        have hMg_lt : M / g < M := Nat.div_lt_self (by omega) hg_gt1
        have hcov' := ih (M / g) hMg_lt A' hA'_ne hA'_max hA'_card hA'_pos (x / g)
        exact erdos708_gcd_reduction hA hA_pos hM_sup hg_pos hg_dvd (by omega : A.card ≤ 6) hcov'

theorem erdos708_upper_five : SatisfiesBound 5 6 := by
  intro A hA hval x
  exact erdos708_upper_five_strong (A.max' hA) A hA rfl hval.1
    (fun a ha => lt_of_lt_of_le (by omega) (hval.2 a ha)) x

theorem erdos708_exact_five : SatisfiesBound 5 6 ∧ ¬ SatisfiesBound 5 5 :=
  ⟨erdos708_upper_five, erdos708_lower_five⟩

end Erdos708
