import Erdos708.G6R4

/-!
# PPL 176 (Erdős Problem #708) — Complete Unconditional Proof of `g(4) = 5`

This module proves:
1. **`erdos708_upper_four : SatisfiesBound 4 5`** (`g(4) ≤ 5`):
   Every 4-element valid set `A ⊆ [2, ∞)` has a cover `B` of size `≤ 5` in every
   consecutive interval `consecInterval x (A.max' hA)`.
2. **`erdos708_exact_four : SatisfiesBound 4 5 ∧ ¬ SatisfiesBound 4 4`**:
   Combined with `erdos708_lower_four` from `Erdos708.Lower`, settles `g(4) = 5` cleanly
   in pure elementary algebra (zero small-`M` enumeration, zero custom axioms, `leanchecker: PASS`).
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Elementary Helper Lemmas -/

private lemma sup_id_eq_max'4 {A : Finset ℕ} (hA : A.Nonempty) :
    A.sup id = A.max' hA := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact Finset.le_max' A a ha
  · exact Finset.le_sup (f := id) (Finset.max'_mem A hA)

private lemma erdos708_upper_of_max_le {A : Finset ℕ} (hA : A.Nonempty)
    (hA_pos : ∀ a ∈ A, 0 < a) {k : ℕ} (hle : A.max' hA ≤ k) (x : ℕ) :
    ∃ B ⊆ consecInterval x (A.max' hA), B.card ≤ k ∧ IsCover A B := by
  obtain ⟨B, hBI, hBcard, hcov⟩ :=
    erdos708_trivial_max_bound (fun a ha => hA_pos a ha) x
  have hsup : A.sup id = A.max' hA := sup_id_eq_max'4 hA
  rw [hsup] at hBI hBcard
  exact ⟨B, hBI, le_trans hBcard hle, hcov⟩

private lemma isCover_of_prime_factorization {A B : Finset ℕ}
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    (hfac : ∀ p : ℕ, p.Prime → ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B, b.factorization p) :
    IsCover A B :=
  prod_dvd_prod_of_factorization_le hA0 hB0 hfac

private lemma fac_le_of_dvd {d w p : ℕ} (hw : w ≠ 0) (hdw : d ∣ w) :
    d.factorization p ≤ w.factorization p := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp at hdw; exact absurd hdw hw
  · exact (Nat.factorization_le_iff_dvd hd_pos.ne' hw).mpr hdw p

private lemma fac_gcd_eq_min {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.gcd a b).factorization p = min (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_gcd ha hb]
  rfl

private lemma prime_dvd_of_fac_ne_zero {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    (h : a.factorization p ≠ 0) : p ∣ a := by
  have h1 : 1 ≤ a.factorization p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
  simpa [pow_one] using (hp.pow_dvd_iff_le_factorization ha).mpr h1

private lemma one_le_fac_of_dvd {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) (h : p ∣ a) :
    1 ≤ a.factorization p :=
  (hp.pow_dvd_iff_le_factorization ha).mp (by simpa [pow_one] using h)

private lemma card_finset_le_three (a b c : ℕ) : ({a, b, c} : Finset ℕ).card ≤ 3 := by
  have h1 := Finset.card_insert_le a {b, c}
  have h2 := Finset.card_insert_le b {c}
  simp only [Finset.card_singleton] at h2
  omega

private lemma card_finset_le_four (a b c d : ℕ) : ({a, b, c, d} : Finset ℕ).card ≤ 4 := by
  have h1 := Finset.card_insert_le a {b, c, d}
  have h2 := card_finset_le_three b c d
  omega

private lemma card_finset_le_five (a b c d e : ℕ) : ({a, b, c, d, e} : Finset ℕ).card ≤ 5 := by
  have h1 := Finset.card_insert_le a {b, c, d, e}
  have h2 := card_finset_le_four b c d e
  omega

private lemma lcm_triple_eq (a b c : ℕ) :
    ({a, b, c} : Finset ℕ).lcm id = Nat.lcm (Nat.lcm a b) c := by
  rw [Finset.lcm_insert, Finset.lcm_insert, Finset.lcm_singleton]
  simp only [id_eq, normalize_eq]
  change Nat.lcm a (Nat.lcm b c) = Nat.lcm (Nat.lcm a b) c
  exact (Nat.lcm_assoc a b c).symm

private lemma coprime_factorization_zero {a b p : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) (hcop : Nat.Coprime a b) :
    a.factorization p = 0 ∨ b.factorization p = 0 := by
  by_contra hboth
  push Not at hboth
  have hd1 : p ∣ a := prime_dvd_of_fac_ne_zero hp ha.ne' hboth.1
  have hd2 : p ∣ b := prime_dvd_of_fac_ne_zero hp hb.ne' hboth.2
  have hdp : p ∣ Nat.gcd a b := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hdp
  exact hp.not_dvd_one hdp

private lemma two_mul_gcd_le_4 {a b M : ℕ} (ha : 0 < a) (hab : a < b) (hbM : b ≤ M) :
    2 * Nat.gcd a b ≤ M := by
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a b
  have hle : Nat.gcd a b ≤ a := Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)
  have hq2 : 2 ≤ q := by
    by_contra hlt
    have hq_le1 : q ≤ 1 := by omega
    have hb_le_g : b ≤ Nat.gcd a b := by
      calc b = Nat.gcd a b * q := hq
        _ ≤ Nat.gcd a b * 1 := Nat.mul_le_mul_left _ hq_le1
        _ = Nat.gcd a b := mul_one _
    omega
  have h1 : 2 * Nat.gcd a b ≤ Nat.gcd a b * q := by rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq2
  omega

private lemma three_mul_le_of_three_dvd_distinct {d a₁ a₂ a₃ M : ℕ}
    (hd : 0 < d) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (h1_pos : 0 < a₁) (h2_pos : 0 < a₂) (h3_pos : 0 < a₃)
    (h1M : a₁ ≤ M) (h2M : a₂ ≤ M) (h3M : a₃ ≤ M)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) :
    3 * d ≤ M := by
  have hT := card_mul_le_of_forall_dvd (T := ({a₁, a₂, a₃} : Finset ℕ)) (d := d) (M := M) hd (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨h1_pos, h1M, hd1⟩
    · exact ⟨h2_pos, h2M, hd2⟩
    · exact ⟨h3_pos, h3M, hd3⟩)
  have hcard : ({a₁, a₂, a₃} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  rw [hcard] at hT
  exact hT

private lemma finset_lcm_ne_zero {T : Finset ℕ} (hT : ∀ a ∈ T, a ≠ 0) : T.lcm id ≠ 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s _ ih =>
    rw [Finset.lcm_insert]
    simp only [id_eq]
    exact Nat.lcm_ne_zero (hT a (Finset.mem_insert_self a s))
      (ih (fun b hb => hT b (Finset.mem_insert_of_mem hb)))

private lemma three_mul_le_of_two_gt_half {d a₁ a₂ M : ℕ}
    (_hd : 0 < d) (h12 : a₁ < a₂) (ha₂M : a₂ ≤ M) (hM2 : M < 2 * a₁)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) :
    3 * d ≤ M := by
  obtain ⟨q₁, hq1⟩ := hd1
  obtain ⟨q₂, hq2⟩ := hd2
  have hq1_lt : q₁ < q₂ := by
    by_contra hle
    have h21 : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega)
    omega
  have hq1_pos : 0 < q₁ := by
    by_contra h0
    have hq1_0 : q₁ = 0 := by omega
    rw [hq1_0, mul_zero] at hq1
    omega
  have hq1_ge2 : 2 ≤ q₁ := by
    by_contra hlt2
    have hq1_le1 : q₁ ≤ 1 := by omega
    have hq2_ge2 : 2 ≤ q₂ := by omega
    have h1d : d * q₁ ≤ d * 1 := Nat.mul_le_mul_left d hq1_le1
    have h2d : 2 * d ≤ d * q₂ := by rw [mul_comm 2]; exact Nat.mul_le_mul_left d hq2_ge2
    omega
  have hq2_ge3 : 3 ≤ q₂ := by omega
  have h3d : 3 * d ≤ d * q₂ := by rw [mul_comm 3]; exact Nat.mul_le_mul_left d hq2_ge3
  omega

private lemma three_mul_le_of_two_ne_gt_half {d a₁ a₂ M : ℕ}
    (hd : 0 < d) (hne : a₁ ≠ a₂) (ha₁M : a₁ ≤ M) (ha₂M : a₂ ≤ M)
    (hM1 : M < 2 * a₁) (hM2 : M < 2 * a₂) (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) :
    3 * d ≤ M := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact three_mul_le_of_two_gt_half hd h ha₂M hM1 hd1 hd2
  · exact three_mul_le_of_two_gt_half hd h ha₁M hM2 hd2 hd1

private lemma five_mul_le_of_three_gt_half {d a₁ a₂ a₃ M : ℕ}
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

private lemma five_mul_le_of_three_distinct_gt_half {d a₁ a₂ a₃ M : ℕ}
    (hd : 0 < d) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃)
    (h1M : a₁ ≤ M) (h2M : a₂ ≤ M) (h3M : a₃ ≤ M)
    (hM1 : M < 2 * a₁) (hM2 : M < 2 * a₂) (hM3 : M < 2 * a₃)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) :
    5 * d ≤ M := by
  rcases lt_or_gt_of_ne h12 with h | h <;>
  rcases lt_or_gt_of_ne h13 with h' | h' <;>
  rcases lt_or_gt_of_ne h23 with h'' | h''
  · exact five_mul_le_of_three_gt_half hd h h'' h3M hM1 hd1 hd2 hd3
  · exact five_mul_le_of_three_gt_half hd h' h'' h2M hM1 hd1 hd3 hd2
  · omega
  · exact five_mul_le_of_three_gt_half hd h' h h2M hM3 hd3 hd1 hd2
  · exact five_mul_le_of_three_gt_half hd h h' h3M hM2 hd2 hd1 hd3
  · omega
  · exact five_mul_le_of_three_gt_half hd h'' h' h1M hM2 hd2 hd3 hd1
  · exact five_mul_le_of_three_gt_half hd h'' h h1M hM3 hd3 hd2 hd1

private lemma eq_pair_of_two_dvd_lt_three_mul {d a₁ a₂ M : ℕ}
    (_hd : 0 < d) (ha₁ : 0 < a₁) (h12 : a₁ < a₂) (ha₂M : a₂ ≤ M) (hM3 : M < 3 * d)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) :
    a₁ = d ∧ a₂ = 2 * d := by
  obtain ⟨q₁, hq1⟩ := hd1
  obtain ⟨q₂, hq2⟩ := hd2
  have hq1_pos : 1 ≤ q₁ := by
    by_contra h0
    have : q₁ = 0 := by omega
    rw [this, mul_zero] at hq1
    omega
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

private lemma exists_avoiding_of_not_subset_pair {x M d b₁ b₂ : ℕ}
    (hnot : ¬ ((consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂})) :
    ∃ w ∈ consecInterval x M, w ≠ b₁ ∧ w ≠ b₂ ∧ d ∣ w := by
  obtain ⟨w, hw_flt, hw_not⟩ := Finset.not_subset.mp hnot
  rw [Finset.mem_filter] at hw_flt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw_not
  exact ⟨w, hw_flt.1, hw_not.1, hw_not.2, hw_flt.2⟩

private lemma dvd_pair_of_filter_subset_pair {x M d b₁ b₂ : ℕ}
    (hd : 0 < d) (h2d : 2 * d ≤ M) (hb12 : b₁ ≠ b₂)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂}) :
    d ∣ b₁ ∧ d ∣ b₂ ∧ M < 3 * d := by
  have hcard_ge2 : 2 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 2 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h2d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  have hpair_card : ({b₁, b₂} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hb12]), Finset.card_singleton]
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

private lemma dvd_second_of_filter_subset_triple {x M d b₁ b₂ w₁ : ℕ}
    (hd : 0 < d) (h3d : 3 * d ≤ M)
    (hsub : (consecInterval x M).filter (fun b => d ∣ b) ⊆ {b₁, b₂, w₁}) :
    d ∣ b₂ := by
  have hcard_ge3 : 3 ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card := by
    have h1 := card_multiples_Icc_ge x M d hd
    have h2 : 3 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr h3d
    change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at h1
    omega
  have hle3 : ({b₁, b₂, w₁} : Finset ℕ).card ≤ 3 := card_finset_le_three b₁ b₂ w₁
  have heq : (consecInterval x M).filter (fun b => d ∣ b) = {b₁, b₂, w₁} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm2 : b₂ ∈ (consecInterval x M).filter (fun b => d ∣ b) := by
    rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self b₂ {w₁})
  exact (Finset.mem_filter.mp hm2).2

/-! ## Part 2: Matching Size `r = 2` Closure (`erdos708_upper_four_of_matching_two`) -/

private lemma cover_four_r2_shape22_one_sub {A : Finset ℕ} {x M t₁ t₂ v₁ v₂ c₁ c₂ w₂ : ℕ}
    (hA_eq : A = {t₁, t₂, v₁, v₂})
    (ht12 : t₁ ≠ t₂) (ht1v1 : t₁ ≠ v₁) (ht1v2 : t₁ ≠ v₂)
    (ht2v1 : t₂ ≠ v₁) (ht2v2 : t₂ ≠ v₂) (hv12 : v₁ ≠ v₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hc12 : c₁ ≠ c₂) (hc₁_I : c₁ ∈ consecInterval x M) (hc₂_I : c₂ ∈ consecInterval x M)
    (ht1_c1 : t₁ ∣ c₁) (hv1_c1 : v₁ ∣ c₁) (ht2_c2 : t₂ ∣ c₂) (hv2_c2 : v₂ ∣ c₂)
    (hsub : (consecInterval x M).filter (fun b => Nat.gcd t₁ v₁ ∣ b) ⊆ {c₁, c₂})
    (hw₂_I : w₂ ∈ consecInterval x M) (hw2_c1 : w₂ ≠ c₁) (hw2_c2 : w₂ ≠ c₂)
    (hg2_w2 : Nat.gcd t₂ v₂ ∣ w₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have ht1_pos : 0 < t₁ := hA_pos t₁ (by rw [hA_eq]; simp)
  have ht2_pos : 0 < t₂ := hA_pos t₂ (by rw [hA_eq]; simp)
  have hv1_pos : 0 < v₁ := hA_pos v₁ (by rw [hA_eq]; simp)
  have hv2_pos : 0 < v₂ := hA_pos v₂ (by rw [hA_eq]; simp)
  have ht1_M : t₁ ≤ M := hA_le t₁ (by rw [hA_eq]; simp)
  have ht2_M : t₂ ≤ M := hA_le t₂ (by rw [hA_eq]; simp)
  have hv1_M : v₁ ≤ M := hA_le v₁ (by rw [hA_eq]; simp)
  have hv2_M : v₂ ≤ M := hA_le v₂ (by rw [hA_eq]; simp)
  let gg₁ := Nat.gcd t₁ v₁
  let gg₂ := Nat.gcd t₂ v₂
  have hgg₁_pos : 0 < gg₁ := Nat.gcd_pos_of_pos_left v₁ ht1_pos
  have hgg₂_pos : 0 < gg₂ := Nat.gcd_pos_of_pos_left v₂ ht2_pos
  have h2gg₁ : 2 * gg₁ ≤ M := by
    rcases lt_or_gt_of_ne ht1v1 with h | h
    · exact two_mul_gcd_le_4 ht1_pos h hv1_M
    · rw [show gg₁ = Nat.gcd v₁ t₁ from Nat.gcd_comm t₁ v₁]
      exact two_mul_gcd_le_4 hv1_pos h ht1_M
  have hgg₁_c2 : gg₁ ∣ c₂ := (dvd_pair_of_filter_subset_pair hgg₁_pos h2gg₁ hc12 hsub).2.1
  let e₁ := Nat.gcd gg₁ t₂
  let e₂ := Nat.gcd gg₁ v₂
  have he₁_pos : 0 < e₁ := Nat.gcd_pos_of_pos_left t₂ hgg₁_pos
  have he₂_pos : 0 < e₂ := Nat.gcd_pos_of_pos_left v₂ hgg₁_pos
  have h3e₁ : 3 * e₁ ≤ M := three_mul_le_of_three_dvd_distinct he₁_pos ht1v1 ht12 ht2v1.symm
    ht1_pos hv1_pos ht2_pos ht1_M hv1_M ht2_M
    (dvd_trans (Nat.gcd_dvd_left gg₁ t₂) (Nat.gcd_dvd_left t₁ v₁))
    (dvd_trans (Nat.gcd_dvd_left gg₁ t₂) (Nat.gcd_dvd_right t₁ v₁))
    (Nat.gcd_dvd_right gg₁ t₂)
  have h3e₂ : 3 * e₂ ≤ M := three_mul_le_of_three_dvd_distinct he₂_pos ht1v1 ht1v2 hv12
    ht1_pos hv1_pos hv2_pos ht1_M hv1_M hv2_M
    (dvd_trans (Nat.gcd_dvd_left gg₁ v₂) (Nat.gcd_dvd_left t₁ v₁))
    (dvd_trans (Nat.gcd_dvd_left gg₁ v₂) (Nat.gcd_dvd_right t₁ v₁))
    (Nat.gcd_dvd_right gg₁ v₂)
  have hpair_card : ({c₁, c₂} : Finset ℕ).card + 1 ≤ 3 := by
    have h1 := Finset.card_insert_le c₁ {c₂}
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨wa, hwa_I, hwa_not, he1_wa⟩ := exists_avoiding_multiple_in_consecInterval x M e₁ {c₁, c₂}
    he₁_pos (le_trans (Nat.mul_le_mul_right e₁ hpair_card) h3e₁)
  obtain ⟨wb, hwb_I, hwb_not, he2_wb⟩ := exists_avoiding_multiple_in_consecInterval x M e₂ {c₁, c₂}
    he₂_pos (le_trans (Nat.mul_le_mul_right e₂ hpair_card) h3e₂)
  have hwa_c1 : wa ≠ c₁ := fun h => hwa_not (by simp [h])
  have hwa_c2 : wa ≠ c₂ := fun h => hwa_not (by simp [h])
  have hwb_c1 : wb ≠ c₁ := fun h => hwb_not (by simp [h])
  have hwb_c2 : wb ≠ c₂ := fun h => hwb_not (by simp [h])
  let B : Finset ℕ := {c₁, c₂, wa, wb, w₂}
  have hBI : B ⊆ consecInterval x M := by
    intro b hb
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hBcard : B.card ≤ 5 := card_finset_le_five c₁ c₂ wa wb w₂
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hc₁0 : c₁ ≠ 0 := (pos_of_mem_consecInterval hc₁_I).ne'
  have hc₂0 : c₂ ≠ 0 := (pos_of_mem_consecInterval hc₂_I).ne'
  have hwa0 : wa ≠ 0 := (pos_of_mem_consecInterval hwa_I).ne'
  have hwb0 : wb ≠ 0 := (pos_of_mem_consecInterval hwb_I).ne'
  have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hcop_g12 : Nat.Coprime gg₁ gg₂ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd : Nat.gcd gg₁ gg₂ ∣ A.gcd id := by
      apply Finset.dvd_gcd
      intro a ha
      rw [hA_eq] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · exact dvd_trans (Nat.gcd_dvd_left gg₁ gg₂) (Nat.gcd_dvd_left t₁ v₁)
      · exact dvd_trans (Nat.gcd_dvd_right gg₁ gg₂) (Nat.gcd_dvd_left t₂ v₂)
      · exact dvd_trans (Nat.gcd_dvd_left gg₁ gg₂) (Nat.gcd_dvd_right t₁ v₁)
      · exact dvd_trans (Nat.gcd_dvd_right gg₁ gg₂) (Nat.gcd_dvd_right t₂ v₂)
    rw [hAgcd] at hd
    exact Nat.dvd_one.mp hd
  refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
  intro p hp
  have hsumA_eq : ∑ a ∈ A, a.factorization p =
      t₁.factorization p + t₂.factorization p + v₁.factorization p + v₂.factorization p := by
    rw [hA_eq, Finset.sum_insert (by simp [ht12, ht1v1, ht1v2]),
        Finset.sum_insert (by simp [ht2v1, ht2v2]), Finset.sum_insert (by simp [hv12]),
        Finset.sum_singleton]
    ring
  rw [hsumA_eq]
  have hc1_1 : t₁.factorization p ≤ c₁.factorization p := fac_le_of_dvd hc₁0 ht1_c1
  have hc1_2 : v₁.factorization p ≤ c₁.factorization p := fac_le_of_dvd hc₁0 hv1_c1
  have hc2_t2 : t₂.factorization p ≤ c₂.factorization p := fac_le_of_dvd hc₂0 ht2_c2
  have hc2_v2 : v₂.factorization p ≤ c₂.factorization p := fac_le_of_dvd hc₂0 hv2_c2
  have hc2_g1 : gg₁.factorization p ≤ c₂.factorization p := fac_le_of_dvd hc₂0 hgg₁_c2
  have hwa_e1 : e₁.factorization p ≤ wa.factorization p := fac_le_of_dvd hwa0 he1_wa
  have hwb_e2 : e₂.factorization p ≤ wb.factorization p := fac_le_of_dvd hwb0 he2_wb
  have hw2_g2 : gg₂.factorization p ≤ w₂.factorization p := fac_le_of_dvd hw20 hg2_w2
  rw [fac_gcd_eq_min ht1_pos.ne' hv1_pos.ne'] at hc2_g1
  rw [fac_gcd_eq_min hgg₁_pos.ne' ht2_pos.ne', fac_gcd_eq_min ht1_pos.ne' hv1_pos.ne'] at hwa_e1
  rw [fac_gcd_eq_min hgg₁_pos.ne' hv2_pos.ne', fac_gcd_eq_min ht1_pos.ne' hv1_pos.ne'] at hwb_e2
  rw [fac_gcd_eq_min ht2_pos.ne' hv2_pos.ne'] at hw2_g2
  rcases coprime_factorization_zero hgg₁_pos hgg₂_pos hp hcop_g12 with hg1_0 | hg2_0
  · rw [fac_gcd_eq_min ht1_pos.ne' hv1_pos.ne'] at hg1_0
    have hsub3 : ({c₁, c₂, w₂} : Finset ℕ) ⊆ B := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
    have hleB : ∑ b ∈ ({c₁, c₂, w₂} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
      Finset.sum_le_sum_of_subset hsub3
    rw [Finset.sum_insert (by simp [hc12, hw2_c1.symm]),
        Finset.sum_insert (by simp [hw2_c2.symm]), Finset.sum_singleton] at hleB
    omega
  · rw [fac_gcd_eq_min ht2_pos.ne' hv2_pos.ne'] at hg2_0
    have hg2_cases : t₂.factorization p = 0 ∨ v₂.factorization p = 0 := by omega
    rcases hg2_cases with ht2_0 | hv2_0
    · have hsub3 : ({c₁, c₂, wb} : Finset ℕ) ⊆ B := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
      have hleB : ∑ b ∈ ({c₁, c₂, wb} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
        Finset.sum_le_sum_of_subset hsub3
      rw [Finset.sum_insert (by simp [hc12, hwb_c1.symm]),
          Finset.sum_insert (by simp [hwb_c2.symm]), Finset.sum_singleton] at hleB
      omega
    · have hsub3 : ({c₁, c₂, wa} : Finset ℕ) ⊆ B := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
      have hleB : ∑ b ∈ ({c₁, c₂, wa} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
        Finset.sum_le_sum_of_subset hsub3
      rw [Finset.sum_insert (by simp [hc12, hwa_c1.symm]),
          Finset.sum_insert (by simp [hwa_c2.symm]), Finset.sum_singleton] at hleB
      omega

private lemma cover_four_r2_shape22 {A : Finset ℕ} {x M s₁ s₂ u₁ u₂ b₁ b₂ : ℕ}
    (hA_eq : A = {s₁, s₂, u₁, u₂})
    (hs12 : s₁ ≠ s₂) (hs1u1 : s₁ ≠ u₁) (hs1u2 : s₁ ≠ u₂)
    (hs2u1 : s₂ ≠ u₁) (hs2u2 : s₂ ≠ u₂) (hu12 : u₁ ≠ u₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (hM6 : 6 ≤ M)
    (hb12 : b₁ ≠ b₂) (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M)
    (hs₁_b1 : s₁ ∣ b₁) (hs₂_b2 : s₂ ∣ b₂) (hu₁_b1 : u₁ ∣ b₁) (hu₂_b2 : u₂ ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have hs₁_pos : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hs₂_pos : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs₁_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hs₂_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  have hu₁_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hu₂_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  let g₁ := Nat.gcd s₁ u₁
  let g₂ := Nat.gcd s₂ u₂
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left u₁ hs₁_pos
  have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left u₂ hs₂_pos
  have hcop_g12 : Nat.Coprime g₁ g₂ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd : Nat.gcd g₁ g₂ ∣ A.gcd id := by
      apply Finset.dvd_gcd
      intro a ha
      rw [hA_eq] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · exact dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left s₁ u₁)
      · exact dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left s₂ u₂)
      · exact dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right s₁ u₁)
      · exact dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right s₂ u₂)
    rw [hAgcd] at hd
    exact Nat.dvd_one.mp hd
  have h2g₁ : 2 * g₁ ≤ M := by
    rcases lt_or_gt_of_ne hs1u1 with h | h
    · exact two_mul_gcd_le_4 hs₁_pos h hu₁_M
    · rw [show g₁ = Nat.gcd u₁ s₁ from Nat.gcd_comm s₁ u₁]
      exact two_mul_gcd_le_4 hu₁_pos h hs₁_M
  have h2g₂ : 2 * g₂ ≤ M := by
    rcases lt_or_gt_of_ne hs2u2 with h | h
    · exact two_mul_gcd_le_4 hs₂_pos h hu₂_M
    · rw [show g₂ = Nat.gcd u₂ s₂ from Nat.gcd_comm s₂ u₂]
      exact two_mul_gcd_le_4 hu₂_pos h hs₂_M
  by_cases hsub1 : (consecInterval x M).filter (fun b => g₁ ∣ b) ⊆ {b₁, b₂}
  · by_cases hsub2 : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₁, b₂}
    · -- Both subsets hold: `{s₁, u₁} = {g₁, 2 * g₁}` and `{s₂, u₂} = {g₂, 2 * g₂}`
      obtain ⟨_, hg₁_b2, hM3_g1⟩ := dvd_pair_of_filter_subset_pair hg₁_pos h2g₁ hb12 hsub1
      obtain ⟨hg₂_b1, _, hM3_g2⟩ := dvd_pair_of_filter_subset_pair hg₂_pos h2g₂ hb12 hsub2
      have hpair1 : (s₁ = g₁ ∧ u₁ = 2 * g₁) ∨ (u₁ = g₁ ∧ s₁ = 2 * g₁) := by
        rcases lt_or_gt_of_ne hs1u1 with h | h
        · exact Or.inl (eq_pair_of_two_dvd_lt_three_mul hg₁_pos hs₁_pos h hu₁_M hM3_g1
            (Nat.gcd_dvd_left s₁ u₁) (Nat.gcd_dvd_right s₁ u₁))
        · exact Or.inr (eq_pair_of_two_dvd_lt_three_mul hg₁_pos hu₁_pos h hs₁_M hM3_g1
            (Nat.gcd_dvd_right s₁ u₁) (Nat.gcd_dvd_left s₁ u₁))
      have hpair2 : (s₂ = g₂ ∧ u₂ = 2 * g₂) ∨ (u₂ = g₂ ∧ s₂ = 2 * g₂) := by
        rcases lt_or_gt_of_ne hs2u2 with h | h
        · exact Or.inl (eq_pair_of_two_dvd_lt_three_mul hg₂_pos hs₂_pos h hu₂_M hM3_g2
            (Nat.gcd_dvd_left s₂ u₂) (Nat.gcd_dvd_right s₂ u₂))
        · exact Or.inr (eq_pair_of_two_dvd_lt_three_mul hg₂_pos hu₂_pos h hs₂_M hM3_g2
            (Nat.gcd_dvd_right s₂ u₂) (Nat.gcd_dvd_left s₂ u₂))
      have h2g1_b1 : 2 * g₁ ∣ b₁ := by
        rcases hpair1 with ⟨_, hu1⟩ | ⟨_, hs1⟩
        · exact hu1 ▸ hu₁_b1
        · exact hs1 ▸ hs₁_b1
      have h2g2_b2 : 2 * g₂ ∣ b₂ := by
        rcases hpair2 with ⟨_, hu2⟩ | ⟨_, hs2⟩
        · exact hu2 ▸ hu₂_b2
        · exact hs2 ▸ hs₂_b2
      have hpair_card : ({b₁, b₂} : Finset ℕ).card + 1 ≤ 3 := by
        have h1 := Finset.card_insert_le b₁ {b₂}
        simp only [Finset.card_singleton] at h1
        omega
      obtain ⟨w, hw_I, hw_not, h2_w⟩ := exists_avoiding_multiple_in_consecInterval x M 2 {b₁, b₂}
        (by norm_num) (le_trans (Nat.mul_le_mul_right 2 hpair_card) hM6)
      have hw_b1 : w ≠ b₁ := fun h => hw_not (by simp [h])
      have hw_b2 : w ≠ b₂ := fun h => hw_not (by simp [h])
      let B : Finset ℕ := {b₁, b₂, w}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl <;> assumption
      have hBcard : B.card ≤ 5 := le_trans (card_finset_le_three b₁ b₂ w) (by omega)
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      have hw0 : w ≠ 0 := (pos_of_mem_consecInterval hw_I).ne'
      refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
      intro p hp
      have hsumA_eq : ∑ a ∈ A, a.factorization p =
          (g₁.factorization p + (2 * g₁).factorization p) +
          (g₂.factorization p + (2 * g₂).factorization p) := by
        rw [hA_eq, Finset.sum_insert (by simp [hs12, hs1u1, hs1u2]),
            Finset.sum_insert (by simp [hs2u1, hs2u2]), Finset.sum_insert (by simp [hu12]),
            Finset.sum_singleton]
        rcases hpair1 with ⟨hs1, hu1⟩ | ⟨hu1, hs1⟩ <;>
        rcases hpair2 with ⟨hs2, hu2⟩ | ⟨hu2, hs2⟩ <;>
        · rw [hs1, hu1, hs2, hu2]; ring
      have hsumB_eq : ∑ b ∈ B, b.factorization p =
          b₁.factorization p + b₂.factorization p + w.factorization p := by
        rw [Finset.sum_insert (by simp [hb12, hw_b1.symm]),
            Finset.sum_insert (by simp [hw_b2.symm]), Finset.sum_singleton]
        ring
      rw [hsumA_eq, hsumB_eq]
      have hb1_2g1 := fac_le_of_dvd hb₁0 h2g1_b1 (p := p)
      have hb1_g2 := fac_le_of_dvd hb₁0 hg₂_b1 (p := p)
      have hb2_2g2 := fac_le_of_dvd hb₂0 h2g2_b2 (p := p)
      have hb2_g1 := fac_le_of_dvd hb₂0 hg₁_b2 (p := p)
      have hw_2 := fac_le_of_dvd hw0 h2_w (p := p)
      have hmul2 : (2 * g₁).factorization p = (2 : ℕ).factorization p + g₁.factorization p := by
        rw [Nat.factorization_mul (by norm_num) hg₁_pos.ne', Finsupp.add_apply]
      have hmul2' : (2 * g₂).factorization p = (2 : ℕ).factorization p + g₂.factorization p := by
        rw [Nat.factorization_mul (by norm_num) hg₂_pos.ne', Finsupp.add_apply]
      rw [hmul2] at hb1_2g1
      rw [hmul2'] at hb2_2g2
      rcases coprime_factorization_zero hg₁_pos hg₂_pos hp hcop_g12 with h1_0 | h2_0
      · rw [h1_0] at hb1_2g1 hb2_g1; omega
      · rw [h2_0] at hb1_g2 hb2_2g2; omega
    · obtain ⟨w₂, hw₂_I, hw2_b1, hw2_b2, hg2_w2⟩ := exists_avoiding_of_not_subset_pair hsub2
      exact cover_four_r2_shape22_one_sub hA_eq hs12 hs1u1 hs1u2 hs2u1 hs2u2 hu12
        hA_pos hA_le hAgcd hb12 hb₁_I hb₂_I hs₁_b1 hu₁_b1 hs₂_b2 hu₂_b2 hsub1
        hw₂_I hw2_b1 hw2_b2 hg2_w2
  · obtain ⟨w₁, hw₁_I, hw1_b1, hw1_b2, hg1_w1⟩ := exists_avoiding_of_not_subset_pair hsub1
    by_cases hsub2 : (consecInterval x M).filter (fun b => g₂ ∣ b) ⊆ {b₁, b₂}
    · have hA_eq' : A = {s₂, s₁, u₂, u₁} := by
        rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_four_r2_shape22_one_sub hA_eq' hs12.symm hs2u2 hs2u1 hs1u2 hs1u1 hu12.symm
        hA_pos hA_le hAgcd hb12.symm hb₂_I hb₁_I hs₂_b2 hu₂_b2 hs₁_b1 hu₁_b1
        (by convert hsub2 using 1; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        hw₁_I hw1_b2 hw1_b1 hg1_w1
    · obtain ⟨w₂, hw₂_I, hw2_b1, hw2_b2, hg2_w2⟩ := exists_avoiding_of_not_subset_pair hsub2
      let B : Finset ℕ := {b₁, b₂, w₁, w₂}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hBcard : B.card ≤ 5 := le_trans (card_finset_le_four b₁ b₂ w₁ w₂) (by omega)
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
      intro p hp
      have hsumA_eq : ∑ a ∈ A, a.factorization p =
          s₁.factorization p + s₂.factorization p + u₁.factorization p + u₂.factorization p := by
        rw [hA_eq, Finset.sum_insert (by simp [hs12, hs1u1, hs1u2]),
            Finset.sum_insert (by simp [hs2u1, hs2u2]), Finset.sum_insert (by simp [hu12]),
            Finset.sum_singleton]
        ring
      rw [hsumA_eq]
      have hb1_1 := fac_le_of_dvd hb₁0 hs₁_b1 (p := p)
      have hb1_u1 := fac_le_of_dvd hb₁0 hu₁_b1 (p := p)
      have hb2_2 := fac_le_of_dvd hb₂0 hs₂_b2 (p := p)
      have hb2_u2 := fac_le_of_dvd hb₂0 hu₂_b2 (p := p)
      have hw1_g1 := fac_le_of_dvd hw10 hg1_w1 (p := p)
      have hw2_g2 := fac_le_of_dvd hw20 hg2_w2 (p := p)
      rw [fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hw1_g1
      rw [fac_gcd_eq_min hs₂_pos.ne' hu₂_pos.ne'] at hw2_g2
      rcases coprime_factorization_zero hg₁_pos hg₂_pos hp hcop_g12 with h1_0 | h2_0
      · rw [fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at h1_0
        have hsub3 : ({b₁, b₂, w₂} : Finset ℕ) ⊆ B := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
        have hleB : ∑ b ∈ ({b₁, b₂, w₂} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
          Finset.sum_le_sum_of_subset hsub3
        rw [Finset.sum_insert (by simp [hb12, hw2_b1.symm]),
            Finset.sum_insert (by simp [hw2_b2.symm]), Finset.sum_singleton] at hleB
        omega
      · rw [fac_gcd_eq_min hs₂_pos.ne' hu₂_pos.ne'] at h2_0
        have hsub3 : ({b₁, b₂, w₁} : Finset ℕ) ⊆ B := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
        have hleB : ∑ b ∈ ({b₁, b₂, w₁} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
          Finset.sum_le_sum_of_subset hsub3
        rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm]),
            Finset.sum_insert (by simp [hw1_b2.symm]), Finset.sum_singleton] at hleB
        omega

private lemma not_both_lt_three_mul {x y z M : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M)
    (h1 : M < 3 * Nat.gcd x y) :
    3 * Nat.gcd x z ≤ M := by
  have hyz' := hyz
  let _ := hxz
  let _ := hyM
  let g₁ := Nat.gcd x y
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left y hx
  have hpair1 : (x = g₁ ∧ y = 2 * g₁) ∨ (y = g₁ ∧ x = 2 * g₁) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact Or.inl (eq_pair_of_two_dvd_lt_three_mul hg₁_pos hx h hyM h1
        (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))
    · exact Or.inr (eq_pair_of_two_dvd_lt_three_mul hg₁_pos hy h hxM h1
        (Nat.gcd_dvd_right x y) (Nat.gcd_dvd_left x y))
  by_contra hlt
  have h2 : M < 3 * Nat.gcd x z := Nat.lt_of_not_ge hlt
  let g₂ := Nat.gcd x z
  have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left z hx
  have hpair2 : (x = g₂ ∧ z = 2 * g₂) ∨ (z = g₂ ∧ x = 2 * g₂) := by
    rcases lt_or_gt_of_ne hxz with h | h
    · exact Or.inl (eq_pair_of_two_dvd_lt_three_mul hg₂_pos hx h hzM h2
        (Nat.gcd_dvd_left x z) (Nat.gcd_dvd_right x z))
    · exact Or.inr (eq_pair_of_two_dvd_lt_three_mul hg₂_pos hz h hxM h2
        (Nat.gcd_dvd_right x z) (Nat.gcd_dvd_left x z))
  rcases hpair1 with ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩ <;>
  rcases hpair2 with ⟨hx2, hz2⟩ | ⟨hz2, hx2⟩
  · exact hyz' (by rw [hy1, hz2, ← hx1, hx2])
  · have : M < 3 * g₂ := h2
    omega
  · have : M < 3 * g₁ := h1
    omega
  · exact hyz' (by rw [hy1, hz2]; omega)

private lemma cover_four_r2_shape31_one_sub {A : Finset ℕ} {x M s₂ t₁ t₂ t₃ b₁ b₂ w₁ w₂ : ℕ}
    (hA_eq : A = {t₁, t₂, t₃, s₂})
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h1s : t₁ ≠ s₂)
    (h23 : t₂ ≠ t₃) (h2s : t₂ ≠ s₂) (h3s : t₃ ≠ s₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hb12 : b₁ ≠ b₂) (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M)
    (ht1_b1 : t₁ ∣ b₁) (ht2_b1 : t₂ ∣ b₁) (ht3_b1 : t₃ ∣ b₁) (hs₂_b2 : s₂ ∣ b₂)
    (hw₁_I : w₁ ∈ consecInterval x M) (hw1_b1 : w₁ ≠ b₁) (hw1_b2 : w₁ ≠ b₂)
    (hw₂_I : w₂ ∈ consecInterval x M) (hw2_b1 : w₂ ≠ b₁) (hw2_b2 : w₂ ≠ b₂)
    (hd1_w1 : Nat.gcd t₁ t₂ ∣ w₁) (hd2_w2 : Nat.gcd t₁ t₃ ∣ w₂)
    (hsub3 : (consecInterval x M).filter (fun b => Nat.gcd t₂ t₃ ∣ b) ⊆ {b₁, b₂}) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have ht1_pos : 0 < t₁ := hA_pos t₁ (by rw [hA_eq]; simp)
  have ht2_pos : 0 < t₂ := hA_pos t₂ (by rw [hA_eq]; simp)
  have ht3_pos : 0 < t₃ := hA_pos t₃ (by rw [hA_eq]; simp)
  have hs₂_pos : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have ht2_M : t₂ ≤ M := hA_le t₂ (by rw [hA_eq]; simp)
  have ht3_M : t₃ ≤ M := hA_le t₃ (by rw [hA_eq]; simp)
  have hs₂_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  let d₃ := Nat.gcd t₂ t₃
  have hd₃_pos : 0 < d₃ := Nat.gcd_pos_of_pos_left t₃ ht2_pos
  have h2d₃ : 2 * d₃ ≤ M := by
    rcases lt_or_gt_of_ne h23 with h | h
    · exact two_mul_gcd_le_4 ht2_pos h ht3_M
    · rw [show d₃ = Nat.gcd t₃ t₂ from Nat.gcd_comm t₂ t₃]
      exact two_mul_gcd_le_4 ht3_pos h ht2_M
  have hd₃_b2 : d₃ ∣ b₂ := (dvd_pair_of_filter_subset_pair hd₃_pos h2d₃ hb12 hsub3).2.1
  let e₃ := Nat.gcd s₂ d₃
  have he₃_pos : 0 < e₃ := Nat.gcd_pos_of_pos_left d₃ hs₂_pos
  have h3e₃ : 3 * e₃ ≤ M := three_mul_le_of_three_dvd_distinct he₃_pos h2s.symm h3s.symm h23
    hs₂_pos ht2_pos ht3_pos hs₂_M ht2_M ht3_M
    (Nat.gcd_dvd_left s₂ d₃)
    (dvd_trans (Nat.gcd_dvd_right s₂ d₃) (Nat.gcd_dvd_left t₂ t₃))
    (dvd_trans (Nat.gcd_dvd_right s₂ d₃) (Nat.gcd_dvd_right t₂ t₃))
  have hpair_card : ({b₁, b₂} : Finset ℕ).card + 1 ≤ 3 := by
    have h1 := Finset.card_insert_le b₁ {b₂}
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨w₃, hw₃_I, hw3_not, he3_w3⟩ := exists_avoiding_multiple_in_consecInterval x M e₃ {b₁, b₂}
    he₃_pos (le_trans (Nat.mul_le_mul_right e₃ hpair_card) h3e₃)
  have hw3_b1 : w₃ ≠ b₁ := fun h => hw3_not (by simp [h])
  have hw3_b2 : w₃ ≠ b₂ := fun h => hw3_not (by simp [h])
  let B : Finset ℕ := {b₁, b₂, w₁, w₂, w₃}
  have hBI : B ⊆ consecInterval x M := by
    intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hBcard : B.card ≤ 5 := card_finset_le_five b₁ b₂ w₁ w₂ w₃
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
  have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
  refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
  intro p hp
  have hsumA_eq : ∑ a ∈ A, a.factorization p =
      t₁.factorization p + t₂.factorization p + t₃.factorization p + s₂.factorization p := by
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h1s]),
        Finset.sum_insert (by simp [h23, h2s]), Finset.sum_insert (by simp [h3s]),
        Finset.sum_singleton]
    ring
  rw [hsumA_eq]
  have hmin0 : t₁.factorization p = 0 ∨ t₂.factorization p = 0 ∨
      t₃.factorization p = 0 ∨ s₂.factorization p = 0 := by
    by_contra hpos
    push Not at hpos
    have hd : p ∣ A.gcd id := by
      apply Finset.dvd_gcd
      intro a ha; rw [hA_eq] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · exact prime_dvd_of_fac_ne_zero hp ht1_pos.ne' hpos.1
      · exact prime_dvd_of_fac_ne_zero hp ht2_pos.ne' hpos.2.1
      · exact prime_dvd_of_fac_ne_zero hp ht3_pos.ne' hpos.2.2.1
      · exact prime_dvd_of_fac_ne_zero hp hs₂_pos.ne' hpos.2.2.2
    rw [hAgcd] at hd
    exact hp.not_dvd_one hd
  have hb1_t1 := fac_le_of_dvd hb₁0 ht1_b1 (p := p)
  have hb1_t2 := fac_le_of_dvd hb₁0 ht2_b1 (p := p)
  have hb1_t3 := fac_le_of_dvd hb₁0 ht3_b1 (p := p)
  have hb2_s2 := fac_le_of_dvd hb₂0 hs₂_b2 (p := p)
  have hb2_d3 := fac_le_of_dvd hb₂0 hd₃_b2 (p := p)
  have hw1_d1 := fac_le_of_dvd hw10 hd1_w1 (p := p)
  have hw2_d2 := fac_le_of_dvd hw20 hd2_w2 (p := p)
  have hw3_e3 := fac_le_of_dvd hw30 he3_w3 (p := p)
  rw [fac_gcd_eq_min ht2_pos.ne' ht3_pos.ne'] at hb2_d3
  rw [fac_gcd_eq_min ht1_pos.ne' ht2_pos.ne'] at hw1_d1
  rw [fac_gcd_eq_min ht1_pos.ne' ht3_pos.ne'] at hw2_d2
  rw [fac_gcd_eq_min hs₂_pos.ne' hd₃_pos.ne', fac_gcd_eq_min ht2_pos.ne' ht3_pos.ne'] at hw3_e3
  have hsub_t : ∀ w ∈ ({w₁, w₂, w₃} : Finset ℕ), w ≠ b₁ → w ≠ b₂ →
      b₁.factorization p + b₂.factorization p + w.factorization p ≤ ∑ b ∈ B, b.factorization p := by
    intro w hw hwb1 hwb2
    have hsub3 : ({b₁, b₂, w} : Finset ℕ) ⊆ B := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb hw
      rcases hb with rfl | rfl | rfl
      · simp [B]
      · simp [B]
      · rcases hw with rfl | rfl | rfl <;> simp [B]
    have hle := Finset.sum_le_sum_of_subset hsub3 (f := fun b => b.factorization p)
    rw [Finset.sum_insert (by simp [hb12, hwb1.symm]),
        Finset.sum_insert (by simp [hwb2.symm]), Finset.sum_singleton] at hle
    rw [← add_assoc] at hle
    exact hle
  have hle_w1 := hsub_t w₁ (by simp) hw1_b1 hw1_b2
  have hle_w2 := hsub_t w₂ (by simp) hw2_b1 hw2_b2
  have hle_w3 := hsub_t w₃ (by simp) hw3_b1 hw3_b2
  rcases hmin0 with ht1_0 | ht2_0 | ht3_0 | hs2_0
  · rw [ht1_0] at hb1_t1 hw1_d1 hw2_d2
    rcases le_total (t₂.factorization p) (t₃.factorization p) with h23_le | h32_le <;> omega
  · rw [ht2_0] at hb1_t2 hb2_d3 hw1_d1 hw3_e3
    rcases le_total (t₁.factorization p) (t₃.factorization p) with h13_le | h31_le <;> omega
  · rw [ht3_0] at hb1_t3 hb2_d3 hw2_d2 hw3_e3
    rcases le_total (t₁.factorization p) (t₂.factorization p) with h12_le | h21_le <;> omega
  · rw [hs2_0] at hb2_s2 hw3_e3
    rcases le_total (t₁.factorization p) (t₂.factorization p) with h12_le | h21_le <;>
    rcases le_total (t₂.factorization p) (t₃.factorization p) with h23_le | h32_le <;> omega

private lemma cover_four_r2_shape31 {A : Finset ℕ} {x M s₁ s₂ u₁ u₂ b₁ b₂ : ℕ}
    (hA_eq : A = {s₁, u₁, u₂, s₂})
    (h12 : s₁ ≠ u₁) (h13 : s₁ ≠ u₂) (h1s : s₁ ≠ s₂)
    (h23 : u₁ ≠ u₂) (h2s : u₁ ≠ s₂) (h3s : u₂ ≠ s₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hb12 : b₁ ≠ b₂) (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M)
    (hs₁_b1 : s₁ ∣ b₁) (hu₁_b1 : u₁ ∣ b₁) (hu₂_b1 : u₂ ∣ b₁) (hs₂_b2 : s₂ ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have hs₁_pos : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hs₂_pos : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hs₁_M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hu₁_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hu₂_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hs₂_M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  let d₁ := Nat.gcd s₁ u₁
  let d₂ := Nat.gcd s₁ u₂
  let d₃ := Nat.gcd u₁ u₂
  have hd₁_pos : 0 < d₁ := Nat.gcd_pos_of_pos_left u₁ hs₁_pos
  have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_left u₂ hs₁_pos
  have hd₃_pos : 0 < d₃ := Nat.gcd_pos_of_pos_left u₂ hu₁_pos
  have h2d₁ : 2 * d₁ ≤ M := by
    rcases lt_or_gt_of_ne h12 with h | h
    · exact two_mul_gcd_le_4 hs₁_pos h hu₁_M
    · rw [show d₁ = Nat.gcd u₁ s₁ from Nat.gcd_comm s₁ u₁]; exact two_mul_gcd_le_4 hu₁_pos h hs₁_M
  have h2d₂ : 2 * d₂ ≤ M := by
    rcases lt_or_gt_of_ne h13 with h | h
    · exact two_mul_gcd_le_4 hs₁_pos h hu₂_M
    · rw [show d₂ = Nat.gcd u₂ s₁ from Nat.gcd_comm s₁ u₂]; exact two_mul_gcd_le_4 hu₂_pos h hs₁_M
  have h2d₃ : 2 * d₃ ≤ M := by
    rcases lt_or_gt_of_ne h23 with h | h
    · exact two_mul_gcd_le_4 hu₁_pos h hu₂_M
    · rw [show d₃ = Nat.gcd u₂ u₁ from Nat.gcd_comm u₁ u₂]; exact two_mul_gcd_le_4 hu₂_pos h hu₁_M
  by_cases hsub1 : (consecInterval x M).filter (fun b => d₁ ∣ b) ⊆ {b₁, b₂}
  · have hM3_1 : M < 3 * d₁ := (dvd_pair_of_filter_subset_pair hd₁_pos h2d₁ hb12 hsub1).2.2
    have h3d2 : 3 * d₂ ≤ M := not_both_lt_three_mul hs₁_pos hu₁_pos hu₂_pos h12 h13 h23
      hs₁_M hu₁_M hu₂_M hM3_1
    have h3d3 : 3 * d₃ ≤ M := by
      have h1' : M < 3 * Nat.gcd u₁ s₁ := by rw [Nat.gcd_comm]; exact hM3_1
      have h := not_both_lt_three_mul hu₁_pos hs₁_pos hu₂_pos h12.symm h23 h13
        hu₁_M hs₁_M hu₂_M h1'
      exact h
    have hnot2 : ¬ ((consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {b₁, b₂}) := by
      intro hsub2
      have hM3_2 := (dvd_pair_of_filter_subset_pair hd₂_pos h2d₂ hb12 hsub2).2.2
      omega
    have hnot3 : ¬ ((consecInterval x M).filter (fun b => d₃ ∣ b) ⊆ {b₁, b₂}) := by
      intro hsub3
      have hM3_3 := (dvd_pair_of_filter_subset_pair hd₃_pos h2d₃ hb12 hsub3).2.2
      omega
    obtain ⟨w₂, hw₂_I, hw2_b1, hw2_b2, hd2_w2⟩ := exists_avoiding_of_not_subset_pair hnot2
    obtain ⟨w₃, hw₃_I, hw3_b1, hw3_b2, hd3_w3⟩ := exists_avoiding_of_not_subset_pair hnot3
    have hA_eq' : A = {u₂, s₁, u₁, s₂} := by
      rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact cover_four_r2_shape31_one_sub hA_eq' h13.symm h23.symm h3s h12 h1s h2s
      hA_pos hA_le hAgcd hb12 hb₁_I hb₂_I hu₂_b1 hs₁_b1 hu₁_b1 hs₂_b2
      hw₂_I hw2_b1 hw2_b2 hw₃_I hw3_b1 hw3_b2 (by rw [Nat.gcd_comm]; exact hd2_w2)
      (by rw [Nat.gcd_comm]; exact hd3_w3) hsub1
  · obtain ⟨w₁, hw₁_I, hw1_b1, hw1_b2, hd1_w1⟩ := exists_avoiding_of_not_subset_pair hsub1
    by_cases hsub2 : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ {b₁, b₂}
    · have hM3_2 : M < 3 * d₂ := (dvd_pair_of_filter_subset_pair hd₂_pos h2d₂ hb12 hsub2).2.2
      have h3d3 : 3 * d₃ ≤ M := by
        have h1' : M < 3 * Nat.gcd u₂ s₁ := by rw [Nat.gcd_comm]; exact hM3_2
        have h := not_both_lt_three_mul hu₂_pos hs₁_pos hu₁_pos h13.symm h23.symm h12
          hu₂_M hs₁_M hu₁_M h1'
        rw [Nat.gcd_comm] at h
        exact h
      have hnot3 : ¬ ((consecInterval x M).filter (fun b => d₃ ∣ b) ⊆ {b₁, b₂}) := by
        intro hsub3
        have hM3_3 := (dvd_pair_of_filter_subset_pair hd₃_pos h2d₃ hb12 hsub3).2.2
        omega
      obtain ⟨w₃, hw₃_I, hw3_b1, hw3_b2, hd3_w3⟩ := exists_avoiding_of_not_subset_pair hnot3
      have hA_eq' : A = {u₁, s₁, u₂, s₂} := by
        rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_four_r2_shape31_one_sub hA_eq' h12.symm h23 h2s h13 h1s h3s
        hA_pos hA_le hAgcd hb12 hb₁_I hb₂_I hu₁_b1 hs₁_b1 hu₂_b1 hs₂_b2
        hw₁_I hw1_b1 hw1_b2 hw₃_I hw3_b1 hw3_b2 (by rw [Nat.gcd_comm]; exact hd1_w1)
        hd3_w3 hsub2
    · obtain ⟨w₂, hw₂_I, hw2_b1, hw2_b2, hd2_w2⟩ := exists_avoiding_of_not_subset_pair hsub2
      by_cases hsub3 : (consecInterval x M).filter (fun b => d₃ ∣ b) ⊆ {b₁, b₂}
      · exact cover_four_r2_shape31_one_sub hA_eq h12 h13 h1s h23 h2s h3s
          hA_pos hA_le hAgcd hb12 hb₁_I hb₂_I hs₁_b1 hu₁_b1 hu₂_b1 hs₂_b2
          hw₁_I hw1_b1 hw1_b2 hw₂_I hw2_b1 hw2_b2 hd1_w1 hd2_w2 hsub3
      · obtain ⟨w₃, hw₃_I, hw3_b1, hw3_b2, hd3_w3⟩ := exists_avoiding_of_not_subset_pair hsub3
        have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
        have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
        have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
        have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
            s₁.factorization p + u₁.factorization p + u₂.factorization p + s₂.factorization p := by
          intro p
          rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h1s]),
              Finset.sum_insert (by simp [h23, h2s]), Finset.sum_insert (by simp [h3s]),
              Finset.sum_singleton]
          ring
        by_cases hall : w₁ = w₂ ∧ w₂ = w₃
        · rcases hall with ⟨rfl, rfl⟩
          let D := Nat.gcd (Nat.gcd s₁ u₁) u₂
          have hD_pos : 0 < D := Nat.gcd_pos_of_pos_left u₂ hd₁_pos
          have hD_s1 : D ∣ s₁ := dvd_trans (Nat.gcd_dvd_left d₁ u₂) (Nat.gcd_dvd_left s₁ u₁)
          have hD_u1 : D ∣ u₁ := dvd_trans (Nat.gcd_dvd_left d₁ u₂) (Nat.gcd_dvd_right s₁ u₁)
          have hD_u2 : D ∣ u₂ := Nat.gcd_dvd_right d₁ u₂
          have h3D : 3 * D ≤ M := three_mul_le_of_three_dvd_distinct hD_pos h12 h13 h23
            hs₁_pos hu₁_pos hu₂_pos hs₁_M hu₁_M hu₂_M hD_s1 hD_u1 hD_u2
          have hcop_Ds2 : Nat.Coprime D s₂ := by
            rw [Nat.coprime_iff_gcd_eq_one]
            have hd : Nat.gcd D s₂ ∣ A.gcd id := by
              apply Finset.dvd_gcd
              intro a ha; rw [hA_eq] at ha
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with ha | ha | ha | ha <;> rw [ha]
              · exact dvd_trans (Nat.gcd_dvd_left D s₂) hD_s1
              · exact dvd_trans (Nat.gcd_dvd_left D s₂) hD_u1
              · exact dvd_trans (Nat.gcd_dvd_left D s₂) hD_u2
              · exact Nat.gcd_dvd_right D s₂
            rw [hAgcd] at hd
            exact Nat.dvd_one.mp hd
          by_cases hsubD : (consecInterval x M).filter (fun b => D ∣ b) ⊆ {b₁, b₂, w₁}
          · have hD_b2 : D ∣ b₂ :=
              dvd_second_of_filter_subset_triple hD_pos h3D hsubD
            let B : Finset ℕ := {b₁, b₂, w₁}
            have hBI : B ⊆ consecInterval x M := by
              intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl <;> assumption
            have hBcard : B.card ≤ 5 := le_trans (card_finset_le_three b₁ b₂ w₁) (by omega)
            have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
            have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
            refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
            intro p hp
            rw [hsumA_eq p, Finset.sum_insert (by simp [hb12, hw1_b1.symm]),
                Finset.sum_insert (by simp [hw1_b2.symm]), Finset.sum_singleton]
            have hb1_1 := fac_le_of_dvd hb₁0 hs₁_b1 (p := p)
            have hb1_2 := fac_le_of_dvd hb₁0 hu₁_b1 (p := p)
            have hb1_3 := fac_le_of_dvd hb₁0 hu₂_b1 (p := p)
            have hb2_s2 := fac_le_of_dvd hb₂0 hs₂_b2 (p := p)
            have hb2_D := fac_le_of_dvd hb₂0 hD_b2 (p := p)
            have hw1_1 := fac_le_of_dvd hw10 hd1_w1 (p := p)
            have hw1_2 := fac_le_of_dvd hw10 hd2_w2 (p := p)
            have hw1_3 := fac_le_of_dvd hw10 hd3_w3 (p := p)
            rw [fac_gcd_eq_min hd₁_pos.ne' hu₂_pos.ne', fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hb2_D
            rw [fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hw1_1
            rw [fac_gcd_eq_min hs₁_pos.ne' hu₂_pos.ne'] at hw1_2
            rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw1_3
            rcases coprime_factorization_zero hD_pos hs₂_pos hp hcop_Ds2 with hD0 | hs2_0
            · rw [fac_gcd_eq_min hd₁_pos.ne' hu₂_pos.ne', fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hD0
              rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
              rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;> omega
            · rw [hs2_0] at hb2_s2
              rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
              rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;> omega
          · obtain ⟨w', hw'_flt, hw'_not⟩ := Finset.not_subset.mp hsubD
            rw [Finset.mem_filter] at hw'_flt
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw'_not
            let B : Finset ℕ := {b₁, b₂, w₁, w'}
            have hBI : B ⊆ consecInterval x M := by
              intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl <;> first | assumption | exact hw'_flt.1
            have hBcard : B.card ≤ 5 := le_trans (card_finset_le_four b₁ b₂ w₁ w') (by omega)
            have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
            have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
            have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_flt.1).ne'
            refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
            intro p _hp
            rw [hsumA_eq p]
            rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, Ne.symm hw'_not.1]),
                Finset.sum_insert (by simp [hw1_b2.symm, Ne.symm hw'_not.2.1]),
                Finset.sum_insert (by simp [Ne.symm hw'_not.2.2]), Finset.sum_singleton]
            have hb1_1 := fac_le_of_dvd hb₁0 hs₁_b1 (p := p)
            have hb1_2 := fac_le_of_dvd hb₁0 hu₁_b1 (p := p)
            have hb1_3 := fac_le_of_dvd hb₁0 hu₂_b1 (p := p)
            have hb2_s2 := fac_le_of_dvd hb₂0 hs₂_b2 (p := p)
            have hw1_1 := fac_le_of_dvd hw10 hd1_w1 (p := p)
            have hw1_2 := fac_le_of_dvd hw10 hd2_w2 (p := p)
            have hw1_3 := fac_le_of_dvd hw10 hd3_w3 (p := p)
            have hw'_D := fac_le_of_dvd hw'0 hw'_flt.2 (p := p)
            rw [fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hw1_1
            rw [fac_gcd_eq_min hs₁_pos.ne' hu₂_pos.ne'] at hw1_2
            rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw1_3
            rw [fac_gcd_eq_min hd₁_pos.ne' hu₂_pos.ne', fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hw'_D
            rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
            rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;> omega
        · let B : Finset ℕ := {b₁, b₂, w₁, w₂, w₃}
          have hBI : B ⊆ consecInterval x M := by
            intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
          have hBcard : B.card ≤ 5 := card_finset_le_five b₁ b₂ w₁ w₂ w₃
          have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
          have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
          have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
          have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
          refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
          intro p _hp
          rw [hsumA_eq p]
          have hb1_1 := fac_le_of_dvd hb₁0 hs₁_b1 (p := p)
          have hb1_2 := fac_le_of_dvd hb₁0 hu₁_b1 (p := p)
          have hb1_3 := fac_le_of_dvd hb₁0 hu₂_b1 (p := p)
          have hb2_s2 := fac_le_of_dvd hb₂0 hs₂_b2 (p := p)
          have hw1_d1 := fac_le_of_dvd hw10 hd1_w1 (p := p)
          have hw2_d2 := fac_le_of_dvd hw20 hd2_w2 (p := p)
          have hw3_d3 := fac_le_of_dvd hw30 hd3_w3 (p := p)
          rw [fac_gcd_eq_min hs₁_pos.ne' hu₁_pos.ne'] at hw1_d1
          rw [fac_gcd_eq_min hs₁_pos.ne' hu₂_pos.ne'] at hw2_d2
          rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw3_d3
          by_cases hw12 : w₁ = w₂
          · have hw23 : w₂ ≠ w₃ := fun h => hall ⟨hw12, h⟩
            have hw13 : w₁ ≠ w₃ := by rw [hw12]; exact hw23
            have hsub4 : ({b₁, b₂, w₁, w₃} : Finset ℕ) ⊆ B := by
              intro b hb
              simp only [Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
            have hleB : ∑ b ∈ ({b₁, b₂, w₁, w₃} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
              Finset.sum_le_sum_of_subset hsub4
            rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw3_b1.symm]),
                Finset.sum_insert (by simp [hw1_b2.symm, hw3_b2.symm]),
                Finset.sum_insert (by simp [hw13]), Finset.sum_singleton] at hleB
            rw [← hw12] at hw2_d2
            rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
            rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;>
            rcases le_total (s₁.factorization p) (u₂.factorization p) with h13_le | h31_le <;> omega
          · have hsub4 : ({b₁, b₂, w₁, w₂} : Finset ℕ) ⊆ B := by
              intro b hb
              simp only [Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
            have hleB : ∑ b ∈ ({b₁, b₂, w₁, w₂} : Finset ℕ), b.factorization p ≤ ∑ b ∈ B, b.factorization p :=
              Finset.sum_le_sum_of_subset hsub4
            rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm]),
                Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm]),
                Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
            by_cases hw13 : w₁ = w₃
            · rw [← hw13] at hw3_d3
              rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
              rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;>
              rcases le_total (s₁.factorization p) (u₂.factorization p) with h13_le | h31_le <;> omega
            · by_cases hw23 : w₂ = w₃
              · rw [← hw23] at hw3_d3
                rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
                rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;>
                rcases le_total (s₁.factorization p) (u₂.factorization p) with h13_le | h31_le <;> omega
              · have hleB5 : b₁.factorization p + (b₂.factorization p + (w₁.factorization p +
                    (w₂.factorization p + w₃.factorization p))) ≤ ∑ b ∈ B, b.factorization p := by
                  calc b₁.factorization p + (b₂.factorization p + (w₁.factorization p +
                          (w₂.factorization p + w₃.factorization p)))
                      = ∑ b ∈ ({b₁, b₂, w₁, w₂, w₃} : Finset ℕ), b.factorization p := by
                        rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm, hw3_b1.symm]),
                            Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm, hw3_b2.symm]),
                            Finset.sum_insert (by simp [hw12, hw13]),
                            Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
                    _ ≤ ∑ b ∈ B, b.factorization p := le_rfl
                rcases le_total (s₁.factorization p) (u₁.factorization p) with h12_le | h21_le <;>
                rcases le_total (u₁.factorization p) (u₂.factorization p) with h23_le | h32_le <;>
                rcases le_total (s₁.factorization p) (u₂.factorization p) with h13_le | h31_le <;> omega

theorem erdos708_upper_four_of_matching_two {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 4) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM6 : 6 ≤ M) (hSA : S ⊆ A) (hS_card : S.card = 2)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S)
    (hmax : ∀ u ∈ A \ S, ∀ b ∈ consecInterval x M, u ∣ b → b ∈ S.image f) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  obtain ⟨s₁, s₂, hs12, hS_eq⟩ := Finset.card_eq_two.mp hS_card
  have hdiff_card : (A \ S).card = 2 := by
    have h1 := Finset.card_sdiff_add_card_inter A S
    have h2 : A ∩ S = S := Finset.inter_eq_right.mpr hSA
    rw [h2, hA_card, hS_card] at h1
    omega
  obtain ⟨u₁, u₂, hu12, hdiff_eq⟩ := Finset.card_eq_two.mp hdiff_card
  have hs₁_S : s₁ ∈ S := by rw [hS_eq]; simp
  have hs₂_S : s₂ ∈ S := by rw [hS_eq]; simp
  have hu₁_diff : u₁ ∈ A \ S := by rw [hdiff_eq]; simp
  have hu₂_diff : u₂ ∈ A \ S := by rw [hdiff_eq]; simp
  have hs₁_A : s₁ ∈ A := hSA hs₁_S
  have hs₂_A : s₂ ∈ A := hSA hs₂_S
  have hu₁_A : u₁ ∈ A := (Finset.mem_sdiff.mp hu₁_diff).1
  have hu₂_A : u₂ ∈ A := (Finset.mem_sdiff.mp hu₂_diff).1
  have hu₁_nS : u₁ ∉ S := (Finset.mem_sdiff.mp hu₁_diff).2
  have hu₂_nS : u₂ ∉ S := (Finset.mem_sdiff.mp hu₂_diff).2
  have hs1u1 : s₁ ≠ u₁ := fun h => hu₁_nS (h ▸ hs₁_S)
  have hs1u2 : s₁ ≠ u₂ := fun h => hu₂_nS (h ▸ hs₁_S)
  have hs2u1 : s₂ ≠ u₁ := fun h => hu₁_nS (h ▸ hs₂_S)
  have hs2u2 : s₂ ≠ u₂ := fun h => hu₂_nS (h ▸ hs₂_S)
  have hA_eq : A = {s₁, s₂, u₁, u₂} := by
    rw [← Finset.sdiff_union_of_subset hSA, hdiff_eq, hS_eq]
    ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  let b₁ := f s₁
  let b₂ := f s₂
  have hb12 : b₁ ≠ b₂ := fun h => hs12 (hf_inj hs₁_S hs₂_S h)
  have hb₁_I : b₁ ∈ consecInterval x M := hf_mem s₁ hs₁_S
  have hb₂_I : b₂ ∈ consecInterval x M := hf_mem s₂ hs₂_S
  have hs₁_b1 : s₁ ∣ b₁ := hf_dvd s₁ hs₁_S
  have hs₂_b2 : s₂ ∣ b₂ := hf_dvd s₂ hs₂_S
  have hSimg : S.image f = {b₁, b₂} := by
    rw [hS_eq, Finset.image_insert, Finset.image_singleton]
  obtain ⟨m₁, hm₁_I, hu₁_m₁⟩ :=
    exists_multiple_in_consecInterval x u₁ M (hA_pos u₁ hu₁_A) (hA_le u₁ hu₁_A)
  obtain ⟨m₂, hm₂_I, hu₂_m₂⟩ :=
    exists_multiple_in_consecInterval x u₂ M (hA_pos u₂ hu₂_A) (hA_le u₂ hu₂_A)
  have hm₁_mem := hmax u₁ hu₁_diff m₁ hm₁_I hu₁_m₁
  have hm₂_mem := hmax u₂ hu₂_diff m₂ hm₂_I hu₂_m₂
  rw [hSimg] at hm₁_mem hm₂_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm₁_mem hm₂_mem
  rcases hm₁_mem with rfl | rfl <;> rcases hm₂_mem with rfl | rfl
  · have hA_eq' : A = {s₁, u₁, u₂, s₂} := by
      rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact cover_four_r2_shape31 hA_eq' hs1u1 hs1u2 hs12 hu12 hs2u1.symm hs2u2.symm
      hA_pos hA_le hAgcd hb12 hb₁_I hb₂_I hs₁_b1 hu₁_m₁ hu₂_m₂ hs₂_b2
  · exact cover_four_r2_shape22 hA_eq hs12 hs1u1 hs1u2 hs2u1 hs2u2 hu12
      hA_pos hA_le hAgcd hM6 hb12 hb₁_I hb₂_I hs₁_b1 hs₂_b2 hu₁_m₁ hu₂_m₂
  · have hA_eq' : A = {s₁, s₂, u₂, u₁} := by
      rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact cover_four_r2_shape22 hA_eq' hs12 hs1u2 hs1u1 hs2u2 hs2u1 hu12.symm
      hA_pos hA_le hAgcd hM6 hb12 hb₁_I hb₂_I hs₁_b1 hs₂_b2 hu₂_m₂ hu₁_m₁
  · have hA_eq' : A = {s₂, u₁, u₂, s₁} := by
      rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact cover_four_r2_shape31 hA_eq' hs2u1 hs2u2 hs12.symm hu12 hs1u1.symm hs1u2.symm
      hA_pos hA_le hAgcd hb12.symm hb₂_I hb₁_I hs₂_b2 hu₁_m₁ hu₂_m₂ hs₁_b1

/-! ## Part 3: Matching Size `r = 1` Closure (`erdos708_upper_four_of_matching_one`) -/

private lemma r1_1a_pair_sum_le {a b c d L B0 W4 Wp Wq : ℕ}
    (ha : a ≤ B0) (hb : b ≤ B0) (hc : c ≤ B0) (hd : d ≤ B0)
    (haL : a ≤ L) (hbL : b ≤ L) (hcL : c ≤ L)
    (hw4 : min L d ≤ W4) (hw_ab : min a b ≤ Wp) (hw_ac : min a c ≤ Wp) (hw_bc : min b c ≤ Wq) :
    a + b + c + d ≤ B0 + (W4 + (Wp + Wq)) := by
  have hmaxL : max (max a b) c ≤ L := max_le (max_le haL hbL) hcL
  have hmin_le : min (max (max a b) c) d ≤ min L d := min_le_min hmaxL le_rfl
  rcases le_total a b with _ | _ <;> rcases le_total b c with _ | _ <;>
  rcases le_total a c with _ | _ <;> rcases le_total (max (max a b) c) d with _ | _ <;> omega

private lemma cover_four_r1_subcase1A {A : Finset ℕ} {x M b₀ x₁ x₂ x₃ x₄ : ℕ}
    (hA_eq : A = {x₁, x₂, x₃, x₄})
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M)
    (hdiv_b0 : ∀ a ∈ A, a ∣ b₀) (hn_dvd : ¬ (x₄ ∣ (A.erase x₄).lcm id)) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have hx₁_pos : 0 < x₁ := hA_pos x₁ (by rw [hA_eq]; simp)
  have hx₂_pos : 0 < x₂ := hA_pos x₂ (by rw [hA_eq]; simp)
  have hx₃_pos : 0 < x₃ := hA_pos x₃ (by rw [hA_eq]; simp)
  have hx₄_pos : 0 < x₄ := hA_pos x₄ (by rw [hA_eq]; simp)
  have hx₁_M : x₁ ≤ M := hA_le x₁ (by rw [hA_eq]; simp)
  have hx₂_M : x₂ ≤ M := hA_le x₂ (by rw [hA_eq]; simp)
  have hx₃_M : x₃ ≤ M := hA_le x₃ (by rw [hA_eq]; simp)
  have hx₄_M : x₄ ≤ M := hA_le x₄ (by rw [hA_eq]; simp)
  have hx₁_half : M < 2 * x₁ := hM_half x₁ (by rw [hA_eq]; simp)
  have hx₂_half : M < 2 * x₂ := hM_half x₂ (by rw [hA_eq]; simp)
  have hx₃_half : M < 2 * x₃ := hM_half x₃ (by rw [hA_eq]; simp)
  have hA'_eq : A.erase x₄ = {x₁, x₂, x₃} := by
    rw [hA_eq]
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz4, rfl | rfl | rfl | rfl⟩ <;> simp_all
    · rintro (rfl | rfl | rfl)
      · exact ⟨h14, Or.inl rfl⟩
      · exact ⟨h24, Or.inr (Or.inl rfl)⟩
      · exact ⟨h34, Or.inr (Or.inr (Or.inl rfl))⟩
  let L := Nat.lcm (Nat.lcm x₁ x₂) x₃
  have hL_eq : (A.erase x₄).lcm id = L := by
    rw [hA'_eq]
    exact lcm_triple_eq x₁ x₂ x₃
  rw [hL_eq] at hn_dvd
  have hL_pos : 0 < L := Nat.lcm_pos (Nat.lcm_pos hx₁_pos hx₂_pos) hx₃_pos
  let h := Nat.gcd L x₄
  have hh_pos : 0 < h := Nat.gcd_pos_of_pos_right L hx₄_pos
  have hh_lt : h < x₄ := by
    have hle : h ≤ x₄ := Nat.le_of_dvd hx₄_pos (Nat.gcd_dvd_right L x₄)
    have hne : h ≠ x₄ := fun heq => hn_dvd (heq ▸ Nat.gcd_dvd_left L x₄)
    omega
  have h2h : 2 * h ≤ M := by
    obtain ⟨q, hq⟩ := Nat.gcd_dvd_right L x₄
    have hq2 : 2 ≤ q := by
      by_contra hlt
      have hq_le1 : q ≤ 1 := by omega
      have hle' : x₄ ≤ h := by
        calc x₄ = h * q := hq
          _ ≤ h * 1 := Nat.mul_le_mul_left h hq_le1
          _ = h := mul_one h
      omega
    have h1 : 2 * h ≤ h * q := by rw [mul_comm 2]; exact Nat.mul_le_mul_left h hq2
    rw [← hq] at h1
    exact le_trans h1 hx₄_M
  obtain ⟨w₄, hw₄_I, hw₄_nb0, hh_w₄⟩ := exists_avoiding_multiple_in_consecInterval x M h {b₀}
    hh_pos (by simpa using h2h)
  have hw4_b0 : w₄ ≠ b₀ := by simpa using hw₄_nb0
  let g₁₂ := Nat.gcd x₁ x₂
  let g₁₃ := Nat.gcd x₁ x₃
  let g₂₃ := Nat.gcd x₂ x₃
  have hg₁₂_pos : 0 < g₁₂ := Nat.gcd_pos_of_pos_left x₂ hx₁_pos
  have hg₁₃_pos : 0 < g₁₃ := Nat.gcd_pos_of_pos_left x₃ hx₁_pos
  have hg₂₃_pos : 0 < g₂₃ := Nat.gcd_pos_of_pos_left x₃ hx₂_pos
  have h3g₁₂ : 3 * g₁₂ ≤ M := three_mul_le_of_two_ne_gt_half hg₁₂_pos h12 hx₁_M hx₂_M
    hx₁_half hx₂_half (Nat.gcd_dvd_left x₁ x₂) (Nat.gcd_dvd_right x₁ x₂)
  have h3g₁₃ : 3 * g₁₃ ≤ M := three_mul_le_of_two_ne_gt_half hg₁₃_pos h13 hx₁_M hx₃_M
    hx₁_half hx₃_half (Nat.gcd_dvd_left x₁ x₃) (Nat.gcd_dvd_right x₁ x₃)
  have h3g₂₃ : 3 * g₂₃ ≤ M := three_mul_le_of_two_ne_gt_half hg₂₃_pos h23 hx₂_M hx₃_M
    hx₂_half hx₃_half (Nat.gcd_dvd_left x₂ x₃) (Nat.gcd_dvd_right x₂ x₃)
  have hpair_card : ({b₀, w₄} : Finset ℕ).card + 1 ≤ 3 := by
    have h1 := Finset.card_insert_le b₀ {w₄}
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨w₁, hw₁_I, hw₁_not, hg12_w1⟩ := exists_avoiding_multiple_in_consecInterval x M g₁₂ {b₀, w₄}
    hg₁₂_pos (le_trans (Nat.mul_le_mul_right g₁₂ hpair_card) h3g₁₂)
  obtain ⟨w₂, hw₂_I, hw₂_not, hg13_w2⟩ := exists_avoiding_multiple_in_consecInterval x M g₁₃ {b₀, w₄}
    hg₁₃_pos (le_trans (Nat.mul_le_mul_right g₁₃ hpair_card) h3g₁₃)
  obtain ⟨w₃, hw₃_I, hw₃_not, hg23_w3⟩ := exists_avoiding_multiple_in_consecInterval x M g₂₃ {b₀, w₄}
    hg₂₃_pos (le_trans (Nat.mul_le_mul_right g₂₃ hpair_card) h3g₂₃)
  have hw1_b0 : w₁ ≠ b₀ := fun h => hw₁_not (by simp [h])
  have hw1_w4 : w₁ ≠ w₄ := fun h => hw₁_not (by simp [h])
  have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
  have hw2_w4 : w₂ ≠ w₄ := fun h => hw₂_not (by simp [h])
  have hw3_b0 : w₃ ≠ b₀ := fun h => hw₃_not (by simp [h])
  have hw3_w4 : w₃ ≠ w₄ := fun h => hw₃_not (by simp [h])
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      x₁.factorization p + x₂.factorization p + x₃.factorization p + x₄.factorization p := by
    intro p
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14]),
        Finset.sum_insert (by simp [h23, h24]), Finset.sum_insert (by simp [h34]),
        Finset.sum_singleton]
    ring
  have hb₀_1 := fac_le_of_dvd hb₀0 (hdiv_b0 x₁ (by rw [hA_eq]; simp)) (p := x₁) |> fun _ =>
    (fun (p : ℕ) => fac_le_of_dvd hb₀0 (hdiv_b0 x₁ (by rw [hA_eq]; simp)) (p := p))
  have hb₀_2 := fun (p : ℕ) => fac_le_of_dvd hb₀0 (hdiv_b0 x₂ (by rw [hA_eq]; simp)) (p := p)
  have hb₀_3 := fun (p : ℕ) => fac_le_of_dvd hb₀0 (hdiv_b0 x₃ (by rw [hA_eq]; simp)) (p := p)
  have hb₀_4 := fun (p : ℕ) => fac_le_of_dvd hb₀0 (hdiv_b0 x₄ (by rw [hA_eq]; simp)) (p := p)
  by_cases hall : w₁ = w₂ ∧ w₂ = w₃
  · rcases hall with ⟨rfl, rfl⟩
    let D := Nat.gcd g₁₂ x₃
    have hD_pos : 0 < D := Nat.gcd_pos_of_pos_left x₃ hg₁₂_pos
    have h5D : 5 * D ≤ M := five_mul_le_of_three_distinct_gt_half hD_pos h12 h13 h23
      hx₁_M hx₂_M hx₃_M hx₁_half hx₂_half hx₃_half
      (dvd_trans (Nat.gcd_dvd_left g₁₂ x₃) (Nat.gcd_dvd_left x₁ x₂))
      (dvd_trans (Nat.gcd_dvd_left g₁₂ x₃) (Nat.gcd_dvd_right x₁ x₂))
      (Nat.gcd_dvd_right g₁₂ x₃)
    have h3_card : ({b₀, w₄, w₁} : Finset ℕ).card + 1 ≤ 4 := by
      have h1 := Finset.card_insert_le b₀ {w₄, w₁}
      have h2 := Finset.card_insert_le w₄ {w₁}
      simp only [Finset.card_singleton] at h2
      omega
    obtain ⟨w', hw'_I, hw'_not, hD_w'⟩ := exists_avoiding_multiple_in_consecInterval x M D {b₀, w₄, w₁}
      hD_pos (le_trans (le_trans (Nat.mul_le_mul_right D h3_card) (by omega : 4 * D ≤ 5 * D)) h5D)
    have hw'_b0 : w' ≠ b₀ := fun h => hw'_not (by simp [h])
    have hw'_w4 : w' ≠ w₄ := fun h => hw'_not (by simp [h])
    have hw'_w1 : w' ≠ w₁ := fun h => hw'_not (by simp [h])
    let B : Finset ℕ := {b₀, w₄, w₁, w'}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hBcard : B.card ≤ 5 := le_trans (card_finset_le_four b₀ w₄ w₁ w') (by omega)
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
    have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
    refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
    intro p _hp
    rw [hsumA_eq p, Finset.sum_insert (by simp [hw4_b0.symm, hw1_b0.symm, hw'_b0.symm]),
        Finset.sum_insert (by simp [hw1_w4.symm, hw'_w4.symm]),
        Finset.sum_insert (by simp [hw'_w1.symm]), Finset.sum_singleton]
    have hw4_h := fac_le_of_dvd hw40 hh_w₄ (p := p)
    have hw1_12 := fac_le_of_dvd hw10 hg12_w1 (p := p)
    have hw1_13 := fac_le_of_dvd hw10 hg13_w2 (p := p)
    have hw1_23 := fac_le_of_dvd hw10 hg23_w3 (p := p)
    have hw'_D := fac_le_of_dvd hw'0 hD_w' (p := p)
    rw [fac_gcd_eq_min hL_pos.ne' hx₄_pos.ne'] at hw4_h
    have hL_fac : L.factorization p = max (max (x₁.factorization p) (x₂.factorization p)) (x₃.factorization p) := by
      dsimp only [L]
      rw [Nat.factorization_lcm (Nat.lcm_pos hx₁_pos hx₂_pos).ne' hx₃_pos.ne', Finsupp.sup_apply,
          Nat.factorization_lcm hx₁_pos.ne' hx₂_pos.ne', Finsupp.sup_apply]
      try rfl
    rw [hL_fac] at hw4_h
    rw [fac_gcd_eq_min hx₁_pos.ne' hx₂_pos.ne'] at hw1_12
    rw [fac_gcd_eq_min hx₁_pos.ne' hx₃_pos.ne'] at hw1_13
    rw [fac_gcd_eq_min hx₂_pos.ne' hx₃_pos.ne'] at hw1_23
    rw [fac_gcd_eq_min hg₁₂_pos.ne' hx₃_pos.ne', fac_gcd_eq_min hx₁_pos.ne' hx₂_pos.ne'] at hw'_D
    have := hb₀_1 p; have := hb₀_2 p; have := hb₀_3 p; have := hb₀_4 p
    rcases le_total (x₁.factorization p) (x₂.factorization p) with h12_le | h21_le <;>
    rcases le_total (x₂.factorization p) (x₃.factorization p) with h23_le | h32_le <;>
    rcases le_total (x₁.factorization p) (x₃.factorization p) with h13_le | h31_le <;>
    rcases le_total (x₄.factorization p) (max (max (x₁.factorization p) (x₂.factorization p)) (x₃.factorization p)) with h4L | hL4 <;> omega
  · let B : Finset ℕ := {b₀, w₄, w₁, w₂, w₃}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hBcard : B.card ≤ 5 := card_finset_le_five b₀ w₄ w₁ w₂ w₃
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
    have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
    have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
    refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
    intro p _hp
    rw [hsumA_eq p]
    have hw4_h := fac_le_of_dvd hw40 hh_w₄ (p := p)
    rw [fac_gcd_eq_min hL_pos.ne' hx₄_pos.ne'] at hw4_h
    have hx1_L : x₁.factorization p ≤ L.factorization p :=
      fac_le_of_dvd hL_pos.ne' (dvd_trans (Nat.dvd_lcm_left x₁ x₂) (Nat.dvd_lcm_left (Nat.lcm x₁ x₂) x₃)) (p := p)
    have hx2_L : x₂.factorization p ≤ L.factorization p :=
      fac_le_of_dvd hL_pos.ne' (dvd_trans (Nat.dvd_lcm_right x₁ x₂) (Nat.dvd_lcm_left (Nat.lcm x₁ x₂) x₃)) (p := p)
    have hx3_L : x₃.factorization p ≤ L.factorization p :=
      fac_le_of_dvd hL_pos.ne' (Nat.dvd_lcm_right (Nat.lcm x₁ x₂) x₃) (p := p)
    have hw1_12 := fac_le_of_dvd hw10 hg12_w1 (p := p)
    have hw2_13 := fac_le_of_dvd hw20 hg13_w2 (p := p)
    have hw3_23 := fac_le_of_dvd hw30 hg23_w3 (p := p)
    rw [fac_gcd_eq_min hx₁_pos.ne' hx₂_pos.ne'] at hw1_12
    rw [fac_gcd_eq_min hx₁_pos.ne' hx₃_pos.ne'] at hw2_13
    rw [fac_gcd_eq_min hx₂_pos.ne' hx₃_pos.ne'] at hw3_23
    by_cases hw12 : w₁ = w₂
    · have hw23 : w₂ ≠ w₃ := fun h => hall ⟨hw12, h⟩
      have hw13 : w₁ ≠ w₃ := by rw [hw12]; exact hw23
      have hsub4 : ({b₀, w₄, w₁, w₃} : Finset ℕ) ⊆ B := by
        intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
      have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
      rw [Finset.sum_insert (by simp [hw4_b0.symm, hw1_b0.symm, hw3_b0.symm]),
          Finset.sum_insert (by simp [hw1_w4.symm, hw3_w4.symm]),
          Finset.sum_insert (by simp [hw13]), Finset.sum_singleton] at hleB
      rw [← hw12] at hw2_13
      have hsum := r1_1a_pair_sum_le (hb₀_1 p) (hb₀_2 p) (hb₀_3 p) (hb₀_4 p)
        hx1_L hx2_L hx3_L hw4_h hw1_12 hw2_13 hw3_23
      omega
    · by_cases hw13 : w₁ = w₃
      · have hsub4 : ({b₀, w₄, w₁, w₂} : Finset ℕ) ⊆ B := by
          intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hw4_b0.symm, hw1_b0.symm, hw2_b0.symm]),
            Finset.sum_insert (by simp [hw1_w4.symm, hw2_w4.symm]),
            Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
        rw [← hw13] at hw3_23
        have hsum := r1_1a_pair_sum_le (hb₀_2 p) (hb₀_1 p) (hb₀_3 p) (hb₀_4 p)
          hx2_L hx1_L hx3_L hw4_h (le_of_eq_of_le (min_comm _ _) hw1_12) hw3_23 hw2_13
        omega
      · by_cases hw23 : w₂ = w₃
        · have hsub4 : ({b₀, w₄, w₁, w₂} : Finset ℕ) ⊆ B := by
            intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
          have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
          rw [Finset.sum_insert (by simp [hw4_b0.symm, hw1_b0.symm, hw2_b0.symm]),
              Finset.sum_insert (by simp [hw1_w4.symm, hw2_w4.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
          rw [← hw23] at hw3_23
          have hsum := r1_1a_pair_sum_le (hb₀_3 p) (hb₀_1 p) (hb₀_2 p) (hb₀_4 p)
            hx3_L hx1_L hx2_L hw4_h (le_of_eq_of_le (min_comm _ _) hw2_13)
            (le_of_eq_of_le (min_comm _ _) hw3_23) hw1_12
          omega
        · have hleB : b₀.factorization p + (w₄.factorization p + (w₁.factorization p +
              (w₂.factorization p + w₃.factorization p))) ≤ ∑ b ∈ B, b.factorization p := by
            calc b₀.factorization p + (w₄.factorization p + (w₁.factorization p +
                    (w₂.factorization p + w₃.factorization p)))
                = ∑ b ∈ ({b₀, w₄, w₁, w₂, w₃} : Finset ℕ), b.factorization p := by
                  rw [Finset.sum_insert (by simp [hw4_b0.symm, hw1_b0.symm, hw2_b0.symm, hw3_b0.symm]),
                      Finset.sum_insert (by simp [hw1_w4.symm, hw2_w4.symm, hw3_w4.symm]),
                      Finset.sum_insert (by simp [hw12, hw13]),
                      Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
              _ ≤ ∑ b ∈ B, b.factorization p := le_rfl
          have hsum := r1_1a_pair_sum_le (hb₀_1 p) (hb₀_2 p) (hb₀_3 p) (hb₀_4 p)
            hx1_L hx2_L hx3_L hw4_h
            (le_trans hw1_12 (Nat.le_add_right _ _))
            (le_trans hw2_13 (Nat.le_add_left _ _)) hw3_23
          omega

private lemma exists_cover_five_of_AB_split {A : Finset ℕ} {x M b₀ u₁ u₂ u₃ u₄ Ap Bp : ℕ}
    (hA_eq : A = {u₁, u₂, u₃, u₄})
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h14 : u₁ ≠ u₄)
    (h23 : u₂ ≠ u₃) (h24 : u₂ ≠ u₄) (h34 : u₃ ≠ u₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (hAp_pos : 0 < Ap) (hBp_pos : 0 < Bp) (hcop_AB : Nat.Coprime Ap Bp)
    (h2Ap : 2 * Ap ≤ M) (h2Bp : 2 * Bp ≤ M)
    (hineq : ∀ p : ℕ, p.Prime →
      u₁.factorization p + u₂.factorization p + u₃.factorization p + u₄.factorization p ≤
        max (max (u₁.factorization p) (u₂.factorization p))
            (max (u₃.factorization p) (u₄.factorization p)) +
        Ap.factorization p + Bp.factorization p +
        (Nat.gcd u₁ u₂).factorization p + (Nat.gcd u₃ u₄).factorization p) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hu₃_pos : 0 < u₃ := hA_pos u₃ (by rw [hA_eq]; simp)
  have hu₄_pos : 0 < u₄ := hA_pos u₄ (by rw [hA_eq]; simp)
  have hu₁_M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hu₂_M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hu₃_M : u₃ ≤ M := hA_le u₃ (by rw [hA_eq]; simp)
  have hu₄_M : u₄ ≤ M := hA_le u₄ (by rw [hA_eq]; simp)
  have hu₁_half : M < 2 * u₁ := hM_half u₁ (by rw [hA_eq]; simp)
  have hu₂_half : M < 2 * u₂ := hM_half u₂ (by rw [hA_eq]; simp)
  have hu₃_half : M < 2 * u₃ := hM_half u₃ (by rw [hA_eq]; simp)
  have hu₄_half : M < 2 * u₄ := hM_half u₄ (by rw [hA_eq]; simp)
  obtain ⟨w₁, hw₁_I, hw₁_nb0, hAp_w1⟩ := exists_avoiding_multiple_in_consecInterval x M Ap {b₀}
    hAp_pos (by simpa using h2Ap)
  obtain ⟨w₂, hw₂_I, hw₂_nb0, hBp_w2⟩ := exists_avoiding_multiple_in_consecInterval x M Bp {b₀}
    hBp_pos (by simpa using h2Bp)
  have hw1_b0 : w₁ ≠ b₀ := by simpa using hw₁_nb0
  have hw2_b0 : w₂ ≠ b₀ := by simpa using hw₂_nb0
  let D₃ := Nat.gcd u₁ u₂
  let D₄ := Nat.gcd u₃ u₄
  have hD₃_pos : 0 < D₃ := Nat.gcd_pos_of_pos_left u₂ hu₁_pos
  have hD₄_pos : 0 < D₄ := Nat.gcd_pos_of_pos_left u₄ hu₃_pos
  have h3D₃ : 3 * D₃ ≤ M := three_mul_le_of_two_ne_gt_half hD₃_pos h12 hu₁_M hu₂_M
    hu₁_half hu₂_half (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
  have h3D₄ : 3 * D₄ ≤ M := three_mul_le_of_two_ne_gt_half hD₄_pos h34 hu₃_M hu₄_M
    hu₃_half hu₄_half (Nat.gcd_dvd_left u₃ u₄) (Nat.gcd_dvd_right u₃ u₄)
  have hcop_D34 : Nat.Coprime D₃ D₄ := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd : Nat.gcd D₃ D₄ ∣ A.gcd id := by
      apply Finset.dvd_gcd
      intro a ha; rw [hA_eq] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · exact dvd_trans (Nat.gcd_dvd_left D₃ D₄) (Nat.gcd_dvd_left u₁ u₂)
      · exact dvd_trans (Nat.gcd_dvd_left D₃ D₄) (Nat.gcd_dvd_right u₁ u₂)
      · exact dvd_trans (Nat.gcd_dvd_right D₃ D₄) (Nat.gcd_dvd_left u₃ u₄)
      · exact dvd_trans (Nat.gcd_dvd_right D₃ D₄) (Nat.gcd_dvd_right u₃ u₄)
    rw [hAgcd] at hd
    exact Nat.dvd_one.mp hd
  have hS3_ex : ∃ (S₃ : Finset ℕ), S₃ ⊆ consecInterval x M ∧ S₃.card ≤ 1 ∧
      Disjoint {b₀, w₁, w₂} S₃ ∧
      (∀ p : ℕ, p.Prime → D₃.factorization p + Ap.factorization p + Bp.factorization p ≤
        (∑ b ∈ ({w₁, w₂} : Finset ℕ), b.factorization p) + ∑ b ∈ S₃, b.factorization p) := by
    by_cases hsub3 : (consecInterval x M).filter (fun b => D₃ ∣ b) ⊆ {b₀, w₁, w₂}
    · have hcard3 : 3 ≤ ((consecInterval x M).filter (fun b => D₃ ∣ b)).card := by
        have h1 := card_multiples_Icc_ge x M D₃ hD₃_pos
        have h2 : 3 ≤ M / D₃ := (Nat.le_div_iff_mul_le hD₃_pos).mpr h3D₃
        change M / D₃ ≤ ((consecInterval x M).filter (fun b => D₃ ∣ b)).card at h1
        omega
      have hset_card : ({b₀, w₁, w₂} : Finset ℕ).card ≤ 3 := card_finset_le_three b₀ w₁ w₂
      have heq3 : (consecInterval x M).filter (fun b => D₃ ∣ b) = {b₀, w₁, w₂} :=
        Finset.eq_of_subset_of_card_le hsub3 (by omega)
      have hw12 : w₁ ≠ w₂ := by
        intro h
        have hcard_le2 : ({b₀, w₁, w₂} : Finset ℕ).card ≤ 2 := by
          rw [h, show ({b₀, w₂, w₂} : Finset ℕ) = {b₀, w₂} by ext z; simp]
          exact le_trans (Finset.card_insert_le b₀ {w₂}) (by simp)
        have hcard_flt := Finset.card_le_card hsub3
        omega
      have hw1_D3 : D₃ ∣ w₁ := (Finset.mem_filter.mp (by rw [heq3]; simp)).2
      have hw2_D3 : D₃ ∣ w₂ := (Finset.mem_filter.mp (by rw [heq3]; simp)).2
      refine ⟨∅, Finset.empty_subset _, by simp, Finset.disjoint_empty_right _, ?_⟩
      intro p hp
      rw [Finset.sum_empty, add_zero, Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have h1a := fac_le_of_dvd hw10 hAp_w1 (p := p)
      have h1b := fac_le_of_dvd hw10 hw1_D3 (p := p)
      have h2a := fac_le_of_dvd hw20 hBp_w2 (p := p)
      have h2b := fac_le_of_dvd hw20 hw2_D3 (p := p)
      rcases coprime_factorization_zero hAp_pos hBp_pos hp hcop_AB with hA0' | hB0'
      · rw [hA0']; omega
      · rw [hB0']; omega
    · obtain ⟨w₃, hw₃_flt, hw₃_not⟩ := Finset.not_subset.mp hsub3
      rw [Finset.mem_filter] at hw₃_flt
      refine ⟨{w₃}, Finset.singleton_subset_iff.mpr hw₃_flt.1, by simp,
        Finset.disjoint_singleton_right.mpr hw₃_not, ?_⟩
      intro p hp
      rw [Finset.sum_singleton]
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_flt.1).ne'
      have h1a := fac_le_of_dvd hw10 hAp_w1 (p := p)
      have h2a := fac_le_of_dvd hw20 hBp_w2 (p := p)
      have h3a := fac_le_of_dvd hw30 hw₃_flt.2 (p := p)
      by_cases hw12 : w₁ = w₂
      · rw [hw12] at h1a ⊢
        rw [show ({w₂, w₂} : Finset ℕ) = {w₂} by ext z; simp, Finset.sum_singleton]
        rcases coprime_factorization_zero hAp_pos hBp_pos hp hcop_AB with hA0' | hB0'
        · rw [hA0']; omega
        · rw [hB0']; omega
      · rw [Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
        omega
  have hS4_ex : ∃ (S₄ : Finset ℕ), S₄ ⊆ consecInterval x M ∧ S₄.card ≤ 1 ∧
      Disjoint {b₀, w₁, w₂} S₄ ∧
      (∀ p : ℕ, p.Prime → D₄.factorization p + Ap.factorization p + Bp.factorization p ≤
        (∑ b ∈ ({w₁, w₂} : Finset ℕ), b.factorization p) + ∑ b ∈ S₄, b.factorization p) := by
    by_cases hsub4 : (consecInterval x M).filter (fun b => D₄ ∣ b) ⊆ {b₀, w₁, w₂}
    · have hcard3 : 3 ≤ ((consecInterval x M).filter (fun b => D₄ ∣ b)).card := by
        have h1 := card_multiples_Icc_ge x M D₄ hD₄_pos
        have h2 : 3 ≤ M / D₄ := (Nat.le_div_iff_mul_le hD₄_pos).mpr h3D₄
        change M / D₄ ≤ ((consecInterval x M).filter (fun b => D₄ ∣ b)).card at h1
        omega
      have hset_card : ({b₀, w₁, w₂} : Finset ℕ).card ≤ 3 := card_finset_le_three b₀ w₁ w₂
      have heq4 : (consecInterval x M).filter (fun b => D₄ ∣ b) = {b₀, w₁, w₂} :=
        Finset.eq_of_subset_of_card_le hsub4 (by omega)
      have hw12 : w₁ ≠ w₂ := by
        intro h
        have hcard_le2 : ({b₀, w₁, w₂} : Finset ℕ).card ≤ 2 := by
          rw [h, show ({b₀, w₂, w₂} : Finset ℕ) = {b₀, w₂} by ext z; simp]
          exact le_trans (Finset.card_insert_le b₀ {w₂}) (by simp)
        have hcard_flt := Finset.card_le_card hsub4
        omega
      have hw1_D4 : D₄ ∣ w₁ := (Finset.mem_filter.mp (by rw [heq4]; simp)).2
      have hw2_D4 : D₄ ∣ w₂ := (Finset.mem_filter.mp (by rw [heq4]; simp)).2
      refine ⟨∅, Finset.empty_subset _, by simp, Finset.disjoint_empty_right _, ?_⟩
      intro p hp
      rw [Finset.sum_empty, add_zero, Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have h1a := fac_le_of_dvd hw10 hAp_w1 (p := p)
      have h1b := fac_le_of_dvd hw10 hw1_D4 (p := p)
      have h2a := fac_le_of_dvd hw20 hBp_w2 (p := p)
      have h2b := fac_le_of_dvd hw20 hw2_D4 (p := p)
      rcases coprime_factorization_zero hAp_pos hBp_pos hp hcop_AB with hA0' | hB0'
      · rw [hA0']; omega
      · rw [hB0']; omega
    · obtain ⟨w₄, hw₄_flt, hw₄_not⟩ := Finset.not_subset.mp hsub4
      rw [Finset.mem_filter] at hw₄_flt
      refine ⟨{w₄}, Finset.singleton_subset_iff.mpr hw₄_flt.1, by simp,
        Finset.disjoint_singleton_right.mpr hw₄_not, ?_⟩
      intro p hp
      rw [Finset.sum_singleton]
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_flt.1).ne'
      have h1a := fac_le_of_dvd hw10 hAp_w1 (p := p)
      have h2a := fac_le_of_dvd hw20 hBp_w2 (p := p)
      have h4a := fac_le_of_dvd hw40 hw₄_flt.2 (p := p)
      by_cases hw12 : w₁ = w₂
      · rw [hw12] at h1a ⊢
        rw [show ({w₂, w₂} : Finset ℕ) = {w₂} by ext z; simp, Finset.sum_singleton]
        rcases coprime_factorization_zero hAp_pos hBp_pos hp hcop_AB with hA0' | hB0'
        · rw [hA0']; omega
        · rw [hB0']; omega
      · rw [Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
        omega
  obtain ⟨S₃, hS3_I, hS3_c, hdisj3, hS3_fac⟩ := hS3_ex
  obtain ⟨S₄, hS4_I, hS4_c, hdisj4, hS4_fac⟩ := hS4_ex
  let B₀ : Finset ℕ := {b₀, w₁, w₂}
  let B : Finset ℕ := B₀ ∪ (S₃ ∪ S₄)
  have hBI : B ⊆ consecInterval x M := by
    refine Finset.union_subset ?_ (Finset.union_subset hS3_I hS4_I)
    intro b hb; simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  have hBcard : B.card ≤ 5 := by
    dsimp only [B, B₀]
    have h1 := Finset.card_union_le ({b₀, w₁, w₂} : Finset ℕ) (S₃ ∪ S₄)
    have h2 := Finset.card_union_le S₃ S₄
    have h3 : ({b₀, w₁, w₂} : Finset ℕ).card ≤ 3 := card_finset_le_three b₀ w₁ w₂
    omega
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
  intro p hp
  have hsumA_eq : ∑ a ∈ A, a.factorization p =
      u₁.factorization p + u₂.factorization p + u₃.factorization p + u₄.factorization p := by
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14]),
        Finset.sum_insert (by simp [h23, h24]), Finset.sum_insert (by simp [h34]),
        Finset.sum_singleton]
    ring
  rw [hsumA_eq]
  have hb0_1 := fac_le_of_dvd hb₀0 (hdiv_b0 u₁ (by rw [hA_eq]; simp)) (p := p)
  have hb0_2 := fac_le_of_dvd hb₀0 (hdiv_b0 u₂ (by rw [hA_eq]; simp)) (p := p)
  have hb0_3 := fac_le_of_dvd hb₀0 (hdiv_b0 u₃ (by rw [hA_eq]; simp)) (p := p)
  have hb0_4 := fac_le_of_dvd hb₀0 (hdiv_b0 u₄ (by rw [hA_eq]; simp)) (p := p)
  have hb₀_max : max (max (u₁.factorization p) (u₂.factorization p))
      (max (u₃.factorization p) (u₄.factorization p)) ≤ b₀.factorization p := by
    omega
  have hB_split3 : ({b₀, w₁, w₂} : Finset ℕ) ∪ S₃ ⊆ B :=
    Finset.union_subset Finset.subset_union_left
      (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)
  have hB_split4 : ({b₀, w₁, w₂} : Finset ℕ) ∪ S₄ ⊆ B :=
    Finset.union_subset Finset.subset_union_left
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right)
  have hsumB3 : b₀.factorization p + (∑ b ∈ ({w₁, w₂} : Finset ℕ), b.factorization p) +
      ∑ b ∈ S₃, b.factorization p ≤ ∑ b ∈ B, b.factorization p := by
    have h1 := Finset.sum_le_sum_of_subset hB_split3 (f := fun b => b.factorization p)
    rw [Finset.sum_union hdisj3] at h1
    by_cases hbw : b₀ ∈ ({w₁, w₂} : Finset ℕ)
    · exfalso; simp only [Finset.mem_insert, Finset.mem_singleton] at hbw
      rcases hbw with rfl | rfl
      · exact hw1_b0 rfl
      · exact hw2_b0 rfl
    · rw [Finset.sum_insert hbw] at h1
      exact h1
  have hsumB4 : b₀.factorization p + (∑ b ∈ ({w₁, w₂} : Finset ℕ), b.factorization p) +
      ∑ b ∈ S₄, b.factorization p ≤ ∑ b ∈ B, b.factorization p := by
    have h1 := Finset.sum_le_sum_of_subset hB_split4 (f := fun b => b.factorization p)
    rw [Finset.sum_union hdisj4] at h1
    by_cases hbw : b₀ ∈ ({w₁, w₂} : Finset ℕ)
    · exfalso; simp only [Finset.mem_insert, Finset.mem_singleton] at hbw
      rcases hbw with rfl | rfl
      · exact hw1_b0 rfl
      · exact hw2_b0 rfl
    · rw [Finset.sum_insert hbw] at h1
      exact h1
  have hineq_p := hineq p hp
  have hs3_p := hS3_fac p hp
  have hs4_p := hS4_fac p hp
  have hD3_def : D₃.factorization p = min (u₁.factorization p) (u₂.factorization p) :=
    fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne' (p := p)
  have hD4_def : D₄.factorization p = min (u₃.factorization p) (u₄.factorization p) :=
    fac_gcd_eq_min hu₃_pos.ne' hu₄_pos.ne' (p := p)
  rw [hD3_def, hD4_def] at hineq_p
  rw [hD3_def] at hs3_p
  rw [hD4_def] at hs4_p
  rcases coprime_factorization_zero hD₃_pos hD₄_pos hp hcop_D34 with hD3_0 | hD4_0
  · rw [hD3_def] at hD3_0
    rcases le_total (u₃.factorization p) (u₄.factorization p) with h34_le | h43_le <;> omega
  · rw [hD4_def] at hD4_0
    rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;> omega

private lemma cover_four_r1_three_primes_aux {A : Finset ℕ}
    {x M b₀ p q r x₁ x₂ x₃ x₄ : ℕ}
    (hA_eq : A = {x₁, x₂, x₃, x₄})
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (_hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r)
    (hx3_p : x₃.factorization p = x₂.factorization p)
    (hx3_q : x₃.factorization q = x₁.factorization q)
    (hx2_r : x₂.factorization r = x₁.factorization r)
    (hx1_p0 : x₁.factorization p = 0)
    (hx2_q0 : x₂.factorization q = 0)
    (hx3_r0 : x₃.factorization r = 0)
    (hu_p : x₄.factorization p < x₂.factorization p)
    (_hu_q : x₄.factorization q < x₁.factorization q)
    (_hu_r : x₄.factorization r < x₁.factorization r)
    (hrest : ∀ s : ℕ, s.Prime → s ≠ p → s ≠ q → s ≠ r →
      x₁.factorization s = 0 ∧ x₂.factorization s = 0 ∧ x₃.factorization s = 0 ∧ x₄.factorization s = 0)
    (h2Qq : 2 * q ^ (x₄.factorization q + x₁.factorization q) ≤ M)
    (h2Qr : 2 * r ^ (x₄.factorization r + x₁.factorization r) ≤ M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  have hx₂_pos : 0 < x₂ := hA_pos x₂ (by rw [hA_eq]; simp)
  have hx₃_pos : 0 < x₃ := hA_pos x₃ (by rw [hA_eq]; simp)
  have hx₄_pos : 0 < x₄ := hA_pos x₄ (by rw [hA_eq]; simp)
  have hx₂_M : x₂ ≤ M := hA_le x₂ (by rw [hA_eq]; simp)
  have hx₃_M : x₃ ≤ M := hA_le x₃ (by rw [hA_eq]; simp)
  have hx₄_M : x₄ ≤ M := hA_le x₄ (by rw [hA_eq]; simp)
  have hx₂_half : M < 2 * x₂ := hM_half x₂ (by rw [hA_eq]; simp)
  have hx₃_half : M < 2 * x₃ := hM_half x₃ (by rw [hA_eq]; simp)
  have hx₄_half : M < 2 * x₄ := hM_half x₄ (by rw [hA_eq]; simp)
  let ep := x₂.factorization p
  let up := x₄.factorization p
  let pe := p ^ ep
  let pu := p ^ up
  let Qq := q ^ (x₄.factorization q + x₁.factorization q)
  let Qr := r ^ (x₄.factorization r + x₁.factorization r)
  have hpe_pos : 0 < pe := pow_pos hp.pos ep
  have hpu_pos : 0 < pu := pow_pos hp.pos up
  have hQq_pos : 0 < Qq := pow_pos hq.pos _
  have hQr_pos : 0 < Qr := pow_pos hr.pos _
  have hpe_x2 : pe ∣ x₂ := Nat.ordProj_dvd x₂ p
  have hpe_x3 : pe ∣ x₃ := by
    dsimp only [pe, ep]; rw [← hx3_p]; exact Nat.ordProj_dvd x₃ p
  have h3pe : 3 * pe ≤ M := three_mul_le_of_two_ne_gt_half hpe_pos h23 hx₂_M hx₃_M
    hx₂_half hx₃_half hpe_x2 hpe_x3
  have hpu_x4 : pu ∣ x₄ := Nat.ordProj_dvd x₄ p
  have hpu_x2 : pu ∣ x₂ := dvd_trans (Nat.pow_dvd_pow p hu_p.le) hpe_x2
  have hpu_x3 : pu ∣ x₃ := dvd_trans (Nat.pow_dvd_pow p hu_p.le) hpe_x3
  have h5pu : 5 * pu ≤ M := five_mul_le_of_three_distinct_gt_half hpu_pos h23 h24 h34
    hx₂_M hx₃_M hx₄_M hx₂_half hx₃_half hx₄_half hpu_x2 hpu_x3 hpu_x4
  obtain ⟨w₁, hw₁_I, hw₁_nb0, hpe_w1⟩ := exists_avoiding_multiple_in_consecInterval x M pe {b₀}
    hpe_pos (by simpa using le_trans (by omega : 2 * pe ≤ 3 * pe) h3pe)
  obtain ⟨wq, hwq_I, hwq_nb0, hQq_wq⟩ := exists_avoiding_multiple_in_consecInterval x M Qq {b₀}
    hQq_pos (by simpa using h2Qq)
  obtain ⟨wr, hwr_I, hwr_nb0, hQr_wr⟩ := exists_avoiding_multiple_in_consecInterval x M Qr {b₀}
    hQr_pos (by simpa using h2Qr)
  have h4_card : ({b₀, w₁, wq, wr} : Finset ℕ).card + 1 ≤ 5 := by
    have h1 := Finset.card_insert_le b₀ {w₁, wq, wr}
    have h2 := Finset.card_insert_le w₁ {wq, wr}
    have h3 := Finset.card_insert_le wq {wr}
    simp only [Finset.card_singleton] at h3
    omega
  obtain ⟨w₂, hw₂_I, hw₂_not, hpu_w2⟩ := exists_avoiding_multiple_in_consecInterval x M pu {b₀, w₁, wq, wr}
    hpu_pos (le_trans (Nat.mul_le_mul_right pu h4_card) h5pu)
  have hw1_b0 : w₁ ≠ b₀ := by simpa using hw₁_nb0
  have hwq_b0 : wq ≠ b₀ := by simpa using hwq_nb0
  have hwr_b0 : wr ≠ b₀ := by simpa using hwr_nb0
  have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
  have hw2_w1 : w₂ ≠ w₁ := fun h => hw₂_not (by simp [h])
  have hw2_wq : w₂ ≠ wq := fun h => hw₂_not (by simp [h])
  have hw2_wr : w₂ ≠ wr := fun h => hw₂_not (by simp [h])
  let B : Finset ℕ := {b₀, w₁, w₂, wq, wr}
  have hBI : B ⊆ consecInterval x M := by
    intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hBcard : B.card ≤ 5 := card_finset_le_five b₀ w₁ w₂ wq wr
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
  have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hwq0 : wq ≠ 0 := (pos_of_mem_consecInterval hwq_I).ne'
  have hwr0 : wr ≠ 0 := (pos_of_mem_consecInterval hwr_I).ne'
  refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
  intro s hs
  rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]), Finset.sum_insert (by simp [h34]),
      Finset.sum_singleton]
  by_cases hsp : s = p
  · subst s
    have hsub3 : ({b₀, w₁, w₂} : Finset ℕ) ⊆ B := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
    have hleB := Finset.sum_le_sum_of_subset hsub3 (f := fun b => b.factorization p)
    rw [Finset.sum_insert (by simp [hw1_b0.symm, hw2_b0.symm]),
        Finset.sum_insert (by simp [hw2_w1.symm]), Finset.sum_singleton] at hleB
    have hb0_p := fac_le_of_dvd hb₀0 (hdiv_b0 x₂ (by rw [hA_eq]; simp)) (p := p)
    have hw1_p := fac_le_of_dvd hw10 hpe_w1 (p := p)
    have hw2_p := fac_le_of_dvd hw20 hpu_w2 (p := p)
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hw1_p hw2_p
    omega
  · by_cases hsq : s = q
    · subst s
      have hsub2 : ({b₀, wq} : Finset ℕ) ⊆ B := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
      have hleB := Finset.sum_le_sum_of_subset hsub2 (f := fun b => b.factorization q)
      rw [Finset.sum_insert (by simp [hwq_b0.symm]), Finset.sum_singleton] at hleB
      have hb0_q := fac_le_of_dvd hb₀0 (hdiv_b0 x₁ (by rw [hA_eq]; simp)) (p := q)
      have hwq_q := fac_le_of_dvd hwq0 hQq_wq (p := q)
      rw [hq.factorization_pow, Finsupp.single_eq_same] at hwq_q
      omega
    · by_cases hsr : s = r
      · subst s
        have hsub2 : ({b₀, wr} : Finset ℕ) ⊆ B := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb ⊢; tauto
        have hleB := Finset.sum_le_sum_of_subset hsub2 (f := fun b => b.factorization r)
        rw [Finset.sum_insert (by simp [hwr_b0.symm]), Finset.sum_singleton] at hleB
        have hb0_r := fac_le_of_dvd hb₀0 (hdiv_b0 x₁ (by rw [hA_eq]; simp)) (p := r)
        have hwr_r := fac_le_of_dvd hwr0 hQr_wr (p := r)
        rw [hr.factorization_pow, Finsupp.single_eq_same] at hwr_r
        omega
      · obtain ⟨hz1, hz2, hz3, hz4⟩ := hrest s hs hsp hsq hsr
        omega

private def ValidAB (P : Finset ℕ) (u₁ u₂ u₃ u₄ : ℕ) : Prop :=
  ∃ (T_A : Finset ℕ),
    let mustA := P.filter (fun p =>
      (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
      ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p))
    let mustB := P.filter (fun p =>
      (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
      ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p))
    let ties := P.filter (fun p =>
      (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
      ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
      0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p)
    T_A ⊆ ties ∧
    (∏ p ∈ mustA ∪ T_A, p ^ (u₂.factorization p)) < u₂ ∧
    (∏ p ∈ mustB ∪ (ties \ T_A), p ^ (u₁.factorization p)) < u₁

private lemma validAB_swap34 {P : Finset ℕ} {u₁ u₂ u₃ u₄ : ℕ}
    (h : ValidAB P u₁ u₂ u₃ u₄) : ValidAB P u₁ u₂ u₄ u₃ := by
  rcases h with ⟨T_A, hsub, h1, h2⟩
  refine ⟨T_A, ?_, ?_, ?_⟩
  · intro p hp
    have h := Finset.mem_filter.mp (hsub hp)
    exact Finset.mem_filter.mpr ⟨h.1, Or.symm h.2.1, fun ⟨h4, h3⟩ => h.2.2.1 ⟨h3, h4⟩, h.2.2.2⟩
  · have hEq : (P.filter (fun p =>
        (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
        ((u₄.factorization p = 0 ∨ u₃.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p)) ∪ T_A) =
      (P.filter (fun p =>
        (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p)) ∪ T_A) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hP, hA⟩ | hpT)
        · exact Or.inl ⟨hP, hA.imp_right fun ⟨h34, h12⟩ => ⟨h34.symm, h12⟩⟩
        · exact Or.inr hpT
      · rintro (⟨hP, hA⟩ | hpT)
        · exact Or.inl ⟨hP, hA.imp_right fun ⟨h34, h12⟩ => ⟨h34.symm, h12⟩⟩
        · exact Or.inr hpT
    rw [hEq]
    exact h1
  · have hEq : (P.filter (fun p =>
        (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
        ((u₄.factorization p = 0 ∨ u₃.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p)) ∪
        (P.filter (fun p =>
          (u₄.factorization p = 0 ∨ u₃.factorization p = 0) ∧
          ¬ (u₄.factorization p = 0 ∧ u₃.factorization p = 0) ∧
          0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p) \ T_A)) =
      (P.filter (fun p =>
        (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p)) ∪
        (P.filter (fun p =>
          (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
          ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
          0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p) \ T_A)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro (⟨hP, hB⟩ | ⟨⟨hP, h34, hne, h12⟩, hnot⟩)
        · exact Or.inl ⟨hP, hB.imp_right fun ⟨h34, h12⟩ => ⟨h34.symm, h12⟩⟩
        · exact Or.inr ⟨⟨hP, h34.symm, fun ⟨h3, h4⟩ => hne ⟨h4, h3⟩, h12⟩, hnot⟩
      · rintro (⟨hP, hB⟩ | ⟨⟨hP, h34, hne, h12⟩, hnot⟩)
        · exact Or.inl ⟨hP, hB.imp_right fun ⟨h34, h12⟩ => ⟨h34.symm, h12⟩⟩
        · exact Or.inr ⟨⟨hP, h34.symm, fun ⟨h3, h4⟩ => hne ⟨h4, h3⟩, h12⟩, hnot⟩
    rw [hEq]
    exact h2

private lemma validAB_swap12 {P : Finset ℕ} {u₁ u₂ u₃ u₄ : ℕ}
    (h : ValidAB P u₁ u₂ u₃ u₄) : ValidAB P u₂ u₁ u₃ u₄ := by
  rcases h with ⟨T_A, hsub, h1, h2⟩
  let ties₁ := P.filter (fun p =>
    (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
    ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
    0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p)
  refine ⟨ties₁ \ T_A, ?_, ?_, ?_⟩
  · intro p hp
    have hm := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
    exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1, hm.2.2.1, by omega, hm.2.2.2.2.symm⟩
  · have hEq : (P.filter (fun p =>
        (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p)) ∪
        (ties₁ \ T_A)) =
      (P.filter (fun p =>
        (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p)) ∪
        (ties₁ \ T_A)) := rfl
    exact hEq ▸ h2
  · have hEq : (P.filter (fun p =>
        (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p)) ∪
        (P.filter (fun p =>
          (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
          ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
          0 < u₂.factorization p ∧ u₂.factorization p = u₁.factorization p) \ (ties₁ \ T_A))) =
      (P.filter (fun p =>
        (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
        ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p)) ∪ T_A) := by
      ext p
      simp only [ties₁, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro (hA | ⟨⟨hP, h34, hne, hpos2, heq2⟩, hnot⟩)
        · exact Or.inl hA
        · by_cases hpT : p ∈ T_A
          · exact Or.inr hpT
          · exact absurd ⟨⟨hP, h34, hne, by omega, heq2.symm⟩, hpT⟩ hnot
      · rintro (hA | hpT)
        · exact Or.inl hA
        · have hm := Finset.mem_filter.mp (hsub hpT)
          exact Or.inr ⟨⟨hm.1, hm.2.1, hm.2.2.1, by omega, hm.2.2.2.2.symm⟩, fun h => h.2 hpT⟩
    rw [hEq]
    exact h1

private lemma r1_top2_all {A : Finset ℕ} (hA_pos : ∀ a ∈ A, 0 < a)
    (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    {u₁ u₂ u₃ u₄ : ℕ} (hAu : A = {u₁, u₂, u₃, u₄})
    (_hu12 : u₁ ≠ u₂) (_hu13 : u₁ ≠ u₃) (hu14 : u₁ ≠ u₄)
    (_hu23 : u₂ ≠ u₃) (hu24 : u₂ ≠ u₄) (hu34 : u₃ ≠ u₄)
    (r : ℕ) (_hr : r.Prime) :
    u₄.factorization r ≤ max (max (u₁.factorization r) (u₂.factorization r)) (u₃.factorization r) := by
  have hd := hlcm_all u₄ (by rw [hAu]; simp)
  have hAu_er : A.erase u₄ = {u₁, u₂, u₃} := by
    rw [hAu]; ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl | rfl⟩ <;> simp_all
    · rintro (rfl | rfl | rfl)
      · exact ⟨hu14, Or.inl rfl⟩
      · exact ⟨hu24, Or.inr (Or.inl rfl)⟩
      · exact ⟨hu34, Or.inr (Or.inr (Or.inl rfl))⟩
  have hL_eq : (A.erase u₄).lcm id = Nat.lcm (Nat.lcm u₁ u₂) u₃ := by
    rw [hAu_er]
    exact lcm_triple_eq u₁ u₂ u₃
  rw [hL_eq] at hd
  have hu₁0 : u₁ ≠ 0 := (hA_pos u₁ (by rw [hAu]; simp)).ne'
  have hu₂0 : u₂ ≠ 0 := (hA_pos u₂ (by rw [hAu]; simp)).ne'
  have hu₃0 : u₃ ≠ 0 := (hA_pos u₃ (by rw [hAu]; simp)).ne'
  have hL0 : Nat.lcm (Nat.lcm u₁ u₂) u₃ ≠ 0 :=
    (Nat.lcm_pos (Nat.lcm_pos (Nat.pos_of_ne_zero hu₁0) (Nat.pos_of_ne_zero hu₂0))
      (Nat.pos_of_ne_zero hu₃0)).ne'
  have hle := fac_le_of_dvd hL0 hd (p := r)
  rw [Nat.factorization_lcm (Nat.lcm_pos (Nat.pos_of_ne_zero hu₁0) (Nat.pos_of_ne_zero hu₂0)).ne' hu₃0,
      Finsupp.sup_apply, Nat.factorization_lcm hu₁0 hu₂0, Finsupp.sup_apply] at hle
  exact hle

private lemma r1_min0 {A : Finset ℕ} {a₁ a₂ a₃ a₄ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄})
    (hA_pos : ∀ a ∈ A, 0 < a) (hAgcd : A.gcd id = 1)
    (r : ℕ) (hr : r.Prime) :
    a₁.factorization r = 0 ∨ a₂.factorization r = 0 ∨
    a₃.factorization r = 0 ∨ a₄.factorization r = 0 := by
  by_contra hpos; push Not at hpos
  have hd : r ∣ A.gcd id := by
    apply Finset.dvd_gcd
    intro a ha; rw [hA_eq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha | ha | ha <;> rw [ha]
    · exact prime_dvd_of_fac_ne_zero hr (hA_pos a₁ (by rw [hA_eq]; simp)).ne' hpos.1
    · exact prime_dvd_of_fac_ne_zero hr (hA_pos a₂ (by rw [hA_eq]; simp)).ne' hpos.2.1
    · exact prime_dvd_of_fac_ne_zero hr (hA_pos a₃ (by rw [hA_eq]; simp)).ne' hpos.2.2.1
    · exact prime_dvd_of_fac_ne_zero hr (hA_pos a₄ (by rw [hA_eq]; simp)).ne' hpos.2.2.2
  rw [hAgcd] at hd; exact hr.not_dvd_one hd

private lemma ab_split_pointwise {x₁ x₂ x₃ x₄ a b : ℕ}
    (hcase : (a = x₂ ∧ x₁ ≤ x₂) ∨ (b = x₁ ∧ x₂ ≤ x₁) ∨ (x₁ = 0 ∧ x₂ = 0) ∨ (x₃ = 0 ∧ x₄ = 0)) :
    x₁ + x₂ + x₃ + x₄ ≤ max (max x₁ x₂) (max x₃ x₄) + a + b + min x₁ x₂ + min x₃ x₄ := by
  rcases hcase with ⟨ha, h12⟩ | ⟨hb, h21⟩ | ⟨h10, h20⟩ | ⟨h30, h40⟩
  · subst ha; rcases le_total x₃ x₄ with _ | _ <;> omega
  · subst hb; rcases le_total x₃ x₄ with _ | _ <;> omega
  · rw [h10, h20]; rcases le_total x₃ x₄ with _ | _ <;> omega
  · rw [h30, h40]; rcases le_total x₁ x₂ with _ | _ <;> omega

private lemma cover_four_r1_of_validAB {A : Finset ℕ} {x M b₀ u₁ u₂ u₃ u₄ : ℕ}
    (hAu : A = {u₁, u₂, u₃, u₄})
    (hu12 : u₁ ≠ u₂) (hu13 : u₁ ≠ u₃) (hu14 : u₁ ≠ u₄)
    (hu23 : u₂ ≠ u₃) (hu24 : u₂ ≠ u₄) (hu34 : u₃ ≠ u₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (_hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hV : ValidAB (A.lcm id).primeFactors u₁ u₂ u₃ u₄) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  let P : Finset ℕ := (A.lcm id).primeFactors
  rcases hV with ⟨T_A, hT_sub, hAp_lt, hBp_lt⟩
  let mustA := P.filter (fun p =>
    (u₁.factorization p = 0 ∧ 0 < u₂.factorization p) ∨
    ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ u₁.factorization p < u₂.factorization p))
  let mustB := P.filter (fun p =>
    (u₂.factorization p = 0 ∧ 0 < u₁.factorization p) ∨
    ((u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧ 0 < u₂.factorization p ∧ u₂.factorization p < u₁.factorization p))
  let ties := P.filter (fun p =>
    (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
    ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
    0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p)
  let SA := mustA ∪ T_A
  let SB := mustB ∪ (ties \ T_A)
  let Ap := ∏ p ∈ SA, p ^ (u₂.factorization p)
  let Bp := ∏ p ∈ SB, p ^ (u₁.factorization p)
  have hSA_P : SA ⊆ P := Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans hT_sub (Finset.filter_subset _ _))
  have hSB_P : SB ⊆ P := Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
  have hAp_pos : 0 < Ap := Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (hSA_P hp)).pos _)
  have hBp_pos : 0 < Bp := Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors (hSB_P hp)).pos _)
  have hdisj_AB : Disjoint SA SB := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    simp only [SA, SB, mustA, mustB, ties, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff] at hpA hpB
    rcases hpA with ⟨_, hA_cond⟩ | hpTA
    · rcases hpB with ⟨_, hB_cond⟩ | ⟨⟨_, hT_cond⟩, _⟩
      · omega
      · omega
    · have hpT := hT_sub hpTA
      rw [Finset.mem_filter] at hpT
      rcases hpB with ⟨_, hB_cond⟩ | ⟨_, hnot⟩
      · omega
      · exact hnot hpTA
  have hcop_AB : Nat.Coprime Ap Bp := by
    apply Nat.Coprime.prod_left
    intro p hpA
    apply Nat.Coprime.prod_right
    intro q hqB
    have hne : p ≠ q := fun heq => (Finset.disjoint_left.mp hdisj_AB hpA (heq ▸ hqB))
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hSA_P hpA))
      (Nat.prime_of_mem_primeFactors (hSB_P hqB))).mpr hne).pow _ _
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hAu]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hAu]; simp)
  have hAp_dvd : Ap ∣ u₂ := by
    rw [← Nat.factorization_le_iff_dvd hAp_pos.ne' hu₂_pos.ne']
    intro p
    by_cases hpP : p ∈ P
    · have hne0 : ∀ q ∈ SA, q ^ (u₂.factorization q) ≠ 0 := fun q hq =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSA_P hq)).ne_zero
      rw [Nat.factorization_prod hne0]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
      have hterm : ∀ q ∈ SA, (q ^ (u₂.factorization q)).factorization p =
          if q = p then u₂.factorization q else 0 := by
        intro q hq
        rw [(Nat.prime_of_mem_primeFactors (hSA_P hq)).factorization_pow, Finsupp.single_apply]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs <;> omega
    · have hnot : p ∉ SA := fun h => hpP (hSA_P h)
      have hfac0 : Ap.factorization p = 0 := by
        have hne0 : ∀ q ∈ SA, q ^ (u₂.factorization q) ≠ 0 := fun q hq =>
          pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSA_P hq)).ne_zero
        rw [Nat.factorization_prod hne0]
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro q hq
        have hne : q ≠ p := fun heq => hnot (heq ▸ hq)
        rw [(Nat.prime_of_mem_primeFactors (hSA_P hq)).factorization_pow, Finsupp.single_apply, if_neg hne]
      omega
  have hBp_dvd : Bp ∣ u₁ := by
    rw [← Nat.factorization_le_iff_dvd hBp_pos.ne' hu₁_pos.ne']
    intro p
    by_cases hpP : p ∈ P
    · have hne0 : ∀ q ∈ SB, q ^ (u₁.factorization q) ≠ 0 := fun q hq =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSB_P hq)).ne_zero
      rw [Nat.factorization_prod hne0]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
      have hterm : ∀ q ∈ SB, (q ^ (u₁.factorization q)).factorization p =
          if q = p then u₁.factorization q else 0 := by
        intro q hq
        rw [(Nat.prime_of_mem_primeFactors (hSB_P hq)).factorization_pow, Finsupp.single_apply]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs <;> omega
    · have hnot : p ∉ SB := fun h => hpP (hSB_P h)
      have hfac0 : Bp.factorization p = 0 := by
        have hne0 : ∀ q ∈ SB, q ^ (u₁.factorization q) ≠ 0 := fun q hq =>
          pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSB_P hq)).ne_zero
        rw [Nat.factorization_prod hne0]
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro q hq
        have hne : q ≠ p := fun heq => hnot (heq ▸ hq)
        rw [(Nat.prime_of_mem_primeFactors (hSB_P hq)).factorization_pow, Finsupp.single_apply, if_neg hne]
      omega
  have h2Ap : 2 * Ap ≤ M := by
    change Ap < u₂ at hAp_lt
    obtain ⟨k, hk⟩ := hAp_dvd
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk_le1 : k ≤ 1 := by omega
      have : u₂ ≤ Ap := by
        calc u₂ = Ap * k := hk
          _ ≤ Ap * 1 := Nat.mul_le_mul_left Ap hk_le1
          _ = Ap := mul_one Ap
      omega
    have h1 : 2 * Ap ≤ Ap * k := by rw [mul_comm 2]; exact Nat.mul_le_mul_left Ap hk2
    exact le_trans h1 (by rw [← hk]; exact hA_le u₂ (by rw [hAu]; simp))
  have h2Bp : 2 * Bp ≤ M := by
    change Bp < u₁ at hBp_lt
    obtain ⟨k, hk⟩ := hBp_dvd
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk_le1 : k ≤ 1 := by omega
      have : u₁ ≤ Bp := by
        calc u₁ = Bp * k := hk
          _ ≤ Bp * 1 := Nat.mul_le_mul_left Bp hk_le1
          _ = Bp := mul_one Bp
      omega
    have h1 : 2 * Bp ≤ Bp * k := by rw [mul_comm 2]; exact Nat.mul_le_mul_left Bp hk2
    exact le_trans h1 (by rw [← hk]; exact hA_le u₁ (by rw [hAu]; simp))
  have hAp_fac : ∀ p : ℕ, p ∈ SA → Ap.factorization p = u₂.factorization p := by
    intro p hpSA
    have hne0 : ∀ q ∈ SA, q ^ (u₂.factorization q) ≠ 0 := fun q hq =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSA_P hq)).ne_zero
    rw [Nat.factorization_prod hne0]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ q ∈ SA, (q ^ (u₂.factorization q)).factorization p =
        if q = p then u₂.factorization q else 0 := by
      intro q hq
      rw [(Nat.prime_of_mem_primeFactors (hSA_P hq)).factorization_pow, Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hpSA]
  have hBp_fac : ∀ p : ℕ, p ∈ SB → Bp.factorization p = u₁.factorization p := by
    intro p hpSB
    have hne0 : ∀ q ∈ SB, q ^ (u₁.factorization q) ≠ 0 := fun q hq =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hSB_P hq)).ne_zero
    rw [Nat.factorization_prod hne0]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ q ∈ SB, (q ^ (u₁.factorization q)).factorization p =
        if q = p then u₁.factorization q else 0 := by
      intro q hq
      rw [(Nat.prime_of_mem_primeFactors (hSB_P hq)).factorization_pow, Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hpSB]
  refine exists_cover_five_of_AB_split hAu hu12 hu13 hu14 hu23 hu24 hu34 hA_pos hA_le hAgcd
    hM_half hb₀_I hdiv_b0 hAp_pos hBp_pos hcop_AB h2Ap h2Bp ?_
  intro p hp
  have hu₃_pos : 0 < u₃ := hA_pos u₃ (by rw [hAu]; simp)
  have hu₄_pos : 0 < u₄ := hA_pos u₄ (by rw [hAu]; simp)
  have hz0 : u₁.factorization p = 0 ∨ u₂.factorization p = 0 ∨
      u₃.factorization p = 0 ∨ u₄.factorization p = 0 :=
    r1_min0 hAu hA_pos hAgcd p hp
  rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne', fac_gcd_eq_min hu₃_pos.ne' hu₄_pos.ne']
  refine ab_split_pointwise ?_
  by_cases hpP : p ∈ P
  · by_cases hp_mA : p ∈ mustA
    · have hcond := (Finset.mem_filter.mp hp_mA).2
      exact Or.inl ⟨hAp_fac p (Finset.mem_union_left _ hp_mA), by omega⟩
    · by_cases hp_mB : p ∈ mustB
      · have hcond := (Finset.mem_filter.mp hp_mB).2
        exact Or.inr (Or.inl ⟨hBp_fac p (Finset.mem_union_left _ hp_mB), by omega⟩)
      · by_cases hp_ties : p ∈ ties
        · have hcond := (Finset.mem_filter.mp hp_ties).2
          by_cases hpTA : p ∈ T_A
          · exact Or.inl ⟨hAp_fac p (Finset.mem_union_right _ hpTA), by omega⟩
          · exact Or.inr (Or.inl ⟨hBp_fac p (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp_ties, hpTA⟩)), by omega⟩)
        · simp only [mustA, mustB, ties, Finset.mem_filter, hpP, true_and, not_or] at hp_mA hp_mB hp_ties
          by_cases h34 : u₃.factorization p = 0 ∧ u₄.factorization p = 0
          · exact Or.inr (Or.inr (Or.inr h34))
          · by_cases h12 : u₁.factorization p = 0 ∧ u₂.factorization p = 0
            · exact Or.inr (Or.inr (Or.inl h12))
            · exfalso
              rcases hz0 with h1 | h2 | h3 | h4
              · exact hp_mA.1 ⟨h1, by omega⟩
              · exact hp_mB.1 ⟨h2, by omega⟩
              · by_cases h1_0 : u₁.factorization p = 0
                · exact hp_mA.1 ⟨h1_0, by omega⟩
                · by_cases h2_0 : u₂.factorization p = 0
                  · exact hp_mB.1 ⟨h2_0, by omega⟩
                  · rcases lt_trichotomy (u₁.factorization p) (u₂.factorization p) with hlt | heq | hgt
                    · exact hp_mA.2 ⟨Or.inl h3, Nat.pos_of_ne_zero h1_0, hlt⟩
                    · exact hp_ties ⟨Or.inl h3, h34, Nat.pos_of_ne_zero h1_0, heq⟩
                    · exact hp_mB.2 ⟨Or.inl h3, Nat.pos_of_ne_zero h2_0, hgt⟩
              · by_cases h1_0 : u₁.factorization p = 0
                · exact hp_mA.1 ⟨h1_0, by omega⟩
                · by_cases h2_0 : u₂.factorization p = 0
                  · exact hp_mB.1 ⟨h2_0, by omega⟩
                  · rcases lt_trichotomy (u₁.factorization p) (u₂.factorization p) with hlt | heq | hgt
                    · exact hp_mA.2 ⟨Or.inr h4, Nat.pos_of_ne_zero h1_0, hlt⟩
                    · exact hp_ties ⟨Or.inr h4, h34, Nat.pos_of_ne_zero h1_0, heq⟩
                    · exact hp_mB.2 ⟨Or.inr h4, Nat.pos_of_ne_zero h2_0, hgt⟩
  · have hL_ne0 : A.lcm id ≠ 0 := finset_lcm_ne_zero (fun a ha => (hA_pos a ha).ne')
    have hp_nd : ¬ (p ∣ A.lcm id) := fun h => hpP ((Nat.mem_primeFactors_of_ne_zero hL_ne0).mpr ⟨hp, h⟩)
    have h10 : u₁.factorization p = 0 := by
      by_contra hn
      have hd : p ∣ u₁ := prime_dvd_of_fac_ne_zero hp hu₁_pos.ne' hn
      exact hp_nd (dvd_trans hd (Finset.dvd_lcm (by rw [hAu]; simp : u₁ ∈ A)))
    have h20 : u₂.factorization p = 0 := by
      by_contra hn
      have hd : p ∣ u₂ := prime_dvd_of_fac_ne_zero hp hu₂_pos.ne' hn
      exact hp_nd (dvd_trans hd (Finset.dvd_lcm (by rw [hAu]; simp : u₂ ∈ A)))
    exact Or.inr (Or.inr (Or.inl ⟨h10, h20⟩))

private lemma r1_not_single_prime {A : Finset ℕ} {M a₁ a₂ a₃ a₄ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄}) (h12 : a₁ ≠ a₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    {u : ℕ} (huA : u ∈ A) (p : ℕ) (hp_only : ∀ q ∈ u.primeFactors, q = p) : False := by
  have hu_pos := hA_pos u huA
  have hu_ge2 : 2 ≤ u := by
    have hM_u := hM_half u huA
    have ha₁_le := hA_le a₁ (by rw [hA_eq]; simp)
    have ha₂_le := hA_le a₂ (by rw [hA_eq]; simp)
    have ha₁_pos := hA_pos a₁ (by rw [hA_eq]; simp)
    have ha₂_pos := hA_pos a₂ (by rw [hA_eq]; simp)
    omega
  have hu_pf_ne : u.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hu_ge2
  obtain ⟨p₀, hp₀⟩ := hu_pf_ne
  have hp₀_eq : p₀ = p := hp_only p₀ hp₀
  subst p₀
  have hp_pr := Nat.prime_of_mem_primeFactors hp₀
  have hpf_eq : u.primeFactors = {p} := by
    ext q; constructor
    · intro hq; exact Finset.mem_singleton.mpr (hp_only q hq)
    · intro hq; rw [Finset.mem_singleton.mp hq]; exact hp₀
  have hu_pow : u = p ^ (u.factorization p) := by
    calc u = ∏ q ∈ u.primeFactors, q ^ (u.factorization q) := (Nat.prod_factorization_pow_eq_self hu_pos.ne').symm
      _ = p ^ (u.factorization p) := by rw [hpf_eq, Finset.prod_singleton]
  have hd_lcm := hlcm_all u huA
  have hpe_dvd : p ^ (u.factorization p) ∣ (A.erase u).lcm id := hu_pow ▸ hd_lcm
  have hp_div_ex : ∃ v ∈ A.erase u, p ^ (u.factorization p) ∣ v := by
    have hpp_div_lcm : ∀ (T : Finset ℕ) (k : ℕ), p ^ k ∣ T.lcm id → (∀ v ∈ T, 0 < v) →
        k = 0 ∨ ∃ v ∈ T, p ^ k ∣ v := by
      intro T k hpk hT
      induction T using Finset.induction_on with
      | empty =>
        rw [Finset.lcm_empty] at hpk
        left
        by_contra hk0
        have h1 : p ∣ p ^ k := dvd_pow_self p hk0
        exact hp_pr.not_dvd_one (dvd_trans h1 hpk)
      | @insert v s hvs ih =>
        rw [Finset.lcm_insert] at hpk
        have hv_pos := hT v (Finset.mem_insert_self v s)
        have hs_pos : ∀ w ∈ s, 0 < w := fun w hw => hT w (Finset.mem_insert_of_mem hw)
        have hs_ne0 : s.lcm id ≠ 0 := finset_lcm_ne_zero (fun w hw => (hs_pos w hw).ne')
        have hlcm_ne0 : Nat.lcm v (s.lcm id) ≠ 0 := Nat.lcm_ne_zero hv_pos.ne' hs_ne0
        simp only [id_eq] at hpk
        have hfac' := fac_le_of_dvd hlcm_ne0 hpk (p := p)
        rw [Nat.factorization_lcm hv_pos.ne' hs_ne0, Finsupp.sup_apply,
            hp_pr.factorization_pow, Finsupp.single_eq_same] at hfac'
        rcases le_or_gt k (v.factorization p) with hle | hgt
        · right; refine ⟨v, Finset.mem_insert_self v s, ?_⟩
          exact (hp_pr.pow_dvd_iff_le_factorization hv_pos.ne').mpr hle
        · have hk_s : k ≤ (s.lcm id).factorization p := by
            change k ≤ max (v.factorization p) ((s.lcm id).factorization p) at hfac'
            omega
          have hpk_s : p ^ k ∣ s.lcm id := (hp_pr.pow_dvd_iff_le_factorization hs_ne0).mpr hk_s
          rcases ih hpk_s hs_pos with h0 | ⟨w, hw, hpw⟩
          · exact Or.inl h0
          · exact Or.inr ⟨w, Finset.mem_insert_of_mem hw, hpw⟩
    rcases hpp_div_lcm (A.erase u) (u.factorization p) hpe_dvd
        (fun v hv => hA_pos v (Finset.erase_subset _ _ hv)) with h0 | ⟨v, hv, hdv⟩
    · have := one_le_fac_of_dvd hp_pr hu_pos.ne' ((Nat.mem_primeFactors_of_ne_zero hu_pos.ne').mp hp₀).2
      omega
    · exact ⟨v, hv, hdv⟩
  obtain ⟨v, hv_er, hdv⟩ := hp_div_ex
  rw [← hu_pow] at hdv
  have hv_A := (Finset.mem_erase.mp hv_er).2
  have hvu : v ≠ u := (Finset.mem_erase.mp hv_er).1
  obtain ⟨k, hk⟩ := hdv
  have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact (hA_pos v hv_A).ne' hk
  have hk_ne1 : k ≠ 1 := fun h => hvu (by rw [hk, h, mul_one])
  have hk2 : 2 ≤ k := by omega
  have h2u_v : 2 * u ≤ v := by rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left u hk2
  have hvM := hA_le v hv_A
  have hMu := hM_half u huA
  omega

private lemma r1_strict_lt_of_missing (S' : Finset ℕ) (u p₀ : ℕ)
    (hS'_pr : ∀ q ∈ S', q.Prime) (hu0 : 0 < u) (hp₀_pr : p₀.Prime)
    (hp₀_not : p₀ ∉ S') (hu_p0 : 0 < u.factorization p₀) :
    (∏ q ∈ S', q ^ (u.factorization q)) < u := by
  have hpos_prod : 0 < ∏ q ∈ S', q ^ (u.factorization q) := Finset.prod_pos (fun q hq =>
    pow_pos (hS'_pr q hq).pos _)
  have hdvd : (∏ q ∈ S', q ^ (u.factorization q)) ∣ u := by
    rw [← Nat.factorization_le_iff_dvd hpos_prod.ne' hu0.ne']
    intro r
    have hne0 : ∀ q ∈ S', q ^ (u.factorization q) ≠ 0 := fun q hq =>
      pow_ne_zero _ (hS'_pr q hq).ne_zero
    rw [Nat.factorization_prod hne0]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ q ∈ S', (q ^ (u.factorization q)).factorization r =
        if q = r then u.factorization q else 0 := fun q hq => by
      rw [(hS'_pr q hq).factorization_pow, Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs <;> omega
  have hnd : ¬ (u ∣ ∏ q ∈ S', q ^ (u.factorization q)) := by
    intro hdu
    have hpd : p₀ ∣ ∏ q ∈ S', q ^ (u.factorization q) :=
      dvd_trans (prime_dvd_of_fac_ne_zero hp₀_pr hu0.ne' hu_p0.ne') hdu
    rw [hp₀_pr.prime.dvd_finsetProd_iff] at hpd
    obtain ⟨q, hqS, hqd⟩ := hpd
    have hq_pr := hS'_pr q hqS
    have hqp : p₀ = q := (Nat.prime_dvd_prime_iff_eq hp₀_pr hq_pr).mp (hp₀_pr.dvd_of_dvd_pow hqd)
    exact hp₀_not (hqp ▸ hqS)
  exact Nat.lt_of_le_of_ne (Nat.le_of_dvd hu0 hdvd) fun heq => hnd heq.symm.dvd

private lemma r1_fail_two {A : Finset ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    {u₁ u₂ u₃ u₄ : ℕ} (hAu : A = {u₁, u₂, u₃, u₄})
    (hu12 : u₁ ≠ u₂) (hu13 : u₁ ≠ u₃) (hu14 : u₁ ≠ u₄)
    (hu23 : u₂ ≠ u₃) (hu24 : u₂ ≠ u₄) (hu34 : u₃ ≠ u₄)
    (hFail : ¬ ValidAB (A.lcm id).primeFactors u₁ u₂ u₃ u₄)
    {p : ℕ} (hp : p ∈ (A.lcm id).primeFactors) :
    ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) := by
  rintro ⟨h30, h40⟩
  let P := (A.lcm id).primeFactors
  have hL_ne0 : A.lcm id ≠ 0 := finset_lcm_ne_zero (fun a ha => (hA_pos a ha).ne')
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hAu]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hAu]; simp)
  have ht1 := r1_top2_all hA_pos hlcm_all
    (by rw [hAu]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
    hu23 hu24 hu12.symm hu34 hu13.symm hu14.symm p hp_pr
  have ht2 := r1_top2_all hA_pos hlcm_all
    (by rw [hAu]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
    hu13 hu14 hu12 hu34 hu23.symm hu24.symm p hp_pr
  have h12_eq : u₁.factorization p = u₂.factorization p := by omega
  have hp_pos12 : 0 < u₁.factorization p := by
    have hpd : p ∣ A.lcm id := ((Nat.mem_primeFactors_of_ne_zero hL_ne0).mp hp).2
    have h1d : p ∣ u₁ ∨ p ∣ u₂ ∨ p ∣ u₃ ∨ p ∣ u₄ := by
      by_contra hnone; push Not at hnone
      have hd_lcm : A.lcm id ∣ u₁ * u₂ * u₃ * u₄ := by
        apply Finset.lcm_dvd
        intro a ha; rw [hAu] at ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with ha | ha | ha | ha <;> rw [ha]
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right u₁ u₂) u₃) u₄
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left u₂ u₁) u₃) u₄
        · exact dvd_mul_of_dvd_left (dvd_mul_left u₃ (u₁ * u₂)) u₄
        · exact dvd_mul_left u₄ (u₁ * u₂ * u₃)
      have hpd4 := dvd_trans hpd hd_lcm
      rcases hp_pr.dvd_mul.mp hpd4 with h123 | h4
      · rcases hp_pr.dvd_mul.mp h123 with h12' | h3
        · rcases hp_pr.dvd_mul.mp h12' with h1 | h2
          · exact hnone.1 h1
          · exact hnone.2.1 h2
        · exact hnone.2.2.1 h3
      · exact hnone.2.2.2 h4
    rcases h1d with h1 | h2 | h3 | h4
    · exact one_le_fac_of_dvd hp_pr hu₁_pos.ne' h1
    · have := one_le_fac_of_dvd hp_pr hu₂_pos.ne' h2; omega
    · have := one_le_fac_of_dvd hp_pr (hA_pos u₃ (by rw [hAu]; simp)).ne' h3; omega
    · have := one_le_fac_of_dvd hp_pr (hA_pos u₄ (by rw [hAu]; simp)).ne' h4; omega
  apply hFail
  refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
  · let S' := P.filter (fun q =>
        (u₁.factorization q = 0 ∧ 0 < u₂.factorization q) ∨
        ((u₃.factorization q = 0 ∨ u₄.factorization q = 0) ∧ 0 < u₁.factorization q ∧ u₁.factorization q < u₂.factorization q)) ∪ ∅
    have hnot_mem : p ∉ S' := by
      simp only [S', Finset.union_empty, Finset.mem_filter]; omega
    have hsub : S' ⊆ P := by
      simp [S', Finset.filter_subset]
    exact r1_strict_lt_of_missing S' u₂ p (fun q hq => Nat.prime_of_mem_primeFactors (hsub hq))
      hu₂_pos hp_pr hnot_mem (by omega)
  · let S' := P.filter (fun q =>
        (u₂.factorization q = 0 ∧ 0 < u₁.factorization q) ∨
        ((u₃.factorization q = 0 ∨ u₄.factorization q = 0) ∧ 0 < u₂.factorization q ∧ u₂.factorization q < u₁.factorization q)) ∪
      (P.filter (fun q =>
        (u₃.factorization q = 0 ∨ u₄.factorization q = 0) ∧
        ¬ (u₃.factorization q = 0 ∧ u₄.factorization q = 0) ∧
        0 < u₁.factorization q ∧ u₁.factorization q = u₂.factorization q) \ ∅)
    have hsub : S' ⊆ P := Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
    have hnot_mem : p ∉ S' := by
      simp only [S', Finset.sdiff_empty, Finset.mem_union, Finset.mem_filter, not_or]; constructor <;> omega
    exact r1_strict_lt_of_missing S' u₁ p (fun q hq => Nat.prime_of_mem_primeFactors (hsub hq))
      hu₁_pos hp_pr hnot_mem hp_pos12

private lemma set4_perm {a b c d u v w z : ℕ}
    (hu : u = a ∨ u = b ∨ u = c ∨ u = d) (hv : v = a ∨ v = b ∨ v = c ∨ v = d)
    (hw : w = a ∨ w = b ∨ w = c ∨ w = d) (hz : z = a ∨ z = b ∨ z = c ∨ z = d)
    (ha : a = u ∨ a = v ∨ a = w ∨ a = z) (hb : b = u ∨ b = v ∨ b = w ∨ b = z)
    (hc : c = u ∨ c = v ∨ c = w ∨ c = z) (hd : d = u ∨ d = v ∨ d = w ∨ d = z) :
    ({a, b, c, d} : Finset ℕ) = {u, v, w, z} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> assumption
  · rintro (rfl | rfl | rfl | rfl) <;> assumption

private lemma r1_uniq_zero {A : Finset ℕ} {a₁ a₂ a₃ a₄ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄})
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hAgcd : A.gcd id = 1)
    (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hF12 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₂ a₃ a₄)
    (hF13 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₃ a₂ a₄)
    (hF14 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₄ a₂ a₃)
    (hF23 : ¬ ValidAB (A.lcm id).primeFactors a₂ a₃ a₁ a₄)
    (hF24 : ¬ ValidAB (A.lcm id).primeFactors a₂ a₄ a₁ a₃)
    (hF34 : ¬ ValidAB (A.lcm id).primeFactors a₃ a₄ a₁ a₂)
    {p : ℕ} (hp : p ∈ (A.lcm id).primeFactors) :
    (a₁.factorization p = 0 ∧ 0 < a₂.factorization p ∧ 0 < a₃.factorization p ∧ 0 < a₄.factorization p) ∨
    (0 < a₁.factorization p ∧ a₂.factorization p = 0 ∧ 0 < a₃.factorization p ∧ 0 < a₄.factorization p) ∨
    (0 < a₁.factorization p ∧ 0 < a₂.factorization p ∧ a₃.factorization p = 0 ∧ 0 < a₄.factorization p) ∨
    (0 < a₁.factorization p ∧ 0 < a₂.factorization p ∧ 0 < a₃.factorization p ∧ a₄.factorization p = 0) := by
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have hz := r1_min0 hA_eq hA_pos hAgcd p hp_pr
  have hn12 := r1_fail_two hA_pos hlcm_all
    (hA_eq.trans (set4_perm (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl))))
    h34 h13.symm h23.symm h14.symm h24.symm h12 hF34 hp
  have hn13 := r1_fail_two hA_pos hlcm_all
    (hA_eq.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))))
    h24 h12.symm h23 h14.symm h34.symm h13 hF24 hp
  have hn14 := r1_fail_two hA_pos hlcm_all
    (hA_eq.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))))
    h23 h12.symm h24 h13.symm h34 h14 hF23 hp
  have hn23 := r1_fail_two hA_pos hlcm_all
    (hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))))
    h14 h12 h13 h24.symm h34.symm h23 hF14 hp
  have hn24 := r1_fail_two hA_pos hlcm_all
    (hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))))
    h13 h12 h14 h23.symm h34 h24 hF13 hp
  have hn34 := r1_fail_two hA_pos hlcm_all hA_eq h12 h13 h14 h23 h24 h34 hF12 hp
  rcases hz with h1 | h2 | h3 | h4
  · exact Or.inl ⟨h1, Nat.pos_of_ne_zero fun h2 => hn12 ⟨h1, h2⟩,
      Nat.pos_of_ne_zero fun h3 => hn13 ⟨h1, h3⟩, Nat.pos_of_ne_zero fun h4 => hn14 ⟨h1, h4⟩⟩
  · exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero fun h1 => hn12 ⟨h1, h2⟩, h2,
      Nat.pos_of_ne_zero fun h3 => hn23 ⟨h2, h3⟩, Nat.pos_of_ne_zero fun h4 => hn24 ⟨h2, h4⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨Nat.pos_of_ne_zero fun h1 => hn13 ⟨h1, h3⟩,
      Nat.pos_of_ne_zero fun h2 => hn23 ⟨h2, h3⟩, h3, Nat.pos_of_ne_zero fun h4 => hn34 ⟨h3, h4⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨Nat.pos_of_ne_zero fun h1 => hn14 ⟨h1, h4⟩,
      Nat.pos_of_ne_zero fun h2 => hn24 ⟨h2, h4⟩, Nat.pos_of_ne_zero fun h3 => hn34 ⟨h3, h4⟩, h4⟩))

private lemma r1_key_char {A : Finset ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hpos_of_ne_zero : ∀ p ∈ (A.lcm id).primeFactors, ∀ u v : ℕ, u ∈ A → v ∈ A → u ≠ v →
      u.factorization p = 0 → 0 < v.factorization p)
    {u₁ u₂ u₃ u₄ : ℕ} (hAu : A = {u₁, u₂, u₃, u₄})
    (hu12 : u₁ ≠ u₂) (hu13 : u₁ ≠ u₃) (hu14 : u₁ ≠ u₄)
    (hu23 : u₂ ≠ u₃) (hu24 : u₂ ≠ u₄) (hu34 : u₃ ≠ u₄)
    (hFail : ¬ ValidAB (A.lcm id).primeFactors u₁ u₂ u₃ u₄)
    (hU2 : 2 ≤ ((A.lcm id).primeFactors.filter (fun p => u₃.factorization p = 0) ∪
      (A.lcm id).primeFactors.filter (fun p => u₄.factorization p = 0)).card) :
    (∀ p ∈ (A.lcm id).primeFactors.filter (fun p => u₃.factorization p = 0) ∪
        (A.lcm id).primeFactors.filter (fun p => u₄.factorization p = 0),
      u₁.factorization p < u₂.factorization p) ∨
    (∀ p ∈ (A.lcm id).primeFactors.filter (fun p => u₃.factorization p = 0) ∪
        (A.lcm id).primeFactors.filter (fun p => u₄.factorization p = 0),
      u₂.factorization p < u₁.factorization p) := by
  let P := (A.lcm id).primeFactors
  let ties := P.filter (fun p =>
    (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
    ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧
    0 < u₁.factorization p ∧ u₁.factorization p = u₂.factorization p)
  have hu₁_pos : 0 < u₁ := hA_pos u₁ (by rw [hAu]; simp)
  have hu₂_pos : 0 < u₂ := hA_pos u₂ (by rw [hAu]; simp)
  have hU_mem : ∀ p ∈ P.filter (fun p => u₃.factorization p = 0) ∪ P.filter (fun p => u₄.factorization p = 0),
      p ∈ P ∧ (u₃.factorization p = 0 ∨ u₄.factorization p = 0) ∧
      ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) ∧ 0 < u₁.factorization p ∧ 0 < u₂.factorization p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp3 | hp4
    · have hflt := Finset.mem_filter.mp hp3
      have hne34 := r1_fail_two hA_pos hlcm_all hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail hflt.1
      have hp1 := hpos_of_ne_zero p hflt.1 u₃ u₁ (by rw [hAu]; simp) (by rw [hAu]; simp) hu13.symm hflt.2
      have hp2 := hpos_of_ne_zero p hflt.1 u₃ u₂ (by rw [hAu]; simp) (by rw [hAu]; simp) hu23.symm hflt.2
      exact ⟨hflt.1, Or.inl hflt.2, fun ⟨_, h4⟩ => hne34 ⟨hflt.2, h4⟩, hp1, hp2⟩
    · have hflt := Finset.mem_filter.mp hp4
      have hne34 := r1_fail_two hA_pos hlcm_all hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail hflt.1
      have hp1 := hpos_of_ne_zero p hflt.1 u₄ u₁ (by rw [hAu]; simp) (by rw [hAu]; simp) hu14.symm hflt.2
      have hp2 := hpos_of_ne_zero p hflt.1 u₄ u₂ (by rw [hAu]; simp) (by rw [hAu]; simp) hu24.symm hflt.2
      exact ⟨hflt.1, Or.inr hflt.2, fun ⟨h3, _⟩ => hne34 ⟨h3, hflt.2⟩, hp1, hp2⟩
  by_cases hlt : ∃ p ∈ P.filter (fun p => u₃.factorization p = 0) ∪ P.filter (fun p => u₄.factorization p = 0),
      u₁.factorization p < u₂.factorization p
  · left
    obtain ⟨p, hpU, hp_lt⟩ := hlt
    obtain ⟨hpP, hp34, _, hp1_pos, hp2_pos⟩ := hU_mem p hpU
    intro q hqU
    by_contra hq_ge
    obtain ⟨hqP, hq34, hqne34, hq1_pos, hq2_pos⟩ := hU_mem q hqU
    have hq_le : u₂.factorization q ≤ u₁.factorization q := by omega
    apply hFail
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · apply r1_strict_lt_of_missing _ u₂ q
        (fun r hr => Nat.prime_of_mem_primeFactors (Finset.union_subset (Finset.filter_subset _ _) (Finset.empty_subset _) hr))
        hu₂_pos (Nat.prime_of_mem_primeFactors hqP)
      · simp only [Finset.union_empty, Finset.mem_filter]; omega
      · exact hq2_pos
    · apply r1_strict_lt_of_missing _ u₁ p
        (fun r hr => Nat.prime_of_mem_primeFactors ((Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))) hr))
        hu₁_pos (Nat.prime_of_mem_primeFactors hpP)
      · simp only [Finset.sdiff_empty, Finset.mem_union, Finset.mem_filter]; omega
      · exact hp1_pos
  · by_cases hgt : ∃ p ∈ P.filter (fun p => u₃.factorization p = 0) ∪ P.filter (fun p => u₄.factorization p = 0),
        u₂.factorization p < u₁.factorization p
    · right
      obtain ⟨p, hpU, hp_gt⟩ := hgt
      obtain ⟨hpP, hp34, _, hp1_pos, hp2_pos⟩ := hU_mem p hpU
      intro q hqU
      by_contra hq_ge
      obtain ⟨hqP, hq34, hqne34, hq1_pos, hq2_pos⟩ := hU_mem q hqU
      have hq_le : u₁.factorization q ≤ u₂.factorization q := by omega
      apply hFail
      refine ⟨ties, Finset.Subset.rfl, ?_, ?_⟩
      · apply r1_strict_lt_of_missing _ u₂ p
          (fun r hr => Nat.prime_of_mem_primeFactors ((Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) hr))
          hu₂_pos (Nat.prime_of_mem_primeFactors hpP)
        · simp only [Finset.mem_union, Finset.mem_filter]; omega
        · exact hp2_pos
      · apply r1_strict_lt_of_missing _ u₁ q
          (fun r hr => Nat.prime_of_mem_primeFactors ((Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))) hr))
          hu₁_pos (Nat.prime_of_mem_primeFactors hqP)
        · intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · rw [Finset.mem_filter] at h1; omega
          · exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h2).1
        · exact hq1_pos
    · exfalso
      push Not at hlt hgt
      obtain ⟨p₁, hp1U, p₂, hp2U, hp12⟩ := Finset.one_lt_card.mp hU2
      obtain ⟨hp1P, hp1_34, hp1_ne, hp1_pos, _⟩ := hU_mem p₁ hp1U
      obtain ⟨hp2P, hp2_34, hp2_ne, _, hp2_pos2⟩ := hU_mem p₂ hp2U
      have hp1_eq : u₁.factorization p₁ = u₂.factorization p₁ := by
        have := hlt p₁ hp1U; have := hgt p₁ hp1U; omega
      have hp2_eq : u₁.factorization p₂ = u₂.factorization p₂ := by
        have := hlt p₂ hp2U; have := hgt p₂ hp2U; omega
      have hp1_ties : p₁ ∈ ties := Finset.mem_filter.mpr ⟨hp1P, hp1_34, hp1_ne, hp1_pos, hp1_eq⟩
      apply hFail
      refine ⟨{p₁}, Finset.singleton_subset_iff.mpr hp1_ties, ?_, ?_⟩
      · apply r1_strict_lt_of_missing _ u₂ p₂
          (fun r hr => Nat.prime_of_mem_primeFactors ((Finset.union_subset (Finset.filter_subset _ _) (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hp1_ties).1)) hr))
          hu₂_pos (Nat.prime_of_mem_primeFactors hp2P)
        · simp only [Finset.mem_union, Finset.mem_singleton]
          rintro (h1 | h2)
          · rw [Finset.mem_filter] at h1; omega
          · exact hp12 h2.symm
        · exact hp2_pos2
      · apply r1_strict_lt_of_missing _ u₁ p₁
          (fun r hr => Nat.prime_of_mem_primeFactors ((Finset.union_subset (Finset.filter_subset _ _) (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))) hr))
          hu₁_pos (Nat.prime_of_mem_primeFactors hp1P)
        · simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
          rintro (h1 | ⟨_, h2⟩)
          · rw [Finset.mem_filter] at h1; omega
          · exact h2 trivial
        · exact hp1_pos

private lemma r1_no_three_ne {A : Finset ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hpos_of_ne_zero : ∀ p ∈ (A.lcm id).primeFactors, ∀ u v : ℕ, u ∈ A → v ∈ A → u ≠ v →
      u.factorization p = 0 → 0 < v.factorization p)
    {u₁ u₂ u₃ u₄ : ℕ} (hAu : A = {u₁, u₂, u₃, u₄})
    (hu12 : u₁ ≠ u₂) (hu13 : u₁ ≠ u₃) (hu14 : u₁ ≠ u₄)
    (hu23 : u₂ ≠ u₃) (hu24 : u₂ ≠ u₄) (hu34 : u₃ ≠ u₄)
    (hF12 : ¬ ValidAB (A.lcm id).primeFactors u₁ u₂ u₃ u₄)
    (hF13 : ¬ ValidAB (A.lcm id).primeFactors u₁ u₃ u₂ u₄)
    (hF23 : ¬ ValidAB (A.lcm id).primeFactors u₂ u₃ u₁ u₄)
    (hcond : 2 ≤ ((A.lcm id).primeFactors.filter (fun p => u₄.factorization p = 0)).card ∨
      (1 ≤ ((A.lcm id).primeFactors.filter (fun p => u₄.factorization p = 0)).card ∧
       1 ≤ ((A.lcm id).primeFactors.filter (fun p => u₁.factorization p = 0)).card ∧
       1 ≤ ((A.lcm id).primeFactors.filter (fun p => u₂.factorization p = 0)).card ∧
       1 ≤ ((A.lcm id).primeFactors.filter (fun p => u₃.factorization p = 0)).card)) :
    False := by
  let P := (A.lcm id).primeFactors
  let S : ℕ → Finset ℕ := fun u => P.filter (fun p => u.factorization p = 0)
  have hAu13 : A = {u₁, u₃, u₂, u₄} :=
    hAu.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))))
  have hAu23 : A = {u₂, u₃, u₁, u₄} :=
    hAu.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))))
  have hU12 : 2 ≤ (S u₃ ∪ S u₄).card := by
    rcases hcond with h2 | ⟨h4, _, _, h3⟩
    · exact le_trans h2 (Finset.card_le_card Finset.subset_union_right)
    · have hdisj : Disjoint (S u₃) (S u₄) := by
        rw [Finset.disjoint_left]; intro p hp3 hp4
        exact r1_fail_two hA_pos hlcm_all hAu hu12 hu13 hu14 hu23 hu24 hu34 hF12
          (Finset.mem_filter.mp hp3).1 ⟨(Finset.mem_filter.mp hp3).2, (Finset.mem_filter.mp hp4).2⟩
      rw [Finset.card_union_of_disjoint hdisj]; dsimp only [S, P]; omega
  have hU13 : 2 ≤ (S u₂ ∪ S u₄).card := by
    rcases hcond with h2 | ⟨h4, _, h2, _⟩
    · exact le_trans h2 (Finset.card_le_card Finset.subset_union_right)
    · have hdisj : Disjoint (S u₂) (S u₄) := by
        rw [Finset.disjoint_left]; intro p hp2 hp4
        exact r1_fail_two hA_pos hlcm_all hAu13 hu13 hu12 hu14 hu23.symm hu34 hu24 hF13
          (Finset.mem_filter.mp hp2).1 ⟨(Finset.mem_filter.mp hp2).2, (Finset.mem_filter.mp hp4).2⟩
      rw [Finset.card_union_of_disjoint hdisj]; dsimp only [S, P]; omega
  have hU23 : 2 ≤ (S u₁ ∪ S u₄).card := by
    rcases hcond with h2 | ⟨h4, h1, _, _⟩
    · exact le_trans h2 (Finset.card_le_card Finset.subset_union_right)
    · have hdisj : Disjoint (S u₁) (S u₄) := by
        rw [Finset.disjoint_left]; intro p hp1 hp4
        exact r1_fail_two hA_pos hlcm_all hAu23 hu23 hu12.symm hu24 hu13.symm hu34 hu14 hF23
          (Finset.mem_filter.mp hp1).1 ⟨(Finset.mem_filter.mp hp1).2, (Finset.mem_filter.mp hp4).2⟩
      rw [Finset.card_union_of_disjoint hdisj]; dsimp only [S, P]; omega
  have hS4_ne : (S u₄).Nonempty := by
    apply Finset.card_pos.mp
    rcases hcond with h2 | ⟨h4, _⟩ <;> dsimp only [S, P] <;> omega
  obtain ⟨p, hp4⟩ := hS4_ne
  have hpP := (Finset.mem_filter.mp hp4).1
  have hp_pr := Nat.prime_of_mem_primeFactors hpP
  have kc12 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero hAu hu12 hu13 hu14 hu23 hu24 hu34 hF12 hU12
  have kc13 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero hAu13 hu13 hu12 hu14 hu23.symm hu34 hu24 hF13 hU13
  have kc23 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero hAu23 hu23 hu12.symm hu24 hu13.symm hu34 hu14 hF23 hU23
  have hne12 : u₁.factorization p ≠ u₂.factorization p := by
    rcases kc12 with h | h <;> have := h p (Finset.mem_union_right _ hp4) <;> omega
  have hne13 : u₁.factorization p ≠ u₃.factorization p := by
    rcases kc13 with h | h <;> have := h p (Finset.mem_union_right _ hp4) <;> omega
  have hne23 : u₂.factorization p ≠ u₃.factorization p := by
    rcases kc23 with h | h <;> have := h p (Finset.mem_union_right _ hp4) <;> omega
  have hp4_0 : u₄.factorization p = 0 := (Finset.mem_filter.mp hp4).2
  have ht1 := r1_top2_all hA_pos hlcm_all
    (hAu.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
      (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
    hu23 hu24 hu12.symm hu34 hu13.symm hu14.symm p hp_pr
  have ht2 := r1_top2_all hA_pos hlcm_all
    (hAu.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
    hu13 hu14 hu12 hu34 hu23.symm hu24.symm p hp_pr
  have ht3 := r1_top2_all hA_pos hlcm_all
    (hAu.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))))
    hu12 hu14 hu13 hu24 hu23 hu34.symm p hp_pr
  omega

private lemma r1_close_three_primes {A : Finset ℕ} {x M b₀ x₁ x₂ x₃ x₄ : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hpos_of_ne_zero : ∀ p ∈ (A.lcm id).primeFactors, ∀ u v : ℕ, u ∈ A → v ∈ A → u ≠ v →
      u.factorization p = 0 → 0 < v.factorization p)
    (hP_ge3 : 3 ≤ (A.lcm id).primeFactors.card)
    (hAx : A = {x₁, x₂, x₃, x₄})
    (hx12 : x₁ ≠ x₂) (hx13 : x₁ ≠ x₃) (hx14 : x₁ ≠ x₄)
    (hx23 : x₂ ≠ x₃) (hx24 : x₂ ≠ x₄) (hx34 : x₃ ≠ x₄)
    (hFx14 : ¬ ValidAB (A.lcm id).primeFactors x₁ x₄ x₂ x₃)
    (hFx24 : ¬ ValidAB (A.lcm id).primeFactors x₂ x₄ x₁ x₃)
    (hFx34 : ¬ ValidAB (A.lcm id).primeFactors x₃ x₄ x₁ x₂)
    (hS1 : ((A.lcm id).primeFactors.filter (fun p => x₁.factorization p = 0)).card = 1)
    (hS2 : ((A.lcm id).primeFactors.filter (fun p => x₂.factorization p = 0)).card = 1)
    (hS3 : ((A.lcm id).primeFactors.filter (fun p => x₃.factorization p = 0)).card = 1)
    (hS4 : ((A.lcm id).primeFactors.filter (fun p => x₄.factorization p = 0)).card = 0) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  let P := (A.lcm id).primeFactors
  let S : ℕ → Finset ℕ := fun u => P.filter (fun p => u.factorization p = 0)
  have hL_ne0 : A.lcm id ≠ 0 := finset_lcm_ne_zero (fun a ha => (hA_pos a ha).ne')
  have hpf_sub_P : ∀ u ∈ A, u.primeFactors ⊆ P := by
    intro u hu s hs
    have hs_pr := Nat.prime_of_mem_primeFactors hs
    have hsu : s ∣ u := ((Nat.mem_primeFactors_of_ne_zero (hA_pos u hu).ne').mp hs).2
    exact (Nat.mem_primeFactors_of_ne_zero hL_ne0).mpr ⟨hs_pr, dvd_trans hsu (Finset.dvd_lcm hu)⟩
  obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hS1
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hS2
  obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hS3
  have hpS : p ∈ S x₁ := by rw [show S x₁ = {p} from hp_eq]; exact Finset.mem_singleton_self p
  have hqS : q ∈ S x₂ := by rw [show S x₂ = {q} from hq_eq]; exact Finset.mem_singleton_self q
  have hrS : r ∈ S x₃ := by rw [show S x₃ = {r} from hr_eq]; exact Finset.mem_singleton_self r
  have hpP : p ∈ P := (Finset.mem_filter.mp hpS).1
  have hqP : q ∈ P := (Finset.mem_filter.mp hqS).1
  have hrP : r ∈ P := (Finset.mem_filter.mp hrS).1
  have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hpP
  have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors hqP
  have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hrP
  have h1p0 : x₁.factorization p = 0 := (Finset.mem_filter.mp hpS).2
  have h2q0 : x₂.factorization q = 0 := (Finset.mem_filter.mp hqS).2
  have h3r0 : x₃.factorization r = 0 := (Finset.mem_filter.mp hrS).2
  have hs4_empty : S x₄ = ∅ := Finset.card_eq_zero.mp hS4
  have hpos_of_not_S : ∀ u : ℕ, ∀ s ∈ P, s ∉ S u → 0 < u.factorization s := by
    intro u s hsP hns
    by_contra h0
    exact hns (Finset.mem_filter.mpr ⟨hsP, by omega⟩)
  have hp_n2 : p ∉ S x₂ := fun h => by
    have := hpos_of_ne_zero p hpP x₁ x₂ (by rw [hAx]; simp) (by rw [hAx]; simp) hx12 h1p0
    exact absurd (Finset.mem_filter.mp h).2 this.ne'
  have hp_n3 : p ∉ S x₃ := fun h => by
    have := hpos_of_ne_zero p hpP x₁ x₃ (by rw [hAx]; simp) (by rw [hAx]; simp) hx13 h1p0
    exact absurd (Finset.mem_filter.mp h).2 this.ne'
  have hq_n3 : q ∉ S x₃ := fun h => by
    have := hpos_of_ne_zero q hqP x₂ x₃ (by rw [hAx]; simp) (by rw [hAx]; simp) hx23 h2q0
    exact absurd (Finset.mem_filter.mp h).2 this.ne'
  have hpq : p ≠ q := fun heq => hp_n2 (heq ▸ hqS)
  have hpr : p ≠ r := fun heq => hp_n3 (heq ▸ hrS)
  have hqr : q ≠ r := fun heq => hq_n3 (heq ▸ hrS)
  have hP_eq3 : P = {p, q, r} := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hno; push Not at hno
      have hns1 : s ∉ S x₁ := fun h => hno.1 (Finset.mem_singleton.mp (hp_eq ▸ h))
      have hns2 : s ∉ S x₂ := fun h => hno.2.1 (Finset.mem_singleton.mp (hq_eq ▸ h))
      have hns3 : s ∉ S x₃ := fun h => hno.2.2 (Finset.mem_singleton.mp (hr_eq ▸ h))
      have hns4 : s ∉ S x₄ := by rw [hs4_empty]; simp
      have hs1 := hpos_of_not_S x₁ s hs hns1
      have hs2 := hpos_of_not_S x₂ s hs hns2
      have hs3 := hpos_of_not_S x₃ s hs hns3
      have hs4 := hpos_of_not_S x₄ s hs hns4
      rcases r1_min0 hAx hA_pos hAgcd s (Nat.prime_of_mem_primeFactors hs) with z1 | z2 | z3 | z4 <;> omega
    · have hc3 : ({p, q, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
            Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
      rw [hc3]
      exact hP_ge3
  have hrest : ∀ s : ℕ, s.Prime → s ≠ p → s ≠ q → s ≠ r →
      x₁.factorization s = 0 ∧ x₂.factorization s = 0 ∧
      x₃.factorization s = 0 ∧ x₄.factorization s = 0 := by
    intro s hs hsp hsq hsr
    have hs_notP : s ∉ P := by rw [hP_eq3]; simp [hsp, hsq, hsr]
    have hs_nd : ¬ (s ∣ A.lcm id) := fun hd =>
      hs_notP ((Nat.mem_primeFactors_of_ne_zero hL_ne0).mpr ⟨hs, hd⟩)
    have hzero : ∀ u ∈ A, u.factorization s = 0 := by
      intro u hu
      by_contra hnz
      have hdu : s ∣ u := prime_dvd_of_fac_ne_zero hs (hA_pos u hu).ne' hnz
      exact hs_nd (dvd_trans hdu (Finset.dvd_lcm hu))
    exact ⟨hzero x₁ (by rw [hAx]; simp), hzero x₂ (by rw [hAx]; simp),
           hzero x₃ (by rw [hAx]; simp), hzero x₄ (by rw [hAx]; simp)⟩
  have hkc14 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero
    (hAx.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))))
    hx14 hx12 hx13 hx24.symm hx34.symm hx23 hFx14 (by rw [hq_eq, hr_eq]; simp [hqr])
  have hkc24 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero
    (hAx.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))))
    hx24 hx12.symm hx23 hx14.symm hx34.symm hx13 hFx24 (by rw [hp_eq, hr_eq]; simp [hpr])
  have hkc34 := r1_key_char hA_pos hlcm_all hpos_of_ne_zero
    (hAx.trans (set4_perm (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl))))
    hx34 hx13.symm hx23.symm hx14.symm hx24.symm hx12 hFx34 (by rw [hp_eq, hq_eq]; simp [hpq])
  have hx₁_pos := hA_pos x₁ (by rw [hAx]; simp)
  have hx₂_pos := hA_pos x₂ (by rw [hAx]; simp)
  have hx₃_pos := hA_pos x₃ (by rw [hAx]; simp)
  have hx₄_pos := hA_pos x₄ (by rw [hAx]; simp)
  have hx₁_M := hA_le x₁ (by rw [hAx]; simp)
  have hx₂_M := hA_le x₂ (by rw [hAx]; simp)
  have hx₃_M := hA_le x₃ (by rw [hAx]; simp)
  have h14_lt : x₄.factorization q < x₁.factorization q ∧ x₄.factorization r < x₁.factorization r := by
    rcases hkc14 with h1 | h2
    · exfalso
      have hx1_dvd_x4 : x₁ ∣ x₄ := by
        rw [← Nat.factorization_le_iff_dvd hx₁_pos.ne' hx₄_pos.ne']
        intro s
        by_cases hs : s.Prime
        · by_cases hsp : s = p
          · rw [hsp, h1p0]; exact Nat.zero_le _
          · by_cases hsq : s = q
            · rw [hsq]; exact le_of_lt (h1 q (Finset.mem_union_left _ hqS))
            · by_cases hsr : s = r
              · rw [hsr]; exact le_of_lt (h1 r (Finset.mem_union_right _ hrS))
              · rw [(hrest s hs hsp hsq hsr).1]; exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_prime x₁ hs]; exact Nat.zero_le _
      obtain ⟨k, hk⟩ := hx1_dvd_x4
      have hk0 : 1 ≤ k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hx₄_pos.ne' hk
      have hk1 : k ≠ 1 := fun h => hx14 (by rw [hk, h, mul_one])
      have h2x : 2 * x₁ ≤ x₄ := by rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left x₁ (by omega)
      have := hM_half x₁ (by rw [hAx]; simp); have := hA_le x₄ (by rw [hAx]; simp); omega
    · exact ⟨h2 q (Finset.mem_union_left _ hqS), h2 r (Finset.mem_union_right _ hrS)⟩
  have h24_lt : x₄.factorization p < x₂.factorization p ∧ x₄.factorization r < x₂.factorization r := by
    rcases hkc24 with h1 | h2
    · exfalso
      have hx2_dvd_x4 : x₂ ∣ x₄ := by
        rw [← Nat.factorization_le_iff_dvd hx₂_pos.ne' hx₄_pos.ne']
        intro s
        by_cases hs : s.Prime
        · by_cases hsq : s = q
          · rw [hsq, h2q0]; exact Nat.zero_le _
          · by_cases hsp : s = p
            · rw [hsp]; exact le_of_lt (h1 p (Finset.mem_union_left _ hpS))
            · by_cases hsr : s = r
              · rw [hsr]; exact le_of_lt (h1 r (Finset.mem_union_right _ hrS))
              · rw [(hrest s hs hsp hsq hsr).2.1]; exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_prime x₂ hs]; exact Nat.zero_le _
      obtain ⟨k, hk⟩ := hx2_dvd_x4
      have hk0 : 1 ≤ k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hx₄_pos.ne' hk
      have hk1 : k ≠ 1 := fun h => hx24 (by rw [hk, h, mul_one])
      have h2x : 2 * x₂ ≤ x₄ := by rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left x₂ (by omega)
      have := hM_half x₂ (by rw [hAx]; simp); have := hA_le x₄ (by rw [hAx]; simp); omega
    · exact ⟨h2 p (Finset.mem_union_left _ hpS), h2 r (Finset.mem_union_right _ hrS)⟩
  have h34_lt : x₄.factorization p < x₃.factorization p ∧ x₄.factorization q < x₃.factorization q := by
    rcases hkc34 with h1 | h2
    · exfalso
      have hx3_dvd_x4 : x₃ ∣ x₄ := by
        rw [← Nat.factorization_le_iff_dvd hx₃_pos.ne' hx₄_pos.ne']
        intro s
        by_cases hs : s.Prime
        · by_cases hsr : s = r
          · rw [hsr, h3r0]; exact Nat.zero_le _
          · by_cases hsp : s = p
            · rw [hsp]; exact le_of_lt (h1 p (Finset.mem_union_left _ hpS))
            · by_cases hsq : s = q
              · rw [hsq]; exact le_of_lt (h1 q (Finset.mem_union_right _ hqS))
              · rw [(hrest s hs hsp hsq hsr).2.2.1]; exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_prime x₃ hs]; exact Nat.zero_le _
      obtain ⟨k, hk⟩ := hx3_dvd_x4
      have hk0 : 1 ≤ k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hx₄_pos.ne' hk
      have hk1 : k ≠ 1 := fun h => hx34 (by rw [hk, h, mul_one])
      have h2x : 2 * x₃ ≤ x₄ := by rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left x₃ (by omega)
      have := hM_half x₃ (by rw [hAx]; simp); have := hA_le x₄ (by rw [hAx]; simp); omega
    · exact ⟨h2 p (Finset.mem_union_left _ hpS), h2 q (Finset.mem_union_right _ hqS)⟩
  have hx_eq_p : x₃.factorization p = x₂.factorization p := by
    have ht2 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
        (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
      hx13 hx14 hx12 hx34 hx23.symm hx24.symm p hp_pr
    have ht3 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))
        (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))))
      hx12 hx14 hx13 hx24 hx23 hx34.symm p hp_pr
    omega
  have hx_eq_q : x₃.factorization q = x₁.factorization q := by
    have ht1 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
        (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
      hx23 hx24 hx12.symm hx34 hx13.symm hx14.symm q hq_pr
    have ht3 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))
        (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))))
      hx12 hx14 hx13 hx24 hx23 hx34.symm q hq_pr
    omega
  have hx_eq_r : x₂.factorization r = x₁.factorization r := by
    have ht1 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
        (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
      hx23 hx24 hx12.symm hx34 hx13.symm hx14.symm r hr_pr
    have ht2 := r1_top2_all hA_pos hlcm_all
      (hAx.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
        (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
      hx13 hx14 hx12 hx34 hx23.symm hx24.symm r hr_pr
    omega
  let Qp := p ^ (x₄.factorization p + x₂.factorization p)
  let Qq := q ^ (x₄.factorization q + x₁.factorization q)
  let Qr := r ^ (x₄.factorization r + x₁.factorization r)
  have hx₃_eq_prod : x₃ = p ^ (x₂.factorization p) * q ^ (x₁.factorization q) := by
    have hself := (Nat.prod_factorization_pow_eq_self hx₃_pos.ne').symm
    have hsub3 : x₃.primeFactors ⊆ {p, q} := by
      intro s hs
      have hsP := hpf_sub_P x₃ (by rw [hAx]; simp) hs
      rw [hP_eq3] at hsP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsP ⊢
      rcases hsP with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have hr3 := (Nat.mem_primeFactors_of_ne_zero hx₃_pos.ne').mp hs
        have hfac_r := one_le_fac_of_dvd hr_pr hx₃_pos.ne' hr3.2
        omega
    have hzero_rest : ∀ s ∈ ({p, q} : Finset ℕ), s ∉ x₃.primeFactors → s ^ (x₃.factorization s) = 1 := by
      intro s _ hns
      have hf0 : x₃.factorization s = 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hns
        exact hns
      rw [hf0, pow_zero]
    have heq_prod := Finset.prod_subset hsub3 hzero_rest
    rw [Finset.prod_pair hpq, hx_eq_p, hx_eq_q] at heq_prod
    exact hself.trans heq_prod
  have hx₂_eq_prod : x₂ = p ^ (x₂.factorization p) * r ^ (x₁.factorization r) := by
    have hself := (Nat.prod_factorization_pow_eq_self hx₂_pos.ne').symm
    have hsub2 : x₂.primeFactors ⊆ {p, r} := by
      intro s hs
      have hsP := hpf_sub_P x₂ (by rw [hAx]; simp) hs
      rw [hP_eq3] at hsP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsP ⊢
      rcases hsP with rfl | rfl | rfl
      · exact Or.inl rfl
      · have hq2 := (Nat.mem_primeFactors_of_ne_zero hx₂_pos.ne').mp hs
        have hfac_q := one_le_fac_of_dvd hq_pr hx₂_pos.ne' hq2.2
        omega
      · exact Or.inr rfl
    have hzero_rest : ∀ s ∈ ({p, r} : Finset ℕ), s ∉ x₂.primeFactors → s ^ (x₂.factorization s) = 1 := by
      intro s _ hns
      have hf0 : x₂.factorization s = 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hns
        exact hns
      rw [hf0, pow_zero]
    have heq_prod := Finset.prod_subset hsub2 hzero_rest
    rw [Finset.prod_pair hpr, hx_eq_r] at heq_prod
    exact hself.trans heq_prod
  have hx₁_eq_prod : x₁ = q ^ (x₁.factorization q) * r ^ (x₁.factorization r) := by
    have hself := (Nat.prod_factorization_pow_eq_self hx₁_pos.ne').symm
    have hsub1 : x₁.primeFactors ⊆ {q, r} := by
      intro s hs
      have hsP := hpf_sub_P x₁ (by rw [hAx]; simp) hs
      rw [hP_eq3] at hsP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsP ⊢
      rcases hsP with rfl | rfl | rfl
      · have hp1 := (Nat.mem_primeFactors_of_ne_zero hx₁_pos.ne').mp hs
        have hfac_p := one_le_fac_of_dvd hp_pr hx₁_pos.ne' hp1.2
        omega
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hzero_rest : ∀ s ∈ ({q, r} : Finset ℕ), s ∉ x₁.primeFactors → s ^ (x₁.factorization s) = 1 := by
      intro s _ hns
      have hf0 : x₁.factorization s = 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hns
        exact hns
      rw [hf0, pow_zero]
    have heq_prod := Finset.prod_subset hsub1 hzero_rest
    rw [Finset.prod_pair hqr] at heq_prod
    exact hself.trans heq_prod
  have two_pow_le_of_lt : ∀ (s a b : ℕ), s.Prime → a < b → 2 * s ^ a ≤ s ^ b := by
    intro s a b hs hab
    calc 2 * s ^ a ≤ s * s ^ a := Nat.mul_le_mul_right _ hs.two_le
      _ = s ^ (a + 1) := (pow_succ' s a).symm
      _ ≤ s ^ b := Nat.pow_le_pow_right hs.pos hab
  have h4_pq : 4 * Qp * Qq ≤ M * M := by
    have h2p := two_pow_le_of_lt p _ _ hp_pr h24_lt.1
    have h2q := two_pow_le_of_lt q _ _ hq_pr h14_lt.1
    calc 4 * Qp * Qq
        = (2 * p ^ (x₄.factorization p)) * p ^ (x₂.factorization p) *
          ((2 * q ^ (x₄.factorization q)) * q ^ (x₁.factorization q)) := by
            dsimp only [Qp, Qq]; rw [pow_add, pow_add]; ring
      _ ≤ (p ^ (x₂.factorization p) * p ^ (x₂.factorization p)) *
          (q ^ (x₁.factorization q) * q ^ (x₁.factorization q)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h2p) (Nat.mul_le_mul_right _ h2q)
      _ = (p ^ (x₂.factorization p) * q ^ (x₁.factorization q)) *
          (p ^ (x₂.factorization p) * q ^ (x₁.factorization q)) := by ring
      _ = x₃ * x₃ := by rw [← hx₃_eq_prod]
      _ ≤ M * M := Nat.mul_le_mul hx₃_M hx₃_M
  have h4_pr : 4 * Qp * Qr ≤ M * M := by
    have h2p := two_pow_le_of_lt p _ _ hp_pr h24_lt.1
    have h2r := two_pow_le_of_lt r _ _ hr_pr h14_lt.2
    calc 4 * Qp * Qr
        = (2 * p ^ (x₄.factorization p)) * p ^ (x₂.factorization p) *
          ((2 * r ^ (x₄.factorization r)) * r ^ (x₁.factorization r)) := by
            dsimp only [Qp, Qr]; rw [pow_add, pow_add]; ring
      _ ≤ (p ^ (x₂.factorization p) * p ^ (x₂.factorization p)) *
          (r ^ (x₁.factorization r) * r ^ (x₁.factorization r)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h2p) (Nat.mul_le_mul_right _ h2r)
      _ = (p ^ (x₂.factorization p) * r ^ (x₁.factorization r)) *
          (p ^ (x₂.factorization p) * r ^ (x₁.factorization r)) := by ring
      _ = x₂ * x₂ := by rw [← hx₂_eq_prod]
      _ ≤ M * M := Nat.mul_le_mul hx₂_M hx₂_M
  have h4_qr : 4 * Qq * Qr ≤ M * M := by
    have h2q := two_pow_le_of_lt q _ _ hq_pr h14_lt.1
    have h2r := two_pow_le_of_lt r _ _ hr_pr h14_lt.2
    calc 4 * Qq * Qr
        = (2 * q ^ (x₄.factorization q)) * q ^ (x₁.factorization q) *
          ((2 * r ^ (x₄.factorization r)) * r ^ (x₁.factorization r)) := by
            dsimp only [Qq, Qr]; rw [pow_add, pow_add]; ring
      _ ≤ (q ^ (x₁.factorization q) * q ^ (x₁.factorization q)) *
          (r ^ (x₁.factorization r) * r ^ (x₁.factorization r)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h2q) (Nat.mul_le_mul_right _ h2r)
      _ = (q ^ (x₁.factorization q) * r ^ (x₁.factorization r)) *
          (q ^ (x₁.factorization q) * r ^ (x₁.factorization r)) := by ring
      _ = x₁ * x₁ := by rw [← hx₁_eq_prod]
      _ ≤ M * M := Nat.mul_le_mul hx₁_M hx₁_M
  by_cases hp_big : M < 2 * Qp
  · have h2Qq : 2 * Qq ≤ M := by
      by_contra hgt
      have h1 : M * M < (2 * Qp) * (2 * Qq) := Nat.mul_lt_mul'' hp_big (Nat.lt_of_not_ge hgt)
      linarith
    have h2Qr : 2 * Qr ≤ M := by
      by_contra hgt
      have h1 : M * M < (2 * Qp) * (2 * Qr) := Nat.mul_lt_mul'' hp_big (Nat.lt_of_not_ge hgt)
      linarith
    exact cover_four_r1_three_primes_aux hAx hx12 hx13 hx14 hx23 hx24 hx34
      hA_pos hA_le hM_half hb₀_I hdiv_b0 hp_pr hq_pr hr_pr hpq hpr hqr
      hx_eq_p hx_eq_q hx_eq_r h1p0 h2q0 h3r0 h24_lt.1 h14_lt.1 h14_lt.2 hrest h2Qq h2Qr
  · have h2Qp : 2 * Qp ≤ M := Nat.le_of_not_lt hp_big
    by_cases hq_big : M < 2 * Qq
    · have h2Qr : 2 * Qr ≤ M := by
        by_contra hgt
        have h1 : M * M < (2 * Qq) * (2 * Qr) := Nat.mul_lt_mul'' hq_big (Nat.lt_of_not_ge hgt)
        linarith
      have hAx' : A = {x₂, x₁, x₃, x₄} :=
        hAx.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
          (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))))
      exact cover_four_r1_three_primes_aux hAx' hx12.symm hx23 hx24 hx13 hx14 hx34
        hA_pos hA_le hM_half hb₀_I hdiv_b0 hq_pr hp_pr hr_pr hpq.symm hqr hpr
        hx_eq_q hx_eq_p hx_eq_r.symm h2q0 h1p0 h3r0 h14_lt.1 h24_lt.1 h24_lt.2
        (fun s hs hs1 hs2 hs3 => by
          have := hrest s hs hs2 hs1 hs3
          exact ⟨this.2.1, this.1, this.2.2.1, this.2.2.2⟩) h2Qp (by rw [hx_eq_r]; exact h2Qr)
    · have h2Qq : 2 * Qq ≤ M := Nat.le_of_not_lt hq_big
      have hAx' : A = {x₃, x₂, x₁, x₄} :=
        hAx.trans (set4_perm (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
          (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))))
      exact cover_four_r1_three_primes_aux hAx' hx23.symm hx13.symm hx34 hx12.symm hx24 hx14
        hA_pos hA_le hM_half hb₀_I hdiv_b0 hr_pr hq_pr hp_pr hqr.symm hpr.symm hpq.symm
        hx_eq_r.symm hx_eq_q.symm hx_eq_p.symm h3r0 h2q0 h1p0 h24_lt.2 h34_lt.2 h34_lt.1
        (fun s hs hs1 hs2 hs3 => by
          have := hrest s hs hs3 hs2 hs1
          exact ⟨this.2.2.1, this.2.1, this.1, this.2.2.2⟩) (by rw [hx_eq_q]; exact h2Qq) (by rw [hx_eq_p]; exact h2Qp)

private lemma cover_four_r1_subcase1B_ii {A : Finset ℕ} {x M b₀ a₁ a₂ a₃ a₄ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄})
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id)
    (hF12 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₂ a₃ a₄)
    (hF13 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₃ a₂ a₄)
    (hF14 : ¬ ValidAB (A.lcm id).primeFactors a₁ a₄ a₂ a₃)
    (hF23 : ¬ ValidAB (A.lcm id).primeFactors a₂ a₃ a₁ a₄)
    (hF24 : ¬ ValidAB (A.lcm id).primeFactors a₂ a₄ a₁ a₃)
    (hF34 : ¬ ValidAB (A.lcm id).primeFactors a₃ a₄ a₁ a₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
    let P : Finset ℕ := (A.lcm id).primeFactors
    have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
    have htop2_all : ∀ (u₁ u₂ u₃ u₄ : ℕ), A = {u₁, u₂, u₃, u₄} →
        u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₂ ≠ u₃ → u₂ ≠ u₄ → u₃ ≠ u₄ →
        ∀ r : ℕ, r.Prime →
          u₄.factorization r ≤ max (max (u₁.factorization r) (u₂.factorization r)) (u₃.factorization r) :=
      fun _ _ _ _ hAu hu12 hu13 hu14 hu23 hu24 hu34 r hr =>
        r1_top2_all hA_pos hlcm_all hAu hu12 hu13 hu14 hu23 hu24 hu34 r hr
    have hL_ne0 : A.lcm id ≠ 0 := finset_lcm_ne_zero hA0
    have hP_pos_dvd : ∀ p ∈ P, p.Prime ∧ p ∣ A.lcm id := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, ((Nat.mem_primeFactors_of_ne_zero hL_ne0).mp hp).2⟩
    have not_single_prime : ∀ u ∈ A, ∀ p : ℕ, (∀ q ∈ u.primeFactors, q = p) → False :=
      fun u huA p hp_only => r1_not_single_prime hA_eq h12 hA_pos hA_le hM_half hlcm_all huA p hp_only
    have hfail_two : ∀ u₁ u₂ u₃ u₄ : ℕ, A = {u₁, u₂, u₃, u₄} →
        u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₂ ≠ u₃ → u₂ ≠ u₄ → u₃ ≠ u₄ →
        ¬ ValidAB P u₁ u₂ u₃ u₄ →
        ∀ p ∈ P, ¬ (u₃.factorization p = 0 ∧ u₄.factorization p = 0) :=
      fun _ _ _ _ hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail _ hp =>
        r1_fail_two hA_pos hlcm_all hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail hp
    have huniq_zero : ∀ p ∈ P,
        (a₁.factorization p = 0 ∧ 0 < a₂.factorization p ∧ 0 < a₃.factorization p ∧ 0 < a₄.factorization p) ∨
        (0 < a₁.factorization p ∧ a₂.factorization p = 0 ∧ 0 < a₃.factorization p ∧ 0 < a₄.factorization p) ∨
        (0 < a₁.factorization p ∧ 0 < a₂.factorization p ∧ a₃.factorization p = 0 ∧ 0 < a₄.factorization p) ∨
        (0 < a₁.factorization p ∧ 0 < a₂.factorization p ∧ 0 < a₃.factorization p ∧ a₄.factorization p = 0) :=
      fun _ hp => r1_uniq_zero hA_eq h12 h13 h14 h23 h24 h34 hA_pos hAgcd hlcm_all hF12 hF13 hF14 hF23 hF24 hF34 hp
    have hpos_of_ne_zero : ∀ p ∈ P, ∀ u v : ℕ, u ∈ A → v ∈ A → u ≠ v →
        u.factorization p = 0 → 0 < v.factorization p := by
      intro p hp u v hu hv huv hu0
      have hz := huniq_zero p hp
      rw [hA_eq] at hu hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl huv | omega
    let S : ℕ → Finset ℕ := fun u => P.filter (fun p => u.factorization p = 0)
    have key_char : ∀ u₁ u₂ u₃ u₄ : ℕ, A = {u₁, u₂, u₃, u₄} →
        u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₂ ≠ u₃ → u₂ ≠ u₄ → u₃ ≠ u₄ →
        ¬ ValidAB P u₁ u₂ u₃ u₄ →
        2 ≤ (S u₃ ∪ S u₄).card →
        (∀ p ∈ S u₃ ∪ S u₄, u₁.factorization p < u₂.factorization p) ∨
        (∀ p ∈ S u₃ ∪ S u₄, u₂.factorization p < u₁.factorization p) :=
      fun _ _ _ _ hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail hU2 =>
        r1_key_char hA_pos hlcm_all hpos_of_ne_zero hAu hu12 hu13 hu14 hu23 hu24 hu34 hFail hU2
    have hno_three_ne : ∀ u₁ u₂ u₃ u₄ : ℕ, A = {u₁, u₂, u₃, u₄} →
        u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₂ ≠ u₃ → u₂ ≠ u₄ → u₃ ≠ u₄ →
        ¬ ValidAB P u₁ u₂ u₃ u₄ → ¬ ValidAB P u₁ u₃ u₂ u₄ → ¬ ValidAB P u₂ u₃ u₁ u₄ →
        2 ≤ (S u₄).card ∨ (1 ≤ (S u₄).card ∧ 1 ≤ (S u₁).card ∧ 1 ≤ (S u₂).card ∧ 1 ≤ (S u₃).card) →
        False :=
      fun _ _ _ _ hAu hu12 hu13 hu14 hu23 hu24 hu34 hF12 hF13 hF23 hcond =>
        r1_no_three_ne hA_pos hlcm_all hpos_of_ne_zero hAu hu12 hu13 hu14 hu23 hu24 hu34 hF12 hF13 hF23 hcond
    have hS4_le1 : (S a₄).card ≤ 1 := by
      by_contra h2; exact hno_three_ne a₁ a₂ a₃ a₄ hA_eq h12 h13 h14 h23 h24 h34 hF12 hF13 hF23 (Or.inl (by omega))
    have hS3_le1 : (S a₃).card ≤ 1 := by
      by_contra h2
      have hAu : A = {a₁, a₂, a₄, a₃} :=
        hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl))))
      exact hno_three_ne a₁ a₂ a₄ a₃ hAu h12 h14 h13 h24 h23 h34.symm
        (fun h => hF12 (validAB_swap34 h)) hF14 hF24 (Or.inl (by omega))
    have hS2_le1 : (S a₂).card ≤ 1 := by
      by_contra h2
      have hAu : A = {a₁, a₃, a₄, a₂} :=
        hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
          (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))))
      exact hno_three_ne a₁ a₃ a₄ a₂ hAu h13 h14 h12 h34 h23.symm h24.symm
        (fun h => hF13 (validAB_swap34 h)) (fun h => hF14 (validAB_swap34 h)) hF34 (Or.inl (by omega))
    have hS1_le1 : (S a₁).card ≤ 1 := by
      by_contra h2
      have hAu : A = {a₂, a₃, a₄, a₁} :=
        hA_eq.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
          (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))))
      exact hno_three_ne a₂ a₃ a₄ a₁ hAu h23 h24 h12.symm h34 h13.symm h14.symm
        (fun h => hF23 (validAB_swap34 h)) (fun h => hF24 (validAB_swap34 h)) (fun h => hF34 (validAB_swap34 h)) (Or.inl (by omega))
    have hnot_all_pos : ¬ (1 ≤ (S a₄).card ∧ 1 ≤ (S a₁).card ∧ 1 ≤ (S a₂).card ∧ 1 ≤ (S a₃).card) := by
      intro h4; exact hno_three_ne a₁ a₂ a₃ a₄ hA_eq h12 h13 h14 h23 h24 h34 hF12 hF13 hF23 (Or.inr h4)
    have hsumS : (S a₁).card + (S a₂).card + (S a₃).card + (S a₄).card ≤ 3 := by omega
    -- Also every prime in `u.primeFactors` for `u ∈ A` lies in `P`, and `P = S a₁ ∪ S a₂ ∪ S a₃ ∪ S a₄`.
    have hpf_sub_P : ∀ u ∈ A, u.primeFactors ⊆ P := by
      intro u hu p hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp
      have hpu : p ∣ u := ((Nat.mem_primeFactors_of_ne_zero (hA_pos u hu).ne').mp hp).2
      exact (Nat.mem_primeFactors_of_ne_zero hL_ne0).mpr ⟨hp_pr, dvd_trans hpu (Finset.dvd_lcm hu)⟩
    have hP_eq_U : P = S a₁ ∪ S a₂ ∪ S a₃ ∪ S a₄ := by
      ext p; constructor
      · intro hp
        rcases huniq_zero p hp with ⟨h1,_⟩ | ⟨_,h2,_⟩ | ⟨_,_,h3,_⟩ | ⟨_,_,_,h4⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h1⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h2⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h3⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h4⟩)
      · intro hp
        simp only [Finset.mem_union, S, Finset.mem_filter] at hp
        rcases hp with ((h | h) | h) | h <;> exact h.1
    have hP_le3 : P.card ≤ 3 := by
      rw [hP_eq_U]
      have h1 := Finset.card_union_le (S a₁ ∪ S a₂ ∪ S a₃) (S a₄)
      have h2 := Finset.card_union_le (S a₁ ∪ S a₂) (S a₃)
      have h3 := Finset.card_union_le (S a₁) (S a₂)
      omega
    have hP_ge3 : 3 ≤ P.card := by
      by_contra hlt3
      have hP_le2 : P.card ≤ 2 := by omega
      have hP_ne : P.Nonempty := by
        have hm1 : (a₁.primeFactors).Nonempty := Nat.nonempty_primeFactors.mpr (by
          by_contra hlt; have h1 : a₁ = 1 := by
            have := hA_pos a₁ (by rw [hA_eq]; simp); omega
          have hm := hM_half a₁ (by rw [hA_eq]; simp); rw [h1, mul_one] at hm
          have := hA_le a₂ (by rw [hA_eq]; simp)
          have := hA_pos a₂ (by rw [hA_eq]; simp)
          omega)
        obtain ⟨p, hp⟩ := hm1
        exact ⟨p, hpf_sub_P a₁ (by rw [hA_eq]; simp) hp⟩
      obtain ⟨p, hpP⟩ := hP_ne
      rcases huniq_zero p hpP with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3, _⟩ | ⟨_, _, _, h4⟩
      · have hpf_sub : a₁.primeFactors ⊆ P.erase p := by
          intro q hq
          have hq_ne : q ≠ p := fun heq => by
            rw [heq] at hq
            have ha₁_pos := hA_pos a₁ (by rw [hA_eq]; simp)
            have := (Nat.mem_primeFactors_of_ne_zero ha₁_pos.ne').mp hq
            have hfac1 := one_le_fac_of_dvd this.1 ha₁_pos.ne' this.2
            omega
          exact Finset.mem_erase.mpr ⟨hq_ne, hpf_sub_P a₁ (by rw [hA_eq]; simp) hq⟩
        have hcard1 : a₁.primeFactors.card ≤ 1 := by
          have := Finset.card_le_card hpf_sub
          rw [Finset.card_erase_of_mem hpP] at this
          omega
        obtain ⟨q, hq_only⟩ : ∃ q, ∀ r ∈ a₁.primeFactors, r = q := by
          rcases Nat.eq_zero_or_pos a₁.primeFactors.card with h0 | h1
          · exact ⟨2, fun r hr => absurd (Finset.card_pos.mpr ⟨r, hr⟩) (by omega)⟩
          · have h1' : a₁.primeFactors.card = 1 := by omega
            obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1'
            exact ⟨q, fun r hr => Finset.mem_singleton.mp (hq ▸ hr)⟩
        exact not_single_prime a₁ (by rw [hA_eq]; simp) q hq_only
      · have hpf_sub : a₂.primeFactors ⊆ P.erase p := by
          intro q hq
          have hq_ne : q ≠ p := fun heq => by
            rw [heq] at hq
            have ha₂_pos := hA_pos a₂ (by rw [hA_eq]; simp)
            have := (Nat.mem_primeFactors_of_ne_zero ha₂_pos.ne').mp hq
            have hfac1 := one_le_fac_of_dvd this.1 ha₂_pos.ne' this.2
            omega
          exact Finset.mem_erase.mpr ⟨hq_ne, hpf_sub_P a₂ (by rw [hA_eq]; simp) hq⟩
        have hcard1 : a₂.primeFactors.card ≤ 1 := by
          have := Finset.card_le_card hpf_sub; rw [Finset.card_erase_of_mem hpP] at this; omega
        obtain ⟨q, hq_only⟩ : ∃ q, ∀ r ∈ a₂.primeFactors, r = q := by
          rcases Nat.eq_zero_or_pos a₂.primeFactors.card with h0 | h1
          · exact ⟨2, fun r hr => absurd (Finset.card_pos.mpr ⟨r, hr⟩) (by omega)⟩
          · have h1' : a₂.primeFactors.card = 1 := by omega
            obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1'
            exact ⟨q, fun r hr => Finset.mem_singleton.mp (hq ▸ hr)⟩
        exact not_single_prime a₂ (by rw [hA_eq]; simp) q hq_only
      · have hpf_sub : a₃.primeFactors ⊆ P.erase p := by
          intro q hq
          have hq_ne : q ≠ p := fun heq => by
            rw [heq] at hq
            have ha₃_pos := hA_pos a₃ (by rw [hA_eq]; simp)
            have := (Nat.mem_primeFactors_of_ne_zero ha₃_pos.ne').mp hq
            have hfac1 := one_le_fac_of_dvd this.1 ha₃_pos.ne' this.2
            omega
          exact Finset.mem_erase.mpr ⟨hq_ne, hpf_sub_P a₃ (by rw [hA_eq]; simp) hq⟩
        have hcard1 : a₃.primeFactors.card ≤ 1 := by
          have := Finset.card_le_card hpf_sub; rw [Finset.card_erase_of_mem hpP] at this; omega
        obtain ⟨q, hq_only⟩ : ∃ q, ∀ r ∈ a₃.primeFactors, r = q := by
          rcases Nat.eq_zero_or_pos a₃.primeFactors.card with h0 | h1
          · exact ⟨2, fun r hr => absurd (Finset.card_pos.mpr ⟨r, hr⟩) (by omega)⟩
          · have h1' : a₃.primeFactors.card = 1 := by omega
            obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1'
            exact ⟨q, fun r hr => Finset.mem_singleton.mp (hq ▸ hr)⟩
        exact not_single_prime a₃ (by rw [hA_eq]; simp) q hq_only
      · have hpf_sub : a₄.primeFactors ⊆ P.erase p := by
          intro q hq
          have hq_ne : q ≠ p := fun heq => by
            rw [heq] at hq
            have ha₄_pos := hA_pos a₄ (by rw [hA_eq]; simp)
            have := (Nat.mem_primeFactors_of_ne_zero ha₄_pos.ne').mp hq
            have hfac1 := one_le_fac_of_dvd this.1 ha₄_pos.ne' this.2
            omega
          exact Finset.mem_erase.mpr ⟨hq_ne, hpf_sub_P a₄ (by rw [hA_eq]; simp) hq⟩
        have hcard1 : a₄.primeFactors.card ≤ 1 := by
          have := Finset.card_le_card hpf_sub; rw [Finset.card_erase_of_mem hpP] at this; omega
        obtain ⟨q, hq_only⟩ : ∃ q, ∀ r ∈ a₄.primeFactors, r = q := by
          rcases Nat.eq_zero_or_pos a₄.primeFactors.card with h0 | h1
          · exact ⟨2, fun r hr => absurd (Finset.card_pos.mpr ⟨r, hr⟩) (by omega)⟩
          · have h1' : a₄.primeFactors.card = 1 := by omega
            obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1'
            exact ⟨q, fun r hr => Finset.mem_singleton.mp (hq ▸ hr)⟩
        exact not_single_prime a₄ (by rw [hA_eq]; simp) q hq_only
    have hP_card3 : P.card = 3 := by omega
    have hS_disj : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → Disjoint (S u) (S v) := by
      intro u hu v hv huv
      rw [Finset.disjoint_left]
      intro p hpu hpv
      have hpP := (Finset.mem_filter.mp hpu).1
      have hu0 := (Finset.mem_filter.mp hpu).2
      have hv0 := (Finset.mem_filter.mp hpv).2
      have := hpos_of_ne_zero p hpP u v hu hv huv hu0
      omega
    have hP_sum : P.card = (S a₁).card + (S a₂).card + (S a₃).card + (S a₄).card := by
      have h12d : Disjoint (S a₁) (S a₂) := hS_disj a₁ (by rw [hA_eq]; simp) a₂ (by rw [hA_eq]; simp) h12
      have h123d : Disjoint (S a₁ ∪ S a₂) (S a₃) := by
        rw [Finset.disjoint_union_left]
        exact ⟨hS_disj a₁ (by rw [hA_eq]; simp) a₃ (by rw [hA_eq]; simp) h13,
               hS_disj a₂ (by rw [hA_eq]; simp) a₃ (by rw [hA_eq]; simp) h23⟩
      have h1234d : Disjoint (S a₁ ∪ S a₂ ∪ S a₃) (S a₄) := by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨hS_disj a₁ (by rw [hA_eq]; simp) a₄ (by rw [hA_eq]; simp) h14,
                hS_disj a₂ (by rw [hA_eq]; simp) a₄ (by rw [hA_eq]; simp) h24⟩,
               hS_disj a₃ (by rw [hA_eq]; simp) a₄ (by rw [hA_eq]; simp) h34⟩
      rw [hP_eq_U, Finset.card_union_of_disjoint h1234d, Finset.card_union_of_disjoint h123d,
          Finset.card_union_of_disjoint h12d]
    have hS_cases :
        ((S a₁).card = 1 ∧ (S a₂).card = 1 ∧ (S a₃).card = 1 ∧ (S a₄).card = 0) ∨
        ((S a₁).card = 1 ∧ (S a₂).card = 1 ∧ (S a₄).card = 1 ∧ (S a₃).card = 0) ∨
        ((S a₁).card = 1 ∧ (S a₃).card = 1 ∧ (S a₄).card = 1 ∧ (S a₂).card = 0) ∨
        ((S a₂).card = 1 ∧ (S a₃).card = 1 ∧ (S a₄).card = 1 ∧ (S a₁).card = 0) := by omega
    rcases hS_cases with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c4, c3⟩ | ⟨c1, c3, c4, c2⟩ | ⟨c2, c3, c4, c1⟩
    · exact r1_close_three_primes hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all hpos_of_ne_zero hP_ge3
        hA_eq h12 h13 h14 h23 h24 h34 hF14 hF24 hF34 c1 c2 c3 c4
    · exact r1_close_three_primes hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all hpos_of_ne_zero hP_ge3
        (hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inl rfl)))))
        h12 h14 h13 h24 h23 h34.symm hF13 hF23 (fun h => hF34 (validAB_swap12 h)) c1 c2 c4 c3
    · exact r1_close_three_primes hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all hpos_of_ne_zero hP_ge3
        (hA_eq.trans (set4_perm (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl))
          (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
        h13 h14 h12 h34 h23.symm h24.symm hF12 (fun h => hF23 (validAB_swap12 h)) (fun h => hF24 (validAB_swap12 h)) c1 c3 c4 c2
    · exact r1_close_three_primes hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all hpos_of_ne_zero hP_ge3
        (hA_eq.trans (set4_perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
          (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))))
        h23 h24 h12.symm h34 h13.symm h14.symm (fun h => hF12 (validAB_swap12 h)) (fun h => hF13 (validAB_swap12 h)) (fun h => hF14 (validAB_swap12 h)) c2 c3 c4 c1

private lemma cover_four_r1_subcase1B {A : Finset ℕ} {x M b₀ a₁ a₂ a₃ a₄ : ℕ}
    (hA_eq : A = {a₁, a₂, a₃, a₄})
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hM_half : ∀ a ∈ A, M < 2 * a) (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A, a ∣ b₀)
    (hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  let P : Finset ℕ := (A.lcm id).primeFactors
  by_cases hV :
      ValidAB P a₁ a₂ a₃ a₄ ∨ ValidAB P a₁ a₃ a₂ a₄ ∨ ValidAB P a₁ a₄ a₂ a₃ ∨
      ValidAB P a₂ a₃ a₁ a₄ ∨ ValidAB P a₂ a₄ a₁ a₃ ∨ ValidAB P a₃ a₄ a₁ a₂
  · rcases hV with h | h | h | h | h | h
    · exact cover_four_r1_of_validAB hA_eq h12 h13 h14 h23 h24 h34
        hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
    · exact cover_four_r1_of_validAB
        (by rw [hA_eq]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        h13 h12 h14 h23.symm h34 h24 hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
    · exact cover_four_r1_of_validAB
        (by rw [hA_eq]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        h14 h12 h13 h24.symm h34.symm h23 hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
    · exact cover_four_r1_of_validAB
        (by rw [hA_eq]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        h23 h12.symm h24 h13.symm h34 h14 hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
    · exact cover_four_r1_of_validAB
        (by rw [hA_eq]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        h24 h12.symm h23 h14.symm h34.symm h13 hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
    · exact cover_four_r1_of_validAB
        (by rw [hA_eq]; ext z; simp [Finset.mem_insert, Finset.mem_singleton]; tauto)
        h34 h13.symm h23.symm h14.symm h24.symm h12 hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all h
  · push Not at hV
    rcases hV with ⟨hF12, hF13, hF14, hF23, hF24, hF34⟩
    exact cover_four_r1_subcase1B_ii hA_eq h12 h13 h14 h23 h24 h34
      hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all hF12 hF13 hF14 hF23 hF24 hF34

theorem erdos708_upper_four_of_matching_one {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 4) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hSA : S ⊆ A) (hS_card : S.card = 1)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a)
    (hmax : ∀ u ∈ A \ S, ∀ b ∈ consecInterval x M, u ∣ b → b ∈ S.image f) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B := by
  obtain ⟨s₀, hS_eq⟩ := Finset.card_eq_one.mp hS_card
  have hs₀_S : s₀ ∈ S := by rw [hS_eq]; exact Finset.mem_singleton_self s₀
  let b₀ := f s₀
  have hb₀_I : b₀ ∈ consecInterval x M := hf_mem s₀ hs₀_S
  have hs₀_b₀ : s₀ ∣ b₀ := hf_dvd s₀ hs₀_S
  have hSimg : S.image f = {b₀} := by rw [hS_eq, Finset.image_singleton]
  have hdiv_b0 : ∀ a ∈ A, a ∣ b₀ := by
    intro a ha
    by_cases haS : a ∈ S
    · rw [hS_eq, Finset.mem_singleton] at haS; exact haS ▸ hs₀_b₀
    · obtain ⟨m, hm_I, ham⟩ := exists_multiple_in_consecInterval x a M (hA_pos a ha) (hA_le a ha)
      have hm_img := hmax a (Finset.mem_sdiff.mpr ⟨ha, haS⟩) m hm_I ham
      rw [hSimg, Finset.mem_singleton] at hm_img
      exact hm_img ▸ ham
  obtain ⟨u₁, u₂, u₃, hu12, hu13, hu23, hdiff_eq⟩ := Finset.card_eq_three.mp (by
    have h1 := Finset.card_sdiff_add_card_inter A S
    have h2 : A ∩ S = S := Finset.inter_eq_right.mpr hSA
    rw [h2, hA_card, hS_card] at h1
    omega : (A \ S).card = 3)
  have hu₁_diff : u₁ ∈ A \ S := by rw [hdiff_eq]; simp
  have hu₂_diff : u₂ ∈ A \ S := by rw [hdiff_eq]; simp
  have hu₃_diff : u₃ ∈ A \ S := by rw [hdiff_eq]; simp
  have hu₁_A : u₁ ∈ A := (Finset.mem_sdiff.mp hu₁_diff).1
  have hu₂_A : u₂ ∈ A := (Finset.mem_sdiff.mp hu₂_diff).1
  have hu₃_A : u₃ ∈ A := (Finset.mem_sdiff.mp hu₃_diff).1
  have hu₁_nS : u₁ ∉ S := (Finset.mem_sdiff.mp hu₁_diff).2
  have hu₂_nS : u₂ ∉ S := (Finset.mem_sdiff.mp hu₂_diff).2
  have hu₃_nS : u₃ ∉ S := (Finset.mem_sdiff.mp hu₃_diff).2
  have hs₀_A : s₀ ∈ A := hSA hs₀_S
  have hs0u1 : s₀ ≠ u₁ := fun h => hu₁_nS (h ▸ hs₀_S)
  have hs0u2 : s₀ ≠ u₂ := fun h => hu₂_nS (h ▸ hs₀_S)
  have hs0u3 : s₀ ≠ u₃ := fun h => hu₃_nS (h ▸ hs₀_S)
  have hA_eq : A = {s₀, u₁, u₂, u₃} := by
    rw [← Finset.sdiff_union_of_subset hSA, hdiff_eq, hS_eq]
    ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have huniq_half : ∀ u ∈ A \ S, M < 2 * u := by
    intro u hu
    have huA := (Finset.mem_sdiff.mp hu).1
    exact lt_two_mul_of_unique_multiple_in_consecInterval (hA_pos u huA) hb₀_I (hdiv_b0 u huA)
      (fun b hbI hub => by
        have hm := hmax u hu b hbI hub
        rw [hSimg, Finset.mem_singleton] at hm
        exact hm)
  by_cases hs0_half : M < 2 * s₀
  · have hM_half : ∀ a ∈ A, M < 2 * a := by
      intro a ha
      by_cases haS : a ∈ S
      · rw [hS_eq, Finset.mem_singleton] at haS; exact haS ▸ hs0_half
      · exact huniq_half a (Finset.mem_sdiff.mpr ⟨ha, haS⟩)
    by_cases h1 : ¬ (s₀ ∣ (A.erase s₀).lcm id)
    · have hA_eq' : A = {u₁, u₂, u₃, s₀} := by
        rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_four_r1_subcase1A hA_eq' hu12 hu13 hs0u1.symm hu23 hs0u2.symm hs0u3.symm
        hA_pos hA_le hM_half hb₀_I hdiv_b0 h1
    · by_cases h2 : ¬ (u₁ ∣ (A.erase u₁).lcm id)
      · have hA_eq' : A = {s₀, u₂, u₃, u₁} := by
          rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        exact cover_four_r1_subcase1A hA_eq' hs0u2 hs0u3 hs0u1 hu23 hu12.symm hu13.symm
          hA_pos hA_le hM_half hb₀_I hdiv_b0 h2
      · by_cases h3 : ¬ (u₂ ∣ (A.erase u₂).lcm id)
        · have hA_eq' : A = {s₀, u₁, u₃, u₂} := by
            rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
          exact cover_four_r1_subcase1A hA_eq' hs0u1 hs0u3 hs0u2 hu13 hu12 hu23.symm
            hA_pos hA_le hM_half hb₀_I hdiv_b0 h3
        · by_cases h4 : ¬ (u₃ ∣ (A.erase u₃).lcm id)
          · exact cover_four_r1_subcase1A hA_eq hs0u1 hs0u2 hs0u3 hu12 hu13 hu23
              hA_pos hA_le hM_half hb₀_I hdiv_b0 h4
          · have hlcm_all : ∀ a ∈ A, a ∣ (A.erase a).lcm id := by
              intro a ha
              rw [hA_eq] at ha
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl
              · exact not_not.mp h1
              · exact not_not.mp h2
              · exact not_not.mp h3
              · exact not_not.mp h4
            exact cover_four_r1_subcase1B hA_eq hs0u1 hs0u2 hs0u3 hu12 hu13 hu23
              hA_pos hA_le hAgcd hM_half hb₀_I hdiv_b0 hlcm_all
  · have hs₀_pos : 0 < s₀ := hA_pos s₀ hs₀_A
    have h2s₀ : 2 * s₀ ≤ M := by omega
    obtain ⟨b', hb'_I, hb'_b0, hs₀_b'⟩ :=
      exists_second_multiple_in_consecInterval hs₀_pos h2s₀ hb₀_I hs₀_b₀
    have hu₁_pos : 0 < u₁ := hA_pos u₁ hu₁_A
    have hu₂_pos : 0 < u₂ := hA_pos u₂ hu₂_A
    have hu₃_pos : 0 < u₃ := hA_pos u₃ hu₃_A
    have hu₁_M : u₁ ≤ M := hA_le u₁ hu₁_A
    have hu₂_M : u₂ ≤ M := hA_le u₂ hu₂_A
    have hu₃_M : u₃ ≤ M := hA_le u₃ hu₃_A
    have hu₁_half : M < 2 * u₁ := huniq_half u₁ hu₁_diff
    have hu₂_half : M < 2 * u₂ := huniq_half u₂ hu₂_diff
    have hu₃_half : M < 2 * u₃ := huniq_half u₃ hu₃_diff
    let g₁₂ := Nat.gcd u₁ u₂
    let g₁₃ := Nat.gcd u₁ u₃
    let g₂₃ := Nat.gcd u₂ u₃
    have hg₁₂_pos : 0 < g₁₂ := Nat.gcd_pos_of_pos_left u₂ hu₁_pos
    have hg₁₃_pos : 0 < g₁₃ := Nat.gcd_pos_of_pos_left u₃ hu₁_pos
    have hg₂₃_pos : 0 < g₂₃ := Nat.gcd_pos_of_pos_left u₃ hu₂_pos
    have h3g₁₂ : 3 * g₁₂ ≤ M := three_mul_le_of_two_ne_gt_half hg₁₂_pos hu12 hu₁_M hu₂_M
      hu₁_half hu₂_half (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
    have h3g₁₃ : 3 * g₁₃ ≤ M := three_mul_le_of_two_ne_gt_half hg₁₃_pos hu13 hu₁_M hu₃_M
      hu₁_half hu₃_half (Nat.gcd_dvd_left u₁ u₃) (Nat.gcd_dvd_right u₁ u₃)
    have h3g₂₃ : 3 * g₂₃ ≤ M := three_mul_le_of_two_ne_gt_half hg₂₃_pos hu23 hu₂_M hu₃_M
      hu₂_half hu₃_half (Nat.gcd_dvd_left u₂ u₃) (Nat.gcd_dvd_right u₂ u₃)
    have hpair_card : ({b₀, b'} : Finset ℕ).card + 1 ≤ 3 := by
      have h1 := Finset.card_insert_le b₀ {b'}
      simp only [Finset.card_singleton] at h1
      omega
    obtain ⟨w₁, hw₁_I, hw₁_not, hg12_w1⟩ := exists_avoiding_multiple_in_consecInterval x M g₁₂ {b₀, b'}
      hg₁₂_pos (le_trans (Nat.mul_le_mul_right g₁₂ hpair_card) h3g₁₂)
    obtain ⟨w₂, hw₂_I, hw₂_not, hg13_w2⟩ := exists_avoiding_multiple_in_consecInterval x M g₁₃ {b₀, b'}
      hg₁₃_pos (le_trans (Nat.mul_le_mul_right g₁₃ hpair_card) h3g₁₃)
    obtain ⟨w₃, hw₃_I, hw₃_not, hg23_w3⟩ := exists_avoiding_multiple_in_consecInterval x M g₂₃ {b₀, b'}
      hg₂₃_pos (le_trans (Nat.mul_le_mul_right g₂₃ hpair_card) h3g₂₃)
    have hw1_b0 : w₁ ≠ b₀ := fun h => hw₁_not (by simp [h])
    have hw1_bp : w₁ ≠ b' := fun h => hw₁_not (by simp [h])
    have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
    have hw2_bp : w₂ ≠ b' := fun h => hw₂_not (by simp [h])
    have hw3_b0 : w₃ ≠ b₀ := fun h => hw₃_not (by simp [h])
    have hw3_bp : w₃ ≠ b' := fun h => hw₃_not (by simp [h])
    have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
    have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
    have hbp0 : b' ≠ 0 := (pos_of_mem_consecInterval hb'_I).ne'
    have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
        s₀.factorization p + u₁.factorization p + u₂.factorization p + u₃.factorization p := by
      intro p
      rw [hA_eq, Finset.sum_insert (by simp [hs0u1, hs0u2, hs0u3]),
          Finset.sum_insert (by simp [hu12, hu13]), Finset.sum_insert (by simp [hu23]),
          Finset.sum_singleton]
      ring
    have hb₀_1 : ∀ p : ℕ, u₁.factorization p ≤ b₀.factorization p := fun p =>
      fac_le_of_dvd hb₀0 (hdiv_b0 u₁ hu₁_A)
    have hb₀_2 : ∀ p : ℕ, u₂.factorization p ≤ b₀.factorization p := fun p =>
      fac_le_of_dvd hb₀0 (hdiv_b0 u₂ hu₂_A)
    have hb₀_3 : ∀ p : ℕ, u₃.factorization p ≤ b₀.factorization p := fun p =>
      fac_le_of_dvd hb₀0 (hdiv_b0 u₃ hu₃_A)
    have hbp_s0 : ∀ p : ℕ, s₀.factorization p ≤ b'.factorization p := fun p =>
      fac_le_of_dvd hbp0 hs₀_b'
    by_cases hall : w₁ = w₂ ∧ w₂ = w₃
    · rcases hall with ⟨rfl, rfl⟩
      let D := Nat.gcd g₁₂ u₃
      have hD_pos : 0 < D := Nat.gcd_pos_of_pos_left u₃ hg₁₂_pos
      have h5D : 5 * D ≤ M := five_mul_le_of_three_distinct_gt_half hD_pos hu12 hu13 hu23
        hu₁_M hu₂_M hu₃_M hu₁_half hu₂_half hu₃_half
        (dvd_trans (Nat.gcd_dvd_left g₁₂ u₃) (Nat.gcd_dvd_left u₁ u₂))
        (dvd_trans (Nat.gcd_dvd_left g₁₂ u₃) (Nat.gcd_dvd_right u₁ u₂))
        (Nat.gcd_dvd_right g₁₂ u₃)
      have h3_card : ({b₀, b', w₁} : Finset ℕ).card + 1 ≤ 4 := by
        have h1 := Finset.card_insert_le b₀ {b', w₁}
        have h2 := Finset.card_insert_le b' {w₁}
        simp only [Finset.card_singleton] at h2
        omega
      obtain ⟨w', hw'_I, hw'_not, hD_w'⟩ := exists_avoiding_multiple_in_consecInterval x M D {b₀, b', w₁}
        hD_pos (le_trans (le_trans (Nat.mul_le_mul_right D h3_card) (by omega : 4 * D ≤ 5 * D)) h5D)
      have hw'_b0 : w' ≠ b₀ := fun h => hw'_not (by simp [h])
      have hw'_bp : w' ≠ b' := fun h => hw'_not (by simp [h])
      have hw'_w1 : w' ≠ w₁ := fun h => hw'_not (by simp [h])
      let B : Finset ℕ := {b₀, b', w₁, w'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hBcard : B.card ≤ 5 := le_trans (card_finset_le_four b₀ b' w₁ w') (by omega)
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
      refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
      intro p _hp
      rw [hsumA_eq p, Finset.sum_insert (by simp [hb'_b0.symm, hw1_b0.symm, hw'_b0.symm]),
          Finset.sum_insert (by simp [hw1_bp.symm, hw'_bp.symm]),
          Finset.sum_insert (by simp [hw'_w1.symm]), Finset.sum_singleton]
      have hw1_12 := fac_le_of_dvd hw10 hg12_w1 (p := p)
      have hw1_13 := fac_le_of_dvd hw10 hg13_w2 (p := p)
      have hw1_23 := fac_le_of_dvd hw10 hg23_w3 (p := p)
      have hw'_D := fac_le_of_dvd hw'0 hD_w' (p := p)
      rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw1_12
      rw [fac_gcd_eq_min hu₁_pos.ne' hu₃_pos.ne'] at hw1_13
      rw [fac_gcd_eq_min hu₂_pos.ne' hu₃_pos.ne'] at hw1_23
      rw [fac_gcd_eq_min hg₁₂_pos.ne' hu₃_pos.ne', fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw'_D
      have := hb₀_1 p; have := hb₀_2 p; have := hb₀_3 p; have := hbp_s0 p
      rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;>
      rcases le_total (u₂.factorization p) (u₃.factorization p) with h23_le | h32_le <;>
      rcases le_total (u₁.factorization p) (u₃.factorization p) with h13_le | h31_le <;> omega
    · let B : Finset ℕ := {b₀, b', w₁, w₂, w₃}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hBcard : B.card ≤ 5 := card_finset_le_five b₀ b' w₁ w₂ w₃
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
      refine ⟨B, hBI, hBcard, isCover_of_prime_factorization hA0 hB0 ?_⟩
      intro p _hp
      rw [hsumA_eq p]
      have hw1_12 := fac_le_of_dvd hw10 hg12_w1 (p := p)
      have hw2_13 := fac_le_of_dvd hw20 hg13_w2 (p := p)
      have hw3_23 := fac_le_of_dvd hw30 hg23_w3 (p := p)
      rw [fac_gcd_eq_min hu₁_pos.ne' hu₂_pos.ne'] at hw1_12
      rw [fac_gcd_eq_min hu₁_pos.ne' hu₃_pos.ne'] at hw2_13
      rw [fac_gcd_eq_min hu₂_pos.ne' hu₃_pos.ne'] at hw3_23
      have := hb₀_1 p; have := hb₀_2 p; have := hb₀_3 p; have := hbp_s0 p
      by_cases hw12 : w₁ = w₂
      · have hw23 : w₂ ≠ w₃ := fun h => hall ⟨hw12, h⟩
        have hw13 : w₁ ≠ w₃ := by rw [hw12]; exact hw23
        have hsub4 : ({b₀, b', w₁, w₃} : Finset ℕ) ⊆ B := by
          intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
        have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
        rw [Finset.sum_insert (by simp [hb'_b0.symm, hw1_b0.symm, hw3_b0.symm]),
            Finset.sum_insert (by simp [hw1_bp.symm, hw3_bp.symm]),
            Finset.sum_insert (by simp [hw13]), Finset.sum_singleton] at hleB
        rw [← hw12] at hw2_13
        rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;>
        rcases le_total (u₂.factorization p) (u₃.factorization p) with h23_le | h32_le <;>
        rcases le_total (u₁.factorization p) (u₃.factorization p) with h13_le | h31_le <;> omega
      · by_cases hw13 : w₁ = w₃
        · have hsub4 : ({b₀, b', w₁, w₂} : Finset ℕ) ⊆ B := by
            intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
          have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
          rw [Finset.sum_insert (by simp [hb'_b0.symm, hw1_b0.symm, hw2_b0.symm]),
              Finset.sum_insert (by simp [hw1_bp.symm, hw2_bp.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
          rw [← hw13] at hw3_23
          rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;>
          rcases le_total (u₂.factorization p) (u₃.factorization p) with h23_le | h32_le <;>
          rcases le_total (u₁.factorization p) (u₃.factorization p) with h13_le | h31_le <;> omega
        · by_cases hw23 : w₂ = w₃
          · have hsub4 : ({b₀, b', w₁, w₂} : Finset ℕ) ⊆ B := by
              intro b hb; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl | rfl <;> simp [B]
            have hleB := Finset.sum_le_sum_of_subset hsub4 (f := fun b => b.factorization p)
            rw [Finset.sum_insert (by simp [hb'_b0.symm, hw1_b0.symm, hw2_b0.symm]),
                Finset.sum_insert (by simp [hw1_bp.symm, hw2_bp.symm]),
                Finset.sum_insert (by simp [hw12]), Finset.sum_singleton] at hleB
            rw [← hw23] at hw3_23
            rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;>
            rcases le_total (u₂.factorization p) (u₃.factorization p) with h23_le | h32_le <;>
            rcases le_total (u₁.factorization p) (u₃.factorization p) with h13_le | h31_le <;> omega
          · have hleB : b₀.factorization p + (b'.factorization p + (w₁.factorization p +
                (w₂.factorization p + w₃.factorization p))) ≤ ∑ b ∈ B, b.factorization p := by
              calc b₀.factorization p + (b'.factorization p + (w₁.factorization p +
                      (w₂.factorization p + w₃.factorization p)))
                  = ∑ b ∈ ({b₀, b', w₁, w₂, w₃} : Finset ℕ), b.factorization p := by
                    rw [Finset.sum_insert (by simp [hb'_b0.symm, hw1_b0.symm, hw2_b0.symm, hw3_b0.symm]),
                        Finset.sum_insert (by simp [hw1_bp.symm, hw2_bp.symm, hw3_bp.symm]),
                        Finset.sum_insert (by simp [hw12, hw13]),
                        Finset.sum_insert (by simp [hw23]), Finset.sum_singleton]
                _ ≤ ∑ b ∈ B, b.factorization p := le_rfl
            rcases le_total (u₁.factorization p) (u₂.factorization p) with h12_le | h21_le <;>
            rcases le_total (u₂.factorization p) (u₃.factorization p) with h23_le | h32_le <;>
            rcases le_total (u₁.factorization p) (u₃.factorization p) with h13_le | h31_le <;> omega

theorem erdos708_upper_four : SatisfiesBound 4 5 := by
  suffices hmain : ∀ M : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty), IsValidSet A 4 →
      A.max' hA = M → ∀ x : ℕ, ∃ B ⊆ consecInterval x M, B.card ≤ 5 ∧ IsCover A B by
    intro A hA hvalid x
    exact hmain (A.max' hA) A hA hvalid rfl x
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro A hA hvalid hM x
    rcases hvalid with ⟨hA_card, hA_ge2⟩
    have hA_pos : ∀ a ∈ A, 0 < a := fun a ha => by have := hA_ge2 a ha; omega
    have hA_le : ∀ a ∈ A, a ≤ M := fun a ha => hM ▸ Finset.le_max' A a ha
    have hM_ge2 : 2 ≤ M := by
      have hmem := Finset.max'_mem A hA
      rw [hM] at hmem
      exact hA_ge2 M hmem
    have hsup_eq : A.sup id = M := by rw [sup_id_eq_max'4 hA, hM]
    let g := A.gcd id
    have hg_pos : 0 < g := by
      by_contra h0
      have hg0 : g = 0 := by omega
      obtain ⟨a₀, ha₀⟩ := hA
      have ha₀_dvd := Finset.gcd_dvd (f := id) ha₀
      dsimp [g] at hg0
      rw [hg0, id_eq] at ha₀_dvd
      have := hA_pos a₀ ha₀
      have := Nat.eq_zero_of_zero_dvd ha₀_dvd
      omega
    have hg_dvd : ∀ a ∈ A, g ∣ a := fun a ha => Finset.gcd_dvd (f := id) ha
    by_cases hg1 : 1 < g
    · let C := A.image (· / g)
      have hinj_div : Set.InjOn (· / g) A := by
        intro a ha b hb hab
        dsimp only at hab
        calc a = g * (a / g) := (Nat.mul_div_cancel' (hg_dvd a ha)).symm
          _ = g * (b / g) := by rw [hab]
          _ = b := Nat.mul_div_cancel' (hg_dvd b hb)
      have hC_card : C.card = 4 := by rw [Finset.card_image_of_injOn hinj_div, hA_card]
      have hC_pos : ∀ c ∈ C, 1 ≤ c := by
        intro c hc
        obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hc
        have ha0 := hA_pos a haA
        have hg_le_a := Nat.le_of_dvd ha0 (hg_dvd a haA)
        exact (Nat.le_div_iff_mul_le hg_pos).mpr (by simpa using hg_le_a)
      have hC_le : ∀ c ∈ C, c ≤ M / g := by
        intro c hc
        obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hc
        exact Nat.div_le_div_right (hA_le a haA)
      apply erdos708_gcd_reduction hA hA_pos hsup_eq.symm hg_pos hg_dvd (by omega)
      by_cases h1C : 1 ∈ C
      · let C' := C.erase 1
        have hC'_card : C'.card = 3 := by rw [Finset.card_erase_of_mem h1C, hC_card]
        have hC'_ne : C'.Nonempty := Finset.card_pos.mp (by omega)
        have hC'_valid : IsValidSet C' 3 := by
          refine ⟨hC'_card, ?_⟩
          intro c hc
          have hmem := Finset.mem_erase.mp hc
          have hc1 := hC_pos c hmem.2
          omega
        have hC'_max_le : C'.max' hC'_ne ≤ M / g := by
          apply Finset.max'_le
          intro c hc
          exact hC_le c (Finset.mem_erase.mp hc).2
        obtain ⟨B', hB'I, hB'card, hB'cov⟩ := erdos708_upper_three C' hC'_ne hC'_valid (x / g)
        refine ⟨B', Finset.Subset.trans hB'I ?_, by omega, ?_⟩
        · intro b hb
          simp only [consecInterval, Finset.mem_Icc] at hb ⊢
          exact ⟨hb.1, by omega⟩
        · rw [IsCover] at hB'cov ⊢
          have hC_eq : C = insert 1 C' := (Finset.insert_erase h1C).symm
          have h1_not : (1 : ℕ) ∉ C' := Finset.notMem_erase 1 C
          change ∏ a ∈ C, a ∣ ∏ b ∈ B', b
          rw [hC_eq, Finset.prod_insert h1_not, one_mul]
          exact hB'cov
      · have hC_ne : C.Nonempty := Finset.card_pos.mp (by omega)
        have hC_valid : IsValidSet C 4 := by
          refine ⟨hC_card, ?_⟩
          intro c hc
          have hc1 := hC_pos c hc
          have hne1 : c ≠ 1 := fun h => h1C (h ▸ hc)
          omega
        have hC_max_le : C.max' hC_ne ≤ M / g := by
          apply Finset.max'_le
          exact hC_le
        have hMg_lt : M / g < M := Nat.div_lt_self (by omega) hg1
        obtain ⟨B', hB'I, hB'card, hB'cov⟩ :=
          ih (C.max' hC_ne) (lt_of_le_of_lt hC_max_le hMg_lt) C hC_ne hC_valid rfl (x / g)
        refine ⟨B', Finset.Subset.trans hB'I ?_, hB'card, hB'cov⟩
        intro b hb
        simp only [consecInterval, Finset.mem_Icc] at hb ⊢
        exact ⟨hb.1, by omega⟩
    · have hg_eq1 : g = 1 := by omega
      by_cases hM5 : M ≤ 5
      · rw [← hM]
        exact erdos708_upper_of_max_le hA hA_pos (by omega) x
      · have hM6 : 6 ≤ M := by omega
        obtain ⟨S, f, hSA, hS_ge1, hS_le, hf_mem, hf_dvd, hf_inj, hmax⟩ :=
          exists_max_matching_in_consecInterval hA hA_pos hA_le
        have hS_le4 : S.card ≤ 4 := by omega
        by_cases hSc1 : S.card = 1
        · exact erdos708_upper_four_of_matching_one hA_card hA_pos hA_le hg_eq1 hSA hSc1
            f hf_mem hf_dvd hmax
        · by_cases hSc2 : S.card = 2
          · exact erdos708_upper_four_of_matching_two hA_card hA_pos hA_le hg_eq1 hM6 hSA hSc2
              f hf_mem hf_dvd hf_inj hmax
          · by_cases hSc3 : S.card = 3
            · obtain ⟨B, hBI, hBcard, hBcov⟩ := erdos708_upper_n_of_matching_pred (by omega)
                hA_card hA_pos hA_le hSA hSc3 f hf_mem hf_dvd hf_inj
              exact ⟨B, hBI, by omega, hBcov⟩
            · have hSc4 : S.card = 4 := by omega
              have hS_eq_A : S = A := Finset.eq_of_subset_of_card_le hSA (by omega)
              refine ⟨S.image f, ?_, ?_, ?_⟩
              · intro b hb
                obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hb
                exact hf_mem a haS
              · exact le_trans Finset.card_image_le (by omega)
              · rw [IsCover, ← hS_eq_A, Finset.prod_image (fun a₁ ha₁ a₂ ha₂ h => hf_inj ha₁ ha₂ h)]
                exact Finset.prod_dvd_prod_of_dvd id f (fun a ha => hf_dvd a ha)

theorem erdos708_exact_four : SatisfiesBound 4 5 ∧ ¬ SatisfiesBound 4 4 :=
  ⟨erdos708_upper_four, erdos708_lower_four⟩

#print axioms erdos708_upper_four
#print axioms erdos708_exact_four

end Erdos708