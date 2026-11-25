import Erdos708.G5R2

/-!
# PPL 176 (Erdős Problem #708) — Complete `r = 1` / `C5Core` Closure (`g(5) ≤ 6`)

This module proves `erdos708_upper_five_of_matching_one`: under `A.card = 5`, `A ⊆ [1, M]`,
`A.gcd id = 1`, `7 ≤ M`, and maximum matching size `1` into `consecInterval x M`,
`A` admits an unconditional `≤ 6`-slot cover in `consecInterval x M`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Core Definitions & Cover Rules (`Rule1`, `Rule2`, `Rule2b`) -/

private lemma finset_lcm_pos_core {T : Finset ℕ} (hT : ∀ a ∈ T, 0 < a) : 0 < T.lcm id := by
  refine Nat.pos_of_ne_zero ?_
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s _ ih =>
    rw [Finset.lcm_insert]
    simp only [id_eq]
    exact Nat.lcm_ne_zero (hT a (Finset.mem_insert_self a s)).ne'
      (ih fun b hb => hT b (Finset.mem_insert_of_mem hb))

def PairConst (T : Finset ℕ) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.lcm a b = T.lcm id

def No4Chain (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A,
    a₁ ≠ a₂ → a₁ ≠ a₃ → a₁ ≠ a₄ → a₂ ≠ a₃ → a₂ ≠ a₄ → a₃ ≠ a₄ →
    ¬ (a₃ ∣ Nat.lcm a₁ a₂) → a₄ ∣ Nat.lcm (Nat.lcm a₁ a₂) a₃

def NoType1b (A : Finset ℕ) : Prop :=
  ∀ u ∈ A, ¬ PairConst (A.erase u)

def C5Core (A : Finset ℕ) (M : ℕ) : Prop :=
  A.card = 5 ∧ (∀ a ∈ A, 0 < a) ∧ (∀ a ∈ A, a ≤ M) ∧
    (∀ a ∈ A, M < 2 * a) ∧ A.gcd id = 1 ∧ No4Chain A ∧ NoType1b A

def HasRule1 (A : Finset ℕ) (M : ℕ) : Prop :=
  ∃ u₁ u₂ u₃ u₄ u₅ p d₁ d₂ : ℕ,
    A = {u₁, u₂, u₃, u₄, u₅} ∧
    u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₁ ≠ u₅ ∧
    u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₂ ≠ u₅ ∧
    u₃ ≠ u₄ ∧ u₃ ≠ u₅ ∧ u₄ ≠ u₅ ∧
    ¬ (u₅ ∣ Nat.lcm u₃ u₄) ∧
    p.Prime ∧ 1 ≤ d₁ ∧ d₁ ≤ u₁.factorization p ∧ 1 ≤ d₂ ∧ d₂ ≤ u₂.factorization p ∧
    p ^ (d₁ + d₂) ≤ M ∧ 3 * p ^ ((A.lcm id).factorization p) ≤ M ∧
    5 * (u₁ / p ^ d₁) ≤ M ∧ 6 * (u₂ / p ^ d₂) ≤ M

def HasRule2 (A : Finset ℕ) (M : ℕ) : Prop :=
  ∃ u₁ u₂ u₃ u₄ u₅ D₁ D₂ : ℕ,
    A = {u₁, u₂, u₃, u₄, u₅} ∧
    u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₁ ≠ u₅ ∧
    u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₂ ≠ u₅ ∧
    u₃ ≠ u₄ ∧ u₃ ≠ u₅ ∧ u₄ ≠ u₅ ∧
    ¬ (u₅ ∣ Nat.lcm u₃ u₄) ∧
    0 < D₁ ∧ D₁ ∣ u₁ ∧ 0 < D₂ ∧ D₂ ∣ u₂ ∧
    4 * (D₁ * D₂) ≤ M ∧ 5 * (u₁ / D₁) ≤ M ∧ 6 * (u₂ / D₂) ≤ M

def HasRule2b (A : Finset ℕ) (M : ℕ) : Prop :=
  ∃ u₁ u₂ u₃ u₄ u₅ D₁ D₂ : ℕ,
    A = {u₁, u₂, u₃, u₄, u₅} ∧
    u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₁ ≠ u₄ ∧ u₁ ≠ u₅ ∧
    u₂ ≠ u₃ ∧ u₂ ≠ u₄ ∧ u₂ ≠ u₅ ∧
    u₃ ≠ u₄ ∧ u₃ ≠ u₅ ∧ u₄ ≠ u₅ ∧
    ¬ (u₅ ∣ Nat.lcm u₃ u₄) ∧
    0 < D₁ ∧ D₁ ∣ u₁ ∧ 0 < D₂ ∧ D₂ ∣ u₂ ∧
    3 * (D₁ * D₂) ≤ M ∧ 4 * Nat.gcd u₃ u₄ ≤ M ∧
    5 * (u₁ / D₁) ≤ M ∧ 6 * (u₂ / D₂) ≤ M

private lemma cover_three_of_nonspan {x M b₀ u₃ u₄ u₅ : ℕ}
    (hu3p : 0 < u₃) (hu4p : 0 < u₄) (hu5p : 0 < u₅)
    (hu3M : u₃ ≤ M) (hu4M : u₄ ≤ M) (hu5M : u₅ ≤ M)
    (hu3h : M < 2 * u₃) (hu4h : M < 2 * u₄) (hu34 : u₃ ≠ u₄)
    (hb₀_I : b₀ ∈ consecInterval x M) (h3b : u₃ ∣ b₀) (h4b : u₄ ∣ b₀) (h5b : u₅ ∣ b₀)
    (hns : ¬ (u₅ ∣ Nat.lcm u₃ u₄)) :
    ∃ w₁ w₂ : ℕ, w₁ ∈ consecInterval x M ∧ w₂ ∈ consecInterval x M ∧
      w₂ ≠ b₀ ∧ w₁ ≠ b₀ ∧ w₁ ≠ w₂ ∧
      Nat.gcd u₃ u₄ ∣ w₁ ∧ Nat.gcd (Nat.lcm u₃ u₄) u₅ ∣ w₂ ∧
      ∀ q : ℕ, u₃.factorization q + u₄.factorization q + u₅.factorization q ≤
        b₀.factorization q + w₁.factorization q + w₂.factorization q := by
  let L₃₄ := Nat.lcm u₃ u₄
  let h := Nat.gcd L₃₄ u₅
  let g := Nat.gcd u₃ u₄
  have hL_pos : 0 < L₃₄ := Nat.lcm_pos hu3p hu4p
  have hh_pos : 0 < h := Nat.gcd_pos_of_pos_left u₅ hL_pos
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left u₄ hu3p
  have h2h : 2 * h ≤ M := gcd_not_dvd_mul_le hL_pos hu5p hu5M hns
  have h3g : 3 * g ≤ M := three_mul_le_of_two_gt_half_5 hg_pos hu34 hu3M hu4M hu3h hu4h
    (Nat.gcd_dvd_left u₃ u₄) (Nat.gcd_dvd_right u₃ u₄)
  obtain ⟨w₂, hw₂_I, hw₂_not, hh_w₂⟩ := exists_avoiding_multiple_5 x M h {b₀}
    hh_pos (le_trans (Nat.mul_le_mul_right h (by simp : ({b₀} : Finset ℕ).card + 1 ≤ 2)) h2h)
  obtain ⟨w₁, hw₁_I, hw₁_not, hg_w₁⟩ := exists_avoiding_multiple_5 x M g {b₀, w₂}
    hg_pos (le_trans (Nat.mul_le_mul_right g (by
      have := Finset.card_insert_le b₀ {w₂}; simp at this ⊢; omega)) h3g)
  have hw2_b0 : w₂ ≠ b₀ := by simpa using hw₂_not
  have hw1_b0 : w₁ ≠ b₀ := fun h => hw₁_not (by simp [h])
  have hw1_w2 : w₁ ≠ w₂ := fun h => hw₁_not (by simp [h])
  refine ⟨w₁, w₂, hw₁_I, hw₂_I, hw2_b0, hw1_b0, hw1_w2, hg_w₁, hh_w₂, ?_⟩
  intro q
  have hb00 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
  have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hb3 := fac_le_of_dvd_5 hb00 h3b (p := q)
  have hb4 := fac_le_of_dvd_5 hb00 h4b (p := q)
  have hb5 := fac_le_of_dvd_5 hb00 h5b (p := q)
  have hw1g := fac_le_of_dvd_5 hw10 hg_w₁ (p := q)
  have hw2h := fac_le_of_dvd_5 hw20 hh_w₂ (p := q)
  rw [fac_gcd_eq_min_5 hu3p.ne' hu4p.ne'] at hw1g
  rw [fac_gcd_eq_min_5 hL_pos.ne' hu5p.ne', fac_lcm_eq_max_5 hu3p.ne' hu4p.ne'] at hw2h
  have hineq := r2_nonspan3_val_ineq (u₃.factorization q) (u₄.factorization q) (u₅.factorization q) 0
  omega

private lemma rule1_min_zero_sum_eq (a b c : ℕ) (hmin : min (min a b) c = 0) :
    a + b + c = max (max a b) c + (min a b + min (max a b) c) := by
  simp only [min_def, max_def] at hmin ⊢
  split_ifs at hmin ⊢ <;> omega

private lemma rule1_min2_le_max3 (a b c : ℕ) (hmin : min (min a b) c = 0) :
    min a b + min (max a b) c ≤ max (max a b) c := by
  simp only [min_def, max_def] at hmin ⊢
  split_ifs at hmin ⊢ <;> omega

private lemma rule1_div_pow_fac {u p d q : ℕ} (hu : 0 < u) (hp : p.Prime)
    (hd : d ≤ u.factorization p) :
    (u / p ^ d).factorization q = if q = p then u.factorization p - d else u.factorization q := by
  have hpd_dvd : p ^ d ∣ u := (hp.pow_dvd_iff_le_factorization hu.ne').mpr hd
  have hpd_pos : 0 < p ^ d := pow_pos hp.pos d
  have hdiv_pos : 0 < u / p ^ d := Nat.div_pos (Nat.le_of_dvd hu hpd_dvd) hpd_pos
  have hmul : (u / p ^ d) * p ^ d = u := Nat.div_mul_cancel hpd_dvd
  have hfac := congrArg (fun n => n.factorization q) hmul
  rw [Nat.factorization_mul hdiv_pos.ne' hpd_pos.ne', Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hfac
  split_ifs with hqp
  · subst hqp; simp only [Nat.Prime.factorization_self hp, mul_one] at hfac; omega
  · have : p.factorization q = 0 := by
      rw [hp.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp)]
    rw [this, mul_zero, add_zero] at hfac
    exact hfac

private lemma cover_six_of_rule1 {A : Finset ℕ} {x M b₀ : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hA_half : ∀ a ∈ A, M < 2 * a)
    (hAgcd : A.gcd id = 1) (hb₀_I : b₀ ∈ consecInterval x M) (hb₀_dvd : ∀ a ∈ A, a ∣ b₀)
    (hr1 : HasRule1 A M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨u₁, u₂, u₃, u₄, u₅, p, d₁, d₂, hA_eq,
    h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
    hns, hp, hd1_ge1, hd1_le, hd2_ge1, hd2_le, hpp_M, h3pe_M, h5Y1, h6Y2⟩ := hr1
  have hu1A : u₁ ∈ A := by rw [hA_eq]; simp
  have hu2A : u₂ ∈ A := by rw [hA_eq]; simp
  have hu3A : u₃ ∈ A := by rw [hA_eq]; simp
  have hu4A : u₄ ∈ A := by rw [hA_eq]; simp
  have hu5A : u₅ ∈ A := by rw [hA_eq]; simp
  have hu1p := hA_pos u₁ hu1A; have hu2p := hA_pos u₂ hu2A
  have hu3p := hA_pos u₃ hu3A; have hu4p := hA_pos u₄ hu4A; have hu5p := hA_pos u₅ hu5A
  obtain ⟨w₁, w₂, hw₁_I, hw₂_I, hw2_b0, hw1_b0, hw1_w2, hg_w1, hh_w2, hcov3⟩ :=
    cover_three_of_nonspan hu3p hu4p hu5p (hA_le u₃ hu3A) (hA_le u₄ hu4A) (hA_le u₅ hu5A)
      (hA_half u₃ hu3A) (hA_half u₄ hu4A) h34 hb₀_I
      (hb₀_dvd u₃ hu3A) (hb₀_dvd u₄ hu4A) (hb₀_dvd u₅ hu5A) hns
  let Y₁ := u₁ / p ^ d₁
  let Y₂ := u₂ / p ^ d₂
  have hY1_pos : 0 < Y₁ := Nat.div_pos (Nat.le_of_dvd hu1p ((hp.pow_dvd_iff_le_factorization hu1p.ne').mpr hd1_le)) (pow_pos hp.pos d₁)
  have hY2_pos : 0 < Y₂ := Nat.div_pos (Nat.le_of_dvd hu2p ((hp.pow_dvd_iff_le_factorization hu2p.ne').mpr hd2_le)) (pow_pos hp.pos d₂)
  let B₃ : Finset ℕ := {b₀, w₁, w₂}
  have hB3_I : B₃ ⊆ consecInterval x M := fun b hb => by
    simp only [B₃, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  have hB3_card : B₃.card = 3 := by
    dsimp [B₃]
    rw [Finset.card_insert_of_notMem (by simp [hw1_b0.symm, hw2_b0.symm]),
        Finset.card_insert_of_notMem (by simp [hw1_w2]), Finset.card_singleton]
  have hsumA : ∀ q : ℕ, ∑ a ∈ A, a.factorization q =
      u₁.factorization q + u₂.factorization q + u₃.factorization q + u₄.factorization q + u₅.factorization q := by
    intro q
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14, h15]),
        Finset.sum_insert (by simp [h23, h24, h25]),
        Finset.sum_insert (by simp [h34, h35]),
        Finset.sum_insert (by simp [h45]), Finset.sum_singleton]
    ring
  have hsumB3 : ∀ q : ℕ, ∑ b ∈ B₃, b.factorization q =
      b₀.factorization q + w₁.factorization q + w₂.factorization q := by
    intro q; dsimp [B₃]
    rw [Finset.sum_insert (by simp [hw1_b0.symm, hw2_b0.symm]),
        Finset.sum_insert (by simp [hw1_w2]), Finset.sum_singleton]
    ring
  -- Helper: finish from any `B₄ ⊆ consecInterval x M` with `B₄.card ≤ 4` covering `u₃, u₄, u₅` and `p^(d₁+d₂)`:
  have finish_with_B4 : ∀ B₄ : Finset ℕ, B₄ ⊆ consecInterval x M → B₄.card ≤ 4 →
      u₃.factorization p + u₄.factorization p + u₅.factorization p + d₁ + d₂ ≤ ∑ b ∈ B₄, b.factorization p →
      (∀ q : ℕ, q ≠ p → u₃.factorization q + u₄.factorization q + u₅.factorization q ≤ ∑ b ∈ B₄, b.factorization q) →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro B₄ hB4_I hB4_c hB4_p hB4_np
    obtain ⟨w₅, hw₅_I, hw₅_not, hY1_w⟩ := exists_avoiding_multiple_5 x M Y₁ B₄
      hY1_pos (le_trans (Nat.mul_le_mul_right Y₁ (by omega : B₄.card + 1 ≤ 5)) h5Y1)
    obtain ⟨w₆, hw₆_I, hw₆_not, hY2_w⟩ := exists_avoiding_multiple_5 x M Y₂ (insert w₅ B₄)
      hY2_pos (le_trans (Nat.mul_le_mul_right Y₂ (by
        have := Finset.card_insert_le w₅ B₄; omega)) h6Y2)
    let B : Finset ℕ := insert w₆ (insert w₅ B₄)
    have hBI : B ⊆ consecInterval x M := Finset.insert_subset hw₆_I (Finset.insert_subset hw₅_I hB4_I)
    have hBc : B.card ≤ 6 := by
      dsimp [B]
      have h1 := Finset.card_insert_le w₆ (insert w₅ B₄)
      have h2 := Finset.card_insert_le w₅ B₄
      omega
    have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, hBc, isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
    intro q hq
    have hw₆_ne : w₆ ∉ insert w₅ B₄ := hw₆_not
    have hsumB : ∑ b ∈ B, b.factorization q = w₆.factorization q + w₅.factorization q + ∑ b ∈ B₄, b.factorization q := by
      dsimp [B]
      rw [Finset.sum_insert hw₆_ne, Finset.sum_insert hw₅_not]
      ring
    rw [hsumA q, hsumB]
    have hw5_fac := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₅_I).ne' hY1_w (p := q)
    have hw6_fac := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₆_I).ne' hY2_w (p := q)
    rw [rule1_div_pow_fac hu1p hp hd1_le] at hw5_fac
    rw [rule1_div_pow_fac hu2p hp hd2_le] at hw6_fac
    by_cases hqp : q = p
    · subst hqp
      simp only [ite_true] at hw5_fac hw6_fac
      omega
    · simp only [if_neg hqp] at hw5_fac hw6_fac
      have hnp := hB4_np q hqp
      omega
  let req := u₃.factorization p + u₄.factorization p + u₅.factorization p + d₁ + d₂
  let have_p := b₀.factorization p + w₁.factorization p + w₂.factorization p
  by_cases hdef0 : req ≤ have_p
  · exact finish_with_B4 B₃ hB3_I (by omega) (by rw [hsumB3 p]; exact hdef0)
      (fun q _ => by rw [hsumB3 q]; exact hcov3 q)
  · let def_p := req - have_p
    have hdef_pos : 1 ≤ def_p := by dsimp [def_p]; omega
    by_cases hex4 : ∃ w₄ ∈ consecInterval x M, w₄ ∉ B₃ ∧ p ^ def_p ∣ w₄
    · obtain ⟨w₄, hw₄_I, hw₄_not, hpd_w4⟩ := hex4
      let B₄ : Finset ℕ := insert w₄ B₃
      have hB4_I : B₄ ⊆ consecInterval x M := Finset.insert_subset hw₄_I hB3_I
      have hB4_c : B₄.card ≤ 4 := le_trans (Finset.card_insert_le w₄ B₃) (by omega)
      have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
      have hw4_p : def_p ≤ w₄.factorization p := (hp.pow_dvd_iff_le_factorization hw40).mp hpd_w4
      refine finish_with_B4 B₄ hB4_I hB4_c ?_ ?_
      · rw [Finset.sum_insert hw₄_not, hsumB3 p]
        change req ≤ w₄.factorization p + have_p
        dsimp [def_p] at hw4_p; omega
      · intro q _
        rw [Finset.sum_insert hw₄_not, hsumB3 q]
        exact le_trans (hcov3 q) (Nat.le_add_left _ _)
    · -- `(consecInterval x M).filter (fun b => p ^ def_p ∣ b) ⊆ B₃` ⇒ contradiction!
      exfalso
      push Not at hex4
      have hsub : (consecInterval x M).filter (fun b => p ^ def_p ∣ b) ⊆ B₃ := by
        intro b hb; rw [Finset.mem_filter] at hb
        by_contra hnot; exact hex4 b hb.1 hnot hb.2
      have hmin_zero : min (min (u₃.factorization p) (u₄.factorization p)) (u₅.factorization p) = 0 := by
        by_contra hne0
        have h3p : 1 ≤ u₃.factorization p := by omega
        have h4p : 1 ≤ u₄.factorization p := by omega
        have h5p : 1 ≤ u₅.factorization p := by omega
        have h1p : 1 ≤ u₁.factorization p := by omega
        have h2p : 1 ≤ u₂.factorization p := by omega
        have hpd_A : p ∣ A.gcd id := Finset.dvd_gcd fun a ha => by
          have haA : a ∈ A := ha
          have ha0 : a ≠ 0 := (hA_pos a haA).ne'
          rw [hA_eq] at ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          refine (hp.dvd_iff_one_le_factorization ha0).mpr ?_
          rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption
        rw [hAgcd] at hpd_A
        exact hp.not_dvd_one hpd_A
      let m₁ := max (max (u₃.factorization p) (u₄.factorization p)) (u₅.factorization p)
      let m₂ := min (u₃.factorization p) (u₄.factorization p) +
        min (max (u₃.factorization p) (u₄.factorization p)) (u₅.factorization p)
      have hsum3_eq : u₃.factorization p + u₄.factorization p + u₅.factorization p = m₁ + m₂ :=
        rule1_min_zero_sum_eq _ _ _ hmin_zero
      have hm2_le_m1 : m₂ ≤ m₁ := rule1_min2_le_max3 _ _ _ hmin_zero
      have hL_pos : 0 < A.lcm id := finset_lcm_pos_core hA_pos
      have hep_ge1 : 1 ≤ (A.lcm id).factorization p := by
        have h1L := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hu1A) (p := p)
        simp only [id_eq] at h1L; omega
      have hm1_le_ep : m₁ ≤ (A.lcm id).factorization p := by
        have h3L := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hu3A) (p := p)
        have h4L := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hu4A) (p := p)
        have h5L := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hu5A) (p := p)
        simp only [id_eq] at h3L h4L h5L
        dsimp [m₁]; omega
      have heb0 : (A.lcm id).factorization p ≤ b₀.factorization p :=
        fac_le_of_dvd_5 (pos_of_mem_consecInterval hb₀_I).ne' (Finset.lcm_dvd hb₀_dvd) (p := p)
      have hm2_w12 : m₂ ≤ w₁.factorization p + w₂.factorization p := by
        have hw1g := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₁_I).ne' hg_w1 (p := p)
        have hw2h := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₂_I).ne' hh_w2 (p := p)
        rw [fac_gcd_eq_min_5 hu3p.ne' hu4p.ne'] at hw1g
        rw [fac_gcd_eq_min_5 (Nat.lcm_pos hu3p hu4p).ne' hu5p.ne', fac_lcm_eq_max_5 hu3p.ne' hu4p.ne'] at hw2h
        dsimp [m₂]; omega
      have hdef_le_d12 : def_p ≤ d₁ + d₂ := by
        have h3 := hcov3 p
        dsimp [def_p, req, have_p]
        omega
      obtain ⟨b_hi, hbhi_I, hpp_bhi⟩ := exists_multiple_in_consecInterval x (p ^ (d₁ + d₂)) M
        (pow_pos hp.pos _) hpp_M
      have hpd_bhi : p ^ def_p ∣ b_hi := dvd_trans (Nat.pow_dvd_pow p hdef_le_d12) hpp_bhi
      have hbhi_B3 : b_hi ∈ B₃ := hsub (Finset.mem_filter.mpr ⟨hbhi_I, hpd_bhi⟩)
      have hbhi_fac : d₁ + d₂ ≤ b_hi.factorization p :=
        (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hbhi_I).ne').mp hpp_bhi
      have hdef_le_ep : def_p ≤ (A.lcm id).factorization p := by
        simp only [B₃, Finset.mem_insert, Finset.mem_singleton] at hbhi_B3
        dsimp [def_p, req, have_p] at hsum3_eq ⊢
        rcases hbhi_B3 with rfl | rfl | rfl <;> omega
      rcases lt_or_eq_of_le hdef_le_ep with hlt_ep | heq_ep
      · have hpd_pos : 0 < p ^ def_p := pow_pos hp.pos _
        have hpow : p ^ (def_p + 1) ≤ p ^ (A.lcm id).factorization p := Nat.pow_le_pow_right hp.pos (by omega)
        have h4_le : 4 * p ^ def_p ≤ 2 * p ^ (A.lcm id).factorization p := by
          calc 4 * p ^ def_p = 2 * (2 * p ^ def_p) := by ring
            _ ≤ 2 * (p * p ^ def_p) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hp.two_le)
            _ = 2 * p ^ (def_p + 1) := by rw [pow_succ']
            _ ≤ 2 * p ^ (A.lcm id).factorization p := Nat.mul_le_mul_left 2 hpow
        have h4M : 4 * p ^ def_p ≤ M := by omega
        have hcard_ge4 : 4 ≤ ((Finset.Icc (x + 1) (x + M)).filter (fun b => p ^ def_p ∣ b)).card := by
          have h1 := card_multiples_Icc_ge x M (p ^ def_p) hpd_pos
          change M / p ^ def_p ≤ ((Finset.Icc (x + 1) (x + M)).filter (fun b => p ^ def_p ∣ b)).card at h1
          have h2 : 4 ≤ M / p ^ def_p := (Nat.le_div_iff_mul_le hpd_pos).mpr h4M
          omega
        have hsub' : (Finset.Icc (x + 1) (x + M)).filter (fun b => p ^ def_p ∣ b) ⊆ B₃ := hsub
        have := Finset.card_le_card hsub'
        omega
      · have hpe_pos : 0 < p ^ (A.lcm id).factorization p := pow_pos hp.pos _
        have hcard_ge3 : 3 ≤ ((Finset.Icc (x + 1) (x + M)).filter (fun b => p ^ (A.lcm id).factorization p ∣ b)).card := by
          have h1 := card_multiples_Icc_ge x M (p ^ (A.lcm id).factorization p) hpe_pos
          change M / p ^ (A.lcm id).factorization p ≤
            ((Finset.Icc (x + 1) (x + M)).filter (fun b => p ^ (A.lcm id).factorization p ∣ b)).card at h1
          have h2 : 3 ≤ M / p ^ (A.lcm id).factorization p := (Nat.le_div_iff_mul_le hpe_pos).mpr h3pe_M
          omega
        have heq_sub : (consecInterval x M).filter (fun b => p ^ (A.lcm id).factorization p ∣ b) = B₃ := by
          apply Finset.eq_of_subset_of_card_le
          · rw [← heq_ep]; exact hsub
          · rw [hB3_card]; exact hcard_ge3
        have hb0_ep : (A.lcm id).factorization p ≤ b₀.factorization p := heb0
        have hw1_ep : (A.lcm id).factorization p ≤ w₁.factorization p := by
          have hdvd : p ^ (A.lcm id).factorization p ∣ w₁ := (Finset.mem_filter.mp (heq_sub ▸ (by simp [B₃] : w₁ ∈ B₃))).2
          exact (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hw₁_I).ne').mp hdvd
        have hw2_ep : (A.lcm id).factorization p ≤ w₂.factorization p := by
          have hdvd : p ^ (A.lcm id).factorization p ∣ w₂ := (Finset.mem_filter.mp (heq_sub ▸ (by simp [B₃] : w₂ ∈ B₃))).2
          exact (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hw₂_I).ne').mp hdvd
        simp only [B₃, Finset.mem_insert, Finset.mem_singleton] at hbhi_B3
        dsimp [req, have_p] at hdef0
        rcases hbhi_B3 with rfl | rfl | rfl <;> omega

private lemma cover_six_of_rule2 {A : Finset ℕ} {x M b₀ : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hA_half : ∀ a ∈ A, M < 2 * a)
    (hb₀_I : b₀ ∈ consecInterval x M) (hb₀_dvd : ∀ a ∈ A, a ∣ b₀)
    (hr2 : HasRule2 A M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨u₁, u₂, u₃, u₄, u₅, D₁, D₂, hA_eq,
    h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
    hns, hD1_pos, hD1_u1, hD2_pos, hD2_u2, h4D, h5Y1, h6Y2⟩ := hr2
  have hu1A : u₁ ∈ A := by rw [hA_eq]; simp
  have hu2A : u₂ ∈ A := by rw [hA_eq]; simp
  have hu3A : u₃ ∈ A := by rw [hA_eq]; simp
  have hu4A : u₄ ∈ A := by rw [hA_eq]; simp
  have hu5A : u₅ ∈ A := by rw [hA_eq]; simp
  have hu1p := hA_pos u₁ hu1A; have hu2p := hA_pos u₂ hu2A
  have hu3p := hA_pos u₃ hu3A; have hu4p := hA_pos u₄ hu4A; have hu5p := hA_pos u₅ hu5A
  obtain ⟨w₁, w₂, hw₁_I, hw₂_I, hw2_b0, hw1_b0, hw1_w2, _, _, hcov3⟩ :=
    cover_three_of_nonspan hu3p hu4p hu5p (hA_le u₃ hu3A) (hA_le u₄ hu4A) (hA_le u₅ hu5A)
      (hA_half u₃ hu3A) (hA_half u₄ hu4A) h34 hb₀_I
      (hb₀_dvd u₃ hu3A) (hb₀_dvd u₄ hu4A) (hb₀_dvd u₅ hu5A) hns
  let Y₁ := u₁ / D₁
  let Y₂ := u₂ / D₂
  have hY1_pos : 0 < Y₁ := Nat.div_pos (Nat.le_of_dvd hu1p hD1_u1) hD1_pos
  have hY2_pos : 0 < Y₂ := Nat.div_pos (Nat.le_of_dvd hu2p hD2_u2) hD2_pos
  let B₃ : Finset ℕ := {b₀, w₁, w₂}
  have hB3_I : B₃ ⊆ consecInterval x M := fun b hb => by
    simp only [B₃, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> assumption
  have hB3_c : B₃.card = 3 := by
    dsimp [B₃]
    rw [Finset.card_insert_of_notMem (by simp [hw1_b0.symm, hw2_b0.symm]),
        Finset.card_insert_of_notMem (by simp [hw1_w2]), Finset.card_singleton]
  obtain ⟨w₄, hw₄_I, hw₄_not, hD_w4⟩ := exists_avoiding_multiple_5 x M (D₁ * D₂) B₃
    (mul_pos hD1_pos hD2_pos) (le_trans (Nat.mul_le_mul_right _ (by omega : B₃.card + 1 ≤ 4)) h4D)
  obtain ⟨w₅, hw₅_I, hw₅_not, hY1_w5⟩ := exists_avoiding_multiple_5 x M Y₁ (insert w₄ B₃)
    hY1_pos (le_trans (Nat.mul_le_mul_right _ (by have := Finset.card_insert_le w₄ B₃; omega)) h5Y1)
  obtain ⟨w₆, hw₆_I, hw₆_not, hY2_w6⟩ := exists_avoiding_multiple_5 x M Y₂ (insert w₅ (insert w₄ B₃))
    hY2_pos (le_trans (Nat.mul_le_mul_right _ (by
      have h1 := Finset.card_insert_le w₅ (insert w₄ B₃)
      have h2 := Finset.card_insert_le w₄ B₃; omega)) h6Y2)
  let B : Finset ℕ := insert w₆ (insert w₅ (insert w₄ B₃))
  have hBI : B ⊆ consecInterval x M :=
    Finset.insert_subset hw₆_I (Finset.insert_subset hw₅_I (Finset.insert_subset hw₄_I hB3_I))
  have hBc : B.card ≤ 6 := by
    dsimp [B]
    have h1 := Finset.card_insert_le w₆ (insert w₅ (insert w₄ B₃))
    have h2 := Finset.card_insert_le w₅ (insert w₄ B₃)
    have h3 := Finset.card_insert_le w₄ B₃
    have : B₃.card ≤ 3 := hB3_c.le
    omega
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  refine ⟨B, hBI, hBc, isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
  intro q _hq
  have hsumA : ∑ a ∈ A, a.factorization q =
      u₁.factorization q + u₂.factorization q + u₃.factorization q + u₄.factorization q + u₅.factorization q := by
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14, h15]),
        Finset.sum_insert (by simp [h23, h24, h25]),
        Finset.sum_insert (by simp [h34, h35]),
        Finset.sum_insert (by simp [h45]), Finset.sum_singleton]
    ring
  have hsumB3 : ∑ b ∈ B₃, b.factorization q =
      b₀.factorization q + w₁.factorization q + w₂.factorization q := by
    dsimp [B₃]
    rw [Finset.sum_insert (by simp [hw1_b0.symm, hw2_b0.symm]),
        Finset.sum_insert (by simp [hw1_w2]), Finset.sum_singleton]
    ring
  have hsumB : ∑ b ∈ B, b.factorization q =
      w₆.factorization q + w₅.factorization q + w₄.factorization q +
        (b₀.factorization q + w₁.factorization q + w₂.factorization q) := by
    dsimp [B]
    rw [Finset.sum_insert hw₆_not, Finset.sum_insert hw₅_not, Finset.sum_insert hw₄_not, hsumB3]
    ring
  rw [hsumA, hsumB]
  have hu1_sp : u₁.factorization q = Y₁.factorization q + D₁.factorization q := by
    have hmul : Y₁ * D₁ = u₁ := Nat.div_mul_cancel hD1_u1
    rw [← hmul, Nat.factorization_mul hY1_pos.ne' hD1_pos.ne', Finsupp.add_apply]
  have hu2_sp : u₂.factorization q = Y₂.factorization q + D₂.factorization q := by
    have hmul : Y₂ * D₂ = u₂ := Nat.div_mul_cancel hD2_u2
    rw [← hmul, Nat.factorization_mul hY2_pos.ne' hD2_pos.ne', Finsupp.add_apply]
  have hw4_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₄_I).ne' hD_w4 (p := q)
  rw [Nat.factorization_mul hD1_pos.ne' hD2_pos.ne', Finsupp.add_apply] at hw4_f
  have hw5_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₅_I).ne' hY1_w5 (p := q)
  have hw6_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₆_I).ne' hY2_w6 (p := q)
  have h3 := hcov3 q
  omega

private lemma cover_six_of_rule2b {A : Finset ℕ} {x M b₀ : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hb₀_I : b₀ ∈ consecInterval x M) (hb₀_dvd : ∀ a ∈ A, a ∣ b₀)
    (hr2b : HasRule2b A M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨u₁, u₂, u₃, u₄, u₅, D₁, D₂, hA_eq,
    h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
    hns, hD1_pos, hD1_u1, hD2_pos, hD2_u2, h3D, h4g, h5Y1, h6Y2⟩ := hr2b
  have hu1A : u₁ ∈ A := by rw [hA_eq]; simp
  have hu2A : u₂ ∈ A := by rw [hA_eq]; simp
  have hu3A : u₃ ∈ A := by rw [hA_eq]; simp
  have hu4A : u₄ ∈ A := by rw [hA_eq]; simp
  have hu5A : u₅ ∈ A := by rw [hA_eq]; simp
  have hu1p := hA_pos u₁ hu1A; have hu2p := hA_pos u₂ hu2A
  have hu3p := hA_pos u₃ hu3A; have hu4p := hA_pos u₄ hu4A; have hu5p := hA_pos u₅ hu5A
  let L₃₄ := Nat.lcm u₃ u₄
  let h := Nat.gcd L₃₄ u₅
  let g := Nat.gcd u₃ u₄
  have hL_pos : 0 < L₃₄ := Nat.lcm_pos hu3p hu4p
  have hh_pos : 0 < h := Nat.gcd_pos_of_pos_left u₅ hL_pos
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left u₄ hu3p
  have h2h : 2 * h ≤ M := gcd_not_dvd_mul_le hL_pos hu5p (hA_le u₅ hu5A) hns
  let Y₁ := u₁ / D₁
  let Y₂ := u₂ / D₂
  have hY1_pos : 0 < Y₁ := Nat.div_pos (Nat.le_of_dvd hu1p hD1_u1) hD1_pos
  have hY2_pos : 0 < Y₂ := Nat.div_pos (Nat.le_of_dvd hu2p hD2_u2) hD2_pos
  obtain ⟨w₂, hw₂_I, hw₂_not, hh_w2⟩ := exists_avoiding_multiple_5 x M h {b₀}
    hh_pos (le_trans (Nat.mul_le_mul_right h (by simp : ({b₀} : Finset ℕ).card + 1 ≤ 2)) h2h)
  let B₁ : Finset ℕ := insert w₂ {b₀}
  have hB1_c : B₁.card ≤ 2 := le_trans (Finset.card_insert_le w₂ ({b₀} : Finset ℕ)) (by simp)
  obtain ⟨w₄, hw₄_I, hw₄_not, hD_w4⟩ := exists_avoiding_multiple_5 x M (D₁ * D₂) B₁
    (mul_pos hD1_pos hD2_pos) (le_trans (Nat.mul_le_mul_right _ (by omega : B₁.card + 1 ≤ 3)) h3D)
  let B₂ : Finset ℕ := insert w₄ B₁
  have hB2_c : B₂.card ≤ 3 := le_trans (Finset.card_insert_le w₄ B₁) (by omega)
  obtain ⟨w₁, hw₁_I, hw₁_not, hg_w1⟩ := exists_avoiding_multiple_5 x M g B₂
    hg_pos (le_trans (Nat.mul_le_mul_right g (by omega : B₂.card + 1 ≤ 4)) h4g)
  let B₃ : Finset ℕ := insert w₁ B₂
  have hB3_c : B₃.card ≤ 4 := le_trans (Finset.card_insert_le w₁ B₂) (by omega)
  obtain ⟨w₅, hw₅_I, hw₅_not, hY1_w5⟩ := exists_avoiding_multiple_5 x M Y₁ B₃
    hY1_pos (le_trans (Nat.mul_le_mul_right Y₁ (by omega : B₃.card + 1 ≤ 5)) h5Y1)
  let B₄ : Finset ℕ := insert w₅ B₃
  have hB4_c : B₄.card ≤ 5 := le_trans (Finset.card_insert_le w₅ B₃) (by omega)
  obtain ⟨w₆, hw₆_I, hw₆_not, hY2_w6⟩ := exists_avoiding_multiple_5 x M Y₂ B₄
    hY2_pos (le_trans (Nat.mul_le_mul_right Y₂ (by omega : B₄.card + 1 ≤ 6)) h6Y2)
  let B : Finset ℕ := insert w₆ B₄
  have hBI : B ⊆ consecInterval x M :=
    Finset.insert_subset hw₆_I (Finset.insert_subset hw₅_I (Finset.insert_subset hw₁_I
      (Finset.insert_subset hw₄_I (Finset.insert_subset hw₂_I (Finset.singleton_subset_iff.mpr hb₀_I)))))
  have hBc : B.card ≤ 6 := le_trans (Finset.card_insert_le w₆ B₄) (by omega)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  refine ⟨B, hBI, hBc, isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
  intro q _hq
  have hw2_n : w₂ ∉ ({b₀} : Finset ℕ) := hw₂_not
  have hsumA : ∑ a ∈ A, a.factorization q =
      u₁.factorization q + u₂.factorization q + u₃.factorization q + u₄.factorization q + u₅.factorization q := by
    rw [hA_eq, Finset.sum_insert (by simp [h12, h13, h14, h15]),
        Finset.sum_insert (by simp [h23, h24, h25]),
        Finset.sum_insert (by simp [h34, h35]),
        Finset.sum_insert (by simp [h45]), Finset.sum_singleton]
    ring
  have hsumB : ∑ b ∈ B, b.factorization q =
      w₆.factorization q + w₅.factorization q + w₁.factorization q +
        w₄.factorization q + w₂.factorization q + b₀.factorization q := by
    dsimp [B, B₄, B₃, B₂, B₁]
    rw [Finset.sum_insert hw₆_not, Finset.sum_insert hw₅_not, Finset.sum_insert hw₁_not,
        Finset.sum_insert hw₄_not, Finset.sum_insert hw2_n, Finset.sum_singleton]
    ring
  rw [hsumA, hsumB]
  have hu1_sp : u₁.factorization q = Y₁.factorization q + D₁.factorization q := by
    have hmul : Y₁ * D₁ = u₁ := Nat.div_mul_cancel hD1_u1
    rw [← hmul, Nat.factorization_mul hY1_pos.ne' hD1_pos.ne', Finsupp.add_apply]
  have hu2_sp : u₂.factorization q = Y₂.factorization q + D₂.factorization q := by
    have hmul : Y₂ * D₂ = u₂ := Nat.div_mul_cancel hD2_u2
    rw [← hmul, Nat.factorization_mul hY2_pos.ne' hD2_pos.ne', Finsupp.add_apply]
  have hb00 := (pos_of_mem_consecInterval hb₀_I).ne'
  have hb3 := fac_le_of_dvd_5 hb00 (hb₀_dvd u₃ hu3A) (p := q)
  have hb4 := fac_le_of_dvd_5 hb00 (hb₀_dvd u₄ hu4A) (p := q)
  have hb5 := fac_le_of_dvd_5 hb00 (hb₀_dvd u₅ hu5A) (p := q)
  have hw1g := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₁_I).ne' hg_w1 (p := q)
  have hw2h := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₂_I).ne' hh_w2 (p := q)
  have hw4D := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₄_I).ne' hD_w4 (p := q)
  have hw5Y := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₅_I).ne' hY1_w5 (p := q)
  have hw6Y := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₆_I).ne' hY2_w6 (p := q)
  rw [fac_gcd_eq_min_5 hu3p.ne' hu4p.ne'] at hw1g
  rw [fac_gcd_eq_min_5 hL_pos.ne' hu5p.ne', fac_lcm_eq_max_5 hu3p.ne' hu4p.ne'] at hw2h
  rw [Nat.factorization_mul hD1_pos.ne' hD2_pos.ne', Finsupp.add_apply] at hw4D
  have hineq := r2_nonspan3_val_ineq (u₃.factorization q) (u₄.factorization q) (u₅.factorization q) 0
  omega

/-! ## Part 2: Structure of `C5Core` (`Facts 1-4`, `Claim A`, and `Case I`) -/

private lemma gcd_one_exists_fac_zero {A : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hAgcd : A.gcd id = 1) (hA_pos : ∀ a ∈ A, 0 < a) :
    ∃ a ∈ A, a.factorization p = 0 := by
  by_contra hnone; push Not at hnone
  have hp_dvd : p ∣ A.gcd id := Finset.dvd_gcd fun a ha =>
    (hp.dvd_iff_one_le_factorization (hA_pos a ha).ne').mpr (Nat.pos_of_ne_zero (hnone a ha))
  rw [hAgcd] at hp_dvd
  exact hp.not_dvd_one hp_dvd

private lemma core_Z_T_props {A : Finset ℕ} {M p : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id) :
    let L := A.lcm id
    let e := L.factorization p
    let Z := A.filter (fun a => a.factorization p < e)
    let T := A.filter (fun a => a.factorization p = e)
    1 ≤ e ∧ Z.card + T.card = 5 ∧ 2 ≤ T.card ∧ 1 ≤ Z.card ∧ Z.card ≤ 3 ∧ 3 * p ^ e ≤ M := by
  rcases hC with ⟨hAc, hA_pos, hA_le, hA_half, hAgcd, hNo4, hNo1b⟩
  let L := A.lcm id
  let e := L.factorization p
  let Z := A.filter (fun a => a.factorization p < e)
  let T := A.filter (fun a => a.factorization p = e)
  have hL_pos : 0 < L := finset_lcm_pos_core hA_pos
  have he_ge1 : 1 ≤ e := (hp.dvd_iff_one_le_factorization hL_pos.ne').mp hpL
  have h_le_e : ∀ a ∈ A, a.factorization p ≤ e := fun a ha =>
    fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm ha) (p := p)
  have hdisj : Disjoint Z T := Finset.disjoint_left.mpr fun a hz ht => by
    have h1 := (Finset.mem_filter.mp hz).2
    have h2 := (Finset.mem_filter.mp ht).2
    omega
  have hunion : Z ∪ T = A := by
    ext a; simp only [Z, T, Finset.mem_union, Finset.mem_filter]
    exact ⟨by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h,
      fun ha => by have := h_le_e a ha; rcases lt_or_eq_of_le this with hlt | heq <;> [exact Or.inl ⟨ha, hlt⟩; exact Or.inr ⟨ha, heq⟩]⟩
  have hsum_card : Z.card + T.card = 5 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hAc]
  have hZ_ge1 : 1 ≤ Z.card := by
    obtain ⟨a₀, ha₀, hz0⟩ := gcd_one_exists_fac_zero hp hAgcd hA_pos
    exact Finset.card_pos.mpr ⟨a₀, Finset.mem_filter.mpr ⟨ha₀, by omega⟩⟩
  have hT_ge2 : 2 ≤ T.card := by
    by_contra hlt2
    have hT_ne : T.Nonempty := by
      -- Since `L.factorization p = e ≥ 1`, some element of `A` must achieve `factorization p ≥ e`.
      by_contra hTe
      rw [Finset.not_nonempty_iff_eq_empty] at hTe
      have hsubL : L ∣ ∏ a ∈ A, a := Finset.lcm_dvd fun a ha => Finset.dvd_prod_of_mem id ha
      -- Actually `L ∣ L'`: every `a ∈ A` has `a.factorization p < e`, so `p^(e-1)` works!
      have hall_lt : ∀ a ∈ A, a ∣ L / p := by
        intro a ha
        rw [← Nat.factorization_le_iff_dvd (hA_pos a ha).ne' (Nat.div_pos (Nat.le_of_dvd hL_pos hpL) hp.pos).ne']
        intro q
        have hdiv : (L / p) * p = L := Nat.div_mul_cancel hpL
        have hfq := congrArg (fun n => n.factorization q) hdiv
        rw [Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hL_pos hpL) hp.pos).ne' hp.ne_zero,
            Finsupp.add_apply] at hfq
        have haL := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm ha) (p := q)
        simp only [id_eq] at haL
        by_cases hqp : q = p
        · subst hqp
          have hna : a ∉ T := fun h => by rw [hTe] at h; simp at h
          have hlt : a.factorization q < e := by
            have := h_le_e a ha
            by_contra hge
            exact hna (Finset.mem_filter.mpr ⟨ha, by omega⟩)
          rw [hp.factorization_self] at hfq
          omega
        · have hpf : p.factorization q = 0 := by
            rw [hp.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp)]
          rw [hpf, add_zero] at hfq
          omega
      have hL_dvd := Finset.lcm_dvd hall_lt
      have hle : L ≤ L / p := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hL_pos hpL) hp.pos) hL_dvd
      have hlt : L / p < L := Nat.div_lt_self hL_pos hp.one_lt
      exact absurd hlt (not_lt_of_ge hle)
    have hT_pos : 0 < T.card := Finset.card_pos.mpr hT_ne
    have hT1 : T.card = 1 := by omega
    obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hT1
    have huT : u ∈ T := by rw [hu_eq]; exact Finset.mem_singleton_self u
    have huA : u ∈ A := (Finset.mem_filter.mp huT).1
    have hZ_eq : A.erase u = Z := by
      rw [← hunion, hu_eq, Finset.union_comm]
      have hndisj : u ∉ Z := fun h => Finset.disjoint_left.mp hdisj h huT
      exact Finset.erase_insert hndisj
    have hnot_pc := hNo1b u huA
    rw [hZ_eq] at hnot_pc
    dsimp [PairConst] at hnot_pc
    push Not at hnot_pc
    obtain ⟨x₁, hx1, x₂, hx2, hx12, hne_L⟩ := hnot_pc
    have hx3_ex : ∃ x₃ ∈ Z, ¬ (x₃ ∣ Nat.lcm x₁ x₂) := by
      by_contra hall; push Not at hall
      exact hne_L (Nat.dvd_antisymm (Nat.lcm_dvd (Finset.dvd_lcm hx1) (Finset.dvd_lcm hx2)) (Finset.lcm_dvd hall))
    obtain ⟨x₃, hx3, hx3_nd⟩ := hx3_ex
    have hx13 : x₁ ≠ x₃ := fun h => hx3_nd (h ▸ Nat.dvd_lcm_left x₁ x₂)
    have hx23 : x₂ ≠ x₃ := fun h => hx3_nd (h ▸ Nat.dvd_lcm_right x₁ x₂)
    have hx1u : x₁ ≠ u := fun h => Finset.disjoint_left.mp hdisj hx1 (h ▸ huT)
    have hx2u : x₂ ≠ u := fun h => Finset.disjoint_left.mp hdisj hx2 (h ▸ huT)
    have hx3u : x₃ ≠ u := fun h => Finset.disjoint_left.mp hdisj hx3 (h ▸ huT)
    have hu_dvd := hNo4 x₁ (Finset.mem_filter.mp hx1).1 x₂ (Finset.mem_filter.mp hx2).1
      x₃ (Finset.mem_filter.mp hx3).1 u huA hx12 hx13 hx1u hx23 hx2u hx3u hx3_nd
    have hL3_pos : 0 < Nat.lcm (Nat.lcm x₁ x₂) x₃ :=
      Nat.lcm_pos (Nat.lcm_pos (hA_pos _ (Finset.mem_filter.mp hx1).1)
        (hA_pos _ (Finset.mem_filter.mp hx2).1)) (hA_pos _ (Finset.mem_filter.mp hx3).1)
    have hfac := fac_le_of_dvd_5 hL3_pos.ne' hu_dvd (p := p)
    rw [fac_lcm_eq_max_5 (Nat.lcm_pos (hA_pos _ (Finset.mem_filter.mp hx1).1)
        (hA_pos _ (Finset.mem_filter.mp hx2).1)).ne' (hA_pos _ (Finset.mem_filter.mp hx3).1).ne',
        fac_lcm_eq_max_5 (hA_pos _ (Finset.mem_filter.mp hx1).1).ne'
        (hA_pos _ (Finset.mem_filter.mp hx2).1).ne'] at hfac
    have hfx1 := (Finset.mem_filter.mp hx1).2
    have hfx2 := (Finset.mem_filter.mp hx2).2
    have hfx3 := (Finset.mem_filter.mp hx3).2
    have hfu := (Finset.mem_filter.mp huT).2
    omega
  have hZ_le3 : Z.card ≤ 3 := by omega
  have h3pe : 3 * p ^ e ≤ M := by
    obtain ⟨t₁, ht1⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    obtain ⟨t₂, ht2⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ht1]; omega : 0 < (T.erase t₁).card)
    have hm := Finset.mem_erase.mp ht2
    have ht1A := (Finset.mem_filter.mp ht1).1
    have ht2A := (Finset.mem_filter.mp hm.2).1
    have hpe1 : p ^ e ∣ t₁ := (hp.pow_dvd_iff_le_factorization (hA_pos t₁ ht1A).ne').mpr (by rw [(Finset.mem_filter.mp ht1).2])
    have hpe2 : p ^ e ∣ t₂ := (hp.pow_dvd_iff_le_factorization (hA_pos t₂ ht2A).ne').mpr (by rw [(Finset.mem_filter.mp hm.2).2])
    exact three_mul_le_of_two_gt_half_5 (pow_pos hp.pos e) hm.1.symm (hA_le t₁ ht1A) (hA_le t₂ ht2A)
      (hA_half t₁ ht1A) (hA_half t₂ ht2A) hpe1 hpe2
  exact ⟨he_ge1, hsum_card, hT_ge2, hZ_ge1, hZ_le3, h3pe⟩

private lemma core_fact1_three_pairconst {A : Finset ℕ} {M p : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hZ3 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3) :
    PairConst (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)) := by
  have ⟨_, _, hT2, _, _, _⟩ := core_Z_T_props hC hp hpL
  rcases hC with ⟨_, hA_pos, _, _, _, hNo4, _⟩
  let e := (A.lcm id).factorization p
  let Z := A.filter (fun a => a.factorization p < e)
  let T := A.filter (fun a => a.factorization p = e)
  intro x₁ hx1 x₂ hx2 hx12
  by_contra hne_L
  have hx3_ex : ∃ x₃ ∈ Z, ¬ (x₃ ∣ Nat.lcm x₁ x₂) := by
    by_contra hall; push Not at hall
    exact hne_L (Nat.dvd_antisymm (Nat.lcm_dvd (Finset.dvd_lcm hx1) (Finset.dvd_lcm hx2)) (Finset.lcm_dvd hall))
  obtain ⟨x₃, hx3, hx3_nd⟩ := hx3_ex
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (by dsimp [T, e] at hT2 ⊢; omega : 0 < T.card)
  have htA := (Finset.mem_filter.mp ht).1
  have hte := (Finset.mem_filter.mp ht).2
  have hx13 : x₁ ≠ x₃ := fun h => hx3_nd (h ▸ Nat.dvd_lcm_left x₁ x₂)
  have hx23 : x₂ ≠ x₃ := fun h => hx3_nd (h ▸ Nat.dvd_lcm_right x₁ x₂)
  have hxt : ∀ z ∈ Z, z ≠ t := fun z hz h => by
    have h1 := (Finset.mem_filter.mp hz).2
    dsimp [Z, e] at h1; subst h; omega
  have ht_dvd := hNo4 x₁ (Finset.mem_filter.mp hx1).1 x₂ (Finset.mem_filter.mp hx2).1
    x₃ (Finset.mem_filter.mp hx3).1 t htA hx12 hx13 (hxt x₁ hx1) hx23 (hxt x₂ hx2) (hxt x₃ hx3) hx3_nd
  have hL3_pos : 0 < Nat.lcm (Nat.lcm x₁ x₂) x₃ :=
    Nat.lcm_pos (Nat.lcm_pos (hA_pos _ (Finset.mem_filter.mp hx1).1)
      (hA_pos _ (Finset.mem_filter.mp hx2).1)) (hA_pos _ (Finset.mem_filter.mp hx3).1)
  have hfac := fac_le_of_dvd_5 hL3_pos.ne' ht_dvd (p := p)
  rw [fac_lcm_eq_max_5 (Nat.lcm_pos (hA_pos _ (Finset.mem_filter.mp hx1).1)
      (hA_pos _ (Finset.mem_filter.mp hx2).1)).ne' (hA_pos _ (Finset.mem_filter.mp hx3).1).ne',
      fac_lcm_eq_max_5 (hA_pos _ (Finset.mem_filter.mp hx1).1).ne'
      (hA_pos _ (Finset.mem_filter.mp hx2).1).ne'] at hfac
  have hfx1 := (Finset.mem_filter.mp hx1).2
  have hfx2 := (Finset.mem_filter.mp hx2).2
  have hfx3 := (Finset.mem_filter.mp hx3).2
  omega

private lemma core_fact2_three_vals {A : Finset ℕ} {M p : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hZ3 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3) :
    ∃ z₀ z₁ z₂ : ℕ,
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) = {z₀, z₁, z₂} ∧
      z₀ ≠ z₁ ∧ z₀ ≠ z₂ ∧ z₁ ≠ z₂ ∧
      z₀.factorization p = 0 ∧ z₁.factorization p = z₂.factorization p ∧
      z₁.factorization p < (A.lcm id).factorization p := by
  have ⟨he1, _, _, _, _, _⟩ := core_Z_T_props hC hp hpL
  have hpc := core_fact1_three_pairconst hC hp hpL hZ3
  rcases hC with ⟨_, hA_pos, _, _, hAgcd, _, _⟩
  let e := (A.lcm id).factorization p
  let Z := A.filter (fun a => a.factorization p < e)
  obtain ⟨z₀, hz0A, hz0_v⟩ := gcd_one_exists_fac_zero hp hAgcd hA_pos
  have hz0Z : z₀ ∈ Z := Finset.mem_filter.mpr ⟨hz0A, by omega⟩
  have he2 : (Z.erase z₀).card = 2 := by rw [Finset.card_erase_of_mem hz0Z, hZ3]
  obtain ⟨z₁, z₂, hz12, hz_er⟩ := Finset.card_eq_two.mp he2
  have hz1Z : z₁ ∈ Z := (Finset.mem_erase.mp (hz_er ▸ by simp : z₁ ∈ Z.erase z₀)).2
  have hz2Z : z₂ ∈ Z := (Finset.mem_erase.mp (hz_er ▸ by simp : z₂ ∈ Z.erase z₀)).2
  have hz01 : z₀ ≠ z₁ := (Finset.mem_erase.mp (hz_er ▸ by simp : z₁ ∈ Z.erase z₀)).1.symm
  have hz02 : z₀ ≠ z₂ := (Finset.mem_erase.mp (hz_er ▸ by simp : z₂ ∈ Z.erase z₀)).1.symm
  have hZ_eq : Z = {z₀, z₁, z₂} := by
    rw [← Finset.insert_erase hz0Z, hz_er]
  have hz0p : 0 < z₀ := hA_pos z₀ hz0A
  have hz1p : 0 < z₁ := hA_pos z₁ (Finset.mem_filter.mp hz1Z).1
  have hz2p : 0 < z₂ := hA_pos z₂ (Finset.mem_filter.mp hz2Z).1
  have hLZ_pos : 0 < Z.lcm id := finset_lcm_pos_core fun z hz => hA_pos z (Finset.mem_filter.mp hz).1
  have hl01 := congrArg (fun n => n.factorization p) (hpc z₀ hz0Z z₁ hz1Z hz01)
  have hl02 := congrArg (fun n => n.factorization p) (hpc z₀ hz0Z z₂ hz2Z hz02)
  change (Nat.lcm z₀ z₁).factorization p = (Z.lcm id).factorization p at hl01
  change (Nat.lcm z₀ z₂).factorization p = (Z.lcm id).factorization p at hl02
  rw [fac_lcm_eq_max_5 hz0p.ne' hz1p.ne', hz0_v] at hl01
  rw [fac_lcm_eq_max_5 hz0p.ne' hz2p.ne', hz0_v] at hl02
  have hv_eq : z₁.factorization p = z₂.factorization p := by omega
  exact ⟨z₀, z₁, z₂, hZ_eq, hz01, hz02, hz12, hz0_v, hv_eq, (Finset.mem_filter.mp hz1Z).2⟩

private lemma core_fact_sub_three_set {A : Finset ℕ} {M p q : ℕ}
    (hC : C5Core A M) (_hp : p.Prime) (_hpL : p ∣ A.lcm id)
    (hq : q.Prime) (hqL : q ∣ A.lcm id)
    (hZp2 : 2 ≤ (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card)
    (hZq3 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card = 3)
    (hsub : A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ⊆
      A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) :
    A.filter (fun a => a.factorization p < (A.lcm id).factorization p) =
      A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := by
  by_contra hne
  let Zp := A.filter (fun a => a.factorization p < (A.lcm id).factorization p)
  let Zq := A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
  have hZp2' : 2 ≤ Zp.card := hZp2
  have hZq3' : Zq.card = 3 := hZq3
  have hlt : Zp.card < Zq.card := Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hZp_eq2 : Zp.card = 2 := by omega
  obtain ⟨a, b, hab, hZp_eq⟩ := Finset.card_eq_two.mp hZp_eq2
  have haZp : a ∈ Zp := by rw [hZp_eq]; simp
  have hbZp : b ∈ Zp := by rw [hZp_eq]; simp
  have haZq : a ∈ Zq := hsub haZp
  have hbZq : b ∈ Zq := hsub hbZp
  obtain ⟨c, hcZq, hcZp⟩ : ∃ c ∈ Zq, c ∉ Zp := by
    by_contra hall; push Not at hall
    exact hne (Finset.Subset.antisymm hsub hall)
  have hcA : c ∈ A := (Finset.mem_filter.mp hcZq).1
  have hL_pos : 0 < A.lcm id := finset_lcm_pos_core hC.2.1
  have hL_c := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hcA) (p := p)
  simp only [id_eq] at hL_c
  have hce : c.factorization p = (A.lcm id).factorization p := by
    by_contra hne_p
    exact hcZp (Finset.mem_filter.mpr ⟨hcA, by omega⟩)
  have hpc := core_fact1_three_pairconst hC hq hqL hZq3
  have hab_L := hpc a haZq b hbZq hab
  have hc_lcm : c ∣ Nat.lcm a b := hab_L ▸ Finset.dvd_lcm hcZq
  have ha0 := (hC.2.1 a (Finset.mem_filter.mp haZp).1).ne'
  have hb0 := (hC.2.1 b (Finset.mem_filter.mp hbZp).1).ne'
  have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hC.2.1 _ (Finset.mem_filter.mp haZp).1)
    (hC.2.1 _ (Finset.mem_filter.mp hbZp).1)).ne' hc_lcm (p := p)
  rw [fac_lcm_eq_max_5 ha0 hb0] at hfac
  have hfa := (Finset.mem_filter.mp haZp).2
  have hfb := (Finset.mem_filter.mp hbZp).2
  omega

private lemma core_fact3_two_three_sets {A : Finset ℕ} {M p q : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hq : q.Prime) (hqL : q ∣ A.lcm id)
    (hZp3 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3)
    (hZq3 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card = 3)
    (hne : A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠
           A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) :
    (A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ∩
     A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card = 1 := by
  let Zp := A.filter (fun a => a.factorization p < (A.lcm id).factorization p)
  let Zq := A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
  have hZp3' : Zp.card = 3 := hZp3
  have hZq3' : Zq.card = 3 := hZq3
  have hu_le : (Zp ∪ Zq).card ≤ 5 := by
    calc (Zp ∪ Zq).card ≤ A.card := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    _ = 5 := hC.1
  have hcard_un : (Zp ∪ Zq).card + (Zp ∩ Zq).card = Zp.card + Zq.card :=
    Finset.card_union_add_card_inter Zp Zq
  have h_ge1 : 1 ≤ (Zp ∩ Zq).card := by omega
  by_contra hne1
  change (Zp ∩ Zq).card ≠ 1 at hne1
  have h_ge2 : 2 ≤ (Zp ∩ Zq).card := by omega
  obtain ⟨S, hS_sub, hS2⟩ := Finset.exists_subset_card_eq h_ge2
  obtain ⟨a, b, hab, hS_eq⟩ := Finset.card_eq_two.mp hS2
  have ha_in : a ∈ Zp ∩ Zq := hS_sub (by rw [hS_eq]; simp)
  have hb_in : b ∈ Zp ∩ Zq := hS_sub (by rw [hS_eq]; simp)
  have hp_pc := core_fact1_three_pairconst hC hp hpL hZp3
  have hq_pc := core_fact1_three_pairconst hC hq hqL hZq3
  have hL_eq : Zp.lcm id = Zq.lcm id := by
    rw [← hp_pc a (Finset.mem_inter.mp ha_in).1 b (Finset.mem_inter.mp hb_in).1 hab]
    exact hq_pc a (Finset.mem_inter.mp ha_in).2 b (Finset.mem_inter.mp hb_in).2 hab
  have hnot_sub : ¬ (Zq ⊆ Zp) := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
  rw [Finset.not_subset] at hnot_sub
  obtain ⟨c, hcZq, hcZp⟩ := hnot_sub
  have hcA : c ∈ A := (Finset.mem_filter.mp hcZq).1
  have hL_pos : 0 < A.lcm id := finset_lcm_pos_core hC.2.1
  have hL_c := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hcA) (p := p)
  simp only [id_eq] at hL_c
  have hce : c.factorization p = (A.lcm id).factorization p := by
    by_contra hne_p
    exact hcZp (Finset.mem_filter.mpr ⟨hcA, by omega⟩)
  have hc_dvd : c ∣ Zp.lcm id := hL_eq ▸ Finset.dvd_lcm hcZq
  have hc_lcm : c ∣ Nat.lcm a b := (hp_pc a (Finset.mem_inter.mp ha_in).1 b (Finset.mem_inter.mp hb_in).1 hab) ▸ hc_dvd
  have ha0 := (hC.2.1 a (Finset.mem_filter.mp (Finset.mem_inter.mp ha_in).1).1).ne'
  have hb0 := (hC.2.1 b (Finset.mem_filter.mp (Finset.mem_inter.mp hb_in).1).1).ne'
  have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hC.2.1 _ (Finset.mem_filter.mp (Finset.mem_inter.mp ha_in).1).1)
    (hC.2.1 _ (Finset.mem_filter.mp (Finset.mem_inter.mp hb_in).1).1)).ne' hc_lcm (p := p)
  rw [fac_lcm_eq_max_5 ha0 hb0] at hfac
  have hfa := (Finset.mem_filter.mp (Finset.mem_inter.mp ha_in).1).2
  have hfb := (Finset.mem_filter.mp (Finset.mem_inter.mp hb_in).1).2
  omega

private lemma core_fact4_two_sub_three {A : Finset ℕ} {M p q : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hq : q.Prime) (hqL : q ∣ A.lcm id)
    (hZp2 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 2)
    (hZq3 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card = 3) :
    ¬ (A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ⊆
       A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) := by
  intro hsub
  have heq := core_fact_sub_three_set hC hp hpL hq hqL (by omega) hZq3 hsub
  have := congrArg Finset.card heq
  omega

private lemma not_pairConst_card_four_witness {T : Finset ℕ}
    (hT4 : T.card = 4) (_hT_pos : ∀ a ∈ T, 0 < a) (hNPC : ¬ PairConst T) :
    ∃ t₁ t₂ t₃ t₄ : ℕ, T = {t₁, t₂, t₃, t₄} ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄ ∧
      ¬ (t₃ ∣ Nat.lcm t₁ t₂) := by
  dsimp [PairConst] at hNPC
  push Not at hNPC
  obtain ⟨t₁, ht1, t₂, ht2, ht12, hne⟩ := hNPC
  have ht3_ex : ∃ t₃ ∈ T, ¬ (t₃ ∣ Nat.lcm t₁ t₂) := by
    by_contra hall; push Not at hall
    exact hne (Nat.dvd_antisymm (Nat.lcm_dvd (Finset.dvd_lcm ht1) (Finset.dvd_lcm ht2)) (Finset.lcm_dvd hall))
  obtain ⟨t₃, ht3, ht3_nd⟩ := ht3_ex
  have ht13 : t₁ ≠ t₃ := fun h => ht3_nd (h ▸ Nat.dvd_lcm_left t₁ t₂)
  have ht23 : t₂ ≠ t₃ := fun h => ht3_nd (h ▸ Nat.dvd_lcm_right t₁ t₂)
  let S := ((T.erase t₁).erase t₂).erase t₃
  have hS1 : S.card = 1 := by
    have ht2_e1 : t₂ ∈ T.erase t₁ := Finset.mem_erase.mpr ⟨ht12.symm, ht2⟩
    have ht3_e2 : t₃ ∈ (T.erase t₁).erase t₂ := Finset.mem_erase.mpr ⟨ht23.symm, Finset.mem_erase.mpr ⟨ht13.symm, ht3⟩⟩
    rw [Finset.card_erase_of_mem ht3_e2, Finset.card_erase_of_mem ht2_e1, Finset.card_erase_of_mem ht1, hT4]
  obtain ⟨t₄, ht4_eq⟩ := Finset.card_eq_one.mp hS1
  have ht4S : t₄ ∈ S := by rw [ht4_eq]; exact Finset.mem_singleton_self t₄
  have ht4_3 := Finset.mem_erase.mp ht4S
  have ht4_2 := Finset.mem_erase.mp ht4_3.2
  have ht4_1 := Finset.mem_erase.mp ht4_2.2
  have hT_eq : T = {t₁, t₂, t₃, t₄} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hx1 : x = t₁; · exact Or.inl hx1
      by_cases hx2 : x = t₂; · exact Or.inr (Or.inl hx2)
      by_cases hx3 : x = t₃; · exact Or.inr (Or.inr (Or.inl hx3))
      have hxS : x ∈ S := Finset.mem_erase.mpr ⟨hx3, Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx1, hx⟩⟩⟩
      rw [ht4_eq, Finset.mem_singleton] at hxS
      exact Or.inr (Or.inr (Or.inr hxS))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ht1
      · exact ht2
      · exact ht3
      · exact ht4_1.2
  exact ⟨t₁, t₂, t₃, t₄, hT_eq, ht12, ht13, ht4_1.1.symm, ht23, ht4_2.1.symm, ht4_3.1.symm, ht3_nd⟩

private lemma core_claimA {A : Finset ℕ} {M p : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hZp_le2 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card ≤ 2) :
    p ^ (A.lcm id).factorization p ≤ 5 ∨ M < (p ^ (A.lcm id).factorization p) ^ 2 := by
  by_contra hbad
  push Not at hbad
  rcases hbad with ⟨hpe6, hpe2_le⟩
  have ⟨he1, hsum, hT2, hZ1, _, h3pe⟩ := core_Z_T_props hC hp hpL
  rcases hC with ⟨hA_card, hA_pos, hA_le, _, _, _, hNoType1b⟩
  let e := (A.lcm id).factorization p
  let Z := A.filter (fun a => a.factorization p < e)
  let T := A.filter (fun a => a.factorization p = e)
  have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
  have hmul_T : ∀ t ∈ T, 5 * (t / p ^ e) ≤ M ∧ 6 * (t / p ^ e) ≤ M := by
    intro t ht
    have htA := (Finset.mem_filter.mp ht).1
    have hpe_t : p ^ e ∣ t := (hp.pow_dvd_iff_le_factorization (hA_pos t htA).ne').mpr (by rw [(Finset.mem_filter.mp ht).2])
    have h6 : 6 * (t / p ^ e) ≤ M := by
      calc 6 * (t / p ^ e) ≤ p ^ e * (t / p ^ e) := Nat.mul_le_mul_right _ hpe6
      _ = t := Nat.mul_div_cancel' hpe_t
      _ ≤ M := hA_le t htA
    exact ⟨by omega, h6⟩
  have build_R1 : ∀ u₁ u₂ u₃ u₄ u₅ : ℕ,
      u₁ ∈ T → u₂ ∈ T →
      A = {u₁, u₂, u₃, u₄, u₅} →
      u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₁ ≠ u₅ →
      u₂ ≠ u₃ → u₂ ≠ u₄ → u₂ ≠ u₅ →
      u₃ ≠ u₄ → u₃ ≠ u₅ → u₄ ≠ u₅ →
      ¬ (u₅ ∣ Nat.lcm u₃ u₄) → HasRule1 A M := by
    intro u₁ u₂ u₃ u₄ u₅ hu1T hu2T hAeq h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hnd
    have h1 := (Finset.mem_filter.mp hu1T).2
    have h2 := (Finset.mem_filter.mp hu2T).2
    refine ⟨u₁, u₂, u₃, u₄, u₅, p, e, e, hAeq, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
      hnd, hp, he1, by omega, he1, by omega, ?_, h3pe, (hmul_T u₁ hu1T).1, (hmul_T u₂ hu2T).2⟩
    simpa [pow_add, sq] using hpe2_le
  change Z.card + T.card = 5 at hsum
  change 1 ≤ Z.card at hZ1
  change Z.card ≤ 2 at hZp_le2
  by_cases hZ2 : Z.card = 2
  · obtain ⟨z₁, z₂, hz12, hZ_eq⟩ := Finset.card_eq_two.mp hZ2
    have hT3 : T.card = 3 := by omega
    obtain ⟨t₁, t₂, t₃, ht12, ht13, ht23, hT_eq⟩ := Finset.card_eq_three.mp hT3
    have hz1Z : z₁ ∈ Z := by rw [hZ_eq]; simp
    have hz2Z : z₂ ∈ Z := by rw [hZ_eq]; simp
    have ht1T : t₁ ∈ T := by rw [hT_eq]; simp
    have ht2T : t₂ ∈ T := by rw [hT_eq]; simp
    have ht3T : t₃ ∈ T := by rw [hT_eq]; simp
    have hZT_disj : ∀ z ∈ Z, ∀ t ∈ T, z ≠ t := fun z hz t ht h => by
      have hfz := (Finset.mem_filter.mp hz).2
      have hft := (Finset.mem_filter.mp ht).2
      subst h; omega
    have ht3_nd : ¬ (t₃ ∣ Nat.lcm z₁ z₂) := by
      intro hdvd
      have hz1_pos := (hA_pos z₁ (Finset.mem_filter.mp hz1Z).1).ne'
      have hz2_pos := (hA_pos z₂ (Finset.mem_filter.mp hz2Z).1).ne'
      have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hA_pos z₁ (Finset.mem_filter.mp hz1Z).1)
        (hA_pos z₂ (Finset.mem_filter.mp hz2Z).1)).ne' hdvd (p := p)
      rw [fac_lcm_eq_max_5 hz1_pos hz2_pos] at hfac
      have h1 := (Finset.mem_filter.mp hz1Z).2
      have h2 := (Finset.mem_filter.mp hz2Z).2
      have h3 := (Finset.mem_filter.mp ht3T).2
      omega
    have hA_eq : A = {t₁, t₂, z₁, z₂, t₃} := by
      ext x; constructor
      · intro hx
        by_cases hxf : x.factorization p < e
        · have hxZ : x ∈ Z := Finset.mem_filter.mpr ⟨hx, hxf⟩
          rw [hZ_eq] at hxZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hxZ ⊢
          rcases hxZ with rfl | rfl <;> tauto
        · have hL_pos := finset_lcm_pos_core hA_pos
          have hx_le := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hx) (p := p)
          simp only [id_eq] at hx_le
          have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, by omega⟩
          rw [hT_eq] at hxT; simp only [Finset.mem_insert, Finset.mem_singleton] at hxT ⊢
          rcases hxT with rfl | rfl | rfl <;> tauto
      · intro hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.mem_filter.mp ht1T).1
        · exact (Finset.mem_filter.mp ht2T).1
        · exact (Finset.mem_filter.mp hz1Z).1
        · exact (Finset.mem_filter.mp hz2Z).1
        · exact (Finset.mem_filter.mp ht3T).1
    exact hNR1 (build_R1 t₁ t₂ z₁ z₂ t₃ ht1T ht2T hA_eq
      ht12 (hZT_disj z₁ hz1Z t₁ ht1T).symm (hZT_disj z₂ hz2Z t₁ ht1T).symm ht13
      (hZT_disj z₁ hz1Z t₂ ht2T).symm (hZT_disj z₂ hz2Z t₂ ht2T).symm ht23
      hz12 (hZT_disj z₁ hz1Z t₃ ht3T) (hZT_disj z₂ hz2Z t₃ ht3T) ht3_nd)
  · have hZ1_eq : Z.card = 1 := by omega
    obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hZ1_eq
    have hzZ : z ∈ Z := by rw [hz_eq]; exact Finset.mem_singleton_self z
    have hzA : z ∈ A := (Finset.mem_filter.mp hzZ).1
    have hT_eq_er : T = A.erase z := by
      dsimp [T]; ext x; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hxA, hxe⟩
        exact ⟨fun h => by subst h; have := (Finset.mem_filter.mp hzZ).2; omega, hxA⟩
      · rintro ⟨hne, hxA⟩
        have hxnZ : x ∉ Z := fun hxZ => hne (by rw [hz_eq, Finset.mem_singleton] at hxZ; exact hxZ)
        have hL_pos := finset_lcm_pos_core hA_pos
        have hx_le := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hxA) (p := p)
        simp only [id_eq] at hx_le
        exact ⟨hxA, by by_contra hlt; exact hxnZ (Finset.mem_filter.mpr ⟨hxA, by omega⟩)⟩
    have hT4 : T.card = 4 := by omega
    have hNPC : ¬ PairConst T := hT_eq_er ▸ hNoType1b z hzA
    obtain ⟨t₁, t₂, t₃, t₄, hT_eq, ht12, ht13, ht14, ht23, ht24, ht34, ht3_nd⟩ :=
      not_pairConst_card_four_witness hT4 (fun a ha => hA_pos a (Finset.mem_filter.mp ha).1) hNPC
    have ht1T : t₁ ∈ T := by rw [hT_eq]; simp
    have ht2T : t₂ ∈ T := by rw [hT_eq]; simp
    have ht3T : t₃ ∈ T := by rw [hT_eq]; simp
    have ht4T : t₄ ∈ T := by rw [hT_eq]; simp
    have hzt : ∀ t ∈ T, z ≠ t := fun t ht h => by
      have h1 := (Finset.mem_filter.mp hzZ).2; have h2 := (Finset.mem_filter.mp ht).2
      subst h; omega
    have hL12_pos : 0 < Nat.lcm t₁ t₂ :=
      Nat.lcm_pos (hA_pos _ (Finset.mem_filter.mp ht1T).1) (hA_pos _ (Finset.mem_filter.mp ht2T).1)
    have ht3_pos := hA_pos _ (Finset.mem_filter.mp ht3T).1
    have hq_ex : ∃ q, q.Prime ∧ (Nat.lcm t₁ t₂).factorization q < t₃.factorization q := by
      by_contra hall; push Not at hall
      apply ht3_nd
      rw [← Nat.factorization_le_iff_dvd ht3_pos.ne' hL12_pos.ne']
      intro q
      by_cases hq : q.Prime
      · exact hall q hq
      · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
    obtain ⟨q, _, hq_lt⟩ := hq_ex
    rw [fac_lcm_eq_max_5 (hA_pos _ (Finset.mem_filter.mp ht1T).1).ne'
      (hA_pos _ (Finset.mem_filter.mp ht2T).1).ne'] at hq_lt
    by_cases hzq : z.factorization q < t₃.factorization q
    · have hnd : ¬ (t₃ ∣ Nat.lcm z t₂) := by
        intro hdvd
        have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hA_pos z hzA) (hA_pos _ (Finset.mem_filter.mp ht2T).1)).ne' hdvd (p := q)
        rw [fac_lcm_eq_max_5 (hA_pos z hzA).ne' (hA_pos _ (Finset.mem_filter.mp ht2T).1).ne'] at hfac
        omega
      have hA_eq : A = {t₁, t₄, z, t₂, t₃} := by
        rw [← Finset.insert_erase hzA, ← hT_eq_er, hT_eq]
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      exact hNR1 (build_R1 t₁ t₄ z t₂ t₃ ht1T ht4T hA_eq
        ht14 (hzt t₁ ht1T).symm ht12 ht13
        (hzt t₄ ht4T).symm ht24.symm ht34.symm
        (hzt t₂ ht2T) (hzt t₃ ht3T) ht23 hnd)
    · have hnd : ¬ (z ∣ Nat.lcm t₁ t₂) := by
        intro hdvd
        have hfac := fac_le_of_dvd_5 hL12_pos.ne' hdvd (p := q)
        rw [fac_lcm_eq_max_5 (hA_pos _ (Finset.mem_filter.mp ht1T).1).ne'
          (hA_pos _ (Finset.mem_filter.mp ht2T).1).ne'] at hfac
        omega
      have hA_eq : A = {t₃, t₄, t₁, t₂, z} := by
        rw [← Finset.insert_erase hzA, ← hT_eq_er, hT_eq]
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      exact hNR1 (build_R1 t₃ t₄ t₁ t₂ z ht3T ht4T hA_eq
        ht34 ht13.symm ht23.symm (hzt t₃ ht3T).symm
        ht14.symm ht24.symm (hzt t₄ ht4T).symm
        ht12 (hzt t₁ ht1T).symm (hzt t₂ ht2T).symm hnd)

private lemma core_at_most_one_heavy {A : Finset ℕ} {M p q : ℕ}
    (hC : C5Core A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hq : q.Prime) (hqL : q ∣ A.lcm id) (hpq : p ≠ q)
    (hZp2 : (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card ≤ 2)
    (hZq2 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2)
    (hp_hv : M < (p ^ (A.lcm id).factorization p) ^ 2)
    (hq_hv : M < (q ^ (A.lcm id).factorization q) ^ 2) : False := by
  have ⟨_, hsum_p, _, _, _, _⟩ := core_Z_T_props hC hp hpL
  have ⟨_, hsum_q, _, _, _, _⟩ := core_Z_T_props hC hq hqL
  let Tp := A.filter (fun a => a.factorization p = (A.lcm id).factorization p)
  let Tq := A.filter (fun a => a.factorization q = (A.lcm id).factorization q)
  have hTp3 : 3 ≤ Tp.card := by dsimp [Tp] at hsum_p ⊢; omega
  have hTq3 : 3 ≤ Tq.card := by dsimp [Tq] at hsum_q ⊢; omega
  have h_inter : 1 ≤ (Tp ∩ Tq).card := by
    have hu : (Tp ∪ Tq).card ≤ 5 := by
      calc (Tp ∪ Tq).card ≤ A.card := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      _ = 5 := hC.1
    have hcard := Finset.card_union_add_card_inter Tp Tq
    omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h_inter
  have htp := (Finset.mem_inter.mp ht).1
  have htq := (Finset.mem_inter.mp ht).2
  have htA := (Finset.mem_filter.mp htp).1
  have ht_pos := hC.2.1 t htA
  have hp_dvd : p ^ (A.lcm id).factorization p ∣ t :=
    (hp.pow_dvd_iff_le_factorization ht_pos.ne').mpr (by rw [(Finset.mem_filter.mp htp).2])
  have hq_dvd : q ^ (A.lcm id).factorization q ∣ t :=
    (hq.pow_dvd_iff_le_factorization ht_pos.ne').mpr (by rw [(Finset.mem_filter.mp htq).2])
  have hcop : Nat.Coprime (p ^ (A.lcm id).factorization p) (q ^ (A.lcm id).factorization q) :=
    (hp.coprime_iff_not_dvd.mpr fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)).pow _ _
  have hmul_dvd := hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd
  have hmul_le : p ^ (A.lcm id).factorization p * q ^ (A.lcm id).factorization q ≤ M :=
    (Nat.le_of_dvd ht_pos hmul_dvd).trans (hC.2.2.1 t htA)
  rcases le_total (p ^ (A.lcm id).factorization p) (q ^ (A.lcm id).factorization q) with hle | hle
  · have hsq : (p ^ (A.lcm id).factorization p) ^ 2 ≤
        p ^ (A.lcm id).factorization p * q ^ (A.lcm id).factorization q := by
      rw [sq]; exact Nat.mul_le_mul_left _ hle
    omega
  · have hsq : (q ^ (A.lcm id).factorization q) ^ 2 ≤
        p ^ (A.lcm id).factorization p * q ^ (A.lcm id).factorization q := by
      rw [sq]; exact Nat.mul_le_mul_right _ hle
    omega

private lemma fac_eq_of_pow_dvd_not {n p k : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hpk : p ^ k ∣ n) (hnk : ¬ p ^ (k + 1) ∣ n) : n.factorization p = k := by
  have h1 := (hp.pow_dvd_iff_le_factorization hn).mp hpk
  have h2 : ¬ k + 1 ≤ n.factorization p := fun h => hnk ((hp.pow_dvd_iff_le_factorization hn).mpr h)
  omega

private lemma core_pow_le5_dvd_60 {n : ℕ} (hn0 : n ≠ 0)
    (h5 : ∀ p : ℕ, p.Prime → p ∣ n → p ^ n.factorization p ≤ 5) : n ∣ 60 := by
  rw [← Nat.factorization_le_iff_dvd hn0 (by decide : (60 : ℕ) ≠ 0)]
  intro p
  by_cases hp : p.Prime
  · by_cases hpn : p ∣ n
    · have hle := h5 p hp hpn
      have h60_2 : (60 : ℕ).factorization 2 = 2 :=
        fac_eq_of_pow_dvd_not Nat.prime_two (by decide) (by decide) (by decide)
      have h60_3 : (60 : ℕ).factorization 3 = 1 :=
        fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
      have h60_5 : (60 : ℕ).factorization 5 = 1 :=
        fac_eq_of_pow_dvd_not Nat.prime_five (by decide) (by decide) (by decide)
      by_cases hp2 : p = 2
      · subst hp2
        have hlt : n.factorization 2 < 3 := by
          by_contra hge; push Not at hge
          have : 8 ≤ 2 ^ n.factorization 2 := by
            calc 8 = 2 ^ 3 := by decide
            _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by omega) hge
          omega
        omega
      · by_cases hp3 : p = 3
        · subst hp3
          have hlt : n.factorization 3 < 2 := by
            by_contra hge; push Not at hge
            have : 9 ≤ 3 ^ n.factorization 3 := by
              calc 9 = 3 ^ 2 := by decide
              _ ≤ 3 ^ n.factorization 3 := Nat.pow_le_pow_right (by omega) hge
            omega
          omega
        · by_cases hp5 : p = 5
          · subst hp5
            have hlt : n.factorization 5 < 2 := by
              by_contra hge; push Not at hge
              have : 25 ≤ 5 ^ n.factorization 5 := by
                calc 25 = 5 ^ 2 := by decide
                _ ≤ 5 ^ n.factorization 5 := Nat.pow_le_pow_right (by omega) hge
              omega
            omega
          · have hp6 : 6 ≤ p := by
              rcases Nat.lt_or_ge p 6 with h | h; · interval_cases p <;> contradiction
              · exact h
            have h1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).mp hpn
            have : 6 ≤ p ^ n.factorization p :=
              calc 6 ≤ p := hp6
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hp.pos h1
            omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]; exact Nat.zero_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma decide_case1_no_heavy :
    ((List.range 61).all fun lo =>
      (([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ).filter
        (fun d => lo ≤ d ∧ d < 2 * lo)).length < 5) = true := by
  decide

private lemma decide_case1_heavy_d3 :
    ((List.range 61).all fun lo =>
      let ds := ([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ).filter
        (fun d => lo ≤ d ∧ d < 2 * lo ∧ d ≤ 10)
      ds.length ≤ 3 ∧ (ds.length = 3 → ds = [3, 4, 5] ∨ ds = [4, 5, 6])) = true := by
  decide

private lemma dvd_60_mem_list {d : ℕ} (hd0 : 0 < d) (hd : d ∣ 60) :
    d ∈ ([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ) := by
  have hd_le : d ≤ 60 := Nat.le_of_dvd (by decide) hd
  have h : (List.range 61).all (fun n => decide (0 < n → n ∣ 60 →
      n ∈ ([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ))) = true := by decide
  rw [List.all_eq_true] at h
  exact (of_decide_eq_true (h d (List.mem_range.mpr (by omega)))) hd0 hd

private lemma exists_three_lt_of_three_le_card {D : Finset ℕ} (hD : 3 ≤ D.card) :
    ∃ d₁ d₂ d₃ : ℕ, d₁ ∈ D ∧ d₂ ∈ D ∧ d₃ ∈ D ∧ d₁ < d₂ ∧ d₂ < d₃ := by
  obtain ⟨S, hSD, hS3⟩ := Finset.exists_subset_card_eq hD
  obtain ⟨a, b, c, hab, hac, hbc, hS_eq⟩ := Finset.card_eq_three.mp hS3
  have ha : a ∈ D := hSD (by rw [hS_eq]; simp)
  have hb : b ∈ D := hSD (by rw [hS_eq]; simp)
  have hc : c ∈ D := hSD (by rw [hS_eq]; simp)
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨a, b, c, ha, hb, hc, hab', hbc'⟩
      · exact ⟨a, c, b, ha, hc, hb, hac', hcb'⟩
    · exact ⟨c, a, b, hc, ha, hb, hca', hab'⟩
  · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
    · rcases lt_or_gt_of_ne hac with hac' | hca'
      · exact ⟨b, a, c, hb, ha, hc, hba', hac'⟩
      · exact ⟨b, c, a, hb, hc, ha, hbc', hca'⟩
    · exact ⟨c, b, a, hc, hb, ha, hcb', hba'⟩

private lemma core_case1_no_three_set {A : Finset ℕ} {M : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M)
    (hno3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card ≤ 2) : False := by
  have hL_pos := finset_lcm_pos_core hC.2.1
  by_cases h_heavy : ∃ q : ℕ, q.Prime ∧ q ∣ A.lcm id ∧ M < (q ^ (A.lcm id).factorization q) ^ 2
  · obtain ⟨q, hq, hqL, hq_hv⟩ := h_heavy
    have hZp_le2 := hno3 q hq hqL
    have ⟨he_q, hsum_q, hT2, hZ1, _, h3Q⟩ := core_Z_T_props hC hq hqL
    let e_q := (A.lcm id).factorization q
    let Q := q ^ e_q
    let Zq := A.filter (fun a => a.factorization q < e_q)
    let Tq := A.filter (fun a => a.factorization q = e_q)
    have hTq_ge3 : 3 ≤ Tq.card := by dsimp [Tq, e_q]; omega
    have hQ_pos : 0 < Q := pow_pos hq.pos e_q
    let D := Tq.image (· / Q)
    have hD_card : D.card = Tq.card := by
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      dsimp only at hxy
      have hxQ : Q ∣ x := (hq.pow_dvd_iff_le_factorization (hC.2.1 x (Finset.mem_filter.mp hx).1).ne').mpr
        (by rw [(Finset.mem_filter.mp hx).2])
      have hyQ : Q ∣ y := (hq.pow_dvd_iff_le_factorization (hC.2.1 y (Finset.mem_filter.mp hy).1).ne').mpr
        (by rw [(Finset.mem_filter.mp hy).2])
      rw [← Nat.mul_div_cancel' hxQ, ← Nat.mul_div_cancel' hyQ, hxy]
    have hD_props : ∀ d ∈ D, 0 < d ∧ Q * d ≤ M ∧ M < 2 * (Q * d) ∧ d < Q ∧ d.factorization q = 0 := by
      intro d hd
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp hd
      have htA := (Finset.mem_filter.mp htT).1
      have hte := (Finset.mem_filter.mp htT).2
      have htQ : Q ∣ t := (hq.pow_dvd_iff_le_factorization (hC.2.1 t htA).ne').mpr (by rw [hte])
      have hmul : Q * (t / Q) = t := Nat.mul_div_cancel' htQ
      have hd0 : 0 < t / Q := Nat.div_pos (Nat.le_of_dvd (hC.2.1 t htA) htQ) hQ_pos
      have hQM : Q * (t / Q) ≤ M := hmul.symm ▸ hC.2.2.1 t htA
      have h2Q : M < 2 * (Q * (t / Q)) := hmul.symm ▸ hC.2.2.2.1 t htA
      have hdQ : t / Q < Q := by
        have hsq : Q * (t / Q) < Q * Q := lt_of_le_of_lt hQM (by simpa [sq] using hq_hv)
        exact Nat.lt_of_mul_lt_mul_left hsq
      have hfac0 : (t / Q).factorization q = 0 := by
        rw [Nat.factorization_div htQ]
        dsimp [Q]
        simp only [Nat.Prime.factorization_pow hq, Finsupp.single_eq_same]
        dsimp [e_q] at hte; omega
      exact ⟨hd0, hQM, h2Q, hdQ, hfac0⟩
    have hq_not_small : ∀ p, p.Prime → p ∣ A.lcm id → p ≠ q →
        p ^ (A.lcm id).factorization p ≤ 5 := by
      intro p hp hpL hpq
      rcases core_claimA hC hNR1 hp hpL (hno3 p hp hpL) with hle5 | hhv
      · exact hle5
      · exact False.elim (core_at_most_one_heavy hC hq hqL hp hpL hpq.symm hZp_le2 (hno3 p hp hpL) hq_hv hhv)
    have hD_dvd60 : ∀ a ∈ A, a.factorization q = 0 → a ∣ 60 := by
      intro a ha haq0
      refine core_pow_le5_dvd_60 (hC.2.1 a ha).ne' fun p hp hpa => ?_
      by_cases hpq : p = q
      · subst hpq
        have := (hp.dvd_iff_one_le_factorization (hC.2.1 a ha).ne').mp hpa
        omega
      · have hpL : p ∣ A.lcm id := dvd_trans hpa (Finset.dvd_lcm ha)
        have hfac_le := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm ha) (p := p)
        exact le_trans (Nat.pow_le_pow_right hp.pos hfac_le) (hq_not_small p hp hpL hpq)
    obtain ⟨z₀, hz0A, hz0q⟩ := gcd_one_exists_fac_zero hq hC.2.2.2.2.1 hC.2.1
    have hz0_dvd60 : z₀ ∣ 60 := hD_dvd60 z₀ hz0A hz0q
    have hM_lt120 : M < 120 := by
      have hz0_le : z₀ ≤ 60 := Nat.le_of_dvd (by decide) hz0_dvd60
      exact lt_of_lt_of_le (hC.2.2.2.1 z₀ hz0A) (by omega)
    have hD_le10 : ∀ d ∈ D, d ≤ 10 := by
      intro d hd
      have ⟨_, hQM, _, hdQ, _⟩ := hD_props d hd
      have hsq : d * d < Q * d := Nat.mul_lt_mul_of_pos_right hdQ (hD_props d hd).1
      have h120 : d * d < 120 := lt_of_lt_of_le hsq (le_trans hQM (by omega))
      by_contra h11; push Not at h11
      have : 121 ≤ d * d := Nat.mul_le_mul h11 h11
      omega
    have hD_sub60 : ∀ d ∈ D, d ∣ 60 := by
      intro d hd
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp hd
      have htA := (Finset.mem_filter.mp htT).1
      have htQ : Q ∣ t := (hq.pow_dvd_iff_le_factorization (hC.2.1 t htA).ne').mpr
        (by rw [(Finset.mem_filter.mp htT).2])
      have hdiv_pos := Nat.div_pos (Nat.le_of_dvd (hC.2.1 t htA) htQ) hQ_pos
      refine core_pow_le5_dvd_60 hdiv_pos.ne' fun p hp hpd => ?_
      by_cases hpq : p = q
      · subst hpq
        have h0 := (hD_props (t / Q) hd).2.2.2.2
        have := (hp.dvd_iff_one_le_factorization hdiv_pos.ne').mp hpd
        omega
      · have hpt : p ∣ t := dvd_trans hpd (Nat.div_dvd_of_dvd htQ)
        have hpL : p ∣ A.lcm id := dvd_trans hpt (Finset.dvd_lcm htA)
        have hfac1 : (t / Q).factorization p ≤ t.factorization p := by
          rw [Nat.factorization_div htQ]; simp
        have hfac2 := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm htA) (p := p)
        exact le_trans (Nat.pow_le_pow_right hp.pos (le_trans hfac1 hfac2)) (hq_not_small p hp hpL hpq)
    have hD_nonempty : D.Nonempty := Finset.card_pos.mp (by omega)
    let d₀ := D.min' hD_nonempty
    have hd0_D : d₀ ∈ D := Finset.min'_mem D hD_nonempty
    have hd0_le10 : d₀ ≤ 10 := hD_le10 d₀ hd0_D
    let ds := ([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ).filter
      (fun d => d₀ ≤ d ∧ d < 2 * d₀ ∧ d ≤ 10)
    have hD_sub_ds : ∀ d ∈ D, d ∈ ds := by
      intro d hd
      have hd_min : d₀ ≤ d := Finset.min'_le D d hd
      have hlt2 : d < 2 * d₀ := by
        have ⟨_, hQM, _, _, _⟩ := hD_props d hd
        have ⟨_, _, h2Q0, _, _⟩ := hD_props d₀ hd0_D
        have hQd : Q * d < Q * (2 * d₀) := by
          calc Q * d ≤ M := hQM
            _ < 2 * (Q * d₀) := h2Q0
            _ = Q * (2 * d₀) := by ring
        exact Nat.lt_of_mul_lt_mul_left hQd
      have hmem60 := dvd_60_mem_list (hD_props d hd).1 (hD_sub60 d hd)
      simp only [ds, List.mem_filter, decide_eq_true_eq]
      exact ⟨hmem60, hd_min, hlt2, hD_le10 d hd⟩
    have hdec := decide_case1_heavy_d3
    rw [List.all_eq_true] at hdec
    have hdec_d0 := of_decide_eq_true (hdec d₀ (List.mem_range.mpr (by omega)))
    have hds_le3 : ds.length ≤ 3 := hdec_d0.1
    have hD_le_ds : D.card ≤ ds.length := by
      calc D.card ≤ ds.toFinset.card := Finset.card_le_card (fun d hd => List.mem_toFinset.mpr (hD_sub_ds d hd))
      _ ≤ ds.length := List.toFinset_card_le ds
    have hD3 : D.card = 3 := by omega
    have hds3 : ds.length = 3 := by omega
    have hTq3 : Tq.card = 3 := by omega
    have hZq2 : Zq.card = 2 := by change Zq.card + Tq.card = 5 at hsum_q; omega
    have hds_cases : ds = [3, 4, 5] ∨ ds = [4, 5, 6] := hdec_d0.2 hds3
    have hD_eq_ds : ∀ x, x ∈ ds → x ∈ D := by
      by_contra hmiss; push Not at hmiss
      obtain ⟨x, hxds, hxD⟩ := hmiss
      have hsub_erase : D ⊆ ds.toFinset.erase x := fun y hy =>
        Finset.mem_erase.mpr ⟨fun h => hxD (h ▸ hy), List.mem_toFinset.mpr (hD_sub_ds y hy)⟩
      have h1 : D.card ≤ (ds.toFinset.erase x).card := Finset.card_le_card hsub_erase
      have h2 : (ds.toFinset.erase x).card < ds.toFinset.card :=
        Finset.card_erase_lt_of_mem (List.mem_toFinset.mpr hxds)
      have h3 := List.toFinset_card_le ds
      omega
    have h_mul345 : 4 ∈ D ∧ 5 ∈ D ∧ (3 ∈ D ∨ 6 ∈ D) := by
      rcases hds_cases with h | h
      · change ds = [3, 4, 5] at h
        exact ⟨hD_eq_ds 4 (h ▸ by simp), hD_eq_ds 5 (h ▸ by simp), Or.inl (hD_eq_ds 3 (h ▸ by simp))⟩
      · change ds = [4, 5, 6] at h
        exact ⟨hD_eq_ds 4 (h ▸ by simp), hD_eq_ds 5 (h ▸ by simp), Or.inr (hD_eq_ds 6 (h ▸ by simp))⟩
    obtain ⟨h4D, h5D, h36D⟩ := h_mul345
    have hq_ge7 : 7 ≤ q := by
      have h4_q0 := (hD_props 4 h4D).2.2.2.2
      have h5_q0 := (hD_props 5 h5D).2.2.2.2
      have hq2 : q ≠ 2 := fun h => by
        subst h
        have h42 : (4 : ℕ).factorization 2 = 2 :=
          fac_eq_of_pow_dvd_not Nat.prime_two (by decide) (by decide) (by decide)
        omega
      have hq3 : q ≠ 3 := fun h => by
        subst h
        rcases h36D with h3D | h6D
        · have h30 := (hD_props 3 h3D).2.2.2.2
          have h33 : (3 : ℕ).factorization 3 = 1 :=
            fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
          omega
        · have h60 := (hD_props 6 h6D).2.2.2.2
          have h63 : (6 : ℕ).factorization 3 = 1 :=
            fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
          omega
      have hq5 : q ≠ 5 := fun h => by
        subst h
        have h55 : (5 : ℕ).factorization 5 = 1 :=
          fac_eq_of_pow_dvd_not Nat.prime_five (by decide) (by decide) (by decide)
        omega
      rcases Nat.lt_or_ge q 7 with h | h
      · interval_cases q
        all_goals first | exact absurd hq Nat.not_prime_zero | exact absurd hq Nat.not_prime_one | contradiction
      · exact h
    have hQ_lt40 : Q < 40 := by
      have ⟨_, hQM4, _, _, _⟩ := hD_props 4 h4D
      omega
    have heq1 : e_q = 1 := by
      by_contra hne1
      have h2 : 2 ≤ e_q := by omega
      have : 49 ≤ Q := by
        calc 49 = 7 ^ 2 := by decide
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq_ge7 2
        _ ≤ q ^ e_q := Nat.pow_le_pow_right hq.pos h2
      omega
    obtain ⟨z₁, z₂, hz12, hZq_eq⟩ := Finset.card_eq_two.mp hZq2
    have hz1Z : z₁ ∈ Zq := by rw [hZq_eq]; simp
    have hz2Z : z₂ ∈ Zq := by rw [hZq_eq]; simp
    have hz1q0 : z₁.factorization q = 0 := by have := (Finset.mem_filter.mp hz1Z).2; omega
    have hz2q0 : z₂.factorization q = 0 := by have := (Finset.mem_filter.mp hz2Z).2; omega
    have hz1_dvd60 : z₁ ∣ 60 := hD_dvd60 z₁ (Finset.mem_filter.mp hz1Z).1 hz1q0
    have hz2_dvd60 : z₂ ∣ 60 := hD_dvd60 z₂ (Finset.mem_filter.mp hz2Z).1 hz2q0
    have h_outside_Z : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
        (∃ t₁ ∈ Tq, ∃ t₂ ∈ Tq, t₁ ≠ t₂ ∧
          t₁.factorization p < (A.lcm id).factorization p ∧
          t₂.factorization p < (A.lcm id).factorization p) →
        z₁.factorization p = (A.lcm id).factorization p ∧
        z₂.factorization p = (A.lcm id).factorization p := by
      intro p hp hpL ⟨t₁, ht1T, t₂, ht2T, ht12, hlt1, hlt2⟩
      let Zp := A.filter (fun a => a.factorization p < (A.lcm id).factorization p)
      have ht1Zp : t₁ ∈ Zp := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht1T).1, hlt1⟩
      have ht2Zp : t₂ ∈ Zp := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht2T).1, hlt2⟩
      have hZp_le := hno3 p hp hpL
      have hZp_eq2 : Zp = {t₁, t₂} := by
        refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · rw [Finset.card_pair ht12]; exact hZp_le
      have hnotZp : ∀ z ∈ Zq, z ∉ Zp := fun z hz hzp => by
        rw [hZp_eq2, Finset.mem_insert, Finset.mem_singleton] at hzp
        have hfz := (Finset.mem_filter.mp hz).2
        rcases hzp with rfl | rfl
        · have := (Finset.mem_filter.mp ht1T).2; omega
        · have := (Finset.mem_filter.mp ht2T).2; omega
      have hfac_eq : ∀ z ∈ Zq, z.factorization p = (A.lcm id).factorization p := fun z hz => by
        have hzA := (Finset.mem_filter.mp hz).1
        have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm hzA) (p := p)
        simp only [id_eq] at hle
        by_contra hne
        exact hnotZp z hz (Finset.mem_filter.mpr ⟨hzA, by omega⟩)
      exact ⟨hfac_eq z₁ hz1Z, hfac_eq z₂ hz2Z⟩
    have hD_to_T : ∀ d ∈ D, Q * d ∈ Tq := fun d hd => by
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp hd
      have htQ : Q ∣ t := (hq.pow_dvd_iff_le_factorization (hC.2.1 t (Finset.mem_filter.mp htT).1).ne').mpr
        (by rw [(Finset.mem_filter.mp htT).2])
      rwa [Nat.mul_div_cancel' htQ]
    have hQ_fac_zero : ∀ p : ℕ, p.Prime → p ≠ q → Q.factorization p = 0 := fun p hp hpq => by
      dsimp [Q]; rw [Nat.Prime.factorization_pow hq, Finsupp.single_apply, if_neg hpq.symm]
    have hQd_fac : ∀ p d : ℕ, p.Prime → p ≠ q → 0 < d →
        (Q * d).factorization p = d.factorization p := fun p d hp hpq hd0 => by
      rw [Nat.factorization_mul hQ_pos.ne' hd0.ne', Finsupp.coe_add, Pi.add_apply, hQ_fac_zero p hp hpq, zero_add]
    have h2_4v : (4 : ℕ).factorization 2 = 2 :=
      fac_eq_of_pow_dvd_not Nat.prime_two (by decide) (by decide) (by decide)
    have h5_2v : (5 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h3_2v : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h6_2v : (6 : ℕ).factorization 2 = 1 :=
      fac_eq_of_pow_dvd_not Nat.prime_two (by decide) (by decide) (by decide)
    have h3_3v : (3 : ℕ).factorization 3 = 1 :=
      fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
    have h6_3v : (6 : ℕ).factorization 3 = 1 :=
      fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
    have h4_3v : (4 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h5_3v : (5 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h5_5v : (5 : ℕ).factorization 5 = 1 :=
      fac_eq_of_pow_dvd_not Nat.prime_five (by decide) (by decide) (by decide)
    have h4_5v : (4 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h3_5v : (3 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h6_5v : (6 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
    -- p = 2:
    have h2_out : 2 ≤ z₁.factorization 2 ∧ 2 ≤ z₂.factorization 2 := by
      have h2_4 : 2 ≤ (Q * 4).factorization 2 := by
        rw [hQd_fac 2 4 Nat.prime_two (by omega) (by decide), h2_4v]
      have h2L : 2 ≤ (A.lcm id).factorization 2 :=
        le_trans h2_4 (fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (Finset.mem_filter.mp (hD_to_T 4 h4D)).1))
      have hp2L : 2 ∣ A.lcm id := (Nat.prime_two.dvd_iff_one_le_factorization hL_pos.ne').mpr (by omega)
      have h2_5 : (Q * 5).factorization 2 < (A.lcm id).factorization 2 := by
        rw [hQd_fac 2 5 Nat.prime_two (by omega) (by decide), h5_2v]; omega
      have hother : ∃ d ∈ D, d ≠ 5 ∧ (Q * d).factorization 2 < (A.lcm id).factorization 2 := by
        rcases h36D with h3D | h6D
        · refine ⟨3, h3D, by decide, ?_⟩
          rw [hQd_fac 2 3 Nat.prime_two (by omega) (by decide), h3_2v]; omega
        · refine ⟨6, h6D, by decide, ?_⟩
          rw [hQd_fac 2 6 Nat.prime_two (by omega) (by decide), h6_2v]; omega
      obtain ⟨d', hd'D, hd'5, hd'2⟩ := hother
      have ⟨h1, h2⟩ := h_outside_Z 2 Nat.prime_two hp2L
        ⟨Q * 5, hD_to_T 5 h5D, Q * d', hD_to_T d' hd'D, fun h => hd'5 (Nat.mul_left_cancel hQ_pos h).symm, h2_5, hd'2⟩
      omega
    -- p = 3:
    have h3_out : 1 ≤ z₁.factorization 3 ∧ 1 ≤ z₂.factorization 3 := by
      have h3_ex : ∃ d3 ∈ D, 1 ≤ (Q * d3).factorization 3 := by
        rcases h36D with h3D | h6D
        · exact ⟨3, h3D, by rw [hQd_fac 3 3 Nat.prime_three (by omega) (by decide), h3_3v]⟩
        · exact ⟨6, h6D, by rw [hQd_fac 3 6 Nat.prime_three (by omega) (by decide), h6_3v]⟩
      obtain ⟨d3, hd3D, hd3_v⟩ := h3_ex
      have h3L : 1 ≤ (A.lcm id).factorization 3 :=
        le_trans hd3_v (fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (Finset.mem_filter.mp (hD_to_T d3 hd3D)).1))
      have hp3L : 3 ∣ A.lcm id := (Nat.prime_three.dvd_iff_one_le_factorization hL_pos.ne').mpr (by omega)
      have h3_4 : (Q * 4).factorization 3 < (A.lcm id).factorization 3 := by
        rw [hQd_fac 3 4 Nat.prime_three (by omega) (by decide), h4_3v]; omega
      have h3_5 : (Q * 5).factorization 3 < (A.lcm id).factorization 3 := by
        rw [hQd_fac 3 5 Nat.prime_three (by omega) (by decide), h5_3v]; omega
      have ⟨h1, h2⟩ := h_outside_Z 3 Nat.prime_three hp3L
        ⟨Q * 4, hD_to_T 4 h4D, Q * 5, hD_to_T 5 h5D, fun h => by have := Nat.mul_left_cancel hQ_pos h; omega, h3_4, h3_5⟩
      omega
    -- p = 5:
    have h5_out : 1 ≤ z₁.factorization 5 ∧ 1 ≤ z₂.factorization 5 := by
      have h5_5 : 1 ≤ (Q * 5).factorization 5 := by
        rw [hQd_fac 5 5 Nat.prime_five (by omega) (by decide), h5_5v]
      have h5L : 1 ≤ (A.lcm id).factorization 5 :=
        le_trans h5_5 (fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (Finset.mem_filter.mp (hD_to_T 5 h5D)).1))
      have hp5L : 5 ∣ A.lcm id := (Nat.prime_five.dvd_iff_one_le_factorization hL_pos.ne').mpr (by omega)
      have h5_4 : (Q * 4).factorization 5 < (A.lcm id).factorization 5 := by
        rw [hQd_fac 5 4 Nat.prime_five (by omega) (by decide), h4_5v]; omega
      have hother : ∃ d ∈ D, d ≠ 4 ∧ (Q * d).factorization 5 < (A.lcm id).factorization 5 := by
        rcases h36D with h3D | h6D
        · refine ⟨3, h3D, by decide, ?_⟩
          rw [hQd_fac 5 3 Nat.prime_five (by omega) (by decide), h3_5v]; omega
        · refine ⟨6, h6D, by decide, ?_⟩
          rw [hQd_fac 5 6 Nat.prime_five (by omega) (by decide), h6_5v]; omega
      obtain ⟨d', hd'D, hd'4, hd'5⟩ := hother
      have ⟨h1, h2⟩ := h_outside_Z 5 Nat.prime_five hp5L
        ⟨Q * 4, hD_to_T 4 h4D, Q * d', hD_to_T d' hd'D, fun h => hd'4 (Nat.mul_left_cancel hQ_pos h).symm, h5_4, hd'5⟩
      omega
    have h60_z : ∀ z ∈ ({z₁, z₂} : Finset ℕ),
        2 ≤ z.factorization 2 → 1 ≤ z.factorization 3 → 1 ≤ z.factorization 5 → z ∣ 60 → z = 60 := by
      intro z _hz hz2 hz3 hz5 hzdvd
      have hz_pos : 0 < z := Nat.pos_of_dvd_of_pos hzdvd (by decide)
      have h60_2 : (60 : ℕ).factorization 2 = 2 :=
        fac_eq_of_pow_dvd_not Nat.prime_two (by decide) (by decide) (by decide)
      have h60_3 : (60 : ℕ).factorization 3 = 1 :=
        fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
      have h60_5 : (60 : ℕ).factorization 5 = 1 :=
        fac_eq_of_pow_dvd_not Nat.prime_five (by decide) (by decide) (by decide)
      have h60_dvd_z : 60 ∣ z := by
        rw [← Nat.factorization_le_iff_dvd (by decide) hz_pos.ne']
        intro p
        by_cases hp2 : p = 2; · subst hp2; omega
        by_cases hp3 : p = 3; · subst hp3; omega
        by_cases hp5 : p = 5; · subst hp5; omega
        have h60_0 : (60 : ℕ).factorization p = 0 := by
          by_contra hne0
          have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization 60 ▸ Finsupp.mem_support_iff.mpr hne0)
          have hpd : p ∣ 2 * 2 * 3 * 5 := (hp_pr.dvd_iff_one_le_factorization (by decide)).mpr (Nat.pos_of_ne_zero hne0)
          rcases hp_pr.dvd_mul.mp hpd with h223 | h5
          · rcases hp_pr.dvd_mul.mp h223 with h22 | h3
            · rcases hp_pr.dvd_mul.mp h22 with h2 | h2
              · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp h2)
              · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp h2)
            · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_three).mp h3)
          · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_five).mp h5)
        rw [h60_0]; exact Nat.zero_le _
      exact Nat.dvd_antisymm hzdvd h60_dvd_z
    have hz1_60 := h60_z z₁ (by simp) h2_out.1 h3_out.1 h5_out.1 hz1_dvd60
    have hz2_60 := h60_z z₂ (by simp) h2_out.2 h3_out.2 h5_out.2 hz2_dvd60
    exact hz12 (hz1_60.trans hz2_60.symm)
  · push Not at h_heavy
    have hL_dvd60 : A.lcm id ∣ 60 := by
      refine core_pow_le5_dvd_60 hL_pos.ne' fun p hp hpL => ?_
      rcases core_claimA hC hNR1 hp hpL (hno3 p hp hpL) with hle5 | hhv
      · exact hle5
      · exact False.elim ((lt_irrefl _) (lt_of_lt_of_le hhv (h_heavy p hp hpL)))
    have hAc : A.card = 5 := hC.1
    have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega : 0 < A.card)
    let lo := A.min' hA_ne
    have hloA : lo ∈ A := Finset.min'_mem A hA_ne
    have hlo_le60 : lo ≤ 60 := Nat.le_of_dvd (by decide) (dvd_trans (Finset.dvd_lcm (f := id) hloA) hL_dvd60)
    let ds := ([1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ).filter (fun d => lo ≤ d ∧ d < 2 * lo)
    have hA_sub_ds : A ⊆ ds.toFinset := by
      intro a ha
      have ha60 : a ∣ 60 := dvd_trans (Finset.dvd_lcm (f := id) ha) hL_dvd60
      have hmem60 := dvd_60_mem_list (hC.2.1 a ha) ha60
      have hge : lo ≤ a := Finset.min'_le A a ha
      have hlt2 : a < 2 * lo := lt_of_le_of_lt (hC.2.2.1 a ha) (hC.2.2.2.1 lo hloA)
      rw [List.mem_toFinset]
      simp only [ds, List.mem_filter, decide_eq_true_eq]
      exact ⟨hmem60, hge, hlt2⟩
    have hdec := decide_case1_no_heavy
    rw [List.all_eq_true] at hdec
    have hdec_lo := hdec lo (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hdec_lo
    have hcard_lt : A.card < 5 :=
      lt_of_le_of_lt (Finset.card_le_card hA_sub_ds) (lt_of_le_of_lt (List.toFinset_card_le ds) hdec_lo)
    omega

/-! ## Part 3: Case II (3-Set Decomposition, `Q_k | 60` Closures, `Z_B`-Swap, `r = 1`) -/

private structure ThreeSetProps (A Z : Finset ℕ)
    (a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ) : Prop where
  hZ_eq : Z = {a₁, a₂, a₃}
  ha12 : a₁ < a₂
  ha23 : a₂ < a₃
  hA_eq : A = {a₁, a₂, a₃, a₄, a₅}
  ha45 : a₄ ≠ a₅
  ha4Z : a₄ ∉ Z
  ha5Z : a₅ ∉ Z
  hL3_pos : 0 < L₃
  hg3_pos : 0 < g₃
  hL3_lcm : L₃ = Z.lcm id
  hL3_12 : Nat.lcm a₁ a₂ = L₃
  hL3_13 : Nat.lcm a₁ a₃ = L₃
  hL3_23 : Nat.lcm a₂ a₃ = L₃
  ha1_eq : a₁ = g₃ * Q₂ * Q₃
  ha2_eq : a₂ = g₃ * Q₁ * Q₃
  ha3_eq : a₃ = g₃ * Q₁ * Q₂
  hL3_eq : L₃ = g₃ * Q₁ * Q₂ * Q₃
  hQ3_lt : Q₃ < Q₂
  hQ2_lt : Q₂ < Q₁
  hQ1_lt : Q₁ < 2 * Q₃
  hQ3_ge3 : 3 ≤ Q₃
  hQ2_ge4 : 4 ≤ Q₂
  hQ1_ge5 : 5 ≤ Q₁
  hcop12 : Nat.Coprime Q₁ Q₂
  hcop13 : Nat.Coprime Q₁ Q₃
  hcop23 : Nat.Coprime Q₂ Q₃
  hngcd : ¬ (Nat.gcd a₄ a₅ ∣ L₃)

private lemma exists_three_set_props {A : Finset ℕ} {M p₀ : ℕ}
    (hC : C5Core A M) (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id)
    (hZ3 : (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 3) :
    ∃ a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ,
      ThreeSetProps A (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
        a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ := by
  let Z := A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)
  have hZ_card : Z.card = 3 := hZ3
  obtain ⟨a₁, a₂, a₃, ha1Z, ha2Z, ha3Z, ha12, ha23⟩ :=
    exists_three_lt_of_three_le_card (by omega : 3 ≤ Z.card)
  have ha13 : a₁ < a₃ := lt_trans ha12 ha23
  have hZ_sub_A : Z ⊆ A := Finset.filter_subset _ _
  have hZ_eq : Z = {a₁, a₂, a₃} := by
    refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [ha12.ne, ha13.ne]),
          Finset.card_insert_of_notMem (by simp [ha23.ne]), Finset.card_singleton]; omega
  have hRem2 : (A \ Z).card = 2 := by
    rw [Finset.card_sdiff_of_subset hZ_sub_A, hC.1, hZ_card]
  obtain ⟨a₄, a₅, ha45, hRem_eq⟩ := Finset.card_eq_two.mp hRem2
  have ha4Rem : a₄ ∈ A \ Z := by rw [hRem_eq]; simp
  have ha5Rem : a₅ ∈ A \ Z := by rw [hRem_eq]; simp
  have ha4A : a₄ ∈ A := (Finset.mem_sdiff.mp ha4Rem).1
  have ha5A : a₅ ∈ A := (Finset.mem_sdiff.mp ha5Rem).1
  have ha4Z : a₄ ∉ Z := (Finset.mem_sdiff.mp ha4Rem).2
  have ha5Z : a₅ ∉ Z := (Finset.mem_sdiff.mp ha5Rem).2
  have hA_eq : A = {a₁, a₂, a₃, a₄, a₅} := by
    have hun : Z ∪ (A \ Z) = A := Finset.union_sdiff_of_subset hZ_sub_A
    rw [← hun, hRem_eq, hZ_eq]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hpc := core_fact1_three_pairconst hC hp0 hp0L hZ3
  let L₃ := Z.lcm id
  have hL3_pos : 0 < L₃ := finset_lcm_pos_core fun z hz => hC.2.1 z (hZ_sub_A hz)
  have hL3_12 : Nat.lcm a₁ a₂ = L₃ := hpc a₁ ha1Z a₂ ha2Z ha12.ne
  have hL3_13 : Nat.lcm a₁ a₃ = L₃ := hpc a₁ ha1Z a₃ ha3Z ha13.ne
  have hL3_23 : Nat.lcm a₂ a₃ = L₃ := hpc a₂ ha2Z a₃ ha3Z ha23.ne
  have ha1_pos := hC.2.1 a₁ (hZ_sub_A ha1Z)
  have ha2_pos := hC.2.1 a₂ (hZ_sub_A ha2Z)
  have ha3_pos := hC.2.1 a₃ (hZ_sub_A ha3Z)
  have hdvd1 : a₁ ∣ L₃ := Finset.dvd_lcm ha1Z
  have hdvd2 : a₂ ∣ L₃ := Finset.dvd_lcm ha2Z
  have hdvd3 : a₃ ∣ L₃ := Finset.dvd_lcm ha3Z
  let Q₁ := L₃ / a₁
  let Q₂ := L₃ / a₂
  let Q₃ := L₃ / a₃
  have hQ1_pos : 0 < Q₁ := Nat.div_pos (Nat.le_of_dvd hL3_pos hdvd1) ha1_pos
  have hQ2_pos : 0 < Q₂ := Nat.div_pos (Nat.le_of_dvd hL3_pos hdvd2) ha2_pos
  have hQ3_pos : 0 < Q₃ := Nat.div_pos (Nat.le_of_dvd hL3_pos hdvd3) ha3_pos
  have ha1Q1 : a₁ * Q₁ = L₃ := Nat.mul_div_cancel' hdvd1
  have ha2Q2 : a₂ * Q₂ = L₃ := Nat.mul_div_cancel' hdvd2
  have ha3Q3 : a₃ * Q₃ = L₃ := Nat.mul_div_cancel' hdvd3
  have cop_of_lcm : ∀ u v Qu Qv : ℕ, 0 < u → 0 < v → 0 < Qu → 0 < Qv →
      u * Qu = L₃ → v * Qv = L₃ →
      Nat.lcm u v = L₃ → Nat.Coprime Qu Qv := by
    intro u v Qu Qv hu0 hv0 hQu_pos hQv_pos huQ hvQ hlcm
    by_contra hnc
    have hgcd1 : Nat.gcd Qu Qv ≠ 1 := hnc
    have hgcd_pos : 0 < Nat.gcd Qu Qv := Nat.gcd_pos_of_pos_left Qv hQu_pos
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hgcd1
    have hqQu : q ∣ Qu := dvd_trans hqd (Nat.gcd_dvd_left Qu Qv)
    have hqQv : q ∣ Qv := dvd_trans hqd (Nat.gcd_dvd_right Qu Qv)
    have hf1 := congrArg (fun n => n.factorization q) huQ
    have hf2 := congrArg (fun n => n.factorization q) hvQ
    rw [Nat.factorization_mul hu0.ne' hQu_pos.ne', Finsupp.coe_add, Pi.add_apply] at hf1
    rw [Nat.factorization_mul hv0.ne' hQv_pos.ne', Finsupp.coe_add, Pi.add_apply] at hf2
    have h1 : 1 ≤ Qu.factorization q := (hq.dvd_iff_one_le_factorization hQu_pos.ne').mp hqQu
    have h2 : 1 ≤ Qv.factorization q := (hq.dvd_iff_one_le_factorization hQv_pos.ne').mp hqQv
    have hl : L₃.factorization q = max (u.factorization q) (v.factorization q) := by
      rw [← hlcm, fac_lcm_eq_max_5 hu0.ne' hv0.ne']
    omega
  have hcop12 : Nat.Coprime Q₁ Q₂ := cop_of_lcm a₁ a₂ Q₁ Q₂ ha1_pos ha2_pos hQ1_pos hQ2_pos ha1Q1 ha2Q2 hL3_12
  have hcop13 : Nat.Coprime Q₁ Q₃ := cop_of_lcm a₁ a₃ Q₁ Q₃ ha1_pos ha3_pos hQ1_pos hQ3_pos ha1Q1 ha3Q3 hL3_13
  have hcop23 : Nat.Coprime Q₂ Q₃ := cop_of_lcm a₂ a₃ Q₂ Q₃ ha2_pos ha3_pos hQ2_pos hQ3_pos ha2Q2 ha3Q3 hL3_23
  have hQ1_dvd : Q₁ ∣ L₃ := ⟨a₁, by rw [← ha1Q1, mul_comm]⟩
  have hQ2_dvd : Q₂ ∣ L₃ := ⟨a₂, by rw [← ha2Q2, mul_comm]⟩
  have hQ3_dvd : Q₃ ∣ L₃ := ⟨a₃, by rw [← ha3Q3, mul_comm]⟩
  have hQ123_dvd : Q₁ * Q₂ * Q₃ ∣ L₃ :=
    (hcop13.mul_left hcop23).mul_dvd_of_dvd_of_dvd (hcop12.mul_dvd_of_dvd_of_dvd hQ1_dvd hQ2_dvd) hQ3_dvd
  let g₃ := L₃ / (Q₁ * Q₂ * Q₃)
  have hQ123_pos : 0 < Q₁ * Q₂ * Q₃ := mul_pos (mul_pos hQ1_pos hQ2_pos) hQ3_pos
  have hg3_pos : 0 < g₃ := Nat.div_pos (Nat.le_of_dvd hL3_pos hQ123_dvd) hQ123_pos
  have hL3_eq : L₃ = g₃ * Q₁ * Q₂ * Q₃ := by
    have hmul := Nat.div_mul_cancel hQ123_dvd
    calc L₃ = (L₃ / (Q₁ * Q₂ * Q₃)) * (Q₁ * Q₂ * Q₃) := hmul.symm
      _ = g₃ * Q₁ * Q₂ * Q₃ := by ring
  have ha1_eq : a₁ = g₃ * Q₂ * Q₃ := Nat.mul_left_cancel hQ1_pos (by
    calc Q₁ * a₁ = L₃ := by rw [mul_comm, ha1Q1]
      _ = Q₁ * (g₃ * Q₂ * Q₃) := by rw [hL3_eq]; ring)
  have ha2_eq : a₂ = g₃ * Q₁ * Q₃ := Nat.mul_left_cancel hQ2_pos (by
    calc Q₂ * a₂ = L₃ := by rw [mul_comm, ha2Q2]
      _ = Q₂ * (g₃ * Q₁ * Q₃) := by rw [hL3_eq]; ring)
  have ha3_eq : a₃ = g₃ * Q₁ * Q₂ := Nat.mul_left_cancel hQ3_pos (by
    calc Q₃ * a₃ = L₃ := by rw [mul_comm, ha3Q3]
      _ = Q₃ * (g₃ * Q₁ * Q₂) := by rw [hL3_eq]; ring)
  have hQ3_lt' : Q₃ < Q₂ := by
    have h1 : (g₃ * Q₁) * Q₃ < (g₃ * Q₁) * Q₂ := by
      have : a₂ < a₃ := ha23; rw [ha2_eq, ha3_eq] at this; linarith
    exact Nat.lt_of_mul_lt_mul_left h1
  have hQ2_lt' : Q₂ < Q₁ := by
    have h1 : (g₃ * Q₃) * Q₂ < (g₃ * Q₃) * Q₁ := by
      have : a₁ < a₂ := ha12; rw [ha1_eq, ha2_eq] at this; linarith
    exact Nat.lt_of_mul_lt_mul_left h1
  have hQ1_lt : Q₁ < 2 * Q₃ := by
    have h2 : a₃ < 2 * a₁ := lt_of_le_of_lt (hC.2.2.1 a₃ (hZ_sub_A ha3Z)) (hC.2.2.2.1 a₁ (hZ_sub_A ha1Z))
    rw [ha3_eq, ha1_eq] at h2
    have h3 : (g₃ * Q₂) * Q₁ < (g₃ * Q₂) * (2 * Q₃) := by linarith
    exact Nat.lt_of_mul_lt_mul_left h3
  have hngcd : ¬ (Nat.gcd a₄ a₅ ∣ L₃) := by
    intro hdvd
    have hL_pos := finset_lcm_pos_core hC.2.1
    have ha4_e : (A.lcm id).factorization p₀ ≤ a₄.factorization p₀ := by
      have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha4A) (p := p₀)
      simp only [id_eq] at hle
      by_contra hlt; exact ha4Z (Finset.mem_filter.mpr ⟨ha4A, by omega⟩)
    have ha5_e : (A.lcm id).factorization p₀ ≤ a₅.factorization p₀ := by
      have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha5A) (p := p₀)
      simp only [id_eq] at hle
      by_contra hlt; exact ha5Z (Finset.mem_filter.mpr ⟨ha5A, by omega⟩)
    have hg_e : (A.lcm id).factorization p₀ ≤ (Nat.gcd a₄ a₅).factorization p₀ := by
      rw [fac_gcd_eq_min_5 (hC.2.1 a₄ ha4A).ne' (hC.2.1 a₅ ha5A).ne']; exact le_min ha4_e ha5_e
    have hfac := le_trans hg_e (fac_le_of_dvd_5 hL3_pos.ne' hdvd (p := p₀))
    rw [← hL3_12, fac_lcm_eq_max_5 ha1_pos.ne' ha2_pos.ne'] at hfac
    have h1 := (Finset.mem_filter.mp ha1Z).2
    have h2 := (Finset.mem_filter.mp ha2Z).2
    change a₁.factorization p₀ < (A.lcm id).factorization p₀ at h1
    change a₂.factorization p₀ < (A.lcm id).factorization p₀ at h2
    omega
  exact ⟨a₁, a₂, a₃, a₄, a₅, L₃, Q₁, Q₂, Q₃, g₃,
    ⟨hZ_eq, ha12, ha23, hA_eq, ha45, ha4Z, ha5Z, hL3_pos, hg3_pos, rfl,
     hL3_12, hL3_13, hL3_23, ha1_eq, ha2_eq, ha3_eq, hL3_eq,
     hQ3_lt', hQ2_lt', hQ1_lt, by omega, by omega, by omega, hcop12, hcop13, hcop23, hngcd⟩⟩

private lemma core_at_most_one_other_3set {A Z₁ Z₂ Z_A : Finset ℕ} {M : ℕ}
    (hC : C5Core A M) (hZA3 : Z_A.card = 3) (hZA_sub : Z_A ⊆ A)
    (hZ1_ex : ∃ p₁, p₁.Prime ∧ p₁ ∣ A.lcm id ∧
      Z₁ = A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) ∧ Z₁.card = 3)
    (hZ2_ex : ∃ p₂, p₂.Prime ∧ p₂ ∣ A.lcm id ∧
      Z₂ = A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂) ∧ Z₂.card = 3)
    (h1A : Z₁ ≠ Z_A) (h2A : Z₂ ≠ Z_A)
    (hZA_ex : ∃ p₀, p₀.Prime ∧ p₀ ∣ A.lcm id ∧
      Z_A = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) :
    Z₁ = Z₂ := by
  obtain ⟨p₀, hp0, hp0L, rfl⟩ := hZA_ex
  obtain ⟨p₁, hp1, hp1L, rfl, hZ1_3⟩ := hZ1_ex
  obtain ⟨p₂, hp2, hp2L, rfl, hZ2_3⟩ := hZ2_ex
  have hi1 := core_fact3_two_three_sets hC hp1 hp1L hp0 hp0L hZ1_3 hZA3 h1A
  have hi2 := core_fact3_two_three_sets hC hp2 hp2L hp0 hp0L hZ2_3 hZA3 h2A
  have hs1 : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) ⊆
      A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) := by
    have hrem : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 2 := by
      rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
    have h1rem : (A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) \
        A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 2 := by
      have := Finset.card_sdiff_add_card_inter
        (A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁))
        (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
      omega
    have hsub : (A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) \
        A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) ⊆
        (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) :=
      Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Finset.Subset.refl _)
    have heq := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    exact heq ▸ Finset.sdiff_subset
  have hs2 : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) ⊆
      A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂) := by
    have hrem : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 2 := by
      rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
    have h2rem : (A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂) \
        A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 2 := by
      have := Finset.card_sdiff_add_card_inter
        (A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂))
        (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
      omega
    have hsub : (A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂) \
        A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) ⊆
        (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) :=
      Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Finset.Subset.refl _)
    have heq := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    exact heq ▸ Finset.sdiff_subset
  by_contra hne12
  have hi12 := core_fact3_two_three_sets hC hp1 hp1L hp2 hp2L hZ1_3 hZ2_3 hne12
  have hsub12 : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)) ⊆
      A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) ∩
      A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂) :=
    Finset.subset_inter hs1 hs2
  have hrem : (A \ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 2 := by
    rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
  have := Finset.card_le_card hsub12
  omega

private lemma core_claimC'_aux {A : Finset ℕ} {M p a_k a_i a_j a₄ a₅ c : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M) (hp : p.Prime) (hpL : p ∣ A.lcm id)
    (hA_eq : A = {a_i, a₄, a_j, a_k, a₅})
    (hij : a_i ≠ a_j) (hik : a_i ≠ a_k) (hi4 : a_i ≠ a₄) (hi5 : a_i ≠ a₅)
    (hjk : a_j ≠ a_k) (hj4 : a_j ≠ a₄) (hj5 : a_j ≠ a₅)
    (hk4 : a_k ≠ a₄) (hk5 : a_k ≠ a₅) (h45 : a₄ ≠ a₅)
    (hc1 : 1 ≤ c) (hci : c ≤ a_i.factorization p) (hck0 : a_k.factorization p = 0)
    (h_lt_j : a_j.factorization p < (A.lcm id).factorization p)
    (h_eq4 : a₄.factorization p = (A.lcm id).factorization p)
    (h_eq5 : a₅.factorization p = (A.lcm id).factorization p)
    (hi_lt : a_i.factorization p < (A.lcm id).factorization p)
    (hpc_sq : (p ^ c) ^ 2 ≤ M) : p ^ c ≤ 5 := by
  by_contra h6; push Not at h6
  have ⟨_, _, _, _, _, h3pe⟩ := core_Z_T_props hC hp hpL
  have hc4 : c ≤ a₄.factorization p := by omega
  have hu1A : a_i ∈ A := by rw [hA_eq]; simp
  have hu2A : a₄ ∈ A := by rw [hA_eq]; simp
  have hu3A : a_j ∈ A := by rw [hA_eq]; simp
  have hu4A : a_k ∈ A := by rw [hA_eq]; simp
  have hpc_pos : 0 < p ^ c := pow_pos hp.pos c
  have h5i : 5 * (a_i / p ^ c) ≤ M := by
    have hdvd : p ^ c ∣ a_i := (hp.pow_dvd_iff_le_factorization (hC.2.1 a_i hu1A).ne').mpr hci
    calc 5 * (a_i / p ^ c) ≤ 6 * (a_i / p ^ c) := by omega
      _ ≤ p ^ c * (a_i / p ^ c) := Nat.mul_le_mul_right _ h6
      _ = a_i := Nat.mul_div_cancel' hdvd
      _ ≤ M := hC.2.2.1 a_i hu1A
  have h64 : 6 * (a₄ / p ^ c) ≤ M := by
    have hdvd : p ^ c ∣ a₄ := (hp.pow_dvd_iff_le_factorization (hC.2.1 a₄ hu2A).ne').mpr hc4
    calc 6 * (a₄ / p ^ c) ≤ p ^ c * (a₄ / p ^ c) := Nat.mul_le_mul_right _ h6
      _ = a₄ := Nat.mul_div_cancel' hdvd
      _ ≤ M := hC.2.2.1 a₄ hu2A
  have hnd : ¬ (a₅ ∣ Nat.lcm a_j a_k) := by
    intro hdvd
    have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hC.2.1 a_j hu3A) (hC.2.1 a_k hu4A)).ne' hdvd (p := p)
    rw [fac_lcm_eq_max_5 (hC.2.1 a_j hu3A).ne' (hC.2.1 a_k hu4A).ne', hck0] at hfac
    omega
  exact hNR1 ⟨a_i, a₄, a_j, a_k, a₅, p, c, c, hA_eq,
    hi4, hij, hik, hi5, hj4.symm, hk4.symm, h45, hjk, hj5, hk5,
    hnd, hp, hc1, hci, hc1, hc4, by simpa [pow_add, sq] using hpc_sq, h3pe, h5i, h64⟩

private lemma core_heavy_hit_23_imp_g3_ge2 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ q : ℕ}
    (hC : C5Core A M) (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hq : q.Prime) (hqL : q ∣ A.lcm id)
    (hZq2 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2)
    (hq_hv : M < (q ^ (A.lcm id).factorization q) ^ 2)
    (h_hit23 : a₂ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) ∨
               a₃ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) :
    2 ≤ g₃ := by
  by_contra h1
  have hg3_pos := hd.hg3_pos
  have hg3_1 : g₃ = 1 := by omega
  let e_q := (A.lcm id).factorization q
  let Zq := A.filter (fun a => a.factorization q < e_q)
  let Tq := A.filter (fun a => a.factorization q = e_q)
  have ⟨he_q1, hsum_q, _, _, _, _⟩ := core_Z_T_props hC hq hqL
  have hZq2' : Zq.card ≤ 2 := hZq2
  have hZ3 : Z.card = 3 := by
    rw [hd.hZ_eq, Finset.card_insert_of_notMem (by simp [hd.ha12.ne, (lt_trans hd.ha12 hd.ha23).ne]),
        Finset.card_insert_of_notMem (by simp [hd.ha23.ne]), Finset.card_singleton]
  have hz_ex : ∃ z ∈ Z, z ∈ Tq := by
    by_contra hall; push Not at hall
    have hsub : Z ⊆ Zq := fun z hz => by
      have hzA : z ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
      have hL_pos := finset_lcm_pos_core hC.2.1
      have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) hzA) (p := q)
      simp only [id_eq] at hle
      have hnz : z ∉ Tq := hall z hz
      exact Finset.mem_filter.mpr ⟨hzA, by by_contra hlt; exact hnz (Finset.mem_filter.mpr ⟨hzA, by dsimp [e_q]; omega⟩)⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzZ, hzTq⟩ := hz_ex
  have hzL : z ∣ L₃ := by rw [hd.hL3_lcm]; exact Finset.dvd_lcm hzZ
  have hL3_1 : L₃ = Q₁ * Q₂ * Q₃ := by rw [hd.hL3_eq, hg3_1, one_mul]
  have hqe_z : q ^ e_q ∣ z := (hq.pow_dvd_iff_le_factorization (hC.2.1 z (Finset.mem_filter.mp hzTq).1).ne').mpr
    (by rw [(Finset.mem_filter.mp hzTq).2])
  have hqe_L : q ^ e_q ∣ Q₁ * Q₂ * Q₃ := hL3_1 ▸ dvd_trans hqe_z hzL
  have hq_dvd_Q : q ∣ Q₁ ∨ q ∣ Q₂ ∨ q ∣ Q₃ := by
    have hq123 : q ∣ Q₁ * Q₂ * Q₃ := dvd_trans (dvd_pow_self q (by dsimp [e_q]; omega)) hqe_L
    rcases hq.dvd_mul.mp hq123 with h12 | h3
    · rcases hq.dvd_mul.mp h12 with h1' | h2'
      · exact Or.inl h1'
      · exact Or.inr (Or.inl h2')
    · exact Or.inr (Or.inr h3)
  have hQ1p : 0 < Q₁ := by have := hd.hQ1_ge5; omega
  have hQ2p : 0 < Q₂ := by have := hd.hQ2_ge4; omega
  have hQ3p : 0 < Q₃ := by have := hd.hQ3_ge3; omega
  have hL3_fac : L₃.factorization q = Q₁.factorization q + Q₂.factorization q + Q₃.factorization q := by
    rw [hL3_1, Nat.factorization_mul (mul_pos hQ1p hQ2p).ne' hQ3p.ne',
        Nat.factorization_mul hQ1p.ne' hQ2p.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply]
  have he_le_L : e_q ≤ L₃.factorization q := by
    have hfac_q := fac_le_of_dvd_5 hd.hL3_pos.ne' (dvd_trans hqe_z hzL) (p := q)
    rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hq.factorization_self, mul_one] at hfac_q
    exact hfac_q
  have ha3M : a₃ ≤ M := hC.2.2.1 a₃ (by rw [hd.hA_eq]; simp)
  have ha3_1 : a₃ = Q₁ * Q₂ := by rw [hd.ha3_eq, hg3_1, one_mul]
  rcases hq_dvd_Q with hq1 | hq2 | hq3
  · have hqQ2 : Q₂.factorization q = 0 :=
      (coprime_factorization_zero hQ1p hQ2p hq hd.hcop12).resolve_left (by have := (hq.dvd_iff_one_le_factorization hQ1p.ne').mp hq1; omega)
    have hqQ3 : Q₃.factorization q = 0 :=
      (coprime_factorization_zero hQ1p hQ3p hq hd.hcop13).resolve_left (by have := (hq.dvd_iff_one_le_factorization hQ1p.ne').mp hq1; omega)
    have hqQ1 : e_q ≤ Q₁.factorization q := by omega
    have hqe_Q1 : q ^ e_q ∣ Q₁ := (hq.pow_dvd_iff_le_factorization hQ1p.ne').mpr hqQ1
    have h2 : q ^ e_q ∣ a₂ := dvd_trans hqe_Q1 ⟨g₃ * Q₃, by rw [hd.ha2_eq]; ring⟩
    have h3 : q ^ e_q ∣ a₃ := dvd_trans hqe_Q1 ⟨g₃ * Q₂, by rw [hd.ha3_eq]; ring⟩
    have hf2 := (hq.pow_dvd_iff_le_factorization (hC.2.1 a₂ (by rw [hd.hA_eq]; simp)).ne').mp h2
    have hf3 := (hq.pow_dvd_iff_le_factorization (hC.2.1 a₃ (by rw [hd.hA_eq]; simp)).ne').mp h3
    rcases h_hit23 with ha2Z | ha3Z
    · have := (Finset.mem_filter.mp ha2Z).2; omega
    · have := (Finset.mem_filter.mp ha3Z).2; omega
  · have hqQ1 : Q₁.factorization q = 0 :=
      (coprime_factorization_zero hQ1p hQ2p hq hd.hcop12).resolve_right (by have := (hq.dvd_iff_one_le_factorization hQ2p.ne').mp hq2; omega)
    have hqQ3 : Q₃.factorization q = 0 :=
      (coprime_factorization_zero hQ2p hQ3p hq hd.hcop23).resolve_left (by have := (hq.dvd_iff_one_le_factorization hQ2p.ne').mp hq2; omega)
    have hqQ2 : e_q ≤ Q₂.factorization q := by omega
    have hqe_le : q ^ e_q ≤ Q₂ := Nat.le_of_dvd hQ2p ((hq.pow_dvd_iff_le_factorization hQ2p.ne').mpr hqQ2)
    have hsq : (q ^ e_q) ^ 2 ≤ M := by
      have : Q₂ * Q₂ < Q₁ * Q₂ := Nat.mul_lt_mul_of_pos_right hd.hQ2_lt hQ2p
      rw [sq]; exact le_trans (Nat.mul_le_mul hqe_le hqe_le) (le_of_lt (lt_of_lt_of_le (ha3_1 ▸ this) ha3M))
    dsimp [e_q] at hsq; omega
  · have hqQ1 : Q₁.factorization q = 0 :=
      (coprime_factorization_zero hQ1p hQ3p hq hd.hcop13).resolve_right (by have := (hq.dvd_iff_one_le_factorization hQ3p.ne').mp hq3; omega)
    have hqQ2 : Q₂.factorization q = 0 :=
      (coprime_factorization_zero hQ2p hQ3p hq hd.hcop23).resolve_right (by have := (hq.dvd_iff_one_le_factorization hQ3p.ne').mp hq3; omega)
    have hqQ3 : e_q ≤ Q₃.factorization q := by omega
    have hqe_le : q ^ e_q ≤ Q₃ := Nat.le_of_dvd hQ3p ((hq.pow_dvd_iff_le_factorization hQ3p.ne').mpr hqQ3)
    have hsq : (q ^ e_q) ^ 2 ≤ M := by
      have : Q₃ * Q₃ < Q₁ * Q₂ := by nlinarith [hd.hQ3_lt, hd.hQ2_lt]
      rw [sq]; exact le_trans (Nat.mul_le_mul hqe_le hqe_le) (le_of_lt (lt_of_lt_of_le (ha3_1 ▸ this) ha3M))
    dsimp [e_q] at hsq; omega

private lemma core_Qk_dvd_60 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    {a_k a_i a_j Q_k Q_i Q_j : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hZ_perm : Z = {a_k, a_i, a_j})
    (hki : a_k ≠ a_i) (hkj : a_k ≠ a_j) (hij : a_i ≠ a_j)
    (hQk_pos : 0 < Q_k) (hQi_pos : 0 < Q_i) (hQj_pos : 0 < Q_j)
    (hQk_L : Q_k ∣ L₃)
    (hak_eq : a_k = g₃ * Q_i * Q_j) (hai_eq : a_i = g₃ * Q_k * Q_j) (haj_eq : a_j = g₃ * Q_k * Q_i)
    (hcop_ki : Nat.Coprime Q_k Q_i) (hcop_kj : Nat.Coprime Q_k Q_j)
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a_k ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (h_nohv : ∀ q : ℕ, q.Prime → q ∣ A.lcm id →
      (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 →
      M < (q ^ (A.lcm id).factorization q) ^ 2 →
      a_k ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q))
    (h_sq : Q_k ^ 2 ≤ M ∨
      ∃ q : ℕ, q.Prime ∧ q ∣ A.lcm id ∧
        (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 ∧
        M < (q ^ (A.lcm id).factorization q) ^ 2 ∧
        (a₂ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) ∨
         a₃ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q))) :
    Q_k ∣ 60 := by
  refine core_pow_le5_dvd_60 hQk_pos.ne' fun p hp hpQk => ?_
  have hL_pos := finset_lcm_pos_core hC.2.1
  have hakZ : a_k ∈ Z := by rw [hZ_perm]; simp
  have haiZ : a_i ∈ Z := by rw [hZ_perm]; simp
  have hajZ : a_j ∈ Z := by rw [hZ_perm]; simp
  have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
  have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
  have hakA : a_k ∈ A := by
    rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ
    rcases hakZ with rfl | rfl | rfl <;> simp
  have haiA : a_i ∈ A := by
    rw [hd.hA_eq]; rw [hd.hZ_eq] at haiZ; simp only [Finset.mem_insert, Finset.mem_singleton] at haiZ
    rcases haiZ with rfl | rfl | rfl <;> simp
  have hajA : a_j ∈ A := by
    rw [hd.hA_eq]; rw [hd.hZ_eq] at hajZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hajZ
    rcases hajZ with rfl | rfl | rfl <;> simp
  have hak4 : a_k ≠ a₄ := fun h => hd.ha4Z (h ▸ hakZ)
  have hak5 : a_k ≠ a₅ := fun h => hd.ha5Z (h ▸ hakZ)
  have hai4 : a_i ≠ a₄ := fun h => hd.ha4Z (h ▸ haiZ)
  have hai5 : a_i ≠ a₅ := fun h => hd.ha5Z (h ▸ haiZ)
  have haj4 : a_j ≠ a₄ := fun h => hd.ha4Z (h ▸ hajZ)
  have haj5 : a_j ≠ a₅ := fun h => hd.ha5Z (h ▸ hajZ)
  have hA_perm : A = {a_i, a₄, a_j, a_k, a₅} := by
    refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [hai4, hij, hki.symm, hai5]),
          Finset.card_insert_of_notMem (by simp [haj4.symm, hak4.symm, hd.ha45]),
          Finset.card_insert_of_notMem (by simp [hkj.symm, haj5]),
          Finset.card_insert_of_notMem (by simp [hak5]), Finset.card_singleton, hC.1]
  have hL3_A : L₃ ∣ A.lcm id := by rw [hd.hL3_lcm]; exact Finset.lcm_dvd fun z hz => Finset.dvd_lcm (by
    rw [hd.hA_eq]; rw [hd.hZ_eq] at hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto)
  have hpL : p ∣ A.lcm id := dvd_trans (dvd_trans hpQk hQk_L) hL3_A
  have ⟨_, _, _, _, hZ_le3, _⟩ := core_Z_T_props hC hp hpL
  let e_p := (A.lcm id).factorization p
  let Zp := A.filter (fun a => a.factorization p < e_p)
  have hQi0 : Q_i.factorization p = 0 :=
    (coprime_factorization_zero hQk_pos hQi_pos hp hcop_ki).resolve_left
      (by have := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk; omega)
  have hQj0 : Q_j.factorization p = 0 :=
    (coprime_factorization_zero hQk_pos hQj_pos hp hcop_kj).resolve_left
      (by have := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk; omega)
  have hg3p := hd.hg3_pos
  have hfk : a_k.factorization p = g₃.factorization p := by
    rw [hak_eq, Nat.factorization_mul (mul_pos hg3p hQi_pos).ne' hQj_pos.ne',
        Nat.factorization_mul hg3p.ne' hQi_pos.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply, hQi0, hQj0, add_zero, add_zero]
  have hfi : a_i.factorization p = g₃.factorization p + Q_k.factorization p := by
    rw [hai_eq, Nat.factorization_mul (mul_pos hg3p hQk_pos).ne' hQj_pos.ne',
        Nat.factorization_mul hg3p.ne' hQk_pos.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply, hQj0, add_zero]
  have hfj : a_j.factorization p = g₃.factorization p + Q_k.factorization p := by
    rw [haj_eq, Nat.factorization_mul (mul_pos hg3p hQk_pos).ne' hQi_pos.ne',
        Nat.factorization_mul hg3p.ne' hQk_pos.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply, hQi0, add_zero]
  have hQkp1 : 1 ≤ Q_k.factorization p := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk
  have haiL := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) haiA) (p := p)
  simp only [id_eq] at haiL
  have hakZp : a_k ∈ Zp := Finset.mem_filter.mpr ⟨hakA, by dsimp [e_p]; omega⟩
  have hZp_le3' : Zp.card ≤ 3 := hZ_le3
  rcases Nat.lt_or_eq_of_le hZp_le3' with hZp_le2 | hZp3
  · have hZp_le2' : Zp.card ≤ 2 := by omega
    rcases core_claimA hC hNR1 hp hpL hZp_le2' with h5 | hhv
    · calc p ^ Q_k.factorization p ≤ p ^ (A.lcm id).factorization p := Nat.pow_le_pow_right hp.pos (by omega)
        _ ≤ 5 := h5
    · exact False.elim (h_nohv p hp hpL hZp_le2' hhv hakZp)
  · by_cases hZpZ : Zp = Z
    · obtain ⟨z₀, z₁, z₂, hZ_3v, _, _, _, hz0v, hz12v, _⟩ := core_fact2_three_vals hC hp hpL hZp3
      have hZp_v : Zp = ({z₀, z₁, z₂} : Finset ℕ) := hZ_3v
      have hak_in : a_k ∈ ({z₀, z₁, z₂} : Finset ℕ) := hZp_v ▸ (hZpZ ▸ hakZ)
      have hai_in : a_i ∈ ({z₀, z₁, z₂} : Finset ℕ) := hZp_v ▸ (hZpZ ▸ haiZ)
      have haj_in : a_j ∈ ({z₀, z₁, z₂} : Finset ℕ) := hZp_v ▸ (hZpZ ▸ hajZ)
      have hz0_k : a_k = z₀ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hak_in hai_in haj_in
        rcases hak_in with rfl | h1 | h2
        · rfl
        · rcases hai_in with rfl | h1' | h2'
          · exact False.elim (by rw [hz0v] at hfi; omega)
          · exact absurd (h1.trans h1'.symm) hki
          · rcases haj_in with rfl | h1'' | h2''
            · exact False.elim (by rw [hz0v] at hfj; omega)
            · exact absurd (h1.trans h1''.symm) hkj
            · exact absurd (h2'.trans h2''.symm) hij
        · rcases hai_in with rfl | h1' | h2'
          · exact False.elim (by rw [hz0v] at hfi; omega)
          · rcases haj_in with rfl | h1'' | h2''
            · exact False.elim (by rw [hz0v] at hfj; omega)
            · exact absurd (h1'.trans h1''.symm) hij
            · exact absurd (h2.trans h2''.symm) hkj
          · exact absurd (h2.trans h2'.symm) hki
      have hfk0 : a_k.factorization p = 0 := hz0_k ▸ hz0v
      have hg3_0 : g₃.factorization p = 0 := by omega
      have hfi_c : a_i.factorization p = Q_k.factorization p := by omega
      have h4_eq : a₄.factorization p = e_p := by
        have ha4_not : a₄ ∉ Zp := hZpZ ▸ hd.ha4Z
        have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha4A) (p := p)
        simp only [id_eq] at hle
        by_contra hne; exact ha4_not (Finset.mem_filter.mpr ⟨ha4A, by dsimp [e_p]; omega⟩)
      have h5_eq : a₅.factorization p = e_p := by
        have ha5_not : a₅ ∉ Zp := hZpZ ▸ hd.ha5Z
        have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha5A) (p := p)
        simp only [id_eq] at hle
        by_contra hne; exact ha5_not (Finset.mem_filter.mpr ⟨ha5A, by dsimp [e_p]; omega⟩)
      have hi_mem : a_i ∈ Zp := hZpZ ▸ haiZ
      have hj_mem : a_j ∈ Zp := hZpZ ▸ hajZ
      have hi_lt : a_i.factorization p < e_p := (Finset.mem_filter.mp hi_mem).2
      have hj_lt : a_j.factorization p < e_p := (Finset.mem_filter.mp hj_mem).2
      have hpc_sq : (p ^ Q_k.factorization p) ^ 2 ≤ M := by
        rcases h_sq with hQ_sq | ⟨q, hq, hqL, hZq_le2, hq_hv, hq_hit23⟩
        · have hle : p ^ Q_k.factorization p ≤ Q_k := Nat.le_of_dvd hQk_pos ((hp.pow_dvd_iff_le_factorization hQk_pos.ne').mpr le_rfl)
          calc (p ^ Q_k.factorization p) ^ 2 = (p ^ Q_k.factorization p) * (p ^ Q_k.factorization p) := by ring
            _ ≤ Q_k * Q_k := Nat.mul_le_mul hle hle
            _ = Q_k ^ 2 := by ring
            _ ≤ M := hQ_sq
        · let Zq := A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
          have hpq : p ≠ q := fun h => by
            subst h; have : Zp.card ≤ 2 := hZq_le2; omega
          have h45_ex : ∃ t ∈ ({a₄, a₅} : Finset ℕ), t ∉ Zq := by
            by_contra hall; push Not at hall
            have h4Zq : a₄ ∈ Zq := hall a₄ (by simp)
            have h5Zq : a₅ ∈ Zq := hall a₅ (by simp)
            have hn42 : a₂ ≠ a₄ := fun h => hd.ha4Z (h ▸ (by rw [hd.hZ_eq]; simp))
            have hn52 : a₂ ≠ a₅ := fun h => hd.ha5Z (h ▸ (by rw [hd.hZ_eq]; simp))
            have hn43 : a₃ ≠ a₄ := fun h => hd.ha4Z (h ▸ (by rw [hd.hZ_eq]; simp))
            have hn53 : a₃ ≠ a₅ := fun h => hd.ha5Z (h ▸ (by rw [hd.hZ_eq]; simp))
            rcases hq_hit23 with ha2Z | ha3Z
            · have hsub : {a₂, a₄, a₅} ⊆ Zq := fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              have h3 : ({a₂, a₄, a₅} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [hn42, hn52]),
                    Finset.card_insert_of_notMem (by simp [hd.ha45]), Finset.card_singleton]
              have := Finset.card_le_card hsub; change Zq.card ≤ 2 at hZq_le2; omega
            · have hsub : {a₃, a₄, a₅} ⊆ Zq := fun x hx => by
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl <;> assumption
              have h3 : ({a₃, a₄, a₅} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [hn43, hn53]),
                    Finset.card_insert_of_notMem (by simp [hd.ha45]), Finset.card_singleton]
              have := Finset.card_le_card hsub; change Zq.card ≤ 2 at hZq_le2; omega
          obtain ⟨t, ht45, ht_nZq⟩ := h45_ex
          have htA : t ∈ A := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht45
            rcases ht45 with rfl | rfl <;> assumption
          have ht_pos := hC.2.1 t htA
          have htp : e_p ≤ t.factorization p := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht45
            rcases ht45 with rfl | rfl <;> omega
          have htq : (A.lcm id).factorization q ≤ t.factorization q := by
            have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) htA) (p := q)
            simp only [id_eq] at hle
            by_contra hlt; exact ht_nZq (Finset.mem_filter.mpr ⟨htA, by omega⟩)
          have hpe_t : p ^ Q_k.factorization p ∣ t := (hp.pow_dvd_iff_le_factorization ht_pos.ne').mpr (by omega)
          have hqe_t : q ^ (A.lcm id).factorization q ∣ t := (hq.pow_dvd_iff_le_factorization ht_pos.ne').mpr htq
          have hcop_pq : Nat.Coprime (p ^ Q_k.factorization p) (q ^ (A.lcm id).factorization q) :=
            (hp.coprime_iff_not_dvd.mpr fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)).pow _ _
          have hmul_le : p ^ Q_k.factorization p * q ^ (A.lcm id).factorization q ≤ M :=
            (Nat.le_of_dvd ht_pos (hcop_pq.mul_dvd_of_dvd_of_dvd hpe_t hqe_t)).trans (hC.2.2.1 t htA)
          rcases le_or_gt (p ^ Q_k.factorization p) (q ^ (A.lcm id).factorization q) with hle | hlt
          · have : (p ^ Q_k.factorization p) ^ 2 ≤ p ^ Q_k.factorization p * q ^ (A.lcm id).factorization q := by
              rw [sq]; exact Nat.mul_le_mul_left _ hle
            omega
          · have : (q ^ (A.lcm id).factorization q) ^ 2 < p ^ Q_k.factorization p * q ^ (A.lcm id).factorization q := by
              rw [sq]; exact Nat.mul_lt_mul_of_pos_right hlt (pow_pos hq.pos _)
            omega
      exact core_claimC'_aux hC hNR1 hp hpL hA_perm hij hki.symm hai4 hai5 hkj.symm haj4 haj5
        hak4 hak5 hd.ha45 hQkp1 (by omega) hfk0 hj_lt h4_eq h5_eq hi_lt hpc_sq
    · exact False.elim (h_no3 p hp hpL hZp3 hZpZ hakZp)

private lemma core_unhit_k_dichotomy {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    {a_k a_i a_j Q_k Q_i Q_j p₀ : ℕ}
    (hC : C5Core A M) (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (hZ_perm : Z = {a_k, a_i, a_j})
    (hki : a_k ≠ a_i) (hkj : a_k ≠ a_j) (hij : a_i ≠ a_j)
    (hQk_pos : 0 < Q_k) (hQi_pos : 0 < Q_i) (hQj_pos : 0 < Q_j)
    (hQk_L : Q_k ∣ L₃)
    (hak_eq : a_k = g₃ * Q_i * Q_j) (hai_eq : a_i = g₃ * Q_k * Q_j) (haj_eq : a_j = g₃ * Q_k * Q_i)
    (hcop_ki : Nat.Coprime Q_k Q_i) (hcop_kj : Nat.Coprime Q_k Q_j)
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a_k ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p)) :
    (∃ u₃ u₄ u₅ : ℕ, A = {a_j, a_i, u₃, u₄, u₅} ∧
      a_j ≠ a_i ∧ a_j ≠ u₃ ∧ a_j ≠ u₄ ∧ a_j ≠ u₅ ∧
      a_i ≠ u₃ ∧ a_i ≠ u₄ ∧ a_i ≠ u₅ ∧ u₃ ≠ u₄ ∧ u₃ ≠ u₅ ∧ u₄ ≠ u₅ ∧
      ¬ (u₅ ∣ Nat.lcm u₃ u₄) ∧ Q_k ∣ a_j ∧ Q_k ∣ a_i) ∨
    ((¬ ∃ ZB : Finset ℕ, ZB ≠ Z ∧ ∃ q : ℕ, q.Prime ∧ q ∣ A.lcm id ∧
      ZB = A.filter (fun a => a.factorization q < (A.lcm id).factorization q) ∧ ZB.card = 3) ∧
      PairConst {a_k, a₄, a₅} ∧ Q_k ∣ a₄ ∧ Q_k ∣ a₅ ∧
      A = {a₄, a_i, a_j, a_k, a₅} ∧
      a₄ ≠ a_i ∧ a₄ ≠ a_j ∧ a₄ ≠ a_k ∧ a₄ ≠ a₅ ∧
      a_i ≠ a_j ∧ a_i ≠ a_k ∧ a_i ≠ a₅ ∧ a_j ≠ a_k ∧ a_j ≠ a₅ ∧ a_k ≠ a₅ ∧
      ¬ (a₅ ∣ Nat.lcm a_j a_k)) := by
  have hakZ : a_k ∈ Z := by rw [hZ_perm]; simp
  have haiZ : a_i ∈ Z := by rw [hZ_perm]; simp
  have hajZ : a_j ∈ Z := by rw [hZ_perm]; simp
  have hak4 : a_k ≠ a₄ := fun h => hd.ha4Z (h ▸ hakZ)
  have hak5 : a_k ≠ a₅ := fun h => hd.ha5Z (h ▸ hakZ)
  have hai4 : a_i ≠ a₄ := fun h => hd.ha4Z (h ▸ haiZ)
  have hai5 : a_i ≠ a₅ := fun h => hd.ha5Z (h ▸ haiZ)
  have haj4 : a_j ≠ a₄ := fun h => hd.ha4Z (h ▸ hajZ)
  have haj5 : a_j ≠ a₅ := fun h => hd.ha5Z (h ▸ hajZ)
  have hQk_ai : Q_k ∣ a_i := ⟨g₃ * Q_j, by rw [hai_eq]; ring⟩
  have hQk_aj : Q_k ∣ a_j := ⟨g₃ * Q_i, by rw [haj_eq]; ring⟩
  by_cases hpc : PairConst ({a_k, a₄, a₅} : Finset ℕ)
  · right
    have hno_ZB : ¬ ∃ ZB : Finset ℕ, ZB ≠ Z ∧ ∃ q : ℕ, q.Prime ∧ q ∣ A.lcm id ∧
        ZB = A.filter (fun a => a.factorization q < (A.lcm id).factorization q) ∧ ZB.card = 3 := by
      rintro ⟨ZB, hZB_ne, q, hq, hqL, rfl, hZB3⟩
      have hZA3 : Z.card = 3 := by
        rw [hd.hZ_eq, Finset.card_insert_of_notMem (by simp [hd.ha12.ne, (lt_trans hd.ha12 hd.ha23).ne]),
            Finset.card_insert_of_notMem (by simp [hd.ha23.ne]), Finset.card_singleton]
      have hZA_sub : Z ⊆ A := by rw [hd.hZ_eq, hd.hA_eq]; intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
      have hi := core_fact3_two_three_sets hC hq hqL hp0 hp0L hZB3 (hZ_p0 ▸ hZA3) (hZ_p0 ▸ hZB_ne)
      rw [← hZ_p0] at hi
      have hrem2 : (A \ Z).card = 2 := by rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
      have hZBsdiff : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q) \ Z).card = 2 := by
        have := Finset.card_sdiff_add_card_inter (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) Z
        omega
      have hsub_sdiff : A.filter (fun a => a.factorization q < (A.lcm id).factorization q) \ Z ⊆ A \ Z :=
        Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Finset.Subset.refl _)
      have heq_rem : A.filter (fun a => a.factorization q < (A.lcm id).factorization q) \ Z = A \ Z :=
        Finset.eq_of_subset_of_card_le hsub_sdiff (by omega)
      have ha4_ZB : a₄ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := by
        have : a₄ ∈ A \ Z := Finset.mem_sdiff.mpr ⟨by rw [hd.hA_eq]; simp, hd.ha4Z⟩
        rw [← heq_rem] at this; exact (Finset.mem_sdiff.mp this).1
      have ha5_ZB : a₅ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := by
        have : a₅ ∈ A \ Z := Finset.mem_sdiff.mpr ⟨by rw [hd.hA_eq]; simp, hd.ha5Z⟩
        rw [← heq_rem] at this; exact (Finset.mem_sdiff.mp this).1
      have hq_pc := core_fact1_three_pairconst hC hq hqL hZB3
      have hlcm45 : Nat.lcm a₄ a₅ = (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).lcm id :=
        hq_pc a₄ ha4_ZB a₅ ha5_ZB hd.ha45
      have hak_not_ZB : a_k ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) :=
        h_no3 q hq hqL hZB3 hZB_ne
      have hak_eq_e : a_k.factorization q = (A.lcm id).factorization q := by
        have hakA : a_k ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ ⊢; tauto
        have hL_pos := finset_lcm_pos_core hC.2.1
        have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) hakA) (p := q)
        simp only [id_eq] at hle
        by_contra hlt; exact hak_not_ZB (Finset.mem_filter.mpr ⟨hakA, by omega⟩)
      have hak_dvd : a_k ∣ Nat.lcm a₄ a₅ := by
        have hk1 : a_k ∣ ({a_k, a₄, a₅} : Finset ℕ).lcm id := Finset.dvd_lcm (by simp)
        have h45 : Nat.lcm a₄ a₅ = ({a_k, a₄, a₅} : Finset ℕ).lcm id := hpc a₄ (by simp) a₅ (by simp) hd.ha45
        rw [h45]; exact hk1
      rw [hlcm45] at hak_dvd
      have hLZ_pos : 0 < (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).lcm id :=
        finset_lcm_pos_core fun x hx => hC.2.1 x (Finset.mem_filter.mp hx).1
      have hfac := fac_le_of_dvd_5 hLZ_pos.ne' hak_dvd (p := q)
      have hlcm_q : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).lcm id =
          Nat.lcm a₄ a₅ := hlcm45.symm
      rw [hlcm_q, fac_lcm_eq_max_5 (hC.2.1 a₄ (by rw [hd.hA_eq]; simp)).ne'
          (hC.2.1 a₅ (by rw [hd.hA_eq]; simp)).ne'] at hfac
      have h4f := (Finset.mem_filter.mp ha4_ZB).2
      have h5f := (Finset.mem_filter.mp ha5_ZB).2
      omega
    have hQk_45 : Q_k ∣ a₄ ∧ Q_k ∣ a₅ := by
      have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
      have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
      have hakA : a_k ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ ⊢; tauto
      have h4pos := hC.2.1 a₄ ha4A
      have h5pos := hC.2.1 a₅ ha5A
      have hL_pos := finset_lcm_pos_core hC.2.1
      have hL3_A : L₃ ∣ A.lcm id := by rw [hd.hL3_lcm]; exact Finset.lcm_dvd fun z hz => Finset.dvd_lcm (by
        rw [hd.hA_eq]; rw [hd.hZ_eq] at hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto)
      have hdvd_both : ∀ p : ℕ, p.Prime → p ∣ Q_k →
          Q_k.factorization p ≤ a₄.factorization p ∧ Q_k.factorization p ≤ a₅.factorization p := by
        intro p hp hpQk
        have hpL : p ∣ A.lcm id := dvd_trans (dvd_trans hpQk hQk_L) hL3_A
        have hQi0 : Q_i.factorization p = 0 :=
          (coprime_factorization_zero hQk_pos hQi_pos hp hcop_ki).resolve_left
            (by have := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk; omega)
        have hQj0 : Q_j.factorization p = 0 :=
          (coprime_factorization_zero hQk_pos hQj_pos hp hcop_kj).resolve_left
            (by have := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk; omega)
        have hfk : a_k.factorization p = g₃.factorization p := by
          rw [hak_eq, Nat.factorization_mul (mul_pos hd.hg3_pos hQi_pos).ne' hQj_pos.ne',
              Nat.factorization_mul hd.hg3_pos.ne' hQi_pos.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply, hQi0, hQj0, add_zero, add_zero]
        have hfi : a_i.factorization p = g₃.factorization p + Q_k.factorization p := by
          rw [hai_eq, Nat.factorization_mul (mul_pos hd.hg3_pos hQk_pos).ne' hQj_pos.ne',
              Nat.factorization_mul hd.hg3_pos.ne' hQk_pos.ne', Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply, hQj0, add_zero]
        have haiA : a_i ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at haiZ; simp only [Finset.mem_insert, Finset.mem_singleton] at haiZ ⊢; tauto
        have haiL := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) haiA) (p := p)
        simp only [id_eq] at haiL
        have hQkp1 : 1 ≤ Q_k.factorization p := (hp.dvd_iff_one_le_factorization hQk_pos.ne').mp hpQk
        have hfk_lt : a_k.factorization p < (A.lcm id).factorization p := by omega
        have hk_not_e : a_k.factorization p < (A.lcm id).factorization p := hfk_lt
        let Zp := A.filter (fun a => a.factorization p < (A.lcm id).factorization p)
        have ⟨_, _, _, _, hZ_le3, _⟩ := core_Z_T_props hC hp hpL
        have h45_eq : a₄.factorization p = (A.lcm id).factorization p ∧
                      a₅.factorization p = (A.lcm id).factorization p := by
          have hk4_lcm : Nat.lcm a_k a₄ = Nat.lcm a_k a₅ :=
            (hpc a_k (by simp) a₄ (by simp) hak4).trans (hpc a_k (by simp) a₅ (by simp) hak5).symm
          have hk_fac := congrArg (fun n => n.factorization p) hk4_lcm
          rw [fac_lcm_eq_max_5 (hC.2.1 a_k hakA).ne' h4pos.ne',
              fac_lcm_eq_max_5 (hC.2.1 a_k hakA).ne' h5pos.ne'] at hk_fac
          by_cases h4lt : a₄.factorization p < (A.lcm id).factorization p
          · exfalso
            have h5lt : a₅.factorization p < (A.lcm id).factorization p := by omega
            have hsub : {a_k, a₄, a₅} ⊆ Zp := fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> exact Finset.mem_filter.mpr ⟨by assumption, by assumption⟩
            have h3 : ({a_k, a₄, a₅} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hak4, hak5]),
                  Finset.card_insert_of_notMem (by simp [hd.ha45]), Finset.card_singleton]
            have hZp_eq : Zp = {a_k, a₄, a₅} := Finset.eq_of_subset_of_card_le hsub (by change Zp.card ≤ 3 at hZ_le3; omega) |>.symm
            have hZp_ne : Zp ≠ Z := fun heq => by
              have : a₄ ∈ Z := heq ▸ (by rw [hZp_eq]; simp)
              exact hd.ha4Z this
            exact hno_ZB ⟨Zp, hZp_ne, p, hp, hpL, rfl, by rw [hZp_eq, h3]⟩
          · have h4le := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha4A) (p := p)
            simp only [id_eq] at h4le
            have h4e : a₄.factorization p = (A.lcm id).factorization p := by omega
            have h5le := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha5A) (p := p)
            simp only [id_eq] at h5le
            exact ⟨h4e, by omega⟩
        omega
      have h4_dvd : Q_k ∣ a₄ := by
        rw [← Nat.factorization_le_iff_dvd hQk_pos.ne' h4pos.ne']
        intro p
        by_cases hp : p.Prime
        · by_cases hpQk : p ∣ Q_k
          · exact (hdvd_both p hp hpQk).1
          · rw [Nat.factorization_eq_zero_of_not_dvd hpQk]; exact Nat.zero_le _
        · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
      have h5_dvd : Q_k ∣ a₅ := by
        rw [← Nat.factorization_le_iff_dvd hQk_pos.ne' h5pos.ne']
        intro p
        by_cases hp : p.Prime
        · by_cases hpQk : p ∣ Q_k
          · exact (hdvd_both p hp hpQk).2
          · rw [Nat.factorization_eq_zero_of_not_dvd hpQk]; exact Nat.zero_le _
        · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact ⟨h4_dvd, h5_dvd⟩
    have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
    have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
    have haiA : a_i ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at haiZ; simp only [Finset.mem_insert, Finset.mem_singleton] at haiZ ⊢; tauto
    have hajA : a_j ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at hajZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hajZ ⊢; tauto
    have hakA : a_k ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ ⊢; tauto
    have hA_perm : A = {a₄, a_i, a_j, a_k, a₅} := by
      refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [hai4.symm, haj4.symm, hak4.symm, hd.ha45]),
            Finset.card_insert_of_notMem (by simp [hij, hki.symm, hai5]),
            Finset.card_insert_of_notMem (by simp [hkj.symm, haj5]),
            Finset.card_insert_of_notMem (by simp [hak5]), Finset.card_singleton, hC.1]
    have h5_nd : ¬ (a₅ ∣ Nat.lcm a_j a_k) := by
      intro hdvd
      have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
      have hajA : a_j ∈ A := by
        rw [hd.hA_eq]; rw [hd.hZ_eq] at hajZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hajZ
        rcases hajZ with rfl | rfl | rfl <;> simp
      have hakA : a_k ∈ A := by
        rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ
        rcases hakZ with rfl | rfl | rfl <;> simp
      have hL_pos := finset_lcm_pos_core hC.2.1
      have h5e : (A.lcm id).factorization p₀ ≤ a₅.factorization p₀ := by
        have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) ha5A) (p := p₀)
        simp only [id_eq] at hle
        by_contra hlt; exact hd.ha5Z (hZ_p0 ▸ Finset.mem_filter.mpr ⟨ha5A, by omega⟩)
      have hj_mem : a_j ∈ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀) := hZ_p0 ▸ hajZ
      have hk_mem : a_k ∈ A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀) := hZ_p0 ▸ hakZ
      have hje : a_j.factorization p₀ < (A.lcm id).factorization p₀ := (Finset.mem_filter.mp hj_mem).2
      have hke : a_k.factorization p₀ < (A.lcm id).factorization p₀ := (Finset.mem_filter.mp hk_mem).2
      have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (hC.2.1 a_j hajA) (hC.2.1 a_k hakA)).ne' hdvd (p := p₀)
      rw [fac_lcm_eq_max_5 (hC.2.1 a_j hajA).ne' (hC.2.1 a_k hakA).ne'] at hfac
      omega
    exact ⟨hno_ZB, hpc, hQk_45.1, hQk_45.2, hA_perm,
      hai4.symm, haj4.symm, hak4.symm, hd.ha45, hij, hki.symm, hai5, hkj.symm, haj5, hak5, h5_nd⟩
  · left
    dsimp [PairConst] at hpc
    push Not at hpc
    obtain ⟨u₃, hu3, u₄, hu4, hu34, hne⟩ := hpc
    have hu5_ex : ∃ u₅ ∈ ({a_k, a₄, a₅} : Finset ℕ), ¬ (u₅ ∣ Nat.lcm u₃ u₄) := by
      by_contra hall; push Not at hall
      exact hne (Nat.dvd_antisymm (Nat.lcm_dvd (Finset.dvd_lcm hu3) (Finset.dvd_lcm hu4)) (Finset.lcm_dvd hall))
    obtain ⟨u₅, hu5, hu5_nd⟩ := hu5_ex
    have hu35 : u₃ ≠ u₅ := fun h => hu5_nd (h ▸ Nat.dvd_lcm_left u₃ u₄)
    have hu45 : u₄ ≠ u₅ := fun h => hu5_nd (h ▸ Nat.dvd_lcm_right u₃ u₄)
    have hset3 : ({u₃, u₄, u₅} : Finset ℕ) = {a_k, a₄, a₅} := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [hak4, hak5]),
            Finset.card_insert_of_notMem (by simp [hd.ha45]), Finset.card_singleton,
            Finset.card_insert_of_notMem (by simp [hu34, hu35]),
            Finset.card_insert_of_notMem (by simp [hu45]), Finset.card_singleton]
    have h_not_ij : ∀ x ∈ ({a_k, a₄, a₅} : Finset ℕ), a_j ≠ x ∧ a_i ≠ x := fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hkj.symm, hki.symm⟩
      · exact ⟨haj4, hai4⟩
      · exact ⟨haj5, hai5⟩
    have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
    have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
    have hakA : a_k ∈ A := by
      rw [hd.hA_eq]; rw [hd.hZ_eq] at hakZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hakZ
      rcases hakZ with rfl | rfl | rfl <;> simp
    have haiA : a_i ∈ A := by
      rw [hd.hA_eq]; rw [hd.hZ_eq] at haiZ; simp only [Finset.mem_insert, Finset.mem_singleton] at haiZ
      rcases haiZ with rfl | rfl | rfl <;> simp
    have hajA : a_j ∈ A := by
      rw [hd.hA_eq]; rw [hd.hZ_eq] at hajZ; simp only [Finset.mem_insert, Finset.mem_singleton] at hajZ
      rcases hajZ with rfl | rfl | rfl <;> simp
    have h_in_A : ∀ x ∈ ({a_k, a₄, a₅} : Finset ℕ), x ∈ A := fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hA_perm : A = {a_j, a_i, u₃, u₄, u₅} := by
      refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact hajA
        · exact haiA
        · exact h_in_A x hu3
        · exact h_in_A x hu4
        · exact h_in_A x hu5
      · rw [Finset.card_insert_of_notMem (by simp [hij.symm, (h_not_ij u₃ hu3).1, (h_not_ij u₄ hu4).1, (h_not_ij u₅ hu5).1]),
            Finset.card_insert_of_notMem (by simp [(h_not_ij u₃ hu3).2, (h_not_ij u₄ hu4).2, (h_not_ij u₅ hu5).2]),
            Finset.card_insert_of_notMem (by simp [hu34, hu35]),
            Finset.card_insert_of_notMem (by simp [hu45]), Finset.card_singleton, hC.1]
    exact ⟨u₃, u₄, u₅, hA_perm, hij.symm,
      (h_not_ij u₃ hu3).1, (h_not_ij u₄ hu4).1, (h_not_ij u₅ hu5).1,
      (h_not_ij u₃ hu3).2, (h_not_ij u₄ hu4).2, (h_not_ij u₅ hu5).2,
      hu34, hu35, hu45, hu5_nd, hQk_aj, hQk_ai⟩

private lemma close_Q5_rule1 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    {a_k a_i a_j Q_k Q_i Q_j p₀ : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (hZ_perm : Z = {a_k, a_i, a_j})
    (hki : a_k ≠ a_i) (hkj : a_k ≠ a_j) (hij : a_i ≠ a_j)
    (hQk_pos : 0 < Q_k) (hQi_pos : 0 < Q_i) (hQj_pos : 0 < Q_j)
    (hQk_L : Q_k ∣ L₃)
    (hak_eq : a_k = g₃ * Q_i * Q_j) (hai_eq : a_i = g₃ * Q_k * Q_j) (haj_eq : a_j = g₃ * Q_k * Q_i)
    (hcop_ki : Nat.Coprime Q_k Q_i) (hcop_kj : Nat.Coprime Q_k Q_j)
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a_k ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (hQk5 : Q_k = 5) (h25M : 25 ≤ M) (h6ai : 6 * (a_i / 5) ≤ M) : False := by
  have hL_pos := finset_lcm_pos_core hC.2.1
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have haiZ : a_i ∈ Z := by rw [hZ_perm]; simp
  have haiA : a_i ∈ A := by rw [hd.hA_eq]; rw [hd.hZ_eq] at haiZ; simp only [Finset.mem_insert, Finset.mem_singleton] at haiZ ⊢; tauto
  have h5_ai : 5 ∣ a_i := hQk5 ▸ ⟨g₃ * Q_j, by rw [hai_eq]; ring⟩
  have h5_L : 5 ∣ A.lcm id := dvd_trans h5_ai (Finset.dvd_lcm (f := id) haiA)
  have ⟨_, _, _, _, _, h3_5e⟩ := core_Z_T_props hC Nat.prime_five h5_L
  have h1_ai : 1 ≤ a_i.factorization 5 := (Nat.prime_five.dvd_iff_one_le_factorization (hC.2.1 a_i haiA).ne').mp h5_ai
  have build_5 : ∀ u₁ u₂ u₃ u₄ u₅ : ℕ,
      A = {u₁, u₂, u₃, u₄, u₅} →
      u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₁ ≠ u₅ →
      u₂ ≠ u₃ → u₂ ≠ u₄ → u₂ ≠ u₅ →
      u₃ ≠ u₄ → u₃ ≠ u₅ → u₄ ≠ u₅ →
      ¬ (u₅ ∣ Nat.lcm u₃ u₄) → 5 ∣ u₁ → u₂ = a_i → False := by
    intro u₁ u₂ u₃ u₄ u₅ hAeq h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hnd h5u1 hu2eq
    have hu1A : u₁ ∈ A := by rw [hAeq]; simp
    have h1_u1 : 1 ≤ u₁.factorization 5 := (Nat.prime_five.dvd_iff_one_le_factorization (hC.2.1 u₁ hu1A).ne').mp h5u1
    have h1_u2 : 1 ≤ u₂.factorization 5 := hu2eq ▸ h1_ai
    have h5u1_M : 5 * (u₁ / 5) ≤ M := by
      calc 5 * (u₁ / 5) = u₁ := Nat.mul_div_cancel' h5u1
        _ ≤ M := hC.2.2.1 u₁ hu1A
    have h6u2_M : 6 * (u₂ / 5) ≤ M := hu2eq ▸ h6ai
    exact hNR1 ⟨u₁, u₂, u₃, u₄, u₅, 5, 1, 1, hAeq, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
      hnd, Nat.prime_five, le_rfl, h1_u1, le_rfl, h1_u2, by simpa using h25M, h3_5e, by simpa using h5u1_M, by simpa using h6u2_M⟩
  rcases core_unhit_k_dichotomy hC hd hp0 hp0L hZ_p0 hZ_perm hki hkj hij
      hQk_pos hQi_pos hQj_pos hQk_L hak_eq hai_eq haj_eq hcop_ki hcop_kj h_no3 with
      ⟨u₃, u₄, u₅, hAeq, hji, hj3, hj4, hj5, hi3, hi4, hi5, h34, h35, h45, hnd, hQk_j, _⟩ |
      ⟨_, _, hQk_4, _, hAeq, h4i, h4j, h4k, h45, hij', hik, hi5, hjk, hj5, hk5, hnd⟩
  · exact build_5 a_j a_i u₃ u₄ u₅ hAeq hji hj3 hj4 hj5 hi3 hi4 hi5 h34 h35 h45 hnd (hQk5 ▸ hQk_j) rfl
  · exact build_5 a₄ a_i a_j a_k a₅ hAeq h4i h4j h4k h45 hij' hik hi5 hjk hj5 hk5 hnd (hQk5 ▸ hQk_4) rfl

private lemma close_Rule2_D1_ge5 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    {a_k a_i a_j Q_k Q_i Q_j : ℕ} {p₀ D₁ D₂ : ℕ}
    (hC : C5Core A M) (hNR2 : ¬ HasRule2 A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (hZ_perm : Z = {a_k, a_i, a_j})
    (hki : a_k ≠ a_i) (hkj : a_k ≠ a_j) (hij : a_i ≠ a_j)
    (hQk_pos : 0 < Q_k) (hQi_pos : 0 < Q_i) (hQj_pos : 0 < Q_j)
    (hQk_L : Q_k ∣ L₃)
    (hak_eq : a_k = g₃ * Q_i * Q_j) (hai_eq : a_i = g₃ * Q_k * Q_j) (haj_eq : a_j = g₃ * Q_k * Q_i)
    (hcop_ki : Nat.Coprime Q_k Q_i) (hcop_kj : Nat.Coprime Q_k Q_j)
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a_k ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (hD1_pos : 0 < D₁) (hD1_5 : 5 ≤ D₁) (hD1_Q : D₁ ∣ Q_k)
    (hD2_pos : 0 < D₂) (hD2_Q : D₂ ∣ Q_k)
    (h4D : 4 * (D₁ * D₂) ≤ M) (h6ai : 6 * (a_i / D₂) ≤ M) : False := by
  have hD2_ai : D₂ ∣ a_i := dvd_trans hD2_Q ⟨g₃ * Q_j, by rw [hai_eq]; ring⟩
  have build_r2 : ∀ u₁ u₂ u₃ u₄ u₅ : ℕ,
      A = {u₁, u₂, u₃, u₄, u₅} →
      u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₁ ≠ u₅ →
      u₂ ≠ u₃ → u₂ ≠ u₄ → u₂ ≠ u₅ →
      u₃ ≠ u₄ → u₃ ≠ u₅ → u₄ ≠ u₅ →
      ¬ (u₅ ∣ Nat.lcm u₃ u₄) → Q_k ∣ u₁ → u₂ = a_i → False := by
    intro u₁ u₂ u₃ u₄ u₅ hAeq h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hnd hQku1 hu2eq
    have hu1A : u₁ ∈ A := by rw [hAeq]; simp
    have hD1_u1 : D₁ ∣ u₁ := dvd_trans hD1_Q hQku1
    have h5u1 : 5 * (u₁ / D₁) ≤ M := by
      calc 5 * (u₁ / D₁) ≤ D₁ * (u₁ / D₁) := Nat.mul_le_mul_right _ hD1_5
        _ = u₁ := Nat.mul_div_cancel' hD1_u1
        _ ≤ M := hC.2.2.1 u₁ hu1A
    exact hNR2 ⟨u₁, u₂, u₃, u₄, u₅, D₁, D₂, hAeq, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
      hnd, hD1_pos, hD1_u1, hD2_pos, hu2eq ▸ hD2_ai, h4D, h5u1, hu2eq ▸ h6ai⟩
  rcases core_unhit_k_dichotomy hC hd hp0 hp0L hZ_p0 hZ_perm hki hkj hij
      hQk_pos hQi_pos hQj_pos hQk_L hak_eq hai_eq haj_eq hcop_ki hcop_kj h_no3 with
      ⟨u₃, u₄, u₅, hAeq, hji, hj3, hj4, hj5, hi3, hi4, hi5, h34, h35, h45, hnd, hQk_j, _⟩ |
      ⟨_, _, hQk_4, _, hAeq, h4i, h4j, h4k, h45, hij', hik, hi5, hjk, hj5, hk5, hnd⟩
  · exact build_r2 a_j a_i u₃ u₄ u₅ hAeq hji hj3 hj4 hj5 hi3 hi4 hi5 h34 h35 h45 hnd hQk_j rfl
  · exact build_r2 a₄ a_i a_j a_k a₅ hAeq h4i h4j h4k h45 hij' hik hi5 hjk hj5 hk5 hnd hQk_4 rfl

private lemma decide_gcd_272_2g :
    ((List.range 100).all fun g =>
      decide (69 ≤ g → 3 * g ≠ 255 → ¬ 17 ∣ g)) = true := by
  decide

private lemma close_Q15_16_17 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ p₀ : ℕ}
    (hC : C5Core A M) (hNR2 : ¬ HasRule2 A M) (hNR2b : ¬ HasRule2b A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a₃ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (hQ3 : Q₃ = 15) (hQ2 : Q₂ = 16) (hQ1 : Q₁ = 17) : False := by
  have ha1_eq : a₁ = g₃ * 240 := by rw [hd.ha1_eq, hQ2, hQ3]; ring
  have ha2_eq : a₂ = g₃ * 255 := by rw [hd.ha2_eq, hQ1, hQ3]; ring
  have ha3_eq : a₃ = g₃ * 272 := by rw [hd.ha3_eq, hQ1, hQ2]; ring
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha3M := hC.2.2.1 a₃ ha3A
  have hZ_perm : Z = {a₃, a₁, a₂} := by rw [hd.hZ_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hQ3L : Q₃ ∣ L₃ := ⟨g₃ * 16 * 17, by rw [hd.hL3_eq, hQ3, hQ2, hQ1]; ring⟩
  have ha3_eq' : a₃ = g₃ * Q₁ * Q₂ := hd.ha3_eq
  have ha1_eq' : a₁ = g₃ * Q₃ * Q₂ := by rw [hd.ha1_eq]; ring
  have ha2_eq' : a₂ = g₃ * Q₃ * Q₁ := by rw [hd.ha2_eq]; ring
  by_cases hM300 : 300 ≤ M
  · have h6ai : 6 * (a₁ / 15) ≤ M := by
      have hdiv : a₁ / 15 = g₃ * 16 := by rw [ha1_eq]; omega
      rw [hdiv]; omega
    exact close_Rule2_D1_ge5 (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
      hC hNR2 hd hp0 hp0L hZ_p0 hZ_perm
      (lt_trans hd.ha12 hd.ha23).ne' hd.ha23.ne' hd.ha12.ne
      (by omega) (by omega) (by omega) hQ3L ha3_eq' ha1_eq' ha2_eq'
      hd.hcop13.symm hd.hcop23.symm h_no3
      (by decide : 0 < 5) (by decide : 5 ≤ 5) (by rw [hQ3]; decide)
      (by decide : 0 < 15) (by rw [hQ3]) (by omega) h6ai
  · have hg3_1 : g₃ = 1 := by have := hd.hg3_pos; omega
    have ha1_v : a₁ = 240 := by rw [ha1_eq, hg3_1, one_mul]
    have ha2_v : a₂ = 255 := by rw [ha2_eq, hg3_1, one_mul]
    have ha3_v : a₃ = 272 := by rw [ha3_eq, hg3_1, one_mul]
    have hM272 : 272 ≤ M := by omega
    have hM_lt300 : M < 300 := by omega
    have h3_75 : 3 * (5 * 15) ≤ M := by omega
    have h6_16 : 6 * (a₁ / 15) ≤ M := by rw [ha1_v]; exact le_trans (by decide : 6 * (240 / 15) ≤ 272) hM272
    rcases core_unhit_k_dichotomy (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
        hC hd hp0 hp0L hZ_p0 hZ_perm
        (lt_trans hd.ha12 hd.ha23).ne' hd.ha23.ne' hd.ha12.ne
        (by omega) (by omega) (by omega) hQ3L ha3_eq' ha1_eq' ha2_eq'
        hd.hcop13.symm hd.hcop23.symm h_no3 with
        ⟨u₃, u₄, u₅, hAeq, h21, h23, h24, h25, h13, h14, h15, h34, h35, h45, hnd, _, _⟩ |
        ⟨_, _, hQ3_4, _, hAeq, h41, h42, h43, h45, h12, h13, h15, h23, h25, h35, hnd⟩
    · have ha1_15 : 15 ∣ a₁ := by rw [ha1_v]; decide
      have ha2_5 : 5 ∣ a₂ := by rw [ha2_v]; decide
      by_cases h4g : 4 * Nat.gcd u₃ u₄ ≤ M
      · exact hNR2b ⟨a₂, a₁, u₃, u₄, u₅, 5, 15, hAeq, h21, h23, h24, h25, h13, h14, h15,
          h34, h35, h45, hnd, by decide, ha2_5, by decide, ha1_15, h3_75, h4g, by rw [ha2_v]; omega, h6_16⟩
      · have hbad : M < 4 * Nat.gcd u₃ u₄ := by omega
        let g := Nat.gcd u₃ u₄
        have hu3A : u₃ ∈ A := by rw [hAeq]; simp
        have hu4A : u₄ ∈ A := by rw [hAeq]; simp
        have hu3p := hC.2.1 u₃ hu3A
        have hu4p := hC.2.1 u₄ hu4A
        have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left u₄ hu3p
        have hg3_dvd : g ∣ u₃ := Nat.gcd_dvd_left u₃ u₄
        have hg4_dvd : g ∣ u₄ := Nat.gcd_dvd_right u₃ u₄
        have hq3_pos : 0 < u₃ / g := Nat.div_pos (Nat.le_of_dvd hu3p hg3_dvd) hg_pos
        have hq4_pos : 0 < u₄ / g := Nat.div_pos (Nat.le_of_dvd hu4p hg4_dvd) hg_pos
        have hm3 : g * (u₃ / g) = u₃ := Nat.mul_div_cancel' hg3_dvd
        have hm4 : g * (u₄ / g) = u₄ := Nat.mul_div_cancel' hg4_dvd
        have hlt34 : u₃ / g ≠ u₄ / g := fun h => h34 (by rw [← hm3, ← hm4, h])
        have hle3 : u₃ / g ≤ 3 := by
          by_contra h4; push Not at h4
          have : 4 * g ≤ g * (u₃ / g) := by rw [mul_comm g (u₃ / g)]; exact Nat.mul_le_mul_right g h4
          have := hC.2.2.1 u₃ hu3A; omega
        have hle4 : u₄ / g ≤ 3 := by
          by_contra h4; push Not at h4
          have : 4 * g ≤ g * (u₄ / g) := by rw [mul_comm g (u₄ / g)]; exact Nat.mul_le_mul_right g h4
          have := hC.2.2.1 u₄ hu4A; omega
        have hge2_3 : 2 ≤ u₃ / g := by
          by_contra h1; push Not at h1
          have h1eq : u₃ / g = 1 := by omega
          have hu3g : u₃ = g := by rw [← hm3, h1eq, mul_one]
          have hu4_2g : 2 * g ≤ u₄ := by
            have : 2 ≤ u₄ / g := by omega
            calc 2 * g ≤ (u₄ / g) * g := Nat.mul_le_mul_right g this
              _ = u₄ := by rw [mul_comm, hm4]
          have := hC.2.2.2.1 u₃ hu3A; have := hC.2.2.1 u₄ hu4A; omega
        have hge2_4 : 2 ≤ u₄ / g := by
          by_contra h1; push Not at h1
          have h1eq : u₄ / g = 1 := by omega
          have hu4g : u₄ = g := by rw [← hm4, h1eq, mul_one]
          have hu3_2g : 2 * g ≤ u₃ := by
            have : 2 ≤ u₃ / g := by omega
            calc 2 * g ≤ (u₃ / g) * g := Nat.mul_le_mul_right g this
              _ = u₃ := by rw [mul_comm, hm3]
          have := hC.2.2.2.1 u₄ hu4A; have := hC.2.2.1 u₃ hu3A; omega
        -- So `{u₃, u₄} = {2 * g, 3 * g}`! In particular `a₃ = 272 ∉ {u₃, u₄}`, hence `u₅ = 272`!
        have hu5_eq : u₅ = 272 := by
          have ha3_mem : 272 ∈ A := ha3_v ▸ ha3A
          rw [hAeq] at ha3_mem; simp only [Finset.mem_insert, Finset.mem_singleton] at ha3_mem
          rcases ha3_mem with h | h | h | h | h
          · exact absurd (h.trans ha2_v) (by omega)
          · exact absurd (h.trans ha1_v) (by omega)
          · exfalso
            rcases (by omega : (u₃ / g = 2 ∧ u₄ / g = 3) ∨ (u₃ / g = 3 ∧ u₄ / g = 2)) with ⟨h32, h43⟩ | ⟨h33, h42⟩
            · have : u₃ = 2 * g := by rw [← hm3, h32]; ring
              have : u₄ = 3 * g := by rw [← hm4, h43]; ring
              have := hC.2.2.1 u₄ hu4A; omega
            · have : u₃ = 3 * g := by rw [← hm3, h33]; ring
              omega
          · exfalso
            rcases (by omega : (u₃ / g = 2 ∧ u₄ / g = 3) ∨ (u₃ / g = 3 ∧ u₄ / g = 2)) with ⟨h32, h43⟩ | ⟨h33, h42⟩
            · have : u₄ = 3 * g := by rw [← hm4, h43]; ring
              omega
            · have : u₄ = 2 * g := by rw [← hm4, h42]; ring
              have : u₃ = 3 * g := by rw [← hm3, h33]; ring
              have := hC.2.2.1 u₃ hu3A; omega
          · exact h.symm
        -- Extract `(wlo, whi) = (2 * g, 3 * g)` from `{u₃, u₄}`:
        have hex_23 : ∃ wlo whi : ℕ, {u₃, u₄} = ({wlo, whi} : Finset ℕ) ∧ wlo = 2 * g ∧ whi = 3 * g ∧
            a₂ ≠ wlo ∧ a₂ ≠ whi ∧ a₁ ≠ wlo ∧ a₁ ≠ whi ∧ wlo ≠ whi ∧ 272 ≠ wlo ∧ 272 ≠ whi := by
          rcases (by omega : (u₃ / g = 2 ∧ u₄ / g = 3) ∨ (u₃ / g = 3 ∧ u₄ / g = 2)) with ⟨h32, h43⟩ | ⟨h33, h42⟩
          · refine ⟨u₃, u₄, rfl, by rw [← hm3, h32]; ring, by rw [← hm4, h43]; ring,
              h23, h24, h13, h14, h34, ?_, ?_⟩ <;> [exact hu5_eq ▸ h35.symm; exact hu5_eq ▸ h45.symm]
          · refine ⟨u₄, u₃, Finset.pair_comm _ _, by rw [← hm4, h42]; ring, by rw [← hm3, h33]; ring,
              h24, h23, h14, h13, h34.symm, ?_, ?_⟩ <;> [exact hu5_eq ▸ h45.symm; exact hu5_eq ▸ h35.symm]
        obtain ⟨wlo, whi, h34_set, hwlo_eq, hwhi_eq, h2w, h2wh, h1w, h1wh, hww, h272w, h272wh⟩ := hex_23
        have hnd_new : ¬ (whi ∣ Nat.lcm 272 wlo) := by
          intro hdvd
          have h272p : (272 : ℕ) ≠ 0 := by decide
          have hwlop : wlo ≠ 0 := by omega
          have hfac := fac_le_of_dvd_5 (Nat.lcm_pos (by decide : 0 < 272) (by omega : 0 < wlo)).ne' hdvd (p := 3)
          rw [fac_lcm_eq_max_5 h272p hwlop] at hfac
          have h272_3 : (272 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
          have hwlo_3 : wlo.factorization 3 = g.factorization 3 := by
            rw [hwlo_eq, Nat.factorization_mul (by decide) hg_pos.ne', Finsupp.coe_add, Pi.add_apply,
                Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), zero_add]
          have hwhi_3 : whi.factorization 3 = 1 + g.factorization 3 := by
            have h33 : (3 : ℕ).factorization 3 = 1 := fac_eq_of_pow_dvd_not Nat.prime_three (by decide) (by decide) (by decide)
            rw [hwhi_eq, Nat.factorization_mul (by decide) hg_pos.ne', Finsupp.coe_add, Pi.add_apply, h33]
          omega
        have hg_lt100 : g < 100 := by
          have : 3 * g ≤ M := by
            rw [← hwhi_eq]; exact hC.2.2.1 whi (by
              have : whi ∈ ({wlo, whi} : Finset ℕ) := by simp
              rw [← h34_set] at this; simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with rfl | rfl <;> assumption)
          omega
        have hg_ge69 : 69 ≤ g := by
          have hwloA : wlo ∈ A := by
            have hmem : wlo ∈ ({u₃, u₄} : Finset ℕ) := by rw [h34_set]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl <;> assumption
          have hwloM := hC.2.2.2.1 wlo hwloA
          omega
        have hn17 : ¬ 17 ∣ g := by
          have hdec := decide_gcd_272_2g
          rw [List.all_eq_true] at hdec
          exact of_decide_eq_true (hdec g (List.mem_range.mpr hg_lt100)) hg_ge69
            (by rw [← hwhi_eq, ← ha2_v]; exact h2wh.symm)
        have hgcd_le16 : Nat.gcd 272 wlo ≤ 16 := by
          have hdvd_272 : Nat.gcd 272 wlo ∣ 16 * 17 := Nat.gcd_dvd_left 272 wlo
          have hn17_w : ¬ 17 ∣ Nat.gcd 272 wlo := fun h => by
            have h17w : 17 ∣ 2 * g := hwlo_eq ▸ dvd_trans h (Nat.gcd_dvd_right 272 wlo)
            rcases (by decide : Nat.Prime 17).dvd_mul.mp h17w with h17_2 | h17_g
            · revert h17_2; decide
            · exact hn17 h17_g
          have hcop17 : Nat.Coprime (Nat.gcd 272 wlo) 17 :=
            Nat.Coprime.symm ((by decide : Nat.Prime 17).coprime_iff_not_dvd.mpr hn17_w)
          have hd16 : Nat.gcd 272 wlo ∣ 16 := hcop17.dvd_of_dvd_mul_right hdvd_272
          exact Nat.le_of_dvd (by decide) hd16
        have hA_new : A = {a₂, a₁, 272, wlo, whi} := by
          have hu3_in : u₃ ∈ A := by rw [hAeq]; simp
          have hu4_in : u₄ ∈ A := by rw [hAeq]; simp
          have hwloA : wlo ∈ A := by
            have hm : wlo ∈ ({u₃, u₄} : Finset ℕ) := by rw [h34_set]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl <;> assumption
          have hwhiA : whi ∈ A := by
            have hm : whi ∈ ({u₃, u₄} : Finset ℕ) := by rw [h34_set]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl <;> assumption
          refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl
            · exact by rw [hAeq]; simp
            · exact by rw [hAeq]; simp
            · exact ha3_v ▸ ha3A
            · exact hwloA
            · exact hwhiA
          · rw [Finset.card_insert_of_notMem (by
                  intro hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with h | h | h | h
                  · exact h21 h
                  · rw [ha2_v] at h; omega
                  · exact h2w h
                  · exact h2wh h),
                Finset.card_insert_of_notMem (by
                  intro hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with h | h | h
                  · rw [ha1_v] at h; omega
                  · exact h1w h
                  · exact h1wh h),
                Finset.card_insert_of_notMem (by simp [h272w, h272wh]),
                Finset.card_insert_of_notMem (by simp [hww]), Finset.card_singleton, hC.1]
        exact hNR2b ⟨a₂, a₁, 272, wlo, whi, 5, 15, hA_new, h21, (by rw [ha2_v]; decide), h2w, h2wh,
          (by rw [ha1_v]; decide), h1w, h1wh, h272w, h272wh, hww, hnd_new,
          by decide, ha2_5, by decide, ha1_15, h3_75, by omega, by rw [ha2_v]; omega, h6_16⟩
    · have ha1_15 : 15 ∣ a₁ := by rw [ha1_v]; decide
      have ha4_5 : 5 ∣ a₄ := dvd_trans (by decide : 5 ∣ 15) (hQ3 ▸ hQ3_4)
      have hgcd_255_272 : 4 * Nat.gcd a₂ a₃ ≤ M := by
        rw [ha2_v, ha3_v]; exact le_trans (by decide : 4 * Nat.gcd 255 272 ≤ 272) hM272
      exact hNR2b ⟨a₄, a₁, a₂, a₃, a₅, 5, 15, hAeq, h41, h42, h43, h45, h12, h13, h15,
        h23, h25, h35, hnd, by decide, ha4_5, by decide, ha1_15, h3_75, hgcd_255_272,
        by calc 5 * (a₄ / 5) = a₄ := Nat.mul_div_cancel' ha4_5
          _ ≤ M := hC.2.2.1 a₄ (by rw [hd.hA_eq]; simp), h6_16⟩

private lemma close_Q6_6_7_11 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ p₀ : ℕ}
    (hC : C5Core A M) (hNR2 : ¬ HasRule2 A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a₃ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (hQ3 : Q₃ = 6) (hQ2 : Q₂ = 7) (hQ1 : Q₁ = 11) : False := by
  have ha1_eq : a₁ = g₃ * 42 := by rw [hd.ha1_eq, hQ2, hQ3]; ring
  have ha2_eq : a₂ = g₃ * 66 := by rw [hd.ha2_eq, hQ1, hQ3]; ring
  have ha3_eq : a₃ = g₃ * 77 := by rw [hd.ha3_eq, hQ1, hQ2]; ring
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha3M := hC.2.2.1 a₃ ha3A
  have hg3p := hd.hg3_pos
  have h5a1 : 5 * (a₁ / 3) ≤ M := by
    have : a₁ / 3 = g₃ * 14 := by rw [ha1_eq]; omega
    rw [this]; omega
  have h4_18 : 4 * (3 * 6) ≤ M := by omega
  have h3a1 : 3 ∣ a₁ := ⟨g₃ * 14, by rw [ha1_eq]; ring⟩
  have build_6 : ∀ u₁ u₂ u₃ u₄ u₅ : ℕ,
      A = {u₁, u₂, u₃, u₄, u₅} →
      u₁ ≠ u₂ → u₁ ≠ u₃ → u₁ ≠ u₄ → u₁ ≠ u₅ →
      u₂ ≠ u₃ → u₂ ≠ u₄ → u₂ ≠ u₅ →
      u₃ ≠ u₄ → u₃ ≠ u₅ → u₄ ≠ u₅ →
      ¬ (u₅ ∣ Nat.lcm u₃ u₄) → u₁ = a₁ → 6 ∣ u₂ → False := by
    intro u₁ u₂ u₃ u₄ u₅ hAeq h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hnd hu1eq h6u2
    have hu2A : u₂ ∈ A := by rw [hAeq]; simp
    have h6u2_M : 6 * (u₂ / 6) ≤ M := by
      calc 6 * (u₂ / 6) = u₂ := Nat.mul_div_cancel' h6u2
        _ ≤ M := hC.2.2.1 u₂ hu2A
    exact hNR2 ⟨u₁, u₂, u₃, u₄, u₅, 3, 6, hAeq, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45,
      hnd, by decide, hu1eq ▸ h3a1, by decide, h6u2, h4_18, hu1eq ▸ h5a1, h6u2_M⟩
  have hZ_perm : Z = {a₃, a₁, a₂} := by rw [hd.hZ_eq]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hQ3L : Q₃ ∣ L₃ := ⟨g₃ * 7 * 11, by rw [hd.hL3_eq, hQ3, hQ2, hQ1]; ring⟩
  have ha3_eq' : a₃ = g₃ * Q₁ * Q₂ := hd.ha3_eq
  have ha1_eq' : a₁ = g₃ * Q₃ * Q₂ := by rw [hd.ha1_eq]; ring
  have ha2_eq' : a₂ = g₃ * Q₃ * Q₁ := by rw [hd.ha2_eq]; ring
  rcases core_unhit_k_dichotomy (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
      hC hd hp0 hp0L hZ_p0 hZ_perm
      (lt_trans hd.ha12 hd.ha23).ne' hd.ha23.ne' hd.ha12.ne
      (by omega) (by omega) (by omega) hQ3L ha3_eq' ha1_eq' ha2_eq'
      hd.hcop13.symm hd.hcop23.symm h_no3 with
      ⟨u₃, u₄, u₅, hAeq, h21, h23, h24, h25, h13, h14, h15, h34, h35, h45, hnd, h6_2, _⟩ |
      ⟨_, _, h6_4, _, hAeq, h41, h42, h43, h45, h12, h13, h15, h23, h25, h35, hnd⟩
  · have hA_sw : A = {a₁, a₂, u₃, u₄, u₅} := by rw [hAeq, Finset.insert_comm a₂ a₁ {u₃, u₄, u₅}]
    exact build_6 a₁ a₂ u₃ u₄ u₅ hA_sw h21.symm h13 h14 h15 h23 h24 h25 h34 h35 h45 hnd rfl (hQ3 ▸ h6_2)
  · have ha1A : a₁ ∈ A := by rw [hAeq]; simp
    have ha4A : a₄ ∈ A := by rw [hAeq]; simp
    have ha2A : a₂ ∈ A := by rw [hAeq]; simp
    have ha3A' : a₃ ∈ A := by rw [hAeq]; simp
    have ha5A : a₅ ∈ A := by rw [hAeq]; simp
    have hA_sw : A = {a₁, a₄, a₂, a₃, a₅} := by
      refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [h41.symm, h12, h13, h15]),
            Finset.card_insert_of_notMem (by simp [h42, h43, h45]),
            Finset.card_insert_of_notMem (by simp [h23, h25]),
            Finset.card_insert_of_notMem (by simp [h35]), Finset.card_singleton, hC.1]
    exact build_6 a₁ a₄ a₂ a₃ a₅ hA_sw h41.symm h12 h13 h15 h42 h43 h45 h23 h25 h35 hnd rfl (hQ3 ▸ h6_4)

private lemma decide_567_g1 :
    ((List.range 60).all fun a₄ =>
      (List.range 60).all fun a₅ =>
        decide (22 ≤ a₄ → a₄ < a₅ → a₄ ≠ 30 → a₄ ≠ 35 → a₄ ≠ 42 →
          a₅ ≠ 30 → a₅ ≠ 35 → a₅ ≠ 42 → a₅ < 2 * min 30 a₄ →
          Nat.lcm 42 a₄ = Nat.lcm 42 a₅ → Nat.lcm 42 a₄ = Nat.lcm a₄ a₅ →
          210 % Nat.gcd a₄ a₅ = 0)) = true := by
  decide

private lemma close_567_g1 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    (hC : C5Core A M) (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hQ3 : Q₃ = 5) (hQ2 : Q₂ = 6) (hQ1 : Q₁ = 7) (hg3 : g₃ = 1)
    (hpc_ZB : PairConst ({a₃, a₄, a₅} : Finset ℕ)) : False := by
  have ha1_v : a₁ = 30 := by rw [hd.ha1_eq, hg3, hQ2, hQ3]
  have ha2_v : a₂ = 35 := by rw [hd.ha2_eq, hg3, hQ1, hQ3]
  have ha3_v : a₃ = 42 := by rw [hd.ha3_eq, hg3, hQ1, hQ2]
  have hL3_v : L₃ = 210 := by rw [hd.hL3_eq, hg3, hQ1, hQ2, hQ3]
  have ha1A : a₁ ∈ A := by rw [hd.hA_eq]; simp
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
  have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
  have ha1M : M < 2 * 30 := ha1_v ▸ hC.2.2.2.1 a₁ ha1A
  have ha4M : M < 2 * a₄ := hC.2.2.2.1 a₄ ha4A
  have ha5M : M < 2 * a₅ := hC.2.2.2.1 a₅ ha5A
  have ha4_le : a₄ ≤ M := hC.2.2.1 a₄ ha4A
  have ha5_le : a₅ ≤ M := hC.2.2.1 a₅ ha5A
  have ha3_le : 42 ≤ M := ha3_v ▸ hC.2.2.1 a₃ ha3A
  have ha4_ge22 : 22 ≤ a₄ := by omega
  have ha5_ge22 : 22 ≤ a₅ := by omega
  have ha4_lt60 : a₄ < 60 := by omega
  have ha5_lt60 : a₅ < 60 := by omega
  have hn_Z : ∀ x ∈ ({a₄, a₅} : Finset ℕ), x ≠ 30 ∧ x ≠ 35 ∧ x ≠ 42 := fun x hx => by
    have hnx : x ∉ Z := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hd.ha4Z; exact hd.ha5Z]
    rw [hd.hZ_eq, ha1_v, ha2_v, ha3_v] at hnx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
    push Not at hnx; exact ⟨hnx.1, hnx.2.1, hnx.2.2⟩
  have hlcm1 : Nat.lcm a₃ a₄ = Nat.lcm a₃ a₅ :=
    (hpc_ZB a₃ (by simp) a₄ (by simp) (fun h => hd.ha4Z (h ▸ (by rw [hd.hZ_eq]; simp)))).trans
    (hpc_ZB a₃ (by simp) a₅ (by simp) (fun h => hd.ha5Z (h ▸ (by rw [hd.hZ_eq]; simp)))).symm
  have hlcm2 : Nat.lcm a₃ a₄ = Nat.lcm a₄ a₅ :=
    (hpc_ZB a₃ (by simp) a₄ (by simp) (fun h => hd.ha4Z (h ▸ (by rw [hd.hZ_eq]; simp)))).trans
    (hpc_ZB a₄ (by simp) a₅ (by simp) hd.ha45).symm
  have hngcd : ¬ Nat.gcd a₄ a₅ ∣ 210 := hL3_v ▸ hd.hngcd
  have check_ord : ∀ x y : ℕ, x < 60 → y < 60 → 22 ≤ x → x < y →
      x ≠ 30 → x ≠ 35 → x ≠ 42 → y ≠ 30 → y ≠ 35 → y ≠ 42 →
      y < 2 * min 30 x → Nat.lcm 42 x = Nat.lcm 42 y → Nat.lcm 42 x = Nat.lcm x y →
      Nat.gcd x y ∣ 210 := fun x y hx60 hy60 hx22 hxy h1 h2 h3 h4 h5 h6 hlt hl1 hl2 => by
    have hdec := decide_567_g1
    rw [List.all_eq_true] at hdec
    have hdec2 := hdec x (List.mem_range.mpr hx60)
    rw [List.all_eq_true] at hdec2
    have hmod := of_decide_eq_true (hdec2 y (List.mem_range.mpr hy60)) hx22 hxy h1 h2 h3 h4 h5 h6 hlt hl1 hl2
    exact Nat.dvd_of_mod_eq_zero hmod
  rcases lt_or_gt_of_ne hd.ha45 with h45 | h54
  · refine hngcd (check_ord a₄ a₅ ha4_lt60 ha5_lt60 ha4_ge22 h45
      (hn_Z a₄ (by simp)).1 (hn_Z a₄ (by simp)).2.1 (hn_Z a₄ (by simp)).2.2
      (hn_Z a₅ (by simp)).1 (hn_Z a₅ (by simp)).2.1 (hn_Z a₅ (by simp)).2.2
      (by simp only [min_def]; split_ifs <;> omega) (ha3_v ▸ hlcm1) (ha3_v ▸ hlcm2))
  · have hmod := check_ord a₅ a₄ ha5_lt60 ha4_lt60 ha5_ge22 h54
      (hn_Z a₅ (by simp)).1 (hn_Z a₅ (by simp)).2.1 (hn_Z a₅ (by simp)).2.2
      (hn_Z a₄ (by simp)).1 (hn_Z a₄ (by simp)).2.1 (hn_Z a₄ (by simp)).2.2
      (by simp only [min_def]; split_ifs <;> omega) (ha3_v ▸ hlcm1.symm)
      (by rw [← ha3_v, ← hlcm1, hlcm2, Nat.lcm_comm])
    rw [Nat.gcd_comm] at hmod
    exact hngcd hmod

private lemma decide_345_g1 :
    ((List.range 24).all fun a₄ =>
      (List.range 24).all fun a₅ =>
        decide (11 ≤ a₄ → a₄ < a₅ → a₄ ≠ 12 → a₄ ≠ 15 → a₄ ≠ 20 →
          a₅ ≠ 12 → a₅ ≠ 15 → a₅ ≠ 20 → a₅ < 2 * min 12 a₄ →
          60 % Nat.gcd a₄ a₅ ≠ 0 → a₄ = 14 ∧ a₅ = 21)) = true := by
  decide

private lemma close_345_g1 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    (hC : C5Core A M) (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hQ3 : Q₃ = 3) (hQ2 : Q₂ = 4) (hQ1 : Q₁ = 5) (hg3 : g₃ = 1) : False := by
  have ha1_v : a₁ = 12 := by rw [hd.ha1_eq, hg3, hQ2, hQ3]
  have ha2_v : a₂ = 15 := by rw [hd.ha2_eq, hg3, hQ1, hQ3]
  have ha3_v : a₃ = 20 := by rw [hd.ha3_eq, hg3, hQ1, hQ2]
  have hL3_v : L₃ = 60 := by rw [hd.hL3_eq, hg3, hQ1, hQ2, hQ3]
  have ha1A : a₁ ∈ A := by rw [hd.hA_eq]; simp
  have ha2A : a₂ ∈ A := by rw [hd.hA_eq]; simp
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha4A : a₄ ∈ A := by rw [hd.hA_eq]; simp
  have ha5A : a₅ ∈ A := by rw [hd.hA_eq]; simp
  have ha1M : M < 2 * 12 := ha1_v ▸ hC.2.2.2.1 a₁ ha1A
  have ha4M : M < 2 * a₄ := hC.2.2.2.1 a₄ ha4A
  have ha5M : M < 2 * a₅ := hC.2.2.2.1 a₅ ha5A
  have ha4_le : a₄ ≤ M := hC.2.2.1 a₄ ha4A
  have ha5_le : a₅ ≤ M := hC.2.2.1 a₅ ha5A
  have ha3_le : 20 ≤ M := ha3_v ▸ hC.2.2.1 a₃ ha3A
  have ha4_ge11 : 11 ≤ a₄ := by omega
  have ha5_ge11 : 11 ≤ a₅ := by omega
  have ha4_lt24 : a₄ < 24 := by omega
  have ha5_lt24 : a₅ < 24 := by omega
  have hn_Z : ∀ x ∈ ({a₄, a₅} : Finset ℕ), x ≠ 12 ∧ x ≠ 15 ∧ x ≠ 20 := fun x hx => by
    have hnx : x ∉ Z := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hd.ha4Z; exact hd.ha5Z]
    rw [hd.hZ_eq, ha1_v, ha2_v, ha3_v] at hnx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
    push Not at hnx; exact ⟨hnx.1, hnx.2.1, hnx.2.2⟩
  have hngcd : ¬ Nat.gcd a₄ a₅ ∣ 60 := hL3_v ▸ hd.hngcd
  have check_pair : ∀ x y : ℕ, x < 24 → y < 24 → 11 ≤ x → x < y →
      x ≠ 12 → x ≠ 15 → x ≠ 20 → y ≠ 12 → y ≠ 15 → y ≠ 20 →
      y < 2 * min 12 x → ¬ Nat.gcd x y ∣ 60 → x = 14 ∧ y = 21 := fun x y hx24 hy24 hx11 hxy h1 h2 h3 h4 h5 h6 hlt hnd => by
    have hdec := decide_345_g1
    rw [List.all_eq_true] at hdec
    have hdec2 := hdec x (List.mem_range.mpr hx24)
    rw [List.all_eq_true] at hdec2
    have hmod_ne : 60 % Nat.gcd x y ≠ 0 := fun hm => hnd (Nat.dvd_of_mod_eq_zero hm)
    exact of_decide_eq_true (hdec2 y (List.mem_range.mpr hy24)) hx11 hxy h1 h2 h3 h4 h5 h6 hlt hmod_ne
  have h14_21 : ({a₄, a₅} : Finset ℕ) = {14, 21} := by
    rcases lt_or_gt_of_ne hd.ha45 with h45 | h54
    · have ⟨h1, h2⟩ := check_pair a₄ a₅ ha4_lt24 ha5_lt24 ha4_ge11 h45
        (hn_Z a₄ (by simp)).1 (hn_Z a₄ (by simp)).2.1 (hn_Z a₄ (by simp)).2.2
        (hn_Z a₅ (by simp)).1 (hn_Z a₅ (by simp)).2.1 (hn_Z a₅ (by simp)).2.2
        (by simp only [min_def]; split_ifs <;> omega) hngcd
      rw [h1, h2]
    · have ⟨h1, h2⟩ := check_pair a₅ a₄ ha5_lt24 ha4_lt24 ha5_ge11 h54
        (hn_Z a₅ (by simp)).1 (hn_Z a₅ (by simp)).2.1 (hn_Z a₅ (by simp)).2.2
        (hn_Z a₄ (by simp)).1 (hn_Z a₄ (by simp)).2.1 (hn_Z a₄ (by simp)).2.2
        (by simp only [min_def]; split_ifs <;> omega) (by rw [Nat.gcd_comm]; exact hngcd)
      rw [h1, h2, Finset.pair_comm]
  have h14A : 14 ∈ A := by
    have : (14 : ℕ) ∈ ({a₄, a₅} : Finset ℕ) := by rw [h14_21]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h <;> [exact h ▸ ha4A; exact h ▸ ha5A]
  have h21A : 21 ∈ A := by
    have : (21 : ℕ) ∈ ({a₄, a₅} : Finset ℕ) := by rw [h14_21]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h <;> [exact h ▸ ha4A; exact h ▸ ha5A]
  have h15A : 15 ∈ A := ha2_v ▸ ha2A
  have h20A : 20 ∈ A := ha3_v ▸ ha3A
  have hdvd := hC.2.2.2.2.2.1 15 h15A 21 h21A 14 h14A 20 h20A
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert hdvd; decide

private lemma decide_Qk_Q3 :
    (([3, 4, 5, 6, 10, 15] : List ℕ).all fun Q3 =>
      (List.range 31).all fun Q2 =>
        (List.range 31).all fun Q1 =>
          decide ((3 ≤ Q3 ∧ Q3 < Q2 ∧ Q2 < Q1 ∧ Q1 < 2 * Q3 ∧
            Nat.gcd Q1 Q2 = 1 ∧ Nat.gcd Q1 Q3 = 1 ∧ Nat.gcd Q2 Q3 = 1) →
            (Q3 = 6 → Q2 = 7 ∧ Q1 = 11) ∧
            (Q3 = 4 → Q2 = 5 ∧ Q1 = 7) ∧
            (Q3 = 3 → Q2 = 4 ∧ Q1 = 5))) = true := by
  decide

private lemma decide_Qk_Q2a :
    (([3, 4, 5, 6, 10, 15] : List ℕ).all fun Q2 =>
      (List.range 31).all fun Q3 =>
        (List.range 31).all fun Q1 =>
          decide ((3 ≤ Q3 ∧ Q3 < Q2 ∧ Q2 < Q1 ∧ Q1 < 2 * Q3 ∧
            Nat.gcd Q1 Q2 = 1 ∧ Nat.gcd Q1 Q3 = 1 ∧ Nat.gcd Q2 Q3 = 1) →
            Q2 ≠ 3 ∧
            (Q2 = 6 → Q3 = 5 ∧ Q1 = 7) ∧
            (Q2 = 4 → Q3 = 3 ∧ Q1 = 5))) = true := by
  decide

private lemma decide_Qk_Q2b :
    (([3, 4, 5, 6, 10, 15] : List ℕ).all fun Q2 =>
      (List.range 31).all fun Q3 =>
        (List.range 31).all fun Q1 =>
          decide ((3 ≤ Q3 ∧ Q3 < Q2 ∧ Q2 < Q1 ∧ Q1 < 2 * Q3 ∧
            Nat.gcd Q1 Q2 = 1 ∧ Nat.gcd Q1 Q3 = 1 ∧ Nat.gcd Q2 Q3 = 1) →
            (Q2 = 10 → 6 * Q3 ≤ 5 * Q1) ∧
            (Q2 = 15 → 6 * Q3 ≤ 5 * Q1))) = true := by
  decide

private lemma decide_Qk_Q1 :
    (([3, 4, 5, 6, 10, 15] : List ℕ).all fun Q1 =>
      (List.range 16).all fun Q3 =>
        (List.range 16).all fun Q2 =>
          decide ((3 ≤ Q3 ∧ Q3 < Q2 ∧ Q2 < Q1 ∧ Q1 < 2 * Q3 ∧
            Nat.gcd Q1 Q2 = 1 ∧ Nat.gcd Q1 Q3 = 1 ∧ Nat.gcd Q2 Q3 = 1) →
            Q1 ≠ 3 ∧ Q1 ≠ 4 ∧ Q1 ≠ 6 ∧
            (Q1 = 10 → Q3 = 7 ∧ Q2 = 9))) = true := by
  decide

private lemma close_unhit_Qk_dvd60 {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ : ℕ}
    {a_k a_i a_j Q_k Q_i Q_j : ℕ} {p₀ : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M) (hNR2 : ¬ HasRule2 A M) (hNR2b : ¬ HasRule2b A M)
    (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id) (hZ_p0 : Z = A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
    (hk_perm : (a_k = a₃ ∧ a_i = a₁ ∧ a_j = a₂ ∧ Q_k = Q₃ ∧ Q_i = Q₁ ∧ Q_j = Q₂) ∨
               (a_k = a₂ ∧ a_i = a₁ ∧ a_j = a₃ ∧ Q_k = Q₂ ∧ Q_i = Q₁ ∧ Q_j = Q₃) ∨
               (a_k = a₁ ∧ a_i = a₂ ∧ a_j = a₃ ∧ Q_k = Q₁ ∧ Q_i = Q₂ ∧ Q_j = Q₃ ∧ 2 ≤ g₃))
    (h_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
      (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
      A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
      a_k ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p))
    (hQk_60 : Q_k ∣ 60) :
    (Q₃ = 5 ∧ Q₂ = 6 ∧ Q₁ = 7) ∨ (Q₃ = 4 ∧ Q₂ = 5 ∧ Q₁ = 7) ∨ (Q₃ = 3 ∧ Q₂ = 4 ∧ Q₁ = 5) := by
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha3M : a₃ ≤ M := hC.2.2.1 a₃ ha3A
  have hg3p := hd.hg3_pos
  have ha12 := hd.ha12; have ha23 := hd.ha23; have ha13 := lt_trans ha12 ha23
  have hQ3_3 := hd.hQ3_ge3
  have hQ32 := hd.hQ3_lt
  have hQ21 := hd.hQ2_lt
  have hQ1lt := hd.hQ1_lt
  have ha3_v := hd.ha3_eq
  have hQk_ge3 : 3 ≤ Q_k := by
    rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ <;> rw [hQk] <;> omega
  have hQk_mem : Q_k ∈ ([3, 4, 5, 6, 10, 12, 15, 20, 30, 60] : List ℕ) := by
    have h60 := dvd_60_mem_list (by omega) hQk_60
    simp only [List.mem_cons] at h60 ⊢
    rcases h60 with rfl | rfl | h <;> [omega; omega; exact h]
  have ha1Z : a₁ ∈ Z := by rw [hd.hZ_eq]; simp
  have ha2Z : a₂ ∈ Z := by rw [hd.hZ_eq]; simp
  have ha3Z : a₃ ∈ Z := by rw [hd.hZ_eq]; simp
  have hZ3_card : Z.card = 3 := by
    rw [hd.hZ_eq, Finset.card_insert_of_notMem (by simp [ha12.ne, ha13.ne]),
        Finset.card_insert_of_notMem (by simp [ha23.ne]), Finset.card_singleton]
  have hZ_perm : Z = {a_k, a_i, a_j} := by
    rcases hk_perm with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩
    · refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [ha13.ne', ha23.ne']),
            Finset.card_insert_of_notMem (by simp [ha12.ne]), Finset.card_singleton, hZ3_card]
    · refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [ha12.ne', ha23.ne]),
            Finset.card_insert_of_notMem (by simp [ha13.ne]), Finset.card_singleton, hZ3_card]
    · exact hd.hZ_eq
  have hdist : a_k ≠ a_i ∧ a_k ≠ a_j ∧ a_i ≠ a_j := by
    rcases hk_perm with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;>
      exact ⟨by omega, by omega, by omega⟩
  have hQpos : 0 < Q_k ∧ 0 < Q_i ∧ 0 < Q_j := by
    rcases hk_perm with ⟨_, _, _, rfl, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, rfl, _⟩ <;>
      exact ⟨by omega, by omega, by omega⟩
  have hQk_L : Q_k ∣ L₃ := by
    rcases hk_perm with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩
    · exact ⟨g₃ * Q₁ * Q₂, by rw [hd.hL3_eq]; ring⟩
    · exact ⟨g₃ * Q₁ * Q₃, by rw [hd.hL3_eq]; ring⟩
    · exact ⟨g₃ * Q₂ * Q₃, by rw [hd.hL3_eq]; ring⟩
  have ha_eqs : a_k = g₃ * Q_i * Q_j ∧ a_i = g₃ * Q_k * Q_j ∧ a_j = g₃ * Q_k * Q_i := by
    rcases hk_perm with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    · exact ⟨hd.ha3_eq, by rw [hd.ha1_eq]; ring, by rw [hd.ha2_eq]; ring⟩
    · exact ⟨hd.ha2_eq, hd.ha1_eq, by rw [hd.ha3_eq]; ring⟩
    · exact ⟨hd.ha1_eq, hd.ha2_eq, hd.ha3_eq⟩
  have hcop : Nat.Coprime Q_k Q_i ∧ Nat.Coprime Q_k Q_j := by
    rcases hk_perm with ⟨_, _, _, rfl, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, rfl⟩ | ⟨_, _, _, rfl, rfl, rfl, _⟩
    · exact ⟨hd.hcop13.symm, hd.hcop23.symm⟩
    · exact ⟨hd.hcop12.symm, hd.hcop23⟩
    · exact ⟨hd.hcop12, hd.hcop13⟩
  have run_r2 : ∀ D₁ D₂ : ℕ, 0 < D₁ → 5 ≤ D₁ → D₁ ∣ Q_k → 0 < D₂ → D₂ ∣ Q_k →
      4 * (D₁ * D₂) ≤ M → 6 * (a_i / D₂) ≤ M → False := fun D₁ D₂ h1 h5 h1Q h2 h2Q h4M h6M =>
    close_Rule2_D1_ge5 (a_k := a_k) (a_i := a_i) (a_j := a_j) (Q_k := Q_k) (Q_i := Q_i) (Q_j := Q_j)
      hC hNR2 hd hp0 hp0L hZ_p0 hZ_perm hdist.1 hdist.2.1 hdist.2.2
      hQpos.1 hQpos.2.1 hQpos.2.2 hQk_L ha_eqs.1 ha_eqs.2.1 ha_eqs.2.2 hcop.1 hcop.2 h_no3
      h1 h5 h1Q h2 h2Q h4M h6M
  have mul_le_a3 : ∀ u v : ℕ, u ≤ Q₁ → v ≤ Q₂ → u * v ≤ a₃ := fun u v hu hv => by
    rw [ha3_v]
    calc u * v ≤ Q₁ * Q₂ := Nat.mul_le_mul hu hv
      _ = 1 * (Q₁ * Q₂) := (one_mul _).symm
      _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_right _ hg3p
      _ = g₃ * Q₁ * Q₂ := by ring
  have mul_le_a3_2 : ∀ u v : ℕ, 2 ≤ g₃ → u ≤ Q₁ → v ≤ Q₂ → 2 * u * v ≤ a₃ := fun u v hg2 hu hv => by
    rw [ha3_v]
    calc 2 * u * v = 2 * (u * v) := by ring
      _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul hg2 (Nat.mul_le_mul hu hv)
      _ = g₃ * Q₁ * Q₂ := by ring
  have use_Q3 : Q₃ ∈ ([3, 4, 5, 6, 10, 15] : List ℕ) →
      (Q₃ = 6 → Q₂ = 7 ∧ Q₁ = 11) ∧ (Q₃ = 4 → Q₂ = 5 ∧ Q₁ = 7) ∧ (Q₃ = 3 → Q₂ = 4 ∧ Q₁ = 5) := fun hmem =>
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp decide_Qk_Q3 Q₃ hmem)
      Q₂ (List.mem_range.mpr (by { have : Q₃ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      Q₁ (List.mem_range.mpr (by { have : Q₃ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      ⟨hQ3_3, hQ32, hQ21, hQ1lt, hd.hcop12.gcd_eq_one, hd.hcop13.gcd_eq_one, hd.hcop23.gcd_eq_one⟩
  have use_Q2a : Q₂ ∈ ([3, 4, 5, 6, 10, 15] : List ℕ) →
      Q₂ ≠ 3 ∧ (Q₂ = 6 → Q₃ = 5 ∧ Q₁ = 7) ∧ (Q₂ = 4 → Q₃ = 3 ∧ Q₁ = 5) := fun hmem =>
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp decide_Qk_Q2a Q₂ hmem)
      Q₃ (List.mem_range.mpr (by { have : Q₂ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      Q₁ (List.mem_range.mpr (by { have : Q₂ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      ⟨hQ3_3, hQ32, hQ21, hQ1lt, hd.hcop12.gcd_eq_one, hd.hcop13.gcd_eq_one, hd.hcop23.gcd_eq_one⟩
  have use_Q2b : Q₂ ∈ ([3, 4, 5, 6, 10, 15] : List ℕ) →
      (Q₂ = 10 → 6 * Q₃ ≤ 5 * Q₁) ∧ (Q₂ = 15 → 6 * Q₃ ≤ 5 * Q₁) := fun hmem =>
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp decide_Qk_Q2b Q₂ hmem)
      Q₃ (List.mem_range.mpr (by { have : Q₂ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      Q₁ (List.mem_range.mpr (by { have : Q₂ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      ⟨hQ3_3, hQ32, hQ21, hQ1lt, hd.hcop12.gcd_eq_one, hd.hcop13.gcd_eq_one, hd.hcop23.gcd_eq_one⟩
  have use_Q1 : Q₁ ∈ ([3, 4, 5, 6, 10, 15] : List ℕ) →
      Q₁ ≠ 3 ∧ Q₁ ≠ 4 ∧ Q₁ ≠ 6 ∧ (Q₁ = 10 → Q₃ = 7 ∧ Q₂ = 9) := fun hmem =>
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp decide_Qk_Q1 Q₁ hmem)
      Q₃ (List.mem_range.mpr (by { have : Q₁ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      Q₂ (List.mem_range.mpr (by { have : Q₁ ≤ 15 := by { simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega }; omega })))
      ⟨hQ3_3, hQ32, hQ21, hQ1lt, hd.hcop12.gcd_eq_one, hd.hcop13.gcd_eq_one, hd.hcop23.gcd_eq_one⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQk_mem
  rcases hQk_mem with hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ
  · -- Q_k = 3
    rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩
    · have hQ3 : Q₃ = 3 := hQk.symm.trans hQ
      have ⟨h2, h1'⟩ := (use_Q3 (by simp [hQ3])).2.2 hQ3
      exact Or.inr (Or.inr ⟨hQ3, h2, h1'⟩)
    · have hQ2 : Q₂ = 3 := hQk.symm.trans hQ
      exact absurd hQ2 (use_Q2a (by simp [hQ2])).1
    · have hQ1 : Q₁ = 3 := hQk.symm.trans hQ
      exact absurd hQ1 (use_Q1 (by simp [hQ1])).1
  · -- Q_k = 4
    rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩
    · have hQ3 : Q₃ = 4 := hQk.symm.trans hQ
      have ⟨h2, h1'⟩ := (use_Q3 (by simp [hQ3])).2.1 hQ3
      exact Or.inr (Or.inl ⟨hQ3, h2, h1'⟩)
    · have hQ2 : Q₂ = 4 := hQk.symm.trans hQ
      have ⟨h3, h1'⟩ := (use_Q2a (by simp [hQ2])).2.2 hQ2
      exact Or.inr (Or.inr ⟨h3, hQ2, h1'⟩)
    · have hQ1 : Q₁ = 4 := hQk.symm.trans hQ
      exact absurd hQ1 (use_Q1 (by simp [hQ1])).2.1
  · -- Q_k = 5
    exfalso
    refine close_Q5_rule1 (a_k := a_k) (a_i := a_i) (a_j := a_j) (Q_k := Q_k) (Q_i := Q_i) (Q_j := Q_j)
      hC hNR1 hd hp0 hp0L hZ_p0 hZ_perm hdist.1 hdist.2.1 hdist.2.2
      hQpos.1 hQpos.2.1 hQpos.2.2 hQk_L ha_eqs.1 ha_eqs.2.1 ha_eqs.2.2 hcop.1 hcop.2 h_no3 hQ ?_ ?_
    · rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 5 := hQk.symm.trans hQ
        have hle : 25 ≤ a₃ := le_trans (by decide : 25 ≤ 7 * 6) (mul_le_a3 7 6 (by omega) (by omega))
        omega
      · have hQ2 : Q₂ = 5 := hQk.symm.trans hQ
        have hle : 25 ≤ a₃ := le_trans (by decide : 25 ≤ 6 * 5) (mul_le_a3 6 5 (by omega) (by omega))
        omega
      · have hQ1 : Q₁ = 5 := hQk.symm.trans hQ
        have hle : 25 ≤ a₃ := le_trans (by decide : 25 ≤ 2 * 5 * 4) (mul_le_a3_2 5 4 hg2 (by omega) (by omega))
        omega
    · rcases hk_perm with ⟨_, hai, _, hQk, _, _⟩ | ⟨_, hai, _, hQk, _, _⟩ | ⟨_, hai, _, hQk, _, _, _⟩
      · have hQ3 : Q₃ = 5 := hQk.symm.trans hQ
        have h67 : 6 ≤ Q₁ := by omega
        have hmul : a_i = (g₃ * Q₂) * 5 := by rw [hai, hd.ha1_eq, hQ3]
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * Q₂) ≤ g₃ * Q₁ * Q₂ := by
          calc 6 * (g₃ * Q₂) = g₃ * (6 * Q₂) := by ring
            _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_left g₃ (Nat.mul_le_mul_right Q₂ h67)
            _ = g₃ * Q₁ * Q₂ := by ring
        omega
      · have hQ2 : Q₂ = 5 := hQk.symm.trans hQ
        have hmul : a_i = (g₃ * Q₃) * 5 := by rw [hai, hd.ha1_eq, hQ2]; ring
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * Q₃) ≤ g₃ * Q₁ * Q₂ := by
          have : 6 * Q₃ ≤ Q₁ * Q₂ := by rw [hQ2]; omega
          calc 6 * (g₃ * Q₃) = g₃ * (6 * Q₃) := by ring
            _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_left g₃ this
            _ = g₃ * Q₁ * Q₂ := by ring
        omega
      · have hQ1 : Q₁ = 5 := hQk.symm.trans hQ
        have h3_eq : Q₃ = 3 := by omega
        have h2_eq : Q₂ = 4 := by omega
        have hmul : a_i = (g₃ * Q₃) * 5 := by rw [hai, hd.ha2_eq, hQ1]; ring
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * Q₃) ≤ g₃ * Q₁ * Q₂ := by rw [hQ1, h3_eq, h2_eq]; omega
        omega
  · -- Q_k = 6
    rcases hk_perm with ⟨hak, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩
    · exfalso
      have hQ3 : Q₃ = 6 := hQk.symm.trans hQ
      have ⟨h2, h1'⟩ := (use_Q3 (by simp [hQ3])).1 hQ3
      exact close_Q6_6_7_11 hC hNR2 hd hp0 hp0L hZ_p0 (hak ▸ h_no3) hQ3 h2 h1'
    · have hQ2 : Q₂ = 6 := hQk.symm.trans hQ
      have ⟨h3, h1'⟩ := (use_Q2a (by simp [hQ2])).2.1 hQ2
      exact Or.inl ⟨h3, hQ2, h1'⟩
    · exfalso
      have hQ1 : Q₁ = 6 := hQk.symm.trans hQ
      exact absurd hQ1 (use_Q1 (by simp [hQ1])).2.2.1
  · -- Q_k = 10
    exfalso
    have hD1 : 5 ∣ Q_k := hQ ▸ (by decide : 5 ∣ 10)
    have h100M : 4 * (5 * 5) ≤ M := by
      rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 10 := hQk.symm.trans hQ
        have := le_trans (by decide : 100 ≤ 12 * 11) (mul_le_a3 12 11 (by omega) (by omega)); omega
      · have hQ2 : Q₂ = 10 := hQk.symm.trans hQ
        have := le_trans (by decide : 100 ≤ 11 * 10) (mul_le_a3 11 10 (by omega) (by omega)); omega
      · have hQ1 : Q₁ = 10 := hQk.symm.trans hQ
        have ⟨h3_7, h2_9⟩ := (use_Q1 (by simp [hQ1])).2.2.2 hQ1
        have := le_trans (by decide : 100 ≤ 2 * 10 * 9) (mul_le_a3_2 10 9 hg2 (by omega) (by omega)); omega
    have h6M : 6 * (a_i / 5) ≤ M := by
      rcases hk_perm with ⟨_, hai, _, hQk, _⟩ | ⟨_, hai, _, hQk, _⟩ | ⟨_, hai, _, hQk, _⟩
      · have hQ3 : Q₃ = 10 := hQk.symm.trans hQ
        have hQ1_ge12 : 12 ≤ Q₁ := by
          have hne12 : Q₁ ≠ 12 := fun h12 => by
            have := hd.hcop13; rw [hQ3, h12] at this; revert this; decide
          omega
        have hmul : a_i = (g₃ * (Q₂ * 2)) * 5 := by rw [hai, hd.ha1_eq, hQ3]; ring
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * (Q₂ * 2)) ≤ g₃ * Q₁ * Q₂ := by
          calc 6 * (g₃ * (Q₂ * 2)) = g₃ * (12 * Q₂) := by ring
            _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_left g₃ (Nat.mul_le_mul_right Q₂ hQ1_ge12)
            _ = g₃ * Q₁ * Q₂ := by ring
        omega
      · have hQ2 : Q₂ = 10 := hQk.symm.trans hQ
        have hle_5 := (use_Q2b (by simp [hQ2])).1 hQ2
        have hmul : a_i = (g₃ * (2 * Q₃)) * 5 := by rw [hai, hd.ha1_eq, hQ2]; ring
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * (2 * Q₃)) ≤ g₃ * Q₁ * Q₂ := by
          rw [hQ2]
          calc 6 * (g₃ * (2 * Q₃)) = g₃ * (2 * (6 * Q₃)) := by ring
            _ ≤ g₃ * (2 * (5 * Q₁)) := Nat.mul_le_mul_left g₃ (Nat.mul_le_mul_left 2 hle_5)
            _ = g₃ * Q₁ * 10 := by ring
        omega
      · have hQ1 : Q₁ = 10 := hQk.symm.trans hQ
        have ⟨h3_7, h2_9⟩ := (use_Q1 (by simp [hQ1])).2.2.2 hQ1
        have hmul : a_i = (g₃ * (2 * Q₃)) * 5 := by rw [hai, hd.ha2_eq, hQ1]; ring
        rw [hmul, Nat.mul_div_cancel _ (by decide), h3_7]
        have hle : 6 * (g₃ * (2 * 7)) ≤ g₃ * Q₁ * Q₂ := by rw [hQ1, h2_9]; omega
        omega
    exact run_r2 5 5 (by decide) (by decide) hD1 (by decide) hD1 h100M h6M
  · -- Q_k = 12
    exfalso
    have h144 : 4 * (6 * 6) ≤ M := by
      rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 12 := hQk.symm.trans hQ
        have := le_trans (by decide : 144 ≤ 14 * 13) (mul_le_a3 14 13 (by omega) (by omega)); omega
      · have hQ2 : Q₂ = 12 := hQk.symm.trans hQ
        have := le_trans (by decide : 144 ≤ 13 * 12) (mul_le_a3 13 12 (by omega) (by omega)); omega
      · have hQ1 : Q₁ = 12 := hQk.symm.trans hQ
        have := le_trans (by decide : 144 ≤ 2 * 12 * 8) (mul_le_a3_2 12 8 hg2 (by omega) (by omega)); omega
    have hD : 6 ∣ Q_k := hQ ▸ (by decide : 6 ∣ 12)
    have h6M : 6 * (a_i / 6) ≤ M := by
      calc 6 * (a_i / 6) ≤ a_i := Nat.mul_div_le a_i 6
        _ ≤ a₃ := by rcases hk_perm with ⟨_, hai, _⟩ | ⟨_, hai, _⟩ | ⟨_, hai, _⟩ <;> rw [hai] <;> omega
        _ ≤ M := ha3M
    exact run_r2 6 6 (by decide) (by decide) hD (by decide) hD h144 h6M
  · -- Q_k = 15
    exfalso
    rcases hk_perm with ⟨hak, hai, _, hQk, _⟩ | ⟨_, hai, _, hQk, _⟩ | ⟨_, hai, _, hQk, _, _, hg2⟩
    · have hQ3 : Q₃ = 15 := hQk.symm.trans hQ
      by_cases h18 : 18 ≤ Q₁
      · have h100M : 4 * (5 * 5) ≤ M := by
          have := le_trans (by decide : 100 ≤ 18 * 16) (mul_le_a3 18 16 h18 (by omega)); omega
        have hmul : a_i = (g₃ * (3 * Q₂)) * 5 := by rw [hai, hd.ha1_eq, hQ3]; ring
        have h6M : 6 * (a_i / 5) ≤ M := by
          rw [hmul, Nat.mul_div_cancel _ (by decide)]
          have hle : 6 * (g₃ * (3 * Q₂)) ≤ g₃ * Q₁ * Q₂ := by
            calc 6 * (g₃ * (3 * Q₂)) = g₃ * (18 * Q₂) := by ring
              _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_left g₃ (Nat.mul_le_mul_right Q₂ h18)
              _ = g₃ * Q₁ * Q₂ := by ring
          omega
        exact run_r2 5 5 (by decide) (by decide) (hQ ▸ (by decide : 5 ∣ 15)) (by decide) (hQ ▸ (by decide : 5 ∣ 15)) h100M h6M
      · have hQ2_16 : Q₂ = 16 := by omega
        have hQ1_17 : Q₁ = 17 := by omega
        exact close_Q15_16_17 hC hNR2 hNR2b hd hp0 hp0L hZ_p0 (hak ▸ h_no3) hQ3 hQ2_16 hQ1_17
    · have hQ2 : Q₂ = 15 := hQk.symm.trans hQ
      have hle_5 := (use_Q2b (by simp [hQ2])).2 hQ2
      have h100M : 4 * (5 * 5) ≤ M := by
        have := le_trans (by decide : 100 ≤ 16 * 15) (mul_le_a3 16 15 (by omega) (by omega)); omega
      have hmul : a_i = (g₃ * (3 * Q₃)) * 5 := by rw [hai, hd.ha1_eq, hQ2]; ring
      have h6M : 6 * (a_i / 5) ≤ M := by
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * (3 * Q₃)) ≤ g₃ * Q₁ * Q₂ := by
          rw [hQ2]
          calc 6 * (g₃ * (3 * Q₃)) = g₃ * (3 * (6 * Q₃)) := by ring
            _ ≤ g₃ * (3 * (5 * Q₁)) := Nat.mul_le_mul_left g₃ (Nat.mul_le_mul_left 3 hle_5)
            _ = g₃ * Q₁ * 15 := by ring
        omega
      exact run_r2 5 5 (by decide) (by decide) (hQ ▸ (by decide : 5 ∣ 15)) (by decide) (hQ ▸ (by decide : 5 ∣ 15)) h100M h6M
    · have hQ1 : Q₁ = 15 := hQk.symm.trans hQ
      have h3_8 : 8 ≤ Q₃ := by omega
      have h2_ne9 : Q₂ ≠ 9 := fun h9 => by have := hd.hcop12; rw [hQ1, h9] at this; revert this; decide
      have h2_ne10 : Q₂ ≠ 10 := fun h10 => by have := hd.hcop12; rw [hQ1, h10] at this; revert this; decide
      have h2_11 : 11 ≤ Q₂ := by omega
      have h300M : 4 * (5 * 15) ≤ M := by
        have := le_trans (by decide : 300 ≤ 2 * 15 * 11) (mul_le_a3_2 15 11 hg2 (by omega) h2_11); omega
      have hmul : a_i = (g₃ * Q₃) * 15 := by rw [hai, hd.ha2_eq, hQ1]; ring
      have h6M : 6 * (a_i / 15) ≤ M := by
        rw [hmul, Nat.mul_div_cancel _ (by decide)]
        have hle : 6 * (g₃ * Q₃) ≤ g₃ * Q₁ * Q₂ := by
          rw [hQ1]
          calc 6 * (g₃ * Q₃) = g₃ * (6 * Q₃) := by ring
            _ ≤ g₃ * (15 * Q₂) := Nat.mul_le_mul_left g₃ (by omega)
            _ = g₃ * 15 * Q₂ := by ring
        omega
      exact run_r2 5 15 (by decide) (by decide) (hQ ▸ (by decide : 5 ∣ 15)) (by decide) (by rw [hQ]) h300M h6M
  · -- Q_k = 20
    exfalso
    have h200 : 4 * (5 * 10) ≤ M := by
      rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 20 := hQk.symm.trans hQ
        have := le_trans (by decide : 200 ≤ 22 * 21) (mul_le_a3 22 21 (by omega) (by omega)); omega
      · have hQ2 : Q₂ = 20 := hQk.symm.trans hQ
        have := le_trans (by decide : 200 ≤ 21 * 20) (mul_le_a3 21 20 (by omega) (by omega)); omega
      · have hQ1 : Q₁ = 20 := hQk.symm.trans hQ
        have := le_trans (by decide : 200 ≤ 2 * 20 * 12) (mul_le_a3_2 20 12 hg2 (by omega) (by omega)); omega
    have hD1 : 5 ∣ Q_k := hQ ▸ (by decide : 5 ∣ 20)
    have hD2 : 10 ∣ Q_k := hQ ▸ (by decide : 10 ∣ 20)
    have h6M : 6 * (a_i / 10) ≤ M := by
      calc 6 * (a_i / 10) ≤ 10 * (a_i / 10) := Nat.mul_le_mul_right _ (by decide)
        _ ≤ a_i := Nat.mul_div_le a_i 10
        _ ≤ a₃ := by rcases hk_perm with ⟨_, hai, _⟩ | ⟨_, hai, _⟩ | ⟨_, hai, _⟩ <;> rw [hai] <;> omega
        _ ≤ M := ha3M
    exact run_r2 5 10 (by decide) (by decide) hD1 (by decide) hD2 h200 h6M
  · -- Q_k = 30
    exfalso
    have h120 : 4 * (5 * 6) ≤ M := by
      rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 30 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 32 * 31) (mul_le_a3 32 31 (by omega) (by omega)); omega
      · have hQ2 : Q₂ = 30 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 31 * 30) (mul_le_a3 31 30 (by omega) (by omega)); omega
      · have hQ1 : Q₁ = 30 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 2 * 30 * 17) (mul_le_a3_2 30 17 hg2 (by omega) (by omega)); omega
    have hD1 : 5 ∣ Q_k := hQ ▸ (by decide : 5 ∣ 30)
    have hD2 : 6 ∣ Q_k := hQ ▸ (by decide : 6 ∣ 30)
    have h6M : 6 * (a_i / 6) ≤ M := by
      calc 6 * (a_i / 6) ≤ a_i := Nat.mul_div_le a_i 6
        _ ≤ a₃ := by rcases hk_perm with ⟨_, hai, _⟩ | ⟨_, hai, _⟩ | ⟨_, hai, _⟩ <;> rw [hai] <;> omega
        _ ≤ M := ha3M
    exact run_r2 5 6 (by decide) (by decide) hD1 (by decide) hD2 h120 h6M
  · -- Q_k = 60
    exfalso
    have h120 : 4 * (5 * 6) ≤ M := by
      rcases hk_perm with ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _⟩ | ⟨_, _, _, hQk, _, _, hg2⟩
      · have hQ3 : Q₃ = 60 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 62 * 61) (mul_le_a3 62 61 (by omega) (by omega)); omega
      · have hQ2 : Q₂ = 60 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 61 * 60) (mul_le_a3 61 60 (by omega) (by omega)); omega
      · have hQ1 : Q₁ = 60 := hQk.symm.trans hQ
        have := le_trans (by decide : 120 ≤ 2 * 60 * 32) (mul_le_a3_2 60 32 hg2 (by omega) (by omega)); omega
    have hD1 : 5 ∣ Q_k := hQ ▸ (by decide : 5 ∣ 60)
    have hD2 : 6 ∣ Q_k := hQ ▸ (by decide : 6 ∣ 60)
    have h6M : 6 * (a_i / 6) ≤ M := by
      calc 6 * (a_i / 6) ≤ a_i := Nat.mul_div_le a_i 6
        _ ≤ a₃ := by rcases hk_perm with ⟨_, hai, _⟩ | ⟨_, hai, _⟩ | ⟨_, hai, _⟩ <;> rw [hai] <;> omega
        _ ≤ M := ha3M
    exact run_r2 5 6 (by decide) (by decide) hD1 (by decide) hD2 h120 h6M

private lemma core_Zq_card_le2_at_most_one_in_ZA {A Z : Finset ℕ} {M a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ q : ℕ}
    (hC : C5Core A M) (hd : ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃)
    (_hq : q.Prime) (hZq2 : (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2)
    {x y : ℕ} (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hxy : x ≠ y)
    (hxZq : x ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q))
    (hyZq : y ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) : False := by
  let Zq := A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
  have hZA_sub : Z ⊆ A := by
    rw [hd.hZ_eq, hd.hA_eq]; intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp
  have hZ3 : Z.card = 3 := by
    rw [hd.hZ_eq, Finset.card_insert_of_notMem (by simp [hd.ha12.ne, (lt_trans hd.ha12 hd.ha23).ne]),
        Finset.card_insert_of_notMem (by simp [hd.ha23.ne]), Finset.card_singleton]
  have hsub : Z ⊆ Zq := by
    intro z hz
    have hzA := hZA_sub hz
    have hz_dvd : z ∣ L₃ := hd.hL3_lcm ▸ Finset.dvd_lcm hz
    have hlcm_xy : Nat.lcm x y = L₃ := by
      rw [hd.hZ_eq] at hxZ hyZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxZ hyZ
      rcases hxZ with rfl | rfl | rfl <;> rcases hyZ with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact hd.hL3_12
      · exact hd.hL3_13
      · rw [Nat.lcm_comm]; exact hd.hL3_12
      · exact absurd rfl hxy
      · exact hd.hL3_23
      · rw [Nat.lcm_comm]; exact hd.hL3_13
      · rw [Nat.lcm_comm]; exact hd.hL3_23
      · exact absurd rfl hxy
    have hx_pos := hC.2.1 x (hZA_sub hxZ)
    have hy_pos := hC.2.1 y (hZA_sub hyZ)
    have hz_dvd' : z ∣ Nat.lcm x y := hlcm_xy.symm ▸ hz_dvd
    have hfac := fac_le_of_dvd_5 (Nat.lcm_pos hx_pos hy_pos).ne' hz_dvd' (p := q)
    rw [fac_lcm_eq_max_5 hx_pos.ne' hy_pos.ne'] at hfac
    have hfx := (Finset.mem_filter.mp hxZq).2
    have hfy := (Finset.mem_filter.mp hyZq).2
    exact Finset.mem_filter.mpr ⟨hzA, by omega⟩
  have := Finset.card_le_card hsub
  change Zq.card ≤ 2 at hZq2
  omega

private lemma solve_from_three_set {A : Finset ℕ} {M p₀ : ℕ}
    (hC : C5Core A M) (hNR1 : ¬ HasRule1 A M) (hNR2 : ¬ HasRule2 A M) (hNR2b : ¬ HasRule2b A M)
    (hp0 : p₀.Prime) (hp0L : p₀ ∣ A.lcm id)
    (hZ3 : (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 3) :
    ∃ a₁ a₂ a₃ a₄ a₅ L₃ g₃ : ℕ,
      ThreeSetProps A (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀))
        a₁ a₂ a₃ a₄ a₅ L₃ 5 4 3 g₃ ∧
      2 ≤ g₃ ∧
      ∃ p₁ : ℕ, p₁.Prime ∧ p₁ ∣ A.lcm id ∧
        (A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁)).card = 3 ∧
        A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) ≠
          A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀) ∧
        a₁ ∈ A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁) := by
  let Z := A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)
  obtain ⟨a₁, a₂, a₃, a₄, a₅, L₃, Q₁, Q₂, Q₃, g₃, hd⟩ := exists_three_set_props hC hp0 hp0L hZ3
  change ThreeSetProps A Z a₁ a₂ a₃ a₄ a₅ L₃ Q₁ Q₂ Q₃ g₃ at hd
  have hZA3 : Z.card = 3 := hZ3
  have hZA_sub : Z ⊆ A := Finset.filter_subset _ _
  have hZ_ex : ∃ p, p.Prime ∧ p ∣ A.lcm id ∧
      Z = A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := ⟨p₀, hp0, hp0L, rfl⟩
  let Hits3 := fun x : ℕ => ∃ p : ℕ, p.Prime ∧ p ∣ A.lcm id ∧
    (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 ∧
    A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z ∧
    x ∈ A.filter (fun a => a.factorization p < (A.lcm id).factorization p)
  let HitsHv := fun x : ℕ => ∃ q : ℕ, q.Prime ∧ q ∣ A.lcm id ∧
    (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 ∧
    M < (q ^ (A.lcm id).factorization q) ^ 2 ∧
    x ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
  have hits3_unique : ∀ x y : ℕ, x ∈ Z → y ∈ Z → x ≠ y → Hits3 x → Hits3 y → False := by
    intro x y hxZ hyZ hxy ⟨px, hpx, hpxL, hpx3, hpx_ne, hxpx⟩ ⟨py, hpy, hpyL, hpy3, hpy_ne, hypy⟩
    have heq := core_at_most_one_other_3set hC hZA3 hZA_sub
      ⟨px, hpx, hpxL, rfl, hpx3⟩ ⟨py, hpy, hpyL, rfl, hpy3⟩ hpx_ne hpy_ne hZ_ex
    have hxpy : x ∈ A.filter (fun a => a.factorization py < (A.lcm id).factorization py) := heq ▸ hxpx
    let Zpy := A.filter (fun a => a.factorization py < (A.lcm id).factorization py)
    have hi := core_fact3_two_three_sets hC hpy hpyL hp0 hp0L hpy3 hZA3 hpy_ne
    have hx_in : x ∈ Zpy ∩ Z := Finset.mem_inter.mpr ⟨hxpy, hxZ⟩
    have hy_in : y ∈ Zpy ∩ Z := Finset.mem_inter.mpr ⟨hypy, hyZ⟩
    have h2 : 2 ≤ (Zpy ∩ Z).card := by
      have : ({x, y} : Finset ℕ) ⊆ Zpy ∩ Z := fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hc : ({x, y} : Finset ℕ).card = 2 := Finset.card_pair hxy
      exact hc ▸ Finset.card_le_card this
    change (Zpy ∩ Z).card = 1 at hi
    omega
  have hitsHv_unique : ∀ x y : ℕ, x ∈ Z → y ∈ Z → x ≠ y → HitsHv x → HitsHv y → False := by
    intro x y hxZ hyZ hxy ⟨qx, hqx, hqxL, hqx2, hqx_hv, hxqx⟩ ⟨qy, hqy, hqyL, hqy2, hqy_hv, hyqy⟩
    by_cases hqxy : qx = qy
    · subst hqxy
      exact core_Zq_card_le2_at_most_one_in_ZA hC hd hqx hqx2 hxZ hyZ hxy hxqx hyqy
    · exact core_at_most_one_heavy hC hqx hqxL hqy hqyL hqxy hqx2 hqy2 hqx_hv hqy_hv
  have ha1Z : a₁ ∈ Z := by rw [hd.hZ_eq]; simp
  have ha2Z : a₂ ∈ Z := by rw [hd.hZ_eq]; simp
  have ha3Z : a₃ ∈ Z := by rw [hd.hZ_eq]; simp
  have ha12 := hd.ha12; have ha23 := hd.ha23; have ha13 := lt_trans ha12 ha23
  have ha3A : a₃ ∈ A := by rw [hd.hA_eq]; simp
  have ha3M := hC.2.2.1 a₃ ha3A
  have hQ3_3 := hd.hQ3_ge3; have hQ32 := hd.hQ3_lt; have hQ21 := hd.hQ2_lt
  have hQ1lt := hd.hQ1_lt; have hg3p := hd.hg3_pos; have ha3_v := hd.ha3_eq
  have hZ3_card : Z.card = 3 := hZ3
  have hZ_312 : Z = {a₃, a₁, a₂} := by
    refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [ha13.ne', ha23.ne']),
          Finset.card_insert_of_notMem (by simp [ha12.ne]), Finset.card_singleton, hZ3_card]
  have hZ_213 : Z = {a₂, a₁, a₃} := by
    refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [ha12.ne', ha23.ne]),
          Finset.card_insert_of_notMem (by simp [ha13.ne]), Finset.card_singleton, hZ3_card]
  have ha3_eq' : a₃ = g₃ * Q₁ * Q₂ := hd.ha3_eq
  have ha1_eq' : a₁ = g₃ * Q₃ * Q₂ := by rw [hd.ha1_eq]; ring
  have ha2_eq' : a₂ = g₃ * Q₃ * Q₁ := by rw [hd.ha2_eq]; ring
  have ha3_eq'' : a₃ = g₃ * Q₂ * Q₁ := by rw [hd.ha3_eq]; ring
  have hQ_cases : (Q₃ = 5 ∧ Q₂ = 6 ∧ Q₁ = 7) ∨ (Q₃ = 4 ∧ Q₂ = 5 ∧ Q₁ = 7) ∨ (Q₃ = 3 ∧ Q₂ = 4 ∧ Q₁ = 5) := by
    by_cases h3 : ¬ Hits3 a₃ ∧ ¬ HitsHv a₃
    · have h3_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
          (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
          A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
          a₃ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
        h3.1 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
      have h3_nohv : ∀ q : ℕ, q.Prime → q ∣ A.lcm id →
          (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 →
          M < (q ^ (A.lcm id).factorization q) ^ 2 →
          a₃ ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := fun q hq hqL hq2 hq_hv hmem =>
        h3.2 ⟨q, hq, hqL, hq2, hq_hv, hmem⟩
      have hsq3 : Q₃ ^ 2 ≤ M := by
        have hle : Q₃ * Q₃ ≤ Q₁ * Q₂ := Nat.mul_le_mul (by omega) (by omega)
        have hle2 : Q₁ * Q₂ ≤ g₃ * Q₁ * Q₂ := by
          calc Q₁ * Q₂ = 1 * (Q₁ * Q₂) := (one_mul _).symm
            _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_right _ hg3p
            _ = g₃ * Q₁ * Q₂ := by ring
        rw [← ha3_v] at hle2
        rw [sq]
        omega
      have hQ3_60 := core_Qk_dvd_60 (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
        hC hNR1 hd hZ_312 ha13.ne' ha23.ne' ha12.ne (by omega) (by omega) (by omega)
        ⟨g₃ * Q₁ * Q₂, by rw [hd.hL3_eq]; ring⟩ ha3_eq' ha1_eq' ha2_eq' hd.hcop13.symm hd.hcop23.symm
        h3_no3 h3_nohv (Or.inl hsq3)
      exact close_unhit_Qk_dvd60 (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
        hC hNR1 hNR2 hNR2b hd hp0 hp0L rfl (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) h3_no3 hQ3_60
    · by_cases h2 : ¬ Hits3 a₂ ∧ ¬ HitsHv a₂
      · have h2_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
            (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
            A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
            a₂ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
          h2.1 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
        have h2_nohv : ∀ q : ℕ, q.Prime → q ∣ A.lcm id →
            (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 →
            M < (q ^ (A.lcm id).factorization q) ^ 2 →
            a₂ ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := fun q hq hqL hq2 hq_hv hmem =>
          h2.2 ⟨q, hq, hqL, hq2, hq_hv, hmem⟩
        have hsq2 : Q₂ ^ 2 ≤ M := by
          have hle : Q₂ * Q₂ ≤ Q₁ * Q₂ := Nat.mul_le_mul_right Q₂ (by omega)
          have hle2 : Q₁ * Q₂ ≤ g₃ * Q₁ * Q₂ := by
            calc Q₁ * Q₂ = 1 * (Q₁ * Q₂) := (one_mul _).symm
              _ ≤ g₃ * (Q₁ * Q₂) := Nat.mul_le_mul_right _ hg3p
              _ = g₃ * Q₁ * Q₂ := by ring
          rw [← ha3_v] at hle2
          rw [sq]
          omega
        have hQ2_60 := core_Qk_dvd_60 (a_k := a₂) (a_i := a₁) (a_j := a₃) (Q_k := Q₂) (Q_i := Q₁) (Q_j := Q₃)
          hC hNR1 hd hZ_213 ha12.ne' ha23.ne ha13.ne (by omega) (by omega) (by omega)
          ⟨g₃ * Q₁ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha2_eq hd.ha1_eq ha3_eq'' hd.hcop12.symm hd.hcop23
          h2_no3 h2_nohv (Or.inl hsq2)
        exact close_unhit_Qk_dvd60 (a_k := a₂) (a_i := a₁) (a_j := a₃) (Q_k := Q₂) (Q_i := Q₁) (Q_j := Q₃)
          hC hNR1 hNR2 hNR2b hd hp0 hp0L rfl (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) h2_no3 hQ2_60
      · have hex_hv23 : ∃ q, q.Prime ∧ q ∣ A.lcm id ∧
            (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 ∧
            M < (q ^ (A.lcm id).factorization q) ^ 2 ∧
            (a₂ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) ∨
             a₃ ∈ A.filter (fun a => a.factorization q < (A.lcm id).factorization q)) := by
          by_cases h3_3 : Hits3 a₃
          · have h2_nh3 : ¬ Hits3 a₂ := fun h => hits3_unique a₂ a₃ ha2Z ha3Z hd.ha23.ne h h3_3
            have h2_hv : HitsHv a₂ := by
              by_contra hnh; exact h2 ⟨h2_nh3, hnh⟩
            obtain ⟨q, hq, hqL, hq2, hq_hv, hmem⟩ := h2_hv
            exact ⟨q, hq, hqL, hq2, hq_hv, Or.inl hmem⟩
          · have h3_hv : HitsHv a₃ := by
              by_contra hnh; exact h3 ⟨h3_3, hnh⟩
            obtain ⟨q, hq, hqL, hq2, hq_hv, hmem⟩ := h3_hv
            exact ⟨q, hq, hqL, hq2, hq_hv, Or.inr hmem⟩
        obtain ⟨q_hv, hq_hv_pr, hq_hvL, hq_hv2, hq_hv_sq, h_hit23⟩ := hex_hv23
        have hg3_ge2 : 2 ≤ g₃ := core_heavy_hit_23_imp_g3_ge2 hC hd hq_hv_pr hq_hvL hq_hv2 hq_hv_sq h_hit23
        have h1_nh3 : ¬ Hits3 a₁ := fun h1_3 => by
          by_cases h3_3 : Hits3 a₃
          · exact hits3_unique a₁ a₃ ha1Z ha3Z ha13.ne h1_3 h3_3
          · have h3_hv : HitsHv a₃ := by by_contra hnh; exact h3 ⟨h3_3, hnh⟩
            by_cases h2_3 : Hits3 a₂
            · exact hits3_unique a₁ a₂ ha1Z ha2Z ha12.ne h1_3 h2_3
            · have h2_nh3 : ¬ Hits3 a₂ := h2_3
              have h2_hv : HitsHv a₂ := by by_contra hnh; exact h2 ⟨h2_nh3, hnh⟩
              exact hitsHv_unique a₂ a₃ ha2Z ha3Z hd.ha23.ne h2_hv h3_hv
        have h1_nhhv : ¬ HitsHv a₁ := fun h1_hv => by
          rcases h_hit23 with hmem2 | hmem3
          · exact hitsHv_unique a₁ a₂ ha1Z ha2Z ha12.ne h1_hv ⟨q_hv, hq_hv_pr, hq_hvL, hq_hv2, hq_hv_sq, hmem2⟩
          · exact hitsHv_unique a₁ a₃ ha1Z ha3Z ha13.ne h1_hv ⟨q_hv, hq_hv_pr, hq_hvL, hq_hv2, hq_hv_sq, hmem3⟩
        have h1_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
            (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
            A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
            a₁ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
          h1_nh3 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
        have h1_nohv : ∀ q : ℕ, q.Prime → q ∣ A.lcm id →
            (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 →
            M < (q ^ (A.lcm id).factorization q) ^ 2 →
            a₁ ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := fun q hq hqL hq2 hq_hv hmem =>
          h1_nhhv ⟨q, hq, hqL, hq2, hq_hv, hmem⟩
        have hQ1_60 := core_Qk_dvd_60 (a_k := a₁) (a_i := a₂) (a_j := a₃) (Q_k := Q₁) (Q_i := Q₂) (Q_j := Q₃)
          hC hNR1 hd hd.hZ_eq ha12.ne ha13.ne hd.ha23.ne (by omega) (by omega) (by omega)
          ⟨g₃ * Q₂ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha1_eq hd.ha2_eq hd.ha3_eq hd.hcop12 hd.hcop13
          h1_no3 h1_nohv (Or.inr ⟨q_hv, hq_hv_pr, hq_hvL, hq_hv2, hq_hv_sq, h_hit23⟩)
        exact close_unhit_Qk_dvd60 (a_k := a₁) (a_i := a₂) (a_j := a₃) (Q_k := Q₁) (Q_i := Q₂) (Q_j := Q₃)
          hC hNR1 hNR2 hNR2b hd hp0 hp0L rfl (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, hg3_ge2⟩)) h1_no3 hQ1_60
  rcases hQ_cases with ⟨hQ3, hQ2, hQ1⟩ | ⟨hQ3, hQ2, hQ1⟩ | ⟨hQ3, hQ2, hQ1⟩
  · exfalso
    by_cases h3_hit : Hits3 a₃
    · obtain ⟨p_B, hpB, hpBL, hpB3, hpB_ne, ha3_B⟩ := h3_hit
      have h1_nh3 : ¬ Hits3 a₁ := fun h => hits3_unique a₁ a₃ ha1Z ha3Z ha13.ne h ⟨p_B, hpB, hpBL, hpB3, hpB_ne, ha3_B⟩
      have h2_nh3 : ¬ Hits3 a₂ := fun h => hits3_unique a₂ a₃ ha2Z ha3Z hd.ha23.ne h ⟨p_B, hpB, hpBL, hpB3, hpB_ne, ha3_B⟩
      by_cases hg1 : g₃ = 1
      · have ha4_ZB : a₄ ∈ A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) := by
          have hi := core_fact3_two_three_sets hC hpB hpBL hp0 hp0L hpB3 hZA3 hpB_ne
          change (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) ∩ Z).card = 1 at hi
          have hrem2 : (A \ Z).card = 2 := by rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
          have hZBsdiff : (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z).card = 2 := by
            have := Finset.card_sdiff_add_card_inter (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B)) Z
            omega
          have hsub_sdiff : A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z ⊆ A \ Z :=
            Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Finset.Subset.refl _)
          have heq_rem : A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z = A \ Z :=
            Finset.eq_of_subset_of_card_le hsub_sdiff (by omega)
          have h4_sdiff : a₄ ∈ A \ Z := Finset.mem_sdiff.mpr ⟨by rw [hd.hA_eq]; simp, hd.ha4Z⟩
          rw [← heq_rem] at h4_sdiff; exact (Finset.mem_sdiff.mp h4_sdiff).1
        have ha5_ZB : a₅ ∈ A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) := by
          have hi := core_fact3_two_three_sets hC hpB hpBL hp0 hp0L hpB3 hZA3 hpB_ne
          change (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) ∩ Z).card = 1 at hi
          have hrem2 : (A \ Z).card = 2 := by rw [Finset.card_sdiff_of_subset hZA_sub, hC.1, hZA3]
          have hZBsdiff : (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z).card = 2 := by
            have := Finset.card_sdiff_add_card_inter (A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B)) Z
            omega
          have hsub_sdiff : A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z ⊆ A \ Z :=
            Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) (Finset.Subset.refl _)
          have heq_rem : A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) \ Z = A \ Z :=
            Finset.eq_of_subset_of_card_le hsub_sdiff (by omega)
          have h5_sdiff : a₅ ∈ A \ Z := Finset.mem_sdiff.mpr ⟨by rw [hd.hA_eq]; simp, hd.ha5Z⟩
          rw [← heq_rem] at h5_sdiff; exact (Finset.mem_sdiff.mp h5_sdiff).1
        have hZB_eq : A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B) = {a₃, a₄, a₅} := by
          refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          · rw [Finset.card_insert_of_notMem (by
                  intro hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
                  rcases hm with h | h
                  · exact hd.ha4Z (h ▸ ha3Z)
                  · exact hd.ha5Z (h ▸ ha3Z)),
                Finset.card_insert_of_notMem (by simp [hd.ha45]), Finset.card_singleton]; omega
        have hpc := core_fact1_three_pairconst hC hpB hpBL hpB3
        rw [hZB_eq] at hpc
        exact close_567_g1 hC hd hQ3 hQ2 hQ1 hg1 hpc
      · have hg2 : 2 ≤ g₃ := by omega
        by_cases h1_hv : HitsHv a₁
        · obtain ⟨q, hq, hqL, hq2, hq_hv, hmem1⟩ := h1_hv
          by_cases hg4 : 4 ≤ g₃
          · have ha3_v42 : a₃ = g₃ * 42 := by rw [ha3_v, hQ1, hQ2]; ring
            have h144 : 4 * (6 * 6) ≤ M := by omega
            have hmul : a₁ = (g₃ * 5) * 6 := by rw [hd.ha1_eq, hQ3, hQ2]; ring
            have hdiv : a₁ / 6 = g₃ * 5 := by rw [hmul, Nat.mul_div_cancel _ (by decide)]
            have h6M : 6 * (a₁ / 6) ≤ M := by rw [hdiv]; omega
            exact close_Rule2_D1_ge5 (a_k := a₂) (a_i := a₁) (a_j := a₃) (Q_k := Q₂) (Q_i := Q₁) (Q_j := Q₃)
              hC hNR2 hd hp0 hp0L rfl hZ_213
              ha12.ne' hd.ha23.ne ha13.ne (by omega) (by omega) (by omega)
              ⟨g₃ * Q₁ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha2_eq hd.ha1_eq ha3_eq'' hd.hcop12.symm hd.hcop23
              (fun p hp hpL hp3 hp_ne hmem => h2_nh3 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩)
              (by decide) (by decide) (by rw [hQ2]) (by decide) (by rw [hQ2]) h144 h6M
          · have hg23 : g₃ = 2 ∨ g₃ = 3 := by omega
            let Zq := A.filter (fun a => a.factorization q < (A.lcm id).factorization q)
            have ha2_not_Zq : a₂ ∉ Zq := fun hm =>
              core_Zq_card_le2_at_most_one_in_ZA hC hd hq hq2 ha1Z ha2Z ha12.ne hmem1 hm
            have ha3_not_Zq : a₃ ∉ Zq := fun hm =>
              core_Zq_card_le2_at_most_one_in_ZA hC hd hq hq2 ha1Z ha3Z ha13.ne hmem1 hm
            have hL_pos := finset_lcm_pos_core hC.2.1
            have ha2_eq : a₂.factorization q = (A.lcm id).factorization q := by
              have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) (by rw [hd.hA_eq]; simp : a₂ ∈ A)) (p := q)
              simp only [id_eq] at hle
              by_contra hlt; exact ha2_not_Zq (Finset.mem_filter.mpr ⟨by rw [hd.hA_eq]; simp, by omega⟩)
            have ha3_eq : a₃.factorization q = (A.lcm id).factorization q := by
              have hle := fac_le_of_dvd_5 hL_pos.ne' (Finset.dvd_lcm (f := id) (by rw [hd.hA_eq]; simp : a₃ ∈ A)) (p := q)
              simp only [id_eq] at hle
              by_contra hlt; exact ha3_not_Zq (Finset.mem_filter.mpr ⟨by rw [hd.hA_eq]; simp, by omega⟩)
            have hq_2 : q ^ (A.lcm id).factorization q ∣ a₂ :=
              (hq.pow_dvd_iff_le_factorization (hC.2.1 a₂ (by rw [hd.hA_eq]; simp)).ne').mpr ha2_eq.symm.le
            have hq_3 : q ^ (A.lcm id).factorization q ∣ a₃ :=
              (hq.pow_dvd_iff_le_factorization (hC.2.1 a₃ (by rw [hd.hA_eq]; simp)).ne').mpr ha3_eq.symm.le
            have hqe_le_gcd : q ^ (A.lcm id).factorization q ∣ Nat.gcd a₂ a₃ := Nat.dvd_gcd hq_2 hq_3
            have hgcd_23 : Nat.gcd a₂ a₃ = g₃ * 7 := by
              rw [hd.ha2_eq, hd.ha3_eq, hQ3, hQ2, hQ1]
              calc Nat.gcd (g₃ * 7 * 5) (g₃ * 7 * 6) = (g₃ * 7) * Nat.gcd 5 6 := Nat.gcd_mul_left (g₃ * 7) 5 6
                _ = g₃ * 7 := by simp [(by decide : Nat.gcd 5 6 = 1)]
            have hqe_le7 : q ^ (A.lcm id).factorization q ≤ 7 := by
              have hd7 : q ^ (A.lcm id).factorization q ∣ g₃ * 7 := hgcd_23 ▸ hqe_le_gcd
              have hq1 : 1 ≤ (A.lcm id).factorization q := (core_Z_T_props hC hq hqL).1
              rcases hq.dvd_mul.mp (dvd_trans (dvd_pow_self q (by omega)) hd7) with hq_g | hq_7
              · have hcop_q7 : Nat.Coprime (q ^ (A.lcm id).factorization q) 7 :=
                  (hq.coprime_iff_not_dvd.mpr fun h => by
                    have hq7 : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp h
                    rw [hq7] at hq_g
                    rcases hg23 with rfl | rfl <;> revert hq_g <;> decide).pow_left _
                have hdiv_g : q ^ (A.lcm id).factorization q ∣ g₃ := hcop_q7.dvd_of_dvd_mul_right hd7
                exact le_trans (Nat.le_of_dvd hg3p hdiv_g) (by omega)
              · have hq7_eq : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7)).mp hq_7
                have hcop_qg : Nat.Coprime (q ^ (A.lcm id).factorization q) g₃ :=
                  (hq.coprime_iff_not_dvd.mpr fun h => by
                    rw [hq7_eq] at h
                    rcases hg23 with rfl | rfl <;> revert h <;> decide).pow_left _
                have hdiv_7 : q ^ (A.lcm id).factorization q ∣ 7 := hcop_qg.dvd_of_dvd_mul_left hd7
                exact Nat.le_of_dvd (by decide) hdiv_7
            have hsq49 : (q ^ (A.lcm id).factorization q) ^ 2 ≤ 49 := Nat.pow_le_pow_left hqe_le7 2
            have ha3_84 : 84 ≤ a₃ := by rw [hd.ha3_eq, hQ1, hQ2]; omega
            omega
        · have h1_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
              (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
              A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
              a₁ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
            h1_nh3 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
          have h1_nohv : ∀ q : ℕ, q.Prime → q ∣ A.lcm id →
              (A.filter (fun a => a.factorization q < (A.lcm id).factorization q)).card ≤ 2 →
              M < (q ^ (A.lcm id).factorization q) ^ 2 →
              a₁ ∉ A.filter (fun a => a.factorization q < (A.lcm id).factorization q) := fun q hq hqL hq2 hq_hv hmem =>
            h1_hv ⟨q, hq, hqL, hq2, hq_hv, hmem⟩
          have ha3_v42 : a₃ = g₃ * 42 := by rw [ha3_v, hQ1, hQ2]; ring
          have hsq1 : Q₁ ^ 2 ≤ M := by rw [hQ1]; omega
          have h7_60 := core_Qk_dvd_60 (a_k := a₁) (a_i := a₂) (a_j := a₃) (Q_k := Q₁) (Q_i := Q₂) (Q_j := Q₃)
            hC hNR1 hd hd.hZ_eq ha12.ne ha13.ne hd.ha23.ne (by omega) (by omega) (by omega)
            ⟨g₃ * Q₂ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha1_eq hd.ha2_eq hd.ha3_eq hd.hcop12 hd.hcop13
            h1_no3 h1_nohv (Or.inl hsq1)
          rw [hQ1] at h7_60
          revert h7_60; decide
    · have h3_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
          (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
          A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
          a₃ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
        h3_hit ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
      have ha3_v42 : a₃ = g₃ * 42 := by rw [ha3_v, hQ1, hQ2]; ring
      have ha1_div5 : a₁ / 5 = g₃ * 6 := by rw [hd.ha1_eq, hQ3, hQ2]; omega
      have h25 : 25 ≤ M := by omega
      have h6_1 : 6 * (a₁ / 5) ≤ M := by rw [ha1_div5]; omega
      exact close_Q5_rule1 (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
        hC hNR1 hd hp0 hp0L rfl hZ_312 ha13.ne' hd.ha23.ne' ha12.ne (by omega) (by omega) (by omega)
        ⟨g₃ * Q₁ * Q₂, by rw [hd.hL3_eq]; ring⟩ ha3_eq' ha1_eq' ha2_eq' hd.hcop13.symm hd.hcop23.symm
        h3_no3 hQ3 h25 h6_1
  · exfalso
    by_cases h2_hit : Hits3 a₂
    · obtain ⟨p_B, hpB, hpBL, hpB3, hpB_ne, ha2_B⟩ := h2_hit
      have h3_nh3 : ¬ Hits3 a₃ := fun h => hits3_unique a₃ a₂ ha3Z ha2Z hd.ha23.ne' h ⟨p_B, hpB, hpBL, hpB3, hpB_ne, ha2_B⟩
      have h3_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
          (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
          A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
          a₃ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
        h3_nh3 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
      rcases core_unhit_k_dichotomy (a_k := a₃) (a_i := a₁) (a_j := a₂) (Q_k := Q₃) (Q_i := Q₁) (Q_j := Q₂)
          hC hd hp0 hp0L rfl hZ_312 ha13.ne' hd.ha23.ne' ha12.ne (by omega) (by omega) (by omega)
          ⟨g₃ * Q₁ * Q₂, by rw [hd.hL3_eq]; ring⟩ ha3_eq' ha1_eq' ha2_eq' hd.hcop13.symm hd.hcop23.symm h3_no3 with
          ⟨u₃, u₄, u₅, hAeq, h21, h23, h24, h25, h13, h14, h15, h34, h35, h45, hnd, _, _⟩ |
          ⟨hno_ZB, _⟩
      · have ha1_eq : a₁ = g₃ * 20 := by rw [hd.ha1_eq, hQ3, hQ2]; ring
        have ha2_eq : a₂ = g₃ * 28 := by rw [hd.ha2_eq, hQ3, hQ1]; ring
        have ha3_eq : a₃ = g₃ * 35 := by rw [hd.ha3_eq, hQ2, hQ1]; ring
        have h4_a2 : 2 ^ 2 ∣ a₂ := ⟨g₃ * 7, by rw [ha2_eq]; ring⟩
        have h4_a1 : 2 ^ 2 ∣ a₁ := ⟨g₃ * 5, by rw [ha1_eq]; ring⟩
        have h2L : 2 ∣ A.lcm id := dvd_trans (by decide : 2 ∣ 4) (dvd_trans h4_a2 (Finset.dvd_lcm (f := id) (by rw [hd.hA_eq]; simp : a₂ ∈ A)))
        have ⟨_, _, _, _, _, h3_2e⟩ := core_Z_T_props hC Nat.prime_two h2L
        have hf2_2 : 2 ≤ a₂.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (hC.2.1 a₂ (by rw [hd.hA_eq]; simp)).ne').mp h4_a2
        have hf1_2 : 2 ≤ a₁.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (hC.2.1 a₁ (by rw [hd.hA_eq]; simp)).ne').mp h4_a1
        have h16M : 2 ^ (2 + 2) ≤ M := by omega
        have h5_2 : 5 * (a₂ / 2 ^ 2) ≤ M := by
          have : a₂ / 4 = g₃ * 7 := by rw [ha2_eq]; omega
          change 5 * (a₂ / 4) ≤ M; rw [this]; omega
        have h6_1 : 6 * (a₁ / 2 ^ 2) ≤ M := by
          have : a₁ / 4 = g₃ * 5 := by rw [ha1_eq]; omega
          change 6 * (a₁ / 4) ≤ M; rw [this]; omega
        exact hNR1 ⟨a₂, a₁, u₃, u₄, u₅, 2, 2, 2, hAeq, h21, h23, h24, h25, h13, h14, h15, h34, h35, h45,
          hnd, Nat.prime_two, by decide, hf2_2, by decide, hf1_2, h16M, h3_2e, h5_2, h6_1⟩
      · exact hno_ZB ⟨A.filter (fun a => a.factorization p_B < (A.lcm id).factorization p_B), hpB_ne, p_B, hpB, hpBL, rfl, hpB3⟩
    · have h2_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
          (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
          A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
          a₂ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
        h2_hit ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
      have ha3_v35 : a₃ = g₃ * 35 := by rw [ha3_v, hQ1, hQ2]; ring
      have ha1_div5 : a₁ / 5 = g₃ * 4 := by rw [hd.ha1_eq, hQ3, hQ2]; omega
      have h25 : 25 ≤ M := by omega
      have h6_1 : 6 * (a₁ / 5) ≤ M := by rw [ha1_div5]; omega
      exact close_Q5_rule1 (a_k := a₂) (a_i := a₁) (a_j := a₃) (Q_k := Q₂) (Q_i := Q₁) (Q_j := Q₃)
        hC hNR1 hd hp0 hp0L rfl hZ_213 ha12.ne' hd.ha23.ne ha13.ne (by omega) (by omega) (by omega)
        ⟨g₃ * Q₁ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha2_eq hd.ha1_eq ha3_eq'' hd.hcop12.symm hd.hcop23
        h2_no3 hQ2 h25 h6_1
  · have hg2 : 2 ≤ g₃ := by
      by_contra h1; have hg1 : g₃ = 1 := by omega
      exact close_345_g1 hC hd hQ3 hQ2 hQ1 hg1
    have h1_hit : Hits3 a₁ := by
      by_contra h1_nh3
      have h1_no3 : ∀ p : ℕ, p.Prime → p ∣ A.lcm id →
          (A.filter (fun a => a.factorization p < (A.lcm id).factorization p)).card = 3 →
          A.filter (fun a => a.factorization p < (A.lcm id).factorization p) ≠ Z →
          a₁ ∉ A.filter (fun a => a.factorization p < (A.lcm id).factorization p) := fun p hp hpL hp3 hp_ne hmem =>
        h1_nh3 ⟨p, hp, hpL, hp3, hp_ne, hmem⟩
      have ha3_v20 : a₃ = g₃ * 20 := by rw [ha3_v, hQ1, hQ2]; ring
      have ha2_div5 : a₂ / 5 = g₃ * 3 := by rw [hd.ha2_eq, hQ3, hQ1]; omega
      have h25 : 25 ≤ M := by omega
      have h6_2 : 6 * (a₂ / 5) ≤ M := by rw [ha2_div5]; omega
      exact close_Q5_rule1 (a_k := a₁) (a_i := a₂) (a_j := a₃) (Q_k := Q₁) (Q_i := Q₂) (Q_j := Q₃)
        hC hNR1 hd hp0 hp0L rfl hd.hZ_eq ha12.ne ha13.ne hd.ha23.ne (by omega) (by omega) (by omega)
        ⟨g₃ * Q₂ * Q₃, by rw [hd.hL3_eq]; ring⟩ hd.ha1_eq hd.ha2_eq hd.ha3_eq hd.hcop12 hd.hcop13
        h1_no3 hQ1 h25 h6_2
    obtain ⟨p₁, hp1, hp1L, hp1_3, hp1_ne, ha1_in⟩ := h1_hit
    refine ⟨a₁, a₂, a₃, a₄, a₅, L₃, g₃, ?_, hg2, p₁, hp1, hp1L, hp1_3, hp1_ne, ha1_in⟩
    subst hQ1; subst hQ2; subst hQ3; exact hd

private lemma core_contradiction {A : Finset ℕ} {M : ℕ} (hC : C5Core A M) :
    HasRule1 A M ∨ HasRule2 A M ∨ HasRule2b A M := by
  by_contra hnone; push Not at hnone
  rcases hnone with ⟨hNR1, hNR2, hNR2b⟩
  have h3_ex : ∃ p₀ : ℕ, p₀.Prime ∧ p₀ ∣ A.lcm id ∧
      (A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)).card = 3 := by
    by_contra hno3; push Not at hno3
    refine core_case1_no_three_set hC hNR1 fun p hp hpL => ?_
    have ⟨_, _, _, _, hle3, _⟩ := core_Z_T_props hC hp hpL
    have hne3 := hno3 p hp hpL
    omega
  obtain ⟨p₀, hp0, hp0L, hp0_3⟩ := h3_ex
  obtain ⟨a₁, a₂, a₃, _, _, _, g_A, hdA, _, p₁, hp1, hp1L, hp1_3, hp1_ne, ha1_ZB⟩ :=
    solve_from_three_set hC hNR1 hNR2 hNR2b hp0 hp0L hp0_3
  obtain ⟨b₁, b₂, b₃, _, _, _, g_B, hdB, _, p₂, hp2, hp2L, hp2_3, hp2_ne, hb1_ZC⟩ :=
    solve_from_three_set hC hNR1 hNR2 hNR2b hp1 hp1L hp1_3
  let Z_A := A.filter (fun a => a.factorization p₀ < (A.lcm id).factorization p₀)
  let Z_B := A.filter (fun a => a.factorization p₁ < (A.lcm id).factorization p₁)
  let Z_C := A.filter (fun a => a.factorization p₂ < (A.lcm id).factorization p₂)
  have hZC_eq_ZA : Z_C = Z_A :=
    core_at_most_one_other_3set hC hp1_3 (Finset.filter_subset _ _)
      ⟨p₂, hp2, hp2L, rfl, hp2_3⟩ ⟨p₀, hp0, hp0L, rfl, hp0_3⟩ hp2_ne hp1_ne.symm ⟨p₁, hp1, hp1L, rfl⟩
  have ha1_ZA : a₁ ∈ Z_A := by dsimp only [Z_A]; rw [hdA.hZ_eq]; simp
  have hb1_ZB : b₁ ∈ Z_B := by dsimp only [Z_B]; rw [hdB.hZ_eq]; simp
  have hb1_ZA : b₁ ∈ Z_A := hZC_eq_ZA ▸ hb1_ZC
  have hi := core_fact3_two_three_sets hC hp0 hp0L hp1 hp1L hp0_3 hp1_3 hp1_ne.symm
  have ha1_in : a₁ ∈ Z_A ∩ Z_B := Finset.mem_inter.mpr ⟨ha1_ZA, ha1_ZB⟩
  have hb1_in : b₁ ∈ Z_A ∩ Z_B := Finset.mem_inter.mpr ⟨hb1_ZA, hb1_ZB⟩
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hi
  have ha1_eq_x : a₁ = x := by rw [hx_eq, Finset.mem_singleton] at ha1_in; exact ha1_in
  have hb1_eq_x : b₁ = x := by rw [hx_eq, Finset.mem_singleton] at hb1_in; exact hb1_in
  have hab1 : a₁ = b₁ := ha1_eq_x.trans hb1_eq_x.symm
  have ha1_v : a₁ = 12 * g_A := by rw [hdA.ha1_eq]; ring
  have hb1_v : b₁ = 12 * g_B := by rw [hdB.ha1_eq]; ring
  have hg_eq : g_A = g_B := by omega
  have ha2_v : a₂ = 15 * g_A := by rw [hdA.ha2_eq]; ring
  have hb2_v : b₂ = 15 * g_B := by rw [hdB.ha2_eq]; ring
  have ha3_v : a₃ = 20 * g_A := by rw [hdA.ha3_eq]; ring
  have hb3_v : b₃ = 20 * g_B := by rw [hdB.ha3_eq]; ring
  have hZ_eq : Z_A = Z_B := by
    dsimp only [Z_A, Z_B]
    rw [hdA.hZ_eq, hdB.hZ_eq, ha1_v, ha2_v, ha3_v, hb1_v, hb2_v, hb3_v, hg_eq]
  exact hp1_ne hZ_eq.symm

/-- Master `r = 1` theorem for `g(5) ≤ 6`. -/
theorem erdos708_upper_five_of_matching_one {A S : Finset ℕ} {x M : ℕ} {f : ℕ → ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hS_sub : S ⊆ A) (hS_card : S.card = 1)
    (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a)
    (hmax : ¬ HasMatching A x M 2) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨s₁, hs1_eq⟩ := Finset.card_eq_one.mp hS_card
  have hs1S : s₁ ∈ S := by rw [hs1_eq]; exact Finset.mem_singleton_self s₁
  have hs1A : s₁ ∈ A := hS_sub hs1S
  let b₀ := f s₁
  have hb₀_I : b₀ ∈ consecInterval x M := hf_mem s₁ hs1S
  have hs1_dvd : s₁ ∣ b₀ := hf_dvd s₁ hs1S
  have h_unique_mult : ∀ a ∈ A, ∀ b ∈ consecInterval x M, a ∣ b → b = b₀ := by
    intro a haA b hb_I hab
    by_contra hne
    by_cases has1 : a = s₁
    · obtain ⟨a', ha'A, ha's1⟩ : ∃ a' ∈ A, a' ≠ s₁ := by
        by_contra hall; push Not at hall
        have : A ⊆ {s₁} := fun z hz => by simp [hall z hz]
        have := Finset.card_le_card this; simp at this; omega
      have ha'_b0 : a' ∣ b₀ := by
        by_contra hnd
        obtain ⟨b', hb'_I, hb'_dvd⟩ := exists_multiple_in_consecInterval x a' M (hA_pos a' ha'A) (hA_le a' ha'A)
        have hbb' : b₀ ≠ b' := fun h => hnd (h ▸ hb'_dvd)
        let f' := fun z => if z = s₁ then b₀ else b'
        have hS2 : ({s₁, a'} : Finset ℕ).card = 2 := Finset.card_pair ha's1.symm
        have hInj : Set.InjOn f' ({s₁, a'} : Finset ℕ) := by
          intro u hu v hv huv
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
          · exact hu1.trans hv1.symm
          · dsimp [f'] at huv; rw [if_pos hu1, if_neg (hv2 ▸ ha's1)] at huv; exact absurd huv hbb'
          · dsimp [f'] at huv; rw [if_neg (hu2 ▸ ha's1), if_pos hv1] at huv; exact absurd huv.symm hbb'
          · exact hu2.trans hv2.symm
        exact hmax ⟨{s₁, a'},
          fun z hz => by simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption,
          hS2, f',
          fun z hz => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz1 | hz2
            · dsimp [f']; rw [if_pos hz1]; exact hb₀_I
            · dsimp [f']; rw [if_neg (hz2 ▸ ha's1)]; exact hb'_I,
          fun z hz => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with hz1 | hz2
            · rw [hz1]; dsimp [f']; rw [if_pos rfl]; exact hs1_dvd
            · rw [hz2]; dsimp [f']; rw [if_neg ha's1]; exact hb'_dvd,
          hInj⟩
      let f' := fun z => if z = a' then b₀ else b
      have hS2 : ({a', s₁} : Finset ℕ).card = 2 := Finset.card_pair ha's1
      have hInj : Set.InjOn f' ({a', s₁} : Finset ℕ) := by
        intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
        · exact hu1.trans hv1.symm
        · dsimp [f'] at huv; rw [if_pos hu1, if_neg (hv2 ▸ ha's1.symm)] at huv; exact absurd huv.symm hne
        · dsimp [f'] at huv; rw [if_neg (hu2 ▸ ha's1.symm), if_pos hv1] at huv; exact absurd huv hne
        · exact hu2.trans hv2.symm
      exact hmax ⟨{a', s₁},
        fun z hz => by simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption,
        hS2, f',
        fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz1 | hz2
          · dsimp [f']; rw [if_pos hz1]; exact hb₀_I
          · dsimp [f']; rw [if_neg (hz2 ▸ ha's1.symm)]; exact hb_I,
        fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz1 | hz2
          · rw [hz1]; dsimp [f']; rw [if_pos rfl]; exact ha'_b0
          · rw [hz2]; dsimp [f']; rw [if_neg ha's1.symm]; exact has1 ▸ hab,
        hInj⟩
    · let f' := fun z => if z = s₁ then b₀ else b
      have hS2 : ({s₁, a} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm has1)
      have hInj : Set.InjOn f' ({s₁, a} : Finset ℕ) := by
        intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
        · exact hu1.trans hv1.symm
        · dsimp [f'] at huv; rw [if_pos hu1, if_neg (hv2 ▸ has1)] at huv; exact absurd huv.symm hne
        · dsimp [f'] at huv; rw [if_neg (hu2 ▸ has1), if_pos hv1] at huv; exact absurd huv hne
        · exact hu2.trans hv2.symm
      exact hmax ⟨{s₁, a},
        fun z hz => by simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption,
        hS2, f',
        fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz1 | hz2
          · dsimp [f']; rw [if_pos hz1]; exact hb₀_I
          · dsimp [f']; rw [if_neg (hz2 ▸ has1)]; exact hb_I,
        fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz1 | hz2
          · rw [hz1]; dsimp [f']; rw [if_pos rfl]; exact hs1_dvd
          · rw [hz2]; dsimp [f']; rw [if_neg has1]; exact hab,
        hInj⟩
  have hb₀_dvd : ∀ a ∈ A, a ∣ b₀ := fun a haA => by
    obtain ⟨b, hb_I, hab⟩ := exists_multiple_in_consecInterval x a M (hA_pos a haA) (hA_le a haA)
    rw [h_unique_mult a haA b hb_I hab] at hab; exact hab
  have hA_half : ∀ a ∈ A, M < 2 * a := fun a haA =>
    lt_two_mul_of_unique_multiple_in_consecInterval (hA_pos a haA) hb₀_I (hb₀_dvd a haA)
      fun b hb_I hab => h_unique_mult a haA b hb_I hab
  by_cases hNo4 : No4Chain A
  · by_cases hNo1b : NoType1b A
    · have hC : C5Core A M := ⟨hA_card, hA_pos, hA_le, hA_half, hAgcd, hNo4, hNo1b⟩
      rcases core_contradiction hC with hr1 | hr2 | hr2b
      · exact cover_six_of_rule1 hA_pos hA_le hA_half hAgcd hb₀_I hb₀_dvd hr1
      · exact cover_six_of_rule2 hA_pos hA_le hA_half hb₀_I hb₀_dvd hr2
      · exact cover_six_of_rule2b hA_pos hA_le hb₀_I hb₀_dvd hr2b
    · dsimp [NoType1b] at hNo1b
      push Not at hNo1b
      obtain ⟨u, huA, hpc⟩ := hNo1b
      have hAer_card : (A.erase u).card = 4 := by rw [Finset.card_erase_of_mem huA, hA_card]
      obtain ⟨a₁, a₂, a₃, a₄, h12, h13, h14, h23, h24, h34, hAer_eq⟩ := Finset.card_eq_four.mp hAer_card
      have h4A : ∀ a ∈ ({a₁, a₂, a₃, a₄} : Finset ℕ), a ∈ A := fun a ha =>
        Finset.erase_subset u A (hAer_eq ▸ ha)
      refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 huA ?_
      rw [hAer_eq]
      exact cover_four_of_type1b rfl h12 h13 h14 h23 h24 h34
        (fun a ha => hA_pos a (h4A a ha)) (fun a ha => hA_le a (h4A a ha))
        (fun a ha => hA_half a (h4A a ha)) hb₀_I (fun a ha => hb₀_dvd a (h4A a ha)) (hAer_eq ▸ hpc)
  · dsimp [No4Chain] at hNo4
    push Not at hNo4
    obtain ⟨a₁, ha1A, a₂, ha2A, a₃, ha3A, a₄, ha4A, h12, h13, h14, h23, h24, h34, h3_nd, h4_nd⟩ := hNo4
    have hu_ex : ∃ u ∈ A, u ≠ a₁ ∧ u ≠ a₂ ∧ u ≠ a₃ ∧ u ≠ a₄ := by
      by_contra hnone; push Not at hnone
      have hsub : A ⊆ {a₁, a₂, a₃, a₄} := fun z hz => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno; exact hno.2.2.2 (hnone z hz hno.1 hno.2.1 hno.2.2.1)
      have := Finset.card_le_card hsub; have h4 := card_finset_le_four_5 a₁ a₂ a₃ a₄; omega
    obtain ⟨u, huA, hu1, hu2, hu3, hu4⟩ := hu_ex
    have hsub5 : ({u, a₁, a₂, a₃, a₄} : Finset ℕ) ⊆ A := fun w hw => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
    have h5_card : ({u, a₁, a₂, a₃, a₄} : Finset ℕ).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hu1, hu2, hu3, hu4]),
          Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
          Finset.card_insert_of_notMem (by simp [h23, h24]),
          Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
    have hA_eq5 : A = {u, a₁, a₂, a₃, a₄} :=
      (Finset.eq_of_subset_of_card_le hsub5 (by rw [h5_card, hA_card])).symm
    have hAer_eq : A.erase u = {a₁, a₂, a₃, a₄} := by
      rw [hA_eq5, Finset.erase_insert (by simp [hu1, hu2, hu3, hu4])]
    have h4A : ∀ a ∈ ({a₁, a₂, a₃, a₄} : Finset ℕ), a ∈ A := fun a ha =>
      Finset.erase_subset u A (hAer_eq ▸ ha)
    refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 huA ?_
    rw [hAer_eq]
    exact cover_four_of_chain4 rfl h12 h13 h14 h23 h24 h34
      (fun a ha => hA_pos a (h4A a ha)) (fun a ha => hA_le a (h4A a ha))
      (fun a ha => hA_half a (h4A a ha)) hb₀_I (fun a ha => hb₀_dvd a (h4A a ha)) h3_nd h4_nd

end Erdos708
