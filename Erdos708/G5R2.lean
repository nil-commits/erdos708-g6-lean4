import Erdos708.G5TwoSlot

/-!
# PPL 176 (Erdős Problem #708) — Matching Size `r = 2` Closure for `g(5) ≤ 6`

This module proves `erdos708_upper_five_of_matching_two`: for any `5`-element set `A ⊆ [2, M]`
with `A.gcd id = 1` and `7 ≤ M`, if the maximum bipartite matching into `consecInterval x M` has
size `2`, then `A` admits a `≤ 6`-slot cover in `consecInterval x M`.

Main components:
1. `cover_four_of_two_pairs`: two disjoint pairs `(a₁, a₂) ∣ b₁` and `(a₃, a₄) ∣ b₂` with
   `3 * gcd ≤ M` admit a `≤ 4`-slot cover.
2. `not_two_bad_pairs`: bad pairs (`M < 3 * gcd`) form a matching, so any `3`-element set
   contains a good pair (`3 * gcd ≤ M`).
3. `cover_six_of_four_half_one`: handles `4` half-interval divisors of `b₁` plus `1` divisor of `b₂`.
4. `erdos708_upper_five_of_matching_two`: full `(U₁, U₂, C)` partition dispatch across
   one-sided and two-sided `r = 2` configurations.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Pair-Coverage and Matching-of-Bad-Pairs Lemmas -/

/-- Two disjoint pairs `(a₁, a₂) ∣ b₁` and `(a₃, a₄) ∣ b₂` (`b₁ ≠ b₂`) with
    `3 * gcd(a₁, a₂) ≤ M` and `3 * gcd(a₃, a₄) ≤ M` admit a `≤ 4`-slot cover. -/
lemma cover_four_of_two_pairs {x M b₁ b₂ a₁ a₂ a₃ a₄ : ℕ}
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (h1p : 0 < a₁) (h2p : 0 < a₂) (h3p : 0 < a₃) (h4p : 0 < a₄)
    (h1M : a₁ ≤ M) (h2M : a₂ ≤ M) (h3M : a₃ ≤ M) (h4M : a₄ ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb1_1 : a₁ ∣ b₁) (hb1_2 : a₂ ∣ b₁) (hb2_3 : a₃ ∣ b₂) (hb2_4 : a₄ ∣ b₂)
    (h3g1 : 3 * Nat.gcd a₁ a₂ ≤ M) (h3g2 : 3 * Nat.gcd a₃ a₄ ≤ M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover ({a₁, a₂, a₃, a₄} : Finset ℕ) B := by
  let g₁ := Nat.gcd a₁ a₂
  let g₂ := Nat.gcd a₃ a₄
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left a₂ h1p
  have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left a₄ h3p
  have hcard2 : ({b₁, b₂} : Finset ℕ).card + 1 ≤ 3 := by
    have h1 := Finset.card_insert_le b₁ {b₂}
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨w₁, hw₁_I, hw₁_not, hg₁_w₁⟩ := exists_avoiding_multiple_5 x M g₁ {b₁, b₂}
    hg₁_pos (le_trans (Nat.mul_le_mul_right g₁ hcard2) h3g1)
  obtain ⟨w₂, hw₂_I, hw₂_not, hg₂_w₂⟩ := exists_avoiding_multiple_5 x M g₂ {b₁, b₂}
    hg₂_pos (le_trans (Nat.mul_le_mul_right g₂ hcard2) h3g2)
  have hw1_b1 : w₁ ≠ b₁ := fun h => hw₁_not (by simp [h])
  have hw1_b2 : w₁ ≠ b₂ := fun h => hw₁_not (by simp [h])
  have hw2_b1 : w₂ ≠ b₁ := fun h => hw₂_not (by simp [h])
  have hw2_b2 : w₂ ≠ b₂ := fun h => hw₂_not (by simp [h])
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hA4_0 : ∀ a ∈ ({a₁, a₂, a₃, a₄} : Finset ℕ), a ≠ 0 := fun a ha => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hsumA : ∀ p : ℕ, ∑ a ∈ ({a₁, a₂, a₃, a₄} : Finset ℕ), a.factorization p =
      a₁.factorization p + a₂.factorization p + a₃.factorization p + a₄.factorization p := by
    intro p
    rw [Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
        Finset.sum_insert (by simp [h34]), Finset.sum_singleton]
    ring
  by_cases hw12 : w₁ = w₂
  · let g₁₂ := Nat.gcd g₁ g₂
    have hg₁₂_pos : 0 < g₁₂ := Nat.gcd_pos_of_pos_left g₂ hg₁_pos
    have h4g₁₂ : 4 * g₁₂ ≤ M := four_mul_le_of_four_dvd_distinct hg₁₂_pos h12 h13 h14 h23 h24 h34
      h1p h2p h3p h4p h1M h2M h3M h4M
      (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left a₁ a₂))
      (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right a₁ a₂))
      (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left a₃ a₄))
      (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right a₃ a₄))
    have hcard3 : ({b₁, b₂, w₁} : Finset ℕ).card + 1 ≤ 4 := by
      have h1 := Finset.card_insert_le b₁ {b₂, w₁}
      have h2 := Finset.card_insert_le b₂ {w₁}
      simp only [Finset.card_singleton] at h2
      omega
    obtain ⟨w₃, hw₃_I, hw₃_not, hg₁₂_w₃⟩ := exists_avoiding_multiple_5 x M g₁₂ {b₁, b₂, w₁}
      hg₁₂_pos (le_trans (Nat.mul_le_mul_right g₁₂ hcard3) h4g₁₂)
    have hw3_b1 : w₃ ≠ b₁ := fun h => hw₃_not (by simp [h])
    have hw3_b2 : w₃ ≠ b₂ := fun h => hw₃_not (by simp [h])
    have hw3_w1 : w₃ ≠ w₁ := fun h => hw₃_not (by simp [h])
    let B : Finset ℕ := {b₁, b₂, w₁, w₃}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, card_finset_le_four_5 b₁ b₂ w₁ w₃,
      isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
    intro p _hp
    have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + w₃.factorization p =
        ∑ b ∈ B, b.factorization p := by
      dsimp [B]
      rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw3_b1.symm]),
          Finset.sum_insert (by simp [hw1_b2.symm, hw3_b2.symm]),
          Finset.sum_insert (by simp [hw3_w1.symm]), Finset.sum_singleton]
      ring
    rw [hsumA p, ← hsumB]
    have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_1 (p := p)
    have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_2 (p := p)
    have hb2_3' := fac_le_of_dvd_5 hb₂0 hb2_3 (p := p)
    have hb2_4' := fac_le_of_dvd_5 hb₂0 hb2_4 (p := p)
    have hw10 := (pos_of_mem_consecInterval hw₁_I).ne'
    have hw30 := (pos_of_mem_consecInterval hw₃_I).ne'
    have hw1_g1 := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
    have hw1_g2 := fac_le_of_dvd_5 hw10 (hw12 ▸ hg₂_w₂) (p := p)
    have hw3_g12 := fac_le_of_dvd_5 hw30 hg₁₂_w₃ (p := p)
    rw [fac_gcd_eq_min_5 h1p.ne' h2p.ne'] at hw1_g1
    rw [fac_gcd_eq_min_5 h3p.ne' h4p.ne'] at hw1_g2
    rw [fac_gcd_eq_min_5 hg₁_pos.ne' hg₂_pos.ne',
        fac_gcd_eq_min_5 h1p.ne' h2p.ne', fac_gcd_eq_min_5 h3p.ne' h4p.ne'] at hw3_g12
    have hvi := r2_31_merged_ineq (a₁.factorization p) (a₂.factorization p)
      (a₃.factorization p) (a₄.factorization p)
    omega
  · let B : Finset ℕ := {b₁, b₂, w₁, w₂}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, card_finset_le_four_5 b₁ b₂ w₁ w₂,
      isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
    intro p _hp
    have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + w₂.factorization p =
        ∑ b ∈ B, b.factorization p := by
      dsimp [B]
      rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm]),
          Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm]),
          Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]
      ring
    rw [hsumA p, ← hsumB]
    have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_1 (p := p)
    have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_2 (p := p)
    have hb2_3' := fac_le_of_dvd_5 hb₂0 hb2_3 (p := p)
    have hb2_4' := fac_le_of_dvd_5 hb₂0 hb2_4 (p := p)
    have hw10 := (pos_of_mem_consecInterval hw₁_I).ne'
    have hw20 := (pos_of_mem_consecInterval hw₂_I).ne'
    have hw1_g1 := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
    have hw2_g2 := fac_le_of_dvd_5 hw20 hg₂_w₂ (p := p)
    rw [fac_gcd_eq_min_5 h1p.ne' h2p.ne'] at hw1_g1
    rw [fac_gcd_eq_min_5 h3p.ne' h4p.ne'] at hw2_g2
    omega

private lemma bad_pair_eq_double_aux {a b M : ℕ}
    (ha : 0 < a) (hlt : a < b) (hbM : b ≤ M) (hbad : M < 3 * Nat.gcd a b) :
    a = Nat.gcd a b ∧ b = 2 * Nat.gcd a b ∧ M < 2 * b := by
  let g := Nat.gcd a b
  obtain ⟨qa, hqa⟩ := Nat.gcd_dvd_left a b
  obtain ⟨qb, hqb⟩ := Nat.gcd_dvd_right a b
  have hqa1 : 1 ≤ qa := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hqa; omega)
  have hqab : qa < qb := by
    by_contra hle
    have hmul : g * qb ≤ g * qa := Nat.mul_le_mul_left g (by omega)
    rw [← hqa, ← hqb] at hmul
    omega
  have hqb3 : qb < 3 := by
    by_contra hge
    have : 3 * g ≤ b := by
      calc 3 * g = g * 3 := by ring
        _ ≤ g * qb := Nat.mul_le_mul_left g (by omega)
        _ = b := hqb.symm
    omega
  have hqa_eq : qa = 1 := by omega
  have hqb_eq : qb = 2 := by omega
  have ha_eq : a = g := by rw [hqa, hqa_eq, mul_one]
  have hb_eq : b = 2 * g := by rw [hqb, hqb_eq, mul_comm]
  exact ⟨ha_eq, hb_eq, by omega⟩

private lemma bad_pair_eq_double {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (haM : a ≤ M) (hbM : b ≤ M)
    (hbad : M < 3 * Nat.gcd a b) :
    (a = Nat.gcd a b ∧ b = 2 * Nat.gcd a b ∧ M < 2 * b) ∨
    (b = Nat.gcd a b ∧ a = 2 * Nat.gcd a b ∧ M < 2 * a) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact Or.inl (bad_pair_eq_double_aux ha hlt hbM hbad)
  · rw [Nat.gcd_comm] at hbad ⊢
    exact Or.inr (bad_pair_eq_double_aux hb hgt haM hbad)

private lemma not_two_bad_pairs {a b c M : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (haM : a ≤ M) (hbM : b ≤ M) (hcM : c ≤ M) :
    3 * Nat.gcd a b ≤ M ∨ 3 * Nat.gcd a c ≤ M := by
  by_contra hboth
  push Not at hboth
  rcases bad_pair_eq_double ha hb hab haM hbM hboth.1 with ⟨ha_g, hb_2g, _⟩ | ⟨hb_g, ha_2g, _⟩ <;>
  rcases bad_pair_eq_double ha hc hac haM hcM hboth.2 with ⟨ha_g', hc_2g', _⟩ | ⟨hc_g', ha_2g', _⟩
  · have : b = c := by omega
    exact hbc this
  · have : b = 2 * a := by omega
    have : M < 3 * c := by omega
    omega
  · have : c = 2 * a := by omega
    have : M < 3 * b := by omega
    omega
  · have : b = c := by omega
    exact hbc this

/-! ## Part 2: Four Half-Interval Divisors of `b₁` + One Divisor of `b₂` -/

private lemma cover_four_nonspan_of_h_eq_v1 {x M b₁ b₂ y₁ y₂ y₃ v₁ : ℕ}
    (hy1v : y₁ ≠ v₁) (hy2v : y₂ ≠ v₁) (hy3v : y₃ ≠ v₁)
    (hy12 : y₁ ≠ y₂) (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (hy1p : 0 < y₁) (hy2p : 0 < y₂) (hy3p : 0 < y₃) (hv1p : 0 < v₁)
    (hy1M : y₁ ≤ M) (hy2M : y₂ ≤ M) (hy3M : y₃ ≤ M) (hv1M : v₁ ≤ M)
    (hy1h : M < 2 * y₁) (hy2h : M < 2 * y₂)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb1_y1 : y₁ ∣ b₁) (hb1_y2 : y₂ ∣ b₁) (hb1_y3 : y₃ ∣ b₁) (hb₂_v1 : v₁ ∣ b₂)
    (hh_eq : v₁ = Nat.gcd (Nat.lcm y₁ y₂) y₃) (h3v : 3 * v₁ ≤ M) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover ({y₁, y₂, y₃, v₁} : Finset ℕ) B := by
  let L₁₂ := Nat.lcm y₁ y₂
  have hL12_pos : 0 < L₁₂ := Nat.lcm_pos hy1p hy2p
  let d₂ := Nat.gcd y₁ y₂
  have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_left y₂ hy1p
  have h3d₂ : 3 * d₂ ≤ M := three_mul_le_of_two_gt_half_5 hd₂_pos hy12 hy1M hy2M hy1h hy2h
    (Nat.gcd_dvd_left y₁ y₂) (Nat.gcd_dvd_right y₁ y₂)
  have hcard2 : ({b₁, b₂} : Finset ℕ).card + 1 ≤ 3 := by
    have h1 := Finset.card_insert_le b₁ {b₂}; simp only [Finset.card_singleton] at h1; omega
  obtain ⟨wh, hwh_I, hwh_not, hv1_wh⟩ := exists_avoiding_multiple_5 x M v₁ {b₁, b₂}
    hv1p (le_trans (Nat.mul_le_mul_right v₁ hcard2) h3v)
  have hwh_b1 : wh ≠ b₁ := fun h => hwh_not (by simp [h])
  have hwh_b2 : wh ≠ b₂ := fun h => hwh_not (by simp [h])
  have hA0 : ∀ a ∈ ({y₁, y₂, y₃, v₁} : Finset ℕ), a ≠ 0 := fun a ha => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hsumA : ∀ p : ℕ, ∑ a ∈ ({y₁, y₂, y₃, v₁} : Finset ℕ), a.factorization p =
      y₁.factorization p + y₂.factorization p + y₃.factorization p + v₁.factorization p := by
    intro p
    rw [Finset.sum_insert (by simp [hy12, hy13, hy1v]), Finset.sum_insert (by simp [hy23, hy2v]),
        Finset.sum_insert (by simp [hy3v]), Finset.sum_singleton]; ring
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hwh0 : wh ≠ 0 := (pos_of_mem_consecInterval hwh_I).ne'
  have hv1_eq_gcd : v₁.factorization = (Nat.gcd L₁₂ y₃).factorization := by rw [hh_eq]
  by_cases hex2 : ∃ w₂ ∈ consecInterval x M, w₂ ∉ ({b₁, b₂, wh} : Finset ℕ) ∧ d₂ ∣ w₂
  · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := hex2
    have hw2_b1 : w₂ ≠ b₁ := fun h => hw₂_not (by simp [h])
    have hw2_b2 : w₂ ≠ b₂ := fun h => hw₂_not (by simp [h])
    have hw2_wh : w₂ ≠ wh := fun h => hw₂_not (by simp [h])
    let B : Finset ℕ := {b₁, b₂, wh, w₂}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, card_finset_le_four_5 b₁ b₂ wh w₂, isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
    intro p _hp
    have hsumB : b₁.factorization p + b₂.factorization p + wh.factorization p + w₂.factorization p =
        ∑ b ∈ B, b.factorization p := by
      dsimp [B]
      rw [Finset.sum_insert (by simp [hb12, hwh_b1.symm, hw2_b1.symm]),
          Finset.sum_insert (by simp [hwh_b2.symm, hw2_b2.symm]),
          Finset.sum_insert (by simp [hw2_wh.symm]), Finset.sum_singleton]; ring
    rw [hsumA p, ← hsumB]
    have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
    have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
    have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
    have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
    have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
    have hvh := fac_le_of_dvd_5 hwh0 (hh_eq ▸ hv1_wh) (p := p)
    have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
    rw [fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvh
    rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hvd2
    have hvi := r2_nonspan3_val_ineq (y₁.factorization p) (y₂.factorization p)
      (y₃.factorization p) (v₁.factorization p)
    change y₁.factorization p + y₂.factorization p + y₃.factorization p + v₁.factorization p ≤
      max (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) + v₁.factorization p +
      min (y₁.factorization p) (y₂.factorization p) +
      min (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) at hvi
    omega
  · push Not at hex2
    have hsub : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ ({b₁, b₂, wh} : Finset ℕ) := by
      intro b hb; rw [Finset.mem_filter] at hb; by_contra hnot; exact hex2 b hb.1 hnot hb.2
    have hge3 : 3 ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card := by
      have h1 := card_multiples_Icc_ge x M d₂ hd₂_pos
      change M / d₂ ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card at h1
      have h2 : 3 ≤ M / d₂ := (Nat.le_div_iff_mul_le hd₂_pos).mpr h3d₂
      omega
    have hcard3 : ({b₁, b₂, wh} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hb12, hwh_b1.symm]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hwh_b2]), Finset.card_singleton]
    have heq_sub : (consecInterval x M).filter (fun b => d₂ ∣ b) = {b₁, b₂, wh} :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hd₂_b₂ : d₂ ∣ b₂ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : b₂ ∈ ({b₁, b₂, wh} : Finset ℕ)))).2
    have hd₂_wh : d₂ ∣ wh := (Finset.mem_filter.mp (heq_sub ▸ (by simp : wh ∈ ({b₁, b₂, wh} : Finset ℕ)))).2
    let D' := Nat.gcd d₂ v₁
    have hD'_pos : 0 < D' := Nat.gcd_pos_of_pos_left v₁ hd₂_pos
    have hD'_1 : D' ∣ y₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left y₁ y₂)
    have hD'_2 : D' ∣ y₂ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right y₁ y₂)
    have hD'_3 : D' ∣ y₃ := dvd_trans (Nat.gcd_dvd_right _ _)
      (hh_eq ▸ Nat.gcd_dvd_right L₁₂ y₃)
    have hD'_v : D' ∣ v₁ := Nat.gcd_dvd_right d₂ v₁
    have h4D' : 4 * D' ≤ M := four_mul_le_of_four_dvd_distinct hD'_pos hy12 hy13 hy1v hy23 hy2v hy3v
      hy1p hy2p hy3p hv1p hy1M hy2M hy3M hv1M hD'_1 hD'_2 hD'_3 hD'_v
    have hcard3' : ({b₁, b₂, wh} : Finset ℕ).card + 1 ≤ 4 := by omega
    obtain ⟨w', hw'_I, hw'_not, hD'_w'⟩ := exists_avoiding_multiple_5 x M D' {b₁, b₂, wh}
      hD'_pos (le_trans (Nat.mul_le_mul_right D' hcard3') h4D')
    have hw'_b1 : w' ≠ b₁ := fun h => hw'_not (by simp [h])
    have hw'_b2 : w' ≠ b₂ := fun h => hw'_not (by simp [h])
    have hw'_wh : w' ≠ wh := fun h => hw'_not (by simp [h])
    let B : Finset ℕ := {b₁, b₂, wh, w'}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    refine ⟨B, hBI, card_finset_le_four_5 b₁ b₂ wh w', isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
    intro p _hp
    have hsumB : b₁.factorization p + b₂.factorization p + wh.factorization p + w'.factorization p =
        ∑ b ∈ B, b.factorization p := by
      dsimp [B]
      rw [Finset.sum_insert (by simp [hb12, hwh_b1.symm, hw'_b1.symm]),
          Finset.sum_insert (by simp [Ne.symm hwh_b2, hw'_b2.symm]),
          Finset.sum_insert (by simp [hw'_wh.symm]), Finset.sum_singleton]; ring
    rw [hsumA p, ← hsumB]
    have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
    have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
    have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
    have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
    have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
    have hb2_d2 := fac_le_of_dvd_5 hb₂0 hd₂_b₂ (p := p)
    have hvh := fac_le_of_dvd_5 hwh0 (hh_eq ▸ hv1_wh) (p := p)
    have hvd2_wh := fac_le_of_dvd_5 hwh0 hd₂_wh (p := p)
    have hvdD := fac_le_of_dvd_5 hw'0 hD'_w' (p := p)
    rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hb2_d2 hvd2_wh
    rw [fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvh
    rw [fac_gcd_eq_min_5 hd₂_pos.ne' hv1p.ne', fac_gcd_eq_min_5 hy1p.ne' hy2p.ne',
        hh_eq, fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvdD
    have hv1p_eq : v₁.factorization p = min (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) := by
      rw [hh_eq, fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne']
    omega

private lemma extract_nonspan_four {U : Finset ℕ}
    (hUc : U.card = 4) (hns_pair : ¬ ∀ a ∈ U, ∀ b ∈ U, a ≠ b → Nat.lcm a b = U.lcm id) :
    ∃ y₁ y₂ y₃ y₄ : ℕ, U = {y₁, y₂, y₃, y₄} ∧
      y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₁ ≠ y₄ ∧ y₂ ≠ y₃ ∧ y₂ ≠ y₄ ∧ y₃ ≠ y₄ ∧
      ¬ (y₃ ∣ Nat.lcm y₁ y₂) := by
  push Not at hns_pair
  obtain ⟨y₁, hy1, y₂, hy2, hy12, hne_L⟩ := hns_pair
  have hnd3 : ∃ y₃ ∈ U, ¬ (y₃ ∣ Nat.lcm y₁ y₂) := by
    by_contra hall; push Not at hall
    exact hne_L (Nat.dvd_antisymm
      (Nat.lcm_dvd (Finset.dvd_lcm hy1) (Finset.dvd_lcm hy2)) (Finset.lcm_dvd hall))
  obtain ⟨y₃, hy3, hy3_nd⟩ := hnd3
  have hy13 : y₁ ≠ y₃ := fun heq => hy3_nd (heq ▸ Nat.dvd_lcm_left y₁ y₂)
  have hy23 : y₂ ≠ y₃ := fun heq => hy3_nd (heq ▸ Nat.dvd_lcm_right y₁ y₂)
  have hy4_ex : ∃ y₄ ∈ U, y₄ ≠ y₁ ∧ y₄ ≠ y₂ ∧ y₄ ≠ y₃ := by
    by_contra hnone
    have hsub : U ⊆ ({y₁, y₂, y₃} : Finset ℕ) := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hno; push Not at hno; exact hnone ⟨z, hz, hno.1, hno.2.1, hno.2.2⟩
    have := Finset.card_le_card hsub
    have h3c := card_finset_le_three_5 y₁ y₂ y₃
    omega
  obtain ⟨y₄, hy4, hy41, hy42, hy43⟩ := hy4_ex
  have hU_eq : U = {y₁, y₂, y₃, y₄} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hno; push Not at hno
      have h4sub : {y₁, y₂, y₃, y₄} ⊆ U := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> assumption
      have h5sub : insert z {y₁, y₂, y₃, y₄} ⊆ U := Finset.insert_subset hz h4sub
      have h5c : (insert z ({y₁, y₂, y₃, y₄} : Finset ℕ)).card = 5 := by
        rw [Finset.card_insert_of_notMem (by simp [hno]),
            Finset.card_insert_of_notMem (by simp [hy12, hy13, hy41.symm]),
            Finset.card_insert_of_notMem (by simp [hy23, hy42.symm]),
            Finset.card_insert_of_notMem (by simp [hy43.symm]), Finset.card_singleton]
      have := Finset.card_le_card h5sub
      omega
    · rw [Finset.card_insert_of_notMem (by simp [hy12, hy13, hy41.symm]),
          Finset.card_insert_of_notMem (by simp [hy23, hy42.symm]),
          Finset.card_insert_of_notMem (by simp [hy43.symm]), Finset.card_singleton]
      omega
  exact ⟨y₁, y₂, y₃, y₄, hU_eq, hy12, hy13, hy41.symm, hy23, hy42.symm, hy43.symm, hy3_nd⟩

/-- Four half-interval divisors `{u₁, u₂, u₃, u₄}` of `b₁` plus `v₁ ∣ b₂` (`b₁ ≠ b₂`)
    always admit a `≤ 6`-slot cover of `{u₁, u₂, u₃, u₄, v₁}` (without needing `M < 2 * v₁`). -/
lemma cover_six_of_four_half_one {A : Finset ℕ} {x M b₁ b₂ u₁ u₂ u₃ u₄ v₁ : ℕ}
    (hA_eq : A = {u₁, u₂, u₃, u₄, v₁})
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h14 : u₁ ≠ u₄) (h1v : u₁ ≠ v₁)
    (h23 : u₂ ≠ u₃) (h24 : u₂ ≠ u₄) (h2v : u₂ ≠ v₁)
    (h34 : u₃ ≠ u₄) (h3v : u₃ ≠ v₁) (h4v : u₄ ≠ v₁)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hu1_h : M < 2 * u₁) (hu2_h : M < 2 * u₂) (hu3_h : M < 2 * u₃) (hu4_h : M < 2 * u₄)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb₁_u1 : u₁ ∣ b₁) (hb₁_u2 : u₂ ∣ b₁) (hb₁_u3 : u₃ ∣ b₁) (hb₁_u4 : u₄ ∣ b₁)
    (hb₂_v1 : v₁ ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  let U : Finset ℕ := {u₁, u₂, u₃, u₄}
  have hUc : U.card = 4 := by
    dsimp [U]
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
        Finset.card_insert_of_notMem (by simp [h23, h24]),
        Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  have hAc : A.card = 5 := by
    rw [hA_eq, Finset.card_insert_of_notMem (by simp [h12, h13, h14, h1v]),
        Finset.card_insert_of_notMem (by simp [h23, h24, h2v]),
        Finset.card_insert_of_notMem (by simp [h34, h3v]),
        Finset.card_insert_of_notMem (by simp [h4v]), Finset.card_singleton]
  have hvA : v₁ ∈ A := by rw [hA_eq]; simp
  have hU_sub : U ⊆ A := fun a ha => by
    rw [hA_eq]
    rcases (by simpa only [U, Finset.mem_insert, Finset.mem_singleton] using ha : a = u₁ ∨ a = u₂ ∨ a = u₃ ∨ a = u₄) with rfl | rfl | rfl | rfl <;> simp
  have hU_pos : ∀ a ∈ U, 0 < a := fun a ha => hA_pos a (hU_sub ha)
  have hU_le : ∀ a ∈ U, a ≤ M := fun a ha => hA_le a (hU_sub ha)
  have hU_half : ∀ a ∈ U, M < 2 * a := fun a ha => by
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hU_b1 : ∀ a ∈ U, a ∣ b₁ := fun a ha => by
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hU_nv : ∀ a ∈ U, a ≠ v₁ := fun a ha => by
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hA_ins : A = insert v₁ U := by
    rw [hA_eq]; ext z; simp only [U, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp⟩
  have hAer_v : A.erase v₁ = U := by
    rw [hA_ins, Finset.erase_insert (fun h => hU_nv v₁ h rfl)]
  have h_er4 : ∀ {a₁ a₂ a₃ a₄ : ℕ}, U = {a₁, a₂, a₃, a₄} →
      a₁ ≠ a₄ → a₂ ≠ a₄ → a₃ ≠ a₄ → a₄ ≠ v₁ → A.erase a₄ = {a₁, a₂, a₃, v₁} := by
    intro a₁ a₂ a₃ a₄ hU h14 h24 h34 h4v
    rw [hA_ins, hU]; ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz4, rfl | rfl | rfl | rfl | rfl⟩
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd rfl hz4
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨h14, Or.inr (Or.inl rfl)⟩
      · exact ⟨h24, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨h34, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨h4v.symm, Or.inl rfl⟩
  by_cases hpairU : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → Nat.lcm a b = U.lcm id
  · refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hvA ?_
    rw [hAer_v]
    exact cover_four_of_type1b rfl h12 h13 h14 h23 h24 h34 hU_pos hU_le hU_half hb₁_I hU_b1 hpairU
  · obtain ⟨y₁, y₂, y₃, y₄, hU_y, hy12, hy13, hy14, hy23, hy24, hy34, hy3_nd⟩ :=
      extract_nonspan_four hUc hpairU
    have hyin : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset ℕ), y ∈ U := fun y hy => by rw [← hU_y] at hy; exact hy
    have hy1U := hyin y₁ (by simp); have hy2U := hyin y₂ (by simp)
    have hy3U := hyin y₃ (by simp); have hy4U := hyin y₄ (by simp)
    by_cases hy4_nd : ¬ (y₄ ∣ Nat.lcm (Nat.lcm y₁ y₂) y₃)
    · refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hvA ?_
      rw [hAer_v, hU_y]
      exact cover_four_of_chain4 rfl hy12 hy13 hy14 hy23 hy24 hy34
        (fun a ha => hU_pos a (hU_y ▸ ha)) (fun a ha => hU_le a (hU_y ▸ ha))
        (fun a ha => hU_half a (hU_y ▸ ha)) hb₁_I (fun a ha => hU_b1 a (hU_y ▸ ha)) hy3_nd hy4_nd
    · by_cases hbad : v₁ = Nat.gcd (Nat.lcm y₁ y₂) y₃ ∧ y₃ = 2 * v₁
      · have h2v : 2 * v₁ ≤ M := hbad.2 ▸ hU_le y₃ hy3U
        by_cases h3v_le : 3 * v₁ ≤ M
        · have hy4A : y₄ ∈ A := hU_sub hy4U
          have hAer4 : A.erase y₄ = {y₁, y₂, y₃, v₁} := h_er4 hU_y hy14 hy24 hy34 (hU_nv y₄ hy4U)
          refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hy4A ?_
          rw [hAer4]
          exact cover_four_nonspan_of_h_eq_v1 (hU_nv y₁ hy1U) (hU_nv y₂ hy2U) (hU_nv y₃ hy3U)
            hy12 hy13 hy23 (hU_pos y₁ hy1U) (hU_pos y₂ hy2U) (hU_pos y₃ hy3U) (hA_pos v₁ hvA)
            (hU_le y₁ hy1U) (hU_le y₂ hy2U) (hU_le y₃ hy3U) (hA_le v₁ hvA)
            (hU_half y₁ hy1U) (hU_half y₂ hy2U) hb₁_I hb₂_I hb12
            (hU_b1 y₁ hy1U) (hU_b1 y₂ hy2U) (hU_b1 y₃ hy3U) hb₂_v1 hbad.1 h3v_le
        · have h3v_gt : M < 3 * v₁ := by omega
          by_cases hy4_ns12 : ¬ (y₄ ∣ Nat.lcm y₁ y₂)
          · have hy3A : y₃ ∈ A := hU_sub hy3U
            have hU_y' : U = {y₁, y₂, y₄, y₃} := by
              rw [hU_y]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨by rintro (rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl) <;> simp⟩
            have hAer3 : A.erase y₃ = {y₁, y₂, y₄, v₁} := h_er4 hU_y' hy13 hy23 hy34.symm (hU_nv y₃ hy3U)
            refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hy3A ?_
            rw [hAer3]
            refine cover_four_of_nonspan3 (hU_nv y₁ hy1U) (hU_nv y₂ hy2U) (hU_nv y₄ hy4U)
              hy12 hy14 hy24 (hU_pos y₁ hy1U) (hU_pos y₂ hy2U) (hU_pos y₄ hy4U) (hA_pos v₁ hvA)
              (hU_le y₁ hy1U) (hU_le y₂ hy2U) (hU_le y₄ hy4U) (hA_le v₁ hvA)
              (hU_half y₁ hy1U) (hU_half y₂ hy2U) (hU_half y₄ hy4U)
              hb₁_I hb₂_I hb12 (hU_b1 y₁ hy1U) (hU_b1 y₂ hy2U) (hU_b1 y₄ hy4U) hb₂_v1 hy4_ns12 ?_
            intro ⟨_, hy4_2v⟩
            exact hy34 (by omega)
          · push Not at hy4_ns12
            have hL24_dvd : Nat.lcm (Nat.lcm y₂ y₄) y₁ ∣ Nat.lcm y₁ y₂ :=
              Nat.lcm_dvd (Nat.lcm_dvd (Nat.dvd_lcm_right y₁ y₂) hy4_ns12) (Nat.dvd_lcm_left y₁ y₂)
            have hL14_dvd : Nat.lcm (Nat.lcm y₁ y₄) y₂ ∣ Nat.lcm y₁ y₂ :=
              Nat.lcm_dvd (Nat.lcm_dvd (Nat.dvd_lcm_left y₁ y₂) hy4_ns12) (Nat.dvd_lcm_right y₁ y₂)
            by_cases hy1_ns : ¬ (y₁ ∣ Nat.lcm y₂ y₄)
            · refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hvA ?_
              rw [hAer_v]
              have hU_perm : U = {y₂, y₄, y₁, y₃} := by
                rw [hU_y]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨by rintro (rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl) <;> simp⟩
              rw [hU_perm]
              exact cover_four_of_chain4 rfl hy24 hy12.symm hy23 hy14.symm hy34.symm hy13
                (fun a ha => hU_pos a (hU_perm ▸ ha)) (fun a ha => hU_le a (hU_perm ▸ ha))
                (fun a ha => hU_half a (hU_perm ▸ ha)) hb₁_I (fun a ha => hU_b1 a (hU_perm ▸ ha))
                hy1_ns (fun hd => hy3_nd (dvd_trans hd hL24_dvd))
            · by_cases hy2_ns : ¬ (y₂ ∣ Nat.lcm y₁ y₄)
              · refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hvA ?_
                rw [hAer_v]
                have hU_perm : U = {y₁, y₄, y₂, y₃} := by
                  rw [hU_y]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
                  exact ⟨by rintro (rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl) <;> simp⟩
                rw [hU_perm]
                exact cover_four_of_chain4 rfl hy14 hy12 hy13 hy24.symm hy34.symm hy23
                  (fun a ha => hU_pos a (hU_perm ▸ ha)) (fun a ha => hU_le a (hU_perm ▸ ha))
                  (fun a ha => hU_half a (hU_perm ▸ ha)) hb₁_I (fun a ha => hU_b1 a (hU_perm ▸ ha))
                  hy2_ns (fun hd => hy3_nd (dvd_trans hd hL14_dvd))
              · push Not at hy1_ns hy2_ns
                -- `{y₁, y₂, y₄}` is pair-spanning with `lcm = Nat.lcm y₁ y₂`!
                let U3 : Finset ℕ := {y₁, y₂, y₄}
                have hL3_eq : U3.lcm id = Nat.lcm y₁ y₂ := by
                  apply Nat.dvd_antisymm
                  · refine Finset.lcm_dvd fun a ha => ?_
                    simp only [U3, Finset.mem_insert, Finset.mem_singleton] at ha
                    rcases ha with ha_eq | ha_eq | ha_eq <;> rw [ha_eq]
                    · exact Nat.dvd_lcm_left y₁ y₂
                    · exact Nat.dvd_lcm_right y₁ y₂
                    · exact hy4_ns12
                  · exact Nat.lcm_dvd (Finset.dvd_lcm (by simp [U3])) (Finset.dvd_lcm (by simp [U3]))
                have hpair3 : ∀ a ∈ U3, ∀ b ∈ U3, a ≠ b → Nat.lcm a b = U3.lcm id := by
                  intro a ha b hb hab
                  rw [hL3_eq]
                  apply Nat.dvd_antisymm
                  · refine Nat.lcm_dvd ?_ ?_
                    · simp only [U3, Finset.mem_insert, Finset.mem_singleton] at ha
                      rcases ha with ha_eq | ha_eq | ha_eq <;> rw [ha_eq]
                      · exact Nat.dvd_lcm_left y₁ y₂
                      · exact Nat.dvd_lcm_right y₁ y₂
                      · exact hy4_ns12
                    · simp only [U3, Finset.mem_insert, Finset.mem_singleton] at hb
                      rcases hb with hb_eq | hb_eq | hb_eq <;> rw [hb_eq]
                      · exact Nat.dvd_lcm_left y₁ y₂
                      · exact Nat.dvd_lcm_right y₁ y₂
                      · exact hy4_ns12
                  · simp only [U3, Finset.mem_insert, Finset.mem_singleton] at ha hb
                    have hmem1 : a = y₁ ∨ a = y₂ ∨ a = y₄ := ha
                    have hmem2 : b = y₁ ∨ b = y₂ ∨ b = y₄ := hb
                    refine Nat.lcm_dvd ?_ ?_
                    · rcases hmem1 with ha1 | ha2 | ha3 <;> rcases hmem2 with hb1 | hb2 | hb3
                      · exact absurd (ha1.trans hb1.symm) hab
                      · rw [ha1]; exact Nat.dvd_lcm_left _ _
                      · rw [ha1]; exact Nat.dvd_lcm_left _ _
                      · rw [hb1]; exact Nat.dvd_lcm_right _ _
                      · exact absurd (ha2.trans hb2.symm) hab
                      · rw [ha2, hb3]; exact dvd_trans hy1_ns (Nat.lcm_dvd (Nat.dvd_lcm_left y₂ y₄) (Nat.dvd_lcm_right y₂ y₄))
                      · rw [hb1]; exact Nat.dvd_lcm_right _ _
                      · rw [ha3, hb2]; exact dvd_trans hy1_ns (Nat.lcm_dvd (Nat.dvd_lcm_right y₄ y₂) (Nat.dvd_lcm_left y₄ y₂))
                      · exact absurd (ha3.trans hb3.symm) hab
                    · rcases hmem1 with ha1 | ha2 | ha3 <;> rcases hmem2 with hb1 | hb2 | hb3
                      · exact absurd (ha1.trans hb1.symm) hab
                      · rw [hb2]; exact Nat.dvd_lcm_right _ _
                      · rw [ha1, hb3]; exact dvd_trans hy2_ns (Nat.lcm_dvd (Nat.dvd_lcm_left y₁ y₄) (Nat.dvd_lcm_right y₁ y₄))
                      · rw [ha2]; exact Nat.dvd_lcm_left _ _
                      · exact absurd (ha2.trans hb2.symm) hab
                      · rw [ha2]; exact Nat.dvd_lcm_left _ _
                      · rw [ha3, hb1]; exact dvd_trans hy2_ns (Nat.lcm_dvd (Nat.dvd_lcm_right y₄ y₁) (Nat.dvd_lcm_left y₄ y₁))
                      · rw [hb2]; exact Nat.dvd_lcm_right _ _
                      · exact absurd (ha3.trans hb3.symm) hab
                have hv1_L3 : v₁ ∣ U3.lcm id := by rw [hL3_eq, hbad.1]; exact Nat.gcd_dvd_left _ _
                have hy3_nd3 : ¬ (y₃ ∣ U3.lcm id) := by rw [hL3_eq]; exact hy3_nd
                have sort3' : ∀ a b d : ℕ, a ≠ b → a ≠ d → b ≠ d →
                    ∃ z₁ z₂ z₃ : ℕ, ({a, b, d} : Finset ℕ) = {z₁, z₂, z₃} ∧ z₁ < z₂ ∧ z₂ < z₃ := by
                  intro a b d hab had hbd
                  have hset3 : ∀ p q r : ℕ, (p = a ∨ p = b ∨ p = d) → (q = a ∨ q = b ∨ q = d) → (r = a ∨ r = b ∨ r = d) →
                      (a = p ∨ a = q ∨ a = r) → (b = p ∨ b = q ∨ b = r) → (d = p ∨ d = q ∨ d = r) →
                      ({a, b, d} : Finset ℕ) = {p, q, r} := by
                    intro p q r hp hq hr ha hb hd
                    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨by rintro (rfl|rfl|rfl) <;> assumption, by rintro (rfl|rfl|rfl) <;> assumption⟩
                  rcases lt_or_gt_of_ne hab with h1 | h1
                  · rcases lt_or_gt_of_ne had with h2 | h2
                    · rcases lt_or_gt_of_ne hbd with h3 | h3
                      · exact ⟨a, b, d, rfl, h1, h3⟩
                      · exact ⟨a, d, b, hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h2, h3⟩
                    · exact ⟨d, a, b, hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h2, h1⟩
                  · rcases lt_or_gt_of_ne hbd with h3 | h3
                    · rcases lt_or_gt_of_ne had with h2 | h2
                      · exact ⟨b, a, d, hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h1, h2⟩
                      · exact ⟨b, d, a, hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h3, h2⟩
                    · exact ⟨d, b, a, hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h3, h1⟩
                obtain ⟨z₁, z₂, z₃, hz_eq, hz12, hz23⟩ := sort3' y₁ y₂ y₄ hy12 hy14 hy24
                have hzin : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ∈ U3 := fun z hz => by dsimp [U3]; rw [hz_eq]; exact hz
                have hA_z : A = {z₁, z₂, z₃, v₁, y₃} := by
                  have hz1_u : z₁ ∈ U3 := hzin z₁ (by simp)
                  have hz2_u : z₂ ∈ U3 := hzin z₂ (by simp)
                  have hz3_u : z₃ ∈ U3 := hzin z₃ (by simp)
                  have hy1_z : y₁ = z₁ ∨ y₁ = z₂ ∨ y₁ = z₃ := by
                    have h : y₁ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
                    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
                  have hy2_z : y₂ = z₁ ∨ y₂ = z₂ ∨ y₂ = z₃ := by
                    have h : y₂ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
                    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
                  have hy4_z : y₄ = z₁ ∨ y₄ = z₂ ∨ y₄ = z₃ := by
                    have h : y₄ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
                    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
                  have hz1_y : z₁ = y₁ ∨ z₁ = y₂ ∨ z₁ = y₄ := by
                    simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hz1_u
                  have hz2_y : z₂ = y₁ ∨ z₂ = y₂ ∨ z₂ = y₄ := by
                    simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hz2_u
                  have hz3_y : z₃ = y₁ ∨ z₃ = y₂ ∨ z₃ = y₄ := by
                    simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hz3_u
                  have hy1_u : y₁ ∈ U := by rw [hU_y]; simp
                  have hy2_u : y₂ ∈ U := by rw [hU_y]; simp
                  have hy3_u : y₃ ∈ U := by rw [hU_y]; simp
                  have hy4_u : y₄ ∈ U := by rw [hU_y]; simp
                  have hu_y' : ∀ w ∈ U, w = y₁ ∨ w = y₂ ∨ w = y₃ ∨ w = y₄ := fun w hw => by
                    rw [hU_y] at hw; simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
                  rw [hA_ins]
                  ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · rintro (rfl | hwU)
                    · simp
                    · rcases hu_y' w hwU with rfl | rfl | rfl | rfl
                      · rcases hy1_z with h | h | h <;> simp [h]
                      · rcases hy2_z with h | h | h <;> simp [h]
                      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
                      · rcases hy4_z with h | h | h <;> simp [h]
                  · rintro (rfl | rfl | rfl | rfl | rfl)
                    · right; rcases hz1_y with h | h | h <;> (rw [h]; first | exact hy1_u | exact hy2_u | exact hy4_u)
                    · right; rcases hz2_y with h | h | h <;> (rw [h]; first | exact hy1_u | exact hy2_u | exact hy4_u)
                    · right; rcases hz3_y with h | h | h <;> (rw [h]; first | exact hy1_u | exact hy2_u | exact hy4_u)
                    · left; rfl
                    · exact Or.inr hy3_u
                have hz_nv : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ≠ v₁ := fun z hz =>
                  hU_nv z (by have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> assumption)
                have hz_ny3 : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ≠ y₃ := fun z hz => by
                  have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this
                  rcases this with rfl | rfl | rfl <;> [exact hy13; exact hy23; exact hy34.symm]
                have hz_b1 : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ∣ b₁ := fun z hz =>
                  hU_b1 z (by have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> assumption)
                have hz_h : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), M < 2 * z := fun z hz =>
                  hU_half z (by have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this; rcases this with rfl | rfl | rfl <;> assumption)
                exact cover_six_of_pairspan3_c_2c hA_z hz12 hz23
                  (hz_nv z₁ (by simp)) (hz_nv z₂ (by simp)) (hz_nv z₃ (by simp))
                  (hz_ny3 z₁ (by simp)) (hz_ny3 z₂ (by simp)) (hz_ny3 z₃ (by simp)) (hU_nv y₃ hy3U).symm
                  hA_pos hA_le hAgcd (hz_h z₁ (by simp)) (hz_h z₂ (by simp)) (hz_h z₃ (by simp))
                  h2v h3v_gt hbad.2 hb₁_I hb₂_I hb12
                  (hz_b1 z₁ (by simp)) (hz_b1 z₂ (by simp)) (hz_b1 z₃ (by simp))
                  hb₂_v1 (Or.inr ⟨hU_b1 y₃ hy3U, by rw [← hz_eq]; exact hy3_nd3⟩)
                  (by rw [← hz_eq]; exact hv1_L3) (by rw [← hz_eq]; exact hpair3)
      · have hy4A : y₄ ∈ A := hU_sub hy4U
        have hAer4 : A.erase y₄ = {y₁, y₂, y₃, v₁} := h_er4 hU_y hy14 hy24 hy34 (hU_nv y₄ hy4U)
        refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 hy4A ?_
        rw [hAer4]
        exact cover_four_of_nonspan3 (hU_nv y₁ hy1U) (hU_nv y₂ hy2U) (hU_nv y₃ hy3U)
          hy12 hy13 hy23 (hU_pos y₁ hy1U) (hU_pos y₂ hy2U) (hU_pos y₃ hy3U) (hA_pos v₁ hvA)
          (hU_le y₁ hy1U) (hU_le y₂ hy2U) (hU_le y₃ hy3U) (hA_le v₁ hvA)
          (hU_half y₁ hy1U) (hU_half y₂ hy2U) (hU_half y₃ hy3U)
          hb₁_I hb₂_I hb12 (hU_b1 y₁ hy1U) (hU_b1 y₂ hy2U) (hU_b1 y₃ hy3U) hb₂_v1 hy3_nd hbad

/-! ## Part 3: Full Maximum Matching Existence & `r = 2` Dispatch -/

theorem exists_max_matching_full {A : Finset ℕ} {x M : ℕ}
    (hA_ne : A.Nonempty) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) :
    ∃ (S : Finset ℕ) (f : ℕ → ℕ),
      S ⊆ A ∧ 1 ≤ S.card ∧ S.card ≤ A.card ∧
      (∀ a ∈ S, f a ∈ consecInterval x M) ∧ (∀ a ∈ S, a ∣ f a) ∧ Set.InjOn f S ∧
      ¬ HasMatching A x M (S.card + 1) := by
  classical
  let R : Finset ℕ := (Finset.range (A.card + 1)).filter (HasMatching A x M)
  have h1_mem : 1 ∈ R := by
    rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨a₀, ha₀⟩ := hA_ne
    have hm := exists_multiple_in_consecInterval x a₀ M (hA_pos a₀ ha₀) (hA_le a₀ ha₀)
    obtain ⟨b₀, hb₀, hd₀⟩ := hm
    refine ⟨by have := Finset.card_pos.mpr ⟨a₀, ha₀⟩; omega, {a₀}, Finset.singleton_subset_iff.mpr ha₀,
      Finset.card_singleton a₀, fun _ => b₀, ?_, ?_, ?_⟩
    · intro a ha; rw [Finset.mem_singleton] at ha; subst ha; exact hb₀
    · intro a ha; rw [Finset.mem_singleton] at ha; subst ha; exact hd₀
    · intro a ha b hb _; simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb; rw [ha, hb]
  let r := R.max' ⟨1, h1_mem⟩
  have hr_mem : r ∈ R := Finset.max'_mem R ⟨1, h1_mem⟩
  have hr_ge1 : 1 ≤ r := Finset.le_max' R 1 h1_mem
  have hr_leA : r ≤ A.card := by
    have hlt := (Finset.mem_range.mp (Finset.mem_filter.mp hr_mem).1)
    omega
  have hr_has : HasMatching A x M r := (Finset.mem_filter.mp hr_mem).2
  obtain ⟨S, hSA, hS_card, f, hf_mem, hf_dvd, hf_inj⟩ := hr_has
  refine ⟨S, f, hSA, by omega, by omega, hf_mem, hf_dvd, hf_inj, ?_⟩
  intro hnext
  have hmem_next : (S.card + 1) ∈ R := by
    rw [Finset.mem_filter, Finset.mem_range]
    have hnext' := hnext
    obtain ⟨S', hS'A, hS'c, f', _, _, _⟩ := hnext'
    have h1 := Finset.card_le_card hS'A
    rw [hS_card] at hS'c
    exact ⟨by omega, hnext⟩
  have hle := Finset.le_max' R (S.card + 1) hmem_next
  change S.card + 1 ≤ r at hle
  omega

private lemma max_matching_two_unique_multiples {A S : Finset ℕ} {x M : ℕ} {f : ℕ → ℕ}
    (hSA : S ⊆ A) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S)
    (hnot_succ : ¬ HasMatching A x M (S.card + 1)) :
    (∀ u ∈ A \ S, ∀ b ∈ consecInterval x M, u ∣ b → b ∈ S.image f) ∧
    (∀ s ∈ S, (∃ u ∈ A \ S, u ∣ f s) → ∀ b ∈ consecInterval x M, s ∣ b → b ∈ S.image f) := by
  constructor
  · intro u hu b hb hu_b
    by_contra hnotImg
    let f' : ℕ → ℕ := fun a => if a = u then b else f a
    apply hnot_succ
    have hu_A : u ∈ A := (Finset.mem_sdiff.mp hu).1
    have hu_nS : u ∉ S := (Finset.mem_sdiff.mp hu).2
    refine ⟨insert u S, Finset.insert_subset_iff.mpr ⟨hu_A, hSA⟩,
      Finset.card_insert_of_notMem hu_nS, f', ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hb]
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        simp [f', hne, hf_mem a haS]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hu_b]
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        simp [f', hne, hf_dvd a haS]
    · intro a₁ ha₁ a₂ ha₂ heq
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha₁) with ha1u | ha1S <;>
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha₂) with ha2u | ha2S
      · rw [ha1u, ha2u]
      · have hne : a₂ ≠ u := fun h => hu_nS (h ▸ ha2S)
        dsimp only [f'] at heq
        rw [if_pos ha1u, if_neg hne] at heq
        exact absurd (heq ▸ Finset.mem_image_of_mem f ha2S) hnotImg
      · have hne : a₁ ≠ u := fun h => hu_nS (h ▸ ha1S)
        dsimp only [f'] at heq
        rw [if_neg hne, if_pos ha2u] at heq
        exact absurd (heq.symm ▸ Finset.mem_image_of_mem f ha1S) hnotImg
      · have hne1 : a₁ ≠ u := fun h => hu_nS (h ▸ ha1S)
        have hne2 : a₂ ≠ u := fun h => hu_nS (h ▸ ha2S)
        dsimp only [f'] at heq
        rw [if_neg hne1, if_neg hne2] at heq
        exact hf_inj ha1S ha2S heq
  · intro s hs ⟨u, hu, hu_fs⟩ b hb hs_b
    by_contra hnotImg
    let f' : ℕ → ℕ := fun a => if a = u then f s else if a = s then b else f a
    apply hnot_succ
    have hu_A : u ∈ A := (Finset.mem_sdiff.mp hu).1
    have hu_nS : u ∉ S := (Finset.mem_sdiff.mp hu).2
    have hus : u ≠ s := fun h => hu_nS (h ▸ hs)
    refine ⟨insert u S, Finset.insert_subset_iff.mpr ⟨hu_A, hSA⟩,
      Finset.card_insert_of_notMem hu_nS, f', ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hf_mem s hs]
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        by_cases has : a = s
        · subst has; simp [f', hne, hb]
        · simp [f', hne, has, hf_mem a haS]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hu_fs]
      · have hne : a ≠ u := fun h => hu_nS (h ▸ haS)
        by_cases has : a = s
        · subst has; simp [f', hne, hs_b]
        · simp [f', hne, has, hf_dvd a haS]
    · intro a₁ ha₁ a₂ ha₂ heq
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha₁) with ha1u | ha1S <;>
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha₂) with ha2u | ha2S
      · rw [ha1u, ha2u]
      · have hne2 : a₂ ≠ u := fun h => hu_nS (h ▸ ha2S)
        dsimp only [f'] at heq
        rw [if_pos ha1u, if_neg hne2] at heq
        by_cases has2 : a₂ = s
        · rw [if_pos has2] at heq
          exact absurd (heq.symm ▸ Finset.mem_image_of_mem f hs) hnotImg
        · rw [if_neg has2] at heq
          exact absurd (hf_inj hs ha2S heq).symm has2
      · have hne1 : a₁ ≠ u := fun h => hu_nS (h ▸ ha1S)
        dsimp only [f'] at heq
        rw [if_neg hne1, if_pos ha2u] at heq
        by_cases has1 : a₁ = s
        · rw [if_pos has1] at heq
          exact absurd (heq ▸ Finset.mem_image_of_mem f hs) hnotImg
        · rw [if_neg has1] at heq
          exact absurd (hf_inj ha1S hs heq) has1
      · have hne1 : a₁ ≠ u := fun h => hu_nS (h ▸ ha1S)
        have hne2 : a₂ ≠ u := fun h => hu_nS (h ▸ ha2S)
        dsimp only [f'] at heq
        rw [if_neg hne1, if_neg hne2] at heq
        by_cases has1 : a₁ = s <;> by_cases has2 : a₂ = s
        · rw [has1, has2]
        · rw [if_pos has1, if_neg has2] at heq
          exact absurd (heq ▸ Finset.mem_image_of_mem f ha2S) hnotImg
        · rw [if_neg has1, if_pos has2] at heq
          exact absurd (heq.symm ▸ Finset.mem_image_of_mem f ha1S) hnotImg
        · rw [if_neg has1, if_neg has2] at heq
          exact hf_inj ha1S ha2S heq

private lemma cover_six_of_r2_one_sided {A : Finset ℕ} {x M b₁ b₂ s₁ s₂ u₁ u₂ u₃ : ℕ}
    (hA_eq : A = {u₁, u₂, u₃, s₁, s₂})
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h1s1 : u₁ ≠ s₁) (h1s2 : u₁ ≠ s₂)
    (h23 : u₂ ≠ u₃) (h2s1 : u₂ ≠ s₁) (h2s2 : u₂ ≠ s₂)
    (h3s1 : u₃ ≠ s₁) (h3s2 : u₃ ≠ s₂) (hs12 : s₁ ≠ s₂)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hs1_b1 : s₁ ∣ b₁) (hs2_b2 : s₂ ∣ b₂)
    (hu_only_b1 : ∀ u ∈ ({u₁, u₂, u₃} : Finset ℕ), ∀ b ∈ consecInterval x M, u ∣ b → b = b₁)
    (hs1_all : ∀ b ∈ consecInterval x M, s₁ ∣ b → b = b₁ ∨ b = b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hAc : A.card = 5 := by
    rw [hA_eq, Finset.card_insert_of_notMem (by simp [h12, h13, h1s1, h1s2]),
        Finset.card_insert_of_notMem (by simp [h23, h2s1, h2s2]),
        Finset.card_insert_of_notMem (by simp [h3s1, h3s2]),
        Finset.card_insert_of_notMem (by simp [hs12]), Finset.card_singleton]
  have hu1p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu2p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hu3p : 0 < u₃ := hA_pos u₃ (by rw [hA_eq]; simp)
  have hs1p : 0 < s₁ := hA_pos s₁ (by rw [hA_eq]; simp)
  have hs2p : 0 < s₂ := hA_pos s₂ (by rw [hA_eq]; simp)
  have hu1M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have hu2M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have hu3M : u₃ ≤ M := hA_le u₃ (by rw [hA_eq]; simp)
  have hs1M : s₁ ≤ M := hA_le s₁ (by rw [hA_eq]; simp)
  have hs2M : s₂ ≤ M := hA_le s₂ (by rw [hA_eq]; simp)
  obtain ⟨bu1, hbu1_I, hu1_bu1⟩ := exists_multiple_in_consecInterval x u₁ M hu1p hu1M
  obtain ⟨bu2, hbu2_I, hu2_bu2⟩ := exists_multiple_in_consecInterval x u₂ M hu2p hu2M
  obtain ⟨bu3, hbu3_I, hu3_bu3⟩ := exists_multiple_in_consecInterval x u₃ M hu3p hu3M
  have hu1_b1 : u₁ ∣ b₁ := (hu_only_b1 u₁ (by simp) bu1 hbu1_I hu1_bu1) ▸ hu1_bu1
  have hu2_b1 : u₂ ∣ b₁ := (hu_only_b1 u₂ (by simp) bu2 hbu2_I hu2_bu2) ▸ hu2_bu2
  have hu3_b1 : u₃ ∣ b₁ := (hu_only_b1 u₃ (by simp) bu3 hbu3_I hu3_bu3) ▸ hu3_bu3
  have hu1_h : M < 2 * u₁ := lt_two_mul_of_unique_multiple_in_consecInterval hu1p hb₁_I hu1_b1
    (fun b hb hdb => hu_only_b1 u₁ (by simp) b hb hdb)
  have hu2_h : M < 2 * u₂ := lt_two_mul_of_unique_multiple_in_consecInterval hu2p hb₁_I hu2_b1
    (fun b hb hdb => hu_only_b1 u₂ (by simp) b hb hdb)
  have hu3_h : M < 2 * u₃ := lt_two_mul_of_unique_multiple_in_consecInterval hu3p hb₁_I hu3_b1
    (fun b hb hdb => hu_only_b1 u₃ (by simp) b hb hdb)
  by_cases hs1_b2 : s₁ ∣ b₂
  · by_cases hs2_2 : M < 2 * s₂
    · have hA_eq' : A = {u₁, u₂, u₃, s₂, s₁} := by
        rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp⟩
      exact cover_six_of_r2_C1_31 hA_eq' h12 h13 h1s2 h1s1 h23 h2s2 h2s1 h3s2 h3s1 hs12.symm
        hA_pos hA_le hAgcd hM7 hu1_h hu2_h hu3_h hs2_2 hb₁_I hb₂_I hb12
        hu1_b1 hu2_b1 hu3_b1 hs1_b1 hs2_b2 hs1_b2
    · have h2s2_le : 2 * s₂ ≤ M := by omega
      by_cases h3g : 3 * Nat.gcd s₁ s₂ ≤ M
      · have h3g_u : 3 * Nat.gcd u₁ u₂ ≤ M :=
          three_mul_le_of_two_gt_half_5 (Nat.gcd_pos_of_pos_left u₂ hu1p) h12 hu1M hu2M hu1_h hu2_h
            (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
        have hAer3 : A.erase u₃ = {u₁, u₂, s₁, s₂} := by
          ext z; simp only [hA_eq, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hz3, rfl | rfl | rfl | rfl | rfl⟩
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact absurd rfl hz3
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr rfl))
          · rintro (rfl | rfl | rfl | rfl)
            · exact ⟨h13, Or.inl rfl⟩
            · exact ⟨h23, Or.inr (Or.inl rfl)⟩
            · exact ⟨h3s1.symm, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
            · exact ⟨h3s2.symm, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
        refine cover_six_of_cover_four_erase hAc hA_pos hA_le hAgcd hM7 (u := u₃) (by rw [hA_eq]; simp) ?_
        rw [hAer3]
        exact cover_four_of_two_pairs h12 h1s1 h1s2 h2s1 h2s2 hs12 hu1p hu2p hs1p hs2p
          hu1M hu2M hs1M hs2M hb₁_I hb₂_I hb12 hu1_b1 hu2_b1 hs1_b2 hs2_b2 h3g_u h3g
      · have hbad : M < 3 * Nat.gcd s₁ s₂ := by omega
        rcases bad_pair_eq_double hs1p hs2p hs12 hs1M hs2M hbad with ⟨_, _, _⟩ | ⟨_, _, hs1_h⟩
        · omega
        · exact cover_six_of_four_half_one hA_eq h12 h13 h1s1 h1s2 h23 h2s1 h2s2 h3s1 h3s2 hs12
            hA_pos hA_le hAgcd hM7 hu1_h hu2_h hu3_h hs1_h hb₁_I hb₂_I hb12
            hu1_b1 hu2_b1 hu3_b1 hs1_b1 hs2_b2
  · have hs1_uniq : ∀ b ∈ consecInterval x M, s₁ ∣ b → b = b₁ := fun b hb hdb =>
      (hs1_all b hb hdb).elim id (fun h => absurd (h ▸ hdb) hs1_b2)
    have hs1_h : M < 2 * s₁ := lt_two_mul_of_unique_multiple_in_consecInterval hs1p hb₁_I hs1_b1 hs1_uniq
    exact cover_six_of_four_half_one hA_eq h12 h13 h1s1 h1s2 h23 h2s1 h2s2 h3s1 h3s2 hs12
      hA_pos hA_le hAgcd hM7 hu1_h hu2_h hu3_h hs1_h hb₁_I hb₂_I hb12
      hu1_b1 hu2_b1 hu3_b1 hs1_b1 hs2_b2

private lemma extract_three_of_card_ge3 {T : Finset ℕ} (hT : 3 ≤ T.card) :
    ∃ x ∈ T, ∃ y ∈ T, ∃ z ∈ T, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hne1 : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne1
  have hne2 : (T.erase x).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx]; omega)
  obtain ⟨y, hy⟩ := hne2
  have hne3 : ((T.erase x).erase y).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega)
  obtain ⟨z, hz⟩ := hne3
  have hym := Finset.mem_erase.mp hy
  have hzm := Finset.mem_erase.mp hz
  have hzm' := Finset.mem_erase.mp hzm.2
  exact ⟨x, hx, y, hym.2, z, hzm'.2, hym.1.symm, hzm'.1.symm, hzm.1.symm⟩

private lemma cover_six_of_r2_two_sided_Cge3 {A U₁ U₂ C : Finset ℕ} {x M b₁ b₂ : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hU₁_sub : U₁ ⊆ A) (hU₂_sub : U₂ ⊆ A) (hC_sub : C ⊆ A)
    (hdisj1C : Disjoint U₁ C) (hdisj2C : Disjoint U₂ C) (hdisj12 : Disjoint U₁ U₂)
    (hU_part : A = U₁ ∪ U₂ ∪ C) (hC_ge3 : 3 ≤ C.card) (hU2_le : U₂.card ≤ U₁.card)
    (hU1_b1 : ∀ a ∈ U₁, a ∣ b₁) (hU2_b2 : ∀ a ∈ U₂, a ∣ b₂)
    (hC_both : ∀ a ∈ C, a ∣ b₁ ∧ a ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hc_sum : A.card = U₁.card + U₂.card + C.card := by
    rw [hU_part, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj1C, hdisj2C⟩),
        Finset.card_union_of_disjoint hdisj12]
  by_cases hU2_0 : U₂.card = 0
  · obtain ⟨c₁, hc1, c₂, hc2, c₃, hc3, hc12, hc13, hc23⟩ := extract_three_of_card_ge3 hC_ge3
    have hex_c : ∃ ca ∈ C, ∃ cb ∈ C, ca ≠ cb ∧ 3 * Nat.gcd ca cb ≤ M := by
      rcases not_two_bad_pairs hc12 hc13 hc23
        (hA_pos c₁ (hC_sub hc1)) (hA_pos c₂ (hC_sub hc2)) (hA_pos c₃ (hC_sub hc3))
        (hA_le c₁ (hC_sub hc1)) (hA_le c₂ (hC_sub hc2)) (hA_le c₃ (hC_sub hc3)) with h12 | h13
      · exact ⟨c₁, hc1, c₂, hc2, hc12, h12⟩
      · exact ⟨c₁, hc1, c₃, hc3, hc13, h13⟩
    obtain ⟨ca, hcaC, cb, hcbC, hcab, h3gcd_c⟩ := hex_c
    let R_rem := (A.erase ca).erase cb
    have hR_card : 3 ≤ R_rem.card := by
      have hcb_er : cb ∈ A.erase ca := Finset.mem_erase.mpr ⟨hcab.symm, hC_sub hcbC⟩
      rw [Finset.card_erase_of_mem hcb_er, Finset.card_erase_of_mem (hC_sub hcaC), hA_card]
    obtain ⟨q₁, hq1, q₂, hq2, q₃, hq3, hq12, hq13, hq23⟩ := extract_three_of_card_ge3 hR_card
    have hqA : ∀ q ∈ R_rem, q ∈ A ∧ q ≠ ca ∧ q ≠ cb := fun q hq => by
      have hm1 := Finset.mem_erase.mp hq
      have hm2 := Finset.mem_erase.mp hm1.2
      exact ⟨hm2.2, hm2.1, hm1.1⟩
    have hex_q : ∃ qa ∈ R_rem, ∃ qb ∈ R_rem, qa ≠ qb ∧ 3 * Nat.gcd qa qb ≤ M := by
      rcases not_two_bad_pairs hq12 hq13 hq23
        (hA_pos q₁ (hqA q₁ hq1).1) (hA_pos q₂ (hqA q₂ hq2).1) (hA_pos q₃ (hqA q₃ hq3).1)
        (hA_le q₁ (hqA q₁ hq1).1) (hA_le q₂ (hqA q₂ hq2).1) (hA_le q₃ (hqA q₃ hq3).1) with h12 | h13
      · exact ⟨q₁, hq1, q₂, hq2, hq12, h12⟩
      · exact ⟨q₁, hq1, q₃, hq3, hq13, h13⟩
    obtain ⟨qa, hqaR, qb, hqbR, hqab, h3gcd_q⟩ := hex_q
    have hqa_props := hqA qa hqaR
    have hqb_props := hqA qb hqbR
    have hU2_emp : U₂ = ∅ := Finset.card_eq_zero.mp hU2_0
    have hall_b1 : ∀ a ∈ A, a ∣ b₁ := fun a ha => by
      rw [hU_part, hU2_emp, Finset.union_empty] at ha
      rcases Finset.mem_union.mp ha with haU | haC
      · exact hU1_b1 a haU
      · exact (hC_both a haC).1
    obtain ⟨z, hzA, hzne⟩ : ∃ z ∈ A, z ≠ qa ∧ z ≠ qb ∧ z ≠ ca ∧ z ≠ cb := by
      by_contra hnone; push Not at hnone
      have hsub : A ⊆ ({qa, qb, ca, cb} : Finset ℕ) := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno; exact hno.2.2.2 (hnone w hw hno.1 hno.2.1 hno.2.2.1)
      have := Finset.card_le_card hsub
      have h4 := card_finset_le_four_5 qa qb ca cb
      omega
    have hAer : A.erase z = {qa, qb, ca, cb} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno
        have h4sub : {qa, qb, ca, cb} ⊆ A.erase z := fun u hu => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl | rfl <;> exact Finset.mem_erase.mpr ⟨by tauto, by first | exact hqa_props.1 | exact hqb_props.1 | exact hC_sub hcaC | exact hC_sub hcbC⟩
        have h5sub : insert w {qa, qb, ca, cb} ⊆ A.erase z := Finset.insert_subset hw h4sub
        have h5c : (insert w ({qa, qb, ca, cb} : Finset ℕ)).card = 5 := by
          rw [Finset.card_insert_of_notMem (by simp [hno]),
              Finset.card_insert_of_notMem (by simp [hqab, hqa_props.2.1, hqa_props.2.2]),
              Finset.card_insert_of_notMem (by simp [hqb_props.2.1, hqb_props.2.2]),
              Finset.card_insert_of_notMem (by simp [hcab]), Finset.card_singleton]
        have hec : (A.erase z).card = 4 := by rw [Finset.card_erase_of_mem hzA, hA_card]
        have := Finset.card_le_card h5sub
        omega
      · rw [Finset.card_erase_of_mem hzA, hA_card,
            Finset.card_insert_of_notMem (by simp [hqab, hqa_props.2.1, hqa_props.2.2]),
            Finset.card_insert_of_notMem (by simp [hqb_props.2.1, hqb_props.2.2]),
            Finset.card_insert_of_notMem (by simp [hcab]), Finset.card_singleton]
    refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 hzA ?_
    rw [hAer]
    exact cover_four_of_two_pairs hqab hqa_props.2.1 hqa_props.2.2 hqb_props.2.1 hqb_props.2.2 hcab
      (hA_pos qa hqa_props.1) (hA_pos qb hqb_props.1) (hA_pos ca (hC_sub hcaC)) (hA_pos cb (hC_sub hcbC))
      (hA_le qa hqa_props.1) (hA_le qb hqb_props.1) (hA_le ca (hC_sub hcaC)) (hA_le cb (hC_sub hcbC))
      hb₁_I hb₂_I hb12 (hall_b1 qa hqa_props.1) (hall_b1 qb hqb_props.1)
      (hC_both ca hcaC).2 (hC_both cb hcbC).2 h3gcd_q h3gcd_c
  · -- `1 ≤ U₂.card ≤ U₁.card` and `3 ≤ C.card` and `U₁ + U₂ + C = 5` ⇒ `(1, 1, 3)`!
    have hU1_1 : U₁.card = 1 := by omega
    have hU2_1 : U₂.card = 1 := by omega
    have hC_3 : C.card = 3 := by omega
    obtain ⟨u₁, hu1_eq⟩ := Finset.card_eq_one.mp hU1_1
    obtain ⟨v₁, hv1_eq⟩ := Finset.card_eq_one.mp hU2_1
    obtain ⟨c₁, hc1, c₂, hc2, c₃, hc3, hc12, hc13, hc23⟩ := extract_three_of_card_ge3 hC_ge3
    have hu1U : u₁ ∈ U₁ := by rw [hu1_eq]; exact Finset.mem_singleton_self u₁
    have hv1U : v₁ ∈ U₂ := by rw [hv1_eq]; exact Finset.mem_singleton_self v₁
    have hu1A : u₁ ∈ A := hU₁_sub hu1U
    have hv1A : v₁ ∈ A := hU₂_sub hv1U
    have hC_eq3 : C = {c₁, c₂, c₃} := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno
        have h4sub : insert z {c₁, c₂, c₃} ⊆ C := Finset.insert_subset hz (fun w hw => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption)
        have h4c : (insert z ({c₁, c₂, c₃} : Finset ℕ)).card = 4 := by
          rw [Finset.card_insert_of_notMem (by simp [hno]),
              Finset.card_insert_of_notMem (by simp [hc12, hc13]),
              Finset.card_insert_of_notMem (by simp [hc23]), Finset.card_singleton]
        have := Finset.card_le_card h4sub; omega
      · rw [Finset.card_insert_of_notMem (by simp [hc12, hc13]),
            Finset.card_insert_of_notMem (by simp [hc23]), Finset.card_singleton]; omega
    have huv : u₁ ≠ v₁ := fun h => Finset.disjoint_left.mp hdisj12 hu1U (h ▸ hv1U)
    have huC : ∀ c ∈ C, u₁ ≠ c := fun c hc h => Finset.disjoint_left.mp hdisj1C hu1U (h ▸ hc)
    have hvC : ∀ c ∈ C, v₁ ≠ c := fun c hc h => Finset.disjoint_left.mp hdisj2C hv1U (h ▸ hc)
    -- Pick `ca ∈ {c₁, c₂}` good with `u₁` (`ca_other ∈ {c₁, c₂}`), then among `{ca_other, c₃}` pick `cb` good with `v₁`!
    have hex_ca : (∃ ca ∈ C, ∃ c' ∈ C, ∃ c'' ∈ C, C = {ca, c', c''} ∧ ca ≠ c' ∧ ca ≠ c'' ∧ c' ≠ c'' ∧
        3 * Nat.gcd u₁ ca ≤ M) := by
      rcases not_two_bad_pairs (huC c₁ hc1) (huC c₂ hc2) hc12
        (hA_pos u₁ hu1A) (hA_pos c₁ (hC_sub hc1)) (hA_pos c₂ (hC_sub hc2))
        (hA_le u₁ hu1A) (hA_le c₁ (hC_sub hc1)) (hA_le c₂ (hC_sub hc2)) with h1 | h2
      · exact ⟨c₁, hc1, c₂, hc2, c₃, hc3, hC_eq3, hc12, hc13, hc23, h1⟩
      · refine ⟨c₂, hc2, c₁, hc1, c₃, hc3, ?_, hc12.symm, hc23, hc13, h2⟩
        rw [hC_eq3, Finset.insert_comm c₁ c₂ {c₃}]
    obtain ⟨ca, hcaC, c', hc'C, c'', hc''C, hC_ord, hcac', hcac'', hc'c'', h3g_u⟩ := hex_ca
    have hex_cb : ∃ cb ∈ C, ∃ z ∈ C, cb ≠ z ∧ ca ≠ cb ∧ ca ≠ z ∧ 3 * Nat.gcd v₁ cb ≤ M := by
      rcases not_two_bad_pairs (hvC c' hc'C) (hvC c'' hc''C) hc'c''
        (hA_pos v₁ hv1A) (hA_pos c' (hC_sub hc'C)) (hA_pos c'' (hC_sub hc''C))
        (hA_le v₁ hv1A) (hA_le c' (hC_sub hc'C)) (hA_le c'' (hC_sub hc''C)) with h1 | h2
      · exact ⟨c', hc'C, c'', hc''C, hc'c'', hcac', hcac'', h1⟩
      · exact ⟨c'', hc''C, c', hc'C, hc'c''.symm, hcac'', hcac', h2⟩
    obtain ⟨cb, hcbC, z, hzC, hcbz, hcacb, hcaz, h3g_v⟩ := hex_cb
    have hzA : z ∈ A := hC_sub hzC
    have hAer : A.erase z = {u₁, ca, v₁, cb} := by
      have hcb_m : cb = ca ∨ cb = c' ∨ cb = c'' := by
        have h : cb ∈ ({ca, c', c''} : Finset ℕ) := hC_ord ▸ hcbC
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h
      have hz_m : z = ca ∨ z = c' ∨ z = c'' := by
        have h : z ∈ ({ca, c', c''} : Finset ℕ) := hC_ord ▸ hzC
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h
      have hzC_ord : C = {ca, cb, z} := by
        rw [hC_ord]; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hcb_m with hcb1 | hcb2 | hcb3
        · exact absurd hcb1 hcacb.symm
        · rcases hz_m with hz1 | hz2 | hz3
          · exact absurd hz1 hcaz.symm
          · exact absurd (hcb2.trans hz2.symm) hcbz
          · subst hcb2; subst hz3; exact ⟨fun h => h, fun h => h⟩
        · rcases hz_m with hz1 | hz2 | hz3
          · exact absurd hz1 hcaz.symm
          · subst hcb3; subst hz2
            exact ⟨by rintro (rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl) <;> simp⟩
          · exact absurd (hcb3.trans hz3.symm) hcbz
      rw [hU_part, hu1_eq, hv1_eq, hzC_ord]
      ext w; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hwz, (rfl | rfl) | (rfl | rfl | rfl)⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact absurd rfl hwz
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨huC z hzC, Or.inl (Or.inl rfl)⟩
        · exact ⟨hcaz, Or.inr (Or.inl rfl)⟩
        · exact ⟨hvC z hzC, Or.inl (Or.inr rfl)⟩
        · exact ⟨hcbz, Or.inr (Or.inr (Or.inl rfl))⟩
    refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 hzA ?_
    rw [hAer]
    exact cover_four_of_two_pairs (huC ca hcaC) huv (huC cb hcbC) (hvC ca hcaC).symm hcacb (hvC cb hcbC)
      (hA_pos u₁ hu1A) (hA_pos ca (hC_sub hcaC)) (hA_pos v₁ hv1A) (hA_pos cb (hC_sub hcbC))
      (hA_le u₁ hu1A) (hA_le ca (hC_sub hcaC)) (hA_le v₁ hv1A) (hA_le cb (hC_sub hcbC))
      hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1U) (hC_both ca hcaC).1 (hU2_b2 v₁ hv1U) (hC_both cb hcbC).2
      h3g_u h3g_v

private lemma cover_six_of_r2_two_sided_C01 {A U₁ U₂ C : Finset ℕ} {x M b₁ b₂ : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hU₁_sub : U₁ ⊆ A) (hU₂_sub : U₂ ⊆ A) (hC_sub : C ⊆ A)
    (hdisj1C : Disjoint U₁ C) (hdisj2C : Disjoint U₂ C) (hdisj12 : Disjoint U₁ U₂)
    (hU_part : A = U₁ ∪ U₂ ∪ C) (hC_le1 : C.card ≤ 1) (hU2_le : U₂.card ≤ U₁.card)
    (hU1_half : ∀ a ∈ U₁, M < 2 * a) (hU2_half : ∀ a ∈ U₂, M < 2 * a)
    (hU1_b1 : ∀ a ∈ U₁, a ∣ b₁) (hU2_b2 : ∀ a ∈ U₂, a ∣ b₂)
    (hC_both : ∀ a ∈ C, a ∣ b₁ ∧ a ∣ b₂) (hb2_ex : (U₂ ∪ C).Nonempty) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hc_sum : A.card = U₁.card + U₂.card + C.card := by
    rw [hU_part, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj1C, hdisj2C⟩),
        Finset.card_union_of_disjoint hdisj12]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hC_le1 with hC0 | hC1
  · have hC_emp : C = ∅ := Finset.card_eq_zero.mp hC0
    have hU2_pos : 1 ≤ U₂.card := by
      have : U₂.Nonempty := by simpa [hC_emp] using hb2_ex
      exact Finset.card_pos.mpr this
    rcases (by omega : (U₁.card = 4 ∧ U₂.card = 1) ∨ (U₁.card = 3 ∧ U₂.card = 2)) with
        ⟨hU1_4, hU2_1⟩ | ⟨hU1_3, hU2_2⟩
    · obtain ⟨v₁, hv1_eq⟩ := Finset.card_eq_one.mp hU2_1
      have hv1U : v₁ ∈ U₂ := by rw [hv1_eq]; exact Finset.mem_singleton_self v₁
      have hU1_ge3 : 3 ≤ U₁.card := by omega
      obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 hU1_ge3
      have hu4_ex : ∃ u₄ ∈ U₁, u₄ ≠ u₁ ∧ u₄ ≠ u₂ ∧ u₄ ≠ u₃ := by
        by_contra hnone; push Not at hnone
        have hsub : U₁ ⊆ ({u₁, u₂, u₃} : Finset ℕ) := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno; exact hno.2.2 (hnone z hz hno.1 hno.2.1)
        have := Finset.card_le_card hsub; have h3 := card_finset_le_three_5 u₁ u₂ u₃; omega
      obtain ⟨u₄, hu4, h41, h42, h43⟩ := hu4_ex
      have hU1_eq : U₁ = {u₁, u₂, u₃, u₄} := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno
          have h4sub : {u₁, u₂, u₃, u₄} ⊆ U₁ := fun w hw => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl | rfl <;> assumption
          have h5sub : insert z {u₁, u₂, u₃, u₄} ⊆ U₁ := Finset.insert_subset hz h4sub
          have h5c : (insert z ({u₁, u₂, u₃, u₄} : Finset ℕ)).card = 5 := by
            rw [Finset.card_insert_of_notMem (by simp [hno]),
                Finset.card_insert_of_notMem (by simp [h12, h13, h41.symm]),
                Finset.card_insert_of_notMem (by simp [h23, h42.symm]),
                Finset.card_insert_of_notMem (by simp [h43.symm]), Finset.card_singleton]
          have := Finset.card_le_card h5sub; omega
        · rw [Finset.card_insert_of_notMem (by simp [h12, h13, h41.symm]),
              Finset.card_insert_of_notMem (by simp [h23, h42.symm]),
              Finset.card_insert_of_notMem (by simp [h43.symm]), Finset.card_singleton]; omega
      have hA_eq : A = {u₁, u₂, u₃, u₄, v₁} := by
        rw [hU_part, hC_emp, Finset.union_empty, hU1_eq, hv1_eq]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      have hv_ne : ∀ u ∈ U₁, u ≠ v₁ := fun u hu h => Finset.disjoint_left.mp hdisj12 hu (h ▸ hv1U)
      exact cover_six_of_four_half_one hA_eq h12 h13 h41.symm (hv_ne u₁ hu1)
        h23 h42.symm (hv_ne u₂ hu2) h43.symm (hv_ne u₃ hu3) (hv_ne u₄ hu4)
        hA_pos hA_le hAgcd hM7 (hU1_half u₁ hu1) (hU1_half u₂ hu2) (hU1_half u₃ hu3) (hU1_half u₄ hu4)
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hU1_b1 u₃ hu3) (hU1_b1 u₄ hu4) (hU2_b2 v₁ hv1U)
    · obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 (by omega : 3 ≤ U₁.card)
      obtain ⟨v₁, v₂, hv12, hv_eq⟩ := Finset.card_eq_two.mp hU2_2
      have hv1U : v₁ ∈ U₂ := by rw [hv_eq]; simp
      have hv2U : v₂ ∈ U₂ := by rw [hv_eq]; simp
      have hU1_eq : U₁ = {u₁, u₂, u₃} := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno
          have h4sub : insert z {u₁, u₂, u₃} ⊆ U₁ := Finset.insert_subset hz (fun w hw => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl <;> assumption)
          have h4c : (insert z ({u₁, u₂, u₃} : Finset ℕ)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hno]),
                Finset.card_insert_of_notMem (by simp [h12, h13]),
                Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
          have := Finset.card_le_card h4sub; omega
        · rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
              Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]; omega
      have hA_eq : A = {u₁, u₂, u₃, v₁, v₂} := by
        rw [hU_part, hC_emp, Finset.union_empty, hU1_eq, hv_eq]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      have huv_d : ∀ u ∈ U₁, ∀ v ∈ U₂, u ≠ v := fun u hu v hv h => Finset.disjoint_left.mp hdisj12 hu (h ▸ hv)
      obtain ⟨u, huA, B, hBI, hBc, hBcov⟩ := cover_four_of_32_half h12 h13 (huv_d u₁ hu1 v₁ hv1U)
        (huv_d u₁ hu1 v₂ hv2U) h23 (huv_d u₂ hu2 v₁ hv1U) (huv_d u₂ hu2 v₂ hv2U)
        (huv_d u₃ hu3 v₁ hv1U) (huv_d u₃ hu3 v₂ hv2U) hv12
        (fun a ha => hA_pos a (by rw [hA_eq]; exact ha))
        (fun a ha => hA_le a (by rw [hA_eq]; exact ha))
        (fun a ha => by
          have ha' : a ∈ U₁ ∪ U₂ := by rw [hU1_eq, hv_eq, Finset.mem_union]; simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢; tauto
          rcases Finset.mem_union.mp ha' with h | h <;> [exact hU1_half a h; exact hU2_half a h])
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hU1_b1 u₃ hu3) (hU2_b2 v₁ hv1U) (hU2_b2 v₂ hv2U)
      rw [← hA_eq] at huA hBcov
      exact cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 huA ⟨B, hBI, hBc, hBcov⟩
  · -- `C.card = 1`: `(4, 0, 1)`, `(3, 1, 1)`, `(2, 2, 1)`!
    obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hC1
    have hcC : c ∈ C := by rw [hc_eq]; exact Finset.mem_singleton_self c
    have hcA : c ∈ A := hC_sub hcC
    have huC : ∀ u ∈ U₁, u ≠ c := fun u hu h => Finset.disjoint_left.mp hdisj1C hu (h ▸ hcC)
    have hvC : ∀ v ∈ U₂, v ≠ c := fun v hv h => Finset.disjoint_left.mp hdisj2C hv (h ▸ hcC)
    rcases (by omega : (U₁.card = 4 ∧ U₂.card = 0) ∨ (U₁.card = 3 ∧ U₂.card = 1) ∨ (U₁.card = 2 ∧ U₂.card = 2)) with
        ⟨hU1_4, hU2_0⟩ | ⟨hU1_3, hU2_1⟩ | ⟨hU1_2, hU2_2⟩
    · have hU2_emp : U₂ = ∅ := Finset.card_eq_zero.mp hU2_0
      obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 (by omega : 3 ≤ U₁.card)
      have hu4_ex : ∃ u₄ ∈ U₁, u₄ ≠ u₁ ∧ u₄ ≠ u₂ ∧ u₄ ≠ u₃ := by
        by_contra hnone; push Not at hnone
        have hsub : U₁ ⊆ ({u₁, u₂, u₃} : Finset ℕ) := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno; exact hno.2.2 (hnone z hz hno.1 hno.2.1)
        have := Finset.card_le_card hsub; have h3 := card_finset_le_three_5 u₁ u₂ u₃; omega
      obtain ⟨u₄, hu4, h41, h42, h43⟩ := hu4_ex
      have hU1_eq : U₁ = {u₁, u₂, u₃, u₄} := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno
          have h4sub : {u₁, u₂, u₃, u₄} ⊆ U₁ := fun w hw => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl | rfl <;> assumption
          have h5sub : insert z {u₁, u₂, u₃, u₄} ⊆ U₁ := Finset.insert_subset hz h4sub
          have h5c : (insert z ({u₁, u₂, u₃, u₄} : Finset ℕ)).card = 5 := by
            rw [Finset.card_insert_of_notMem (by simp [hno]),
                Finset.card_insert_of_notMem (by simp [h12, h13, h41.symm]),
                Finset.card_insert_of_notMem (by simp [h23, h42.symm]),
                Finset.card_insert_of_notMem (by simp [h43.symm]), Finset.card_singleton]
          have := Finset.card_le_card h5sub; omega
        · rw [Finset.card_insert_of_notMem (by simp [h12, h13, h41.symm]),
              Finset.card_insert_of_notMem (by simp [h23, h42.symm]),
              Finset.card_insert_of_notMem (by simp [h43.symm]), Finset.card_singleton]; omega
      have hA_eq : A = {u₁, u₂, u₃, u₄, c} := by
        rw [hU_part, hU2_emp, Finset.union_empty, hU1_eq, hc_eq]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_six_of_four_half_one hA_eq h12 h13 h41.symm (huC u₁ hu1)
        h23 h42.symm (huC u₂ hu2) h43.symm (huC u₃ hu3) (huC u₄ hu4)
        hA_pos hA_le hAgcd hM7 (hU1_half u₁ hu1) (hU1_half u₂ hu2) (hU1_half u₃ hu3) (hU1_half u₄ hu4)
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hU1_b1 u₃ hu3) (hU1_b1 u₄ hu4) (hC_both c hcC).2
    · obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 (by omega : 3 ≤ U₁.card)
      obtain ⟨v₁, hv1_eq⟩ := Finset.card_eq_one.mp hU2_1
      have hv1U : v₁ ∈ U₂ := by rw [hv1_eq]; exact Finset.mem_singleton_self v₁
      have hU1_eq : U₁ = {u₁, u₂, u₃} := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno
          have h4sub : insert z {u₁, u₂, u₃} ⊆ U₁ := Finset.insert_subset hz (fun w hw => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl <;> assumption)
          have h4c : (insert z ({u₁, u₂, u₃} : Finset ℕ)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hno]),
                Finset.card_insert_of_notMem (by simp [h12, h13]),
                Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
          have := Finset.card_le_card h4sub; omega
        · rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
              Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]; omega
      have hA_eq : A = {u₁, u₂, u₃, v₁, c} := by
        rw [hU_part, hU1_eq, hv1_eq, hc_eq]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      have huv_d : ∀ u ∈ U₁, u ≠ v₁ := fun u hu h => Finset.disjoint_left.mp hdisj12 hu (h ▸ hv1U)
      exact cover_six_of_r2_C1_31 hA_eq h12 h13 (huv_d u₁ hu1) (huC u₁ hu1)
        h23 (huv_d u₂ hu2) (huC u₂ hu2) (huv_d u₃ hu3) (huC u₃ hu3) (hvC v₁ hv1U)
        hA_pos hA_le hAgcd hM7 (hU1_half u₁ hu1) (hU1_half u₂ hu2) (hU1_half u₃ hu3) (hU2_half v₁ hv1U)
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hU1_b1 u₃ hu3) (hC_both c hcC).1
        (hU2_b2 v₁ hv1U) (hC_both c hcC).2
    · obtain ⟨u₁, u₂, h12, hu_eq⟩ := Finset.card_eq_two.mp hU1_2
      obtain ⟨v₁, v₂, hv12, hv_eq⟩ := Finset.card_eq_two.mp hU2_2
      have hu1U : u₁ ∈ U₁ := by rw [hu_eq]; simp
      have hu2U : u₂ ∈ U₁ := by rw [hu_eq]; simp
      have hv1U : v₁ ∈ U₂ := by rw [hv_eq]; simp
      have hv2U : v₂ ∈ U₂ := by rw [hv_eq]; simp
      have huv_d : ∀ u ∈ U₁, ∀ v ∈ U₂, u ≠ v := fun u hu v hv h => Finset.disjoint_left.mp hdisj12 hu (h ▸ hv)
      have hAer : A.erase c = {u₁, u₂, v₁, v₂} := by
        rw [hU_part, hu_eq, hv_eq, hc_eq]
        ext z; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzc, h⟩
          rcases h with ((rfl | rfl) | (rfl | rfl)) | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact absurd rfl hzc
        · intro hz
          rcases hz with hz | hz | hz | hz
          · rw [hz]; exact ⟨huC u₁ hu1U, Or.inl (Or.inl (Or.inl rfl))⟩
          · rw [hz]; exact ⟨huC u₂ hu2U, Or.inl (Or.inl (Or.inr rfl))⟩
          · rw [hz]; exact ⟨hvC v₁ hv1U, Or.inl (Or.inr (Or.inl rfl))⟩
          · rw [hz]; exact ⟨hvC v₂ hv2U, Or.inl (Or.inr (Or.inr rfl))⟩
      have h3g1 : 3 * Nat.gcd u₁ u₂ ≤ M := three_mul_le_of_two_gt_half_5
        (Nat.gcd_pos_of_pos_left u₂ (hA_pos u₁ (hU₁_sub hu1U))) h12 (hA_le u₁ (hU₁_sub hu1U))
        (hA_le u₂ (hU₁_sub hu2U)) (hU1_half u₁ hu1U) (hU1_half u₂ hu2U)
        (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
      have h3g2 : 3 * Nat.gcd v₁ v₂ ≤ M := three_mul_le_of_two_gt_half_5
        (Nat.gcd_pos_of_pos_left v₂ (hA_pos v₁ (hU₂_sub hv1U))) hv12 (hA_le v₁ (hU₂_sub hv1U))
        (hA_le v₂ (hU₂_sub hv2U)) (hU2_half v₁ hv1U) (hU2_half v₂ hv2U)
        (Nat.gcd_dvd_left v₁ v₂) (Nat.gcd_dvd_right v₁ v₂)
      refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 hcA ?_
      rw [hAer]
      exact cover_four_of_two_pairs h12 (huv_d u₁ hu1U v₁ hv1U) (huv_d u₁ hu1U v₂ hv2U)
        (huv_d u₂ hu2U v₁ hv1U) (huv_d u₂ hu2U v₂ hv2U) hv12
        (hA_pos u₁ (hU₁_sub hu1U)) (hA_pos u₂ (hU₁_sub hu2U))
        (hA_pos v₁ (hU₂_sub hv1U)) (hA_pos v₂ (hU₂_sub hv2U))
        (hA_le u₁ (hU₁_sub hu1U)) (hA_le u₂ (hU₁_sub hu2U))
        (hA_le v₁ (hU₂_sub hv1U)) (hA_le v₂ (hU₂_sub hv2U))
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1U) (hU1_b1 u₂ hu2U) (hU2_b2 v₁ hv1U) (hU2_b2 v₂ hv2U) h3g1 h3g2

private lemma cover_six_of_r2_two_sided_C2 {A U₁ U₂ C : Finset ℕ} {x M b₁ b₂ : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hU₁_sub : U₁ ⊆ A) (_hU₂_sub : U₂ ⊆ A) (hC_sub : C ⊆ A)
    (hdisj1C : Disjoint U₁ C) (hdisj2C : Disjoint U₂ C) (hdisj12 : Disjoint U₁ U₂)
    (hU_part : A = U₁ ∪ U₂ ∪ C) (hC2 : C.card = 2) (hU2_le : U₂.card ≤ U₁.card)
    (hU1_half : ∀ a ∈ U₁, M < 2 * a) (hU2_half : ∀ a ∈ U₂, M < 2 * a)
    (hU1_b1 : ∀ a ∈ U₁, a ∣ b₁) (hU2_b2 : ∀ a ∈ U₂, a ∣ b₂)
    (hC_both : ∀ a ∈ C, a ∣ b₁ ∧ a ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hc_sum : A.card = U₁.card + U₂.card + C.card := by
    rw [hU_part, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj1C, hdisj2C⟩),
        Finset.card_union_of_disjoint hdisj12]
  obtain ⟨c₁, c₂, hc12, hC_eq⟩ := Finset.card_eq_two.mp hC2
  have hc1C : c₁ ∈ C := by rw [hC_eq]; simp
  have hc2C : c₂ ∈ C := by rw [hC_eq]; simp
  have hU1_ge2 : 2 ≤ U₁.card := by omega
  by_cases h3g : 3 * Nat.gcd c₁ c₂ ≤ M
  · obtain ⟨u₁, hu1, u₂, hu2, h12⟩ : ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₁, u₁ ≠ u₂ := by
      have hne1 : U₁.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u₁, hu1⟩ := hne1
      have hne2 : (U₁.erase u₁).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu1]; omega)
      obtain ⟨u₂, hu2⟩ := hne2
      have hm := Finset.mem_erase.mp hu2
      exact ⟨u₁, hu1, u₂, hm.2, hm.1.symm⟩
    have h3g1 : 3 * Nat.gcd u₁ u₂ ≤ M := three_mul_le_of_two_gt_half_5
      (Nat.gcd_pos_of_pos_left u₂ (hA_pos u₁ (hU₁_sub hu1))) h12 (hA_le u₁ (hU₁_sub hu1))
      (hA_le u₂ (hU₁_sub hu2)) (hU1_half u₁ hu1) (hU1_half u₂ hu2)
      (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
    have huC : ∀ u ∈ U₁, ∀ c ∈ C, u ≠ c := fun u hu c hc h => Finset.disjoint_left.mp hdisj1C hu (h ▸ hc)
    obtain ⟨z, hzA, hz1, hz2, hzc1, hzc2⟩ : ∃ z ∈ A, z ≠ u₁ ∧ z ≠ u₂ ∧ z ≠ c₁ ∧ z ≠ c₂ := by
      by_contra hnone; push Not at hnone
      have hsub : A ⊆ ({u₁, u₂, c₁, c₂} : Finset ℕ) := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno; exact hno.2.2.2 (hnone w hw hno.1 hno.2.1 hno.2.2.1)
      have := Finset.card_le_card hsub; have h4 := card_finset_le_four_5 u₁ u₂ c₁ c₂; omega
    have hAer : A.erase z = {u₁, u₂, c₁, c₂} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hno; push Not at hno
        have h4sub : {u₁, u₂, c₁, c₂} ⊆ A.erase z := fun q hq => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> exact Finset.mem_erase.mpr ⟨by tauto, by first | exact hU₁_sub hu1 | exact hU₁_sub hu2 | exact hC_sub hc1C | exact hC_sub hc2C⟩
        have h5sub : insert w {u₁, u₂, c₁, c₂} ⊆ A.erase z := Finset.insert_subset hw h4sub
        have h5c : (insert w ({u₁, u₂, c₁, c₂} : Finset ℕ)).card = 5 := by
          rw [Finset.card_insert_of_notMem (by simp [hno]),
              Finset.card_insert_of_notMem (by simp [h12, huC u₁ hu1 c₁ hc1C, huC u₁ hu1 c₂ hc2C]),
              Finset.card_insert_of_notMem (by simp [huC u₂ hu2 c₁ hc1C, huC u₂ hu2 c₂ hc2C]),
              Finset.card_insert_of_notMem (by simp [hc12]), Finset.card_singleton]
        have hec : (A.erase z).card = 4 := by rw [Finset.card_erase_of_mem hzA, hA_card]
        have := Finset.card_le_card h5sub; omega
      · rw [Finset.card_erase_of_mem hzA, hA_card,
            Finset.card_insert_of_notMem (by simp [h12, huC u₁ hu1 c₁ hc1C, huC u₁ hu1 c₂ hc2C]),
            Finset.card_insert_of_notMem (by simp [huC u₂ hu2 c₁ hc1C, huC u₂ hu2 c₂ hc2C]),
            Finset.card_insert_of_notMem (by simp [hc12]), Finset.card_singleton]
    refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 hzA ?_
    rw [hAer]
    exact cover_four_of_two_pairs h12 (huC u₁ hu1 c₁ hc1C) (huC u₁ hu1 c₂ hc2C)
      (huC u₂ hu2 c₁ hc1C) (huC u₂ hu2 c₂ hc2C) hc12
      (hA_pos u₁ (hU₁_sub hu1)) (hA_pos u₂ (hU₁_sub hu2))
      (hA_pos c₁ (hC_sub hc1C)) (hA_pos c₂ (hC_sub hc2C))
      (hA_le u₁ (hU₁_sub hu1)) (hA_le u₂ (hU₁_sub hu2))
      (hA_le c₁ (hC_sub hc1C)) (hA_le c₂ (hC_sub hc2C))
      hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hC_both c₁ hc1C).2 (hC_both c₂ hc2C).2 h3g1 h3g
  · -- `M < 3 * gcd c₁ c₂`: WLOG `c_hi = 2 * c_lo`, `M < 2 * c_hi`, `c_hi ∣ b₁`, `c_lo ∣ b₁ ∧ c_lo ∣ b₂`!
    have hbad : M < 3 * Nat.gcd c₁ c₂ := by omega
    have hex_half : ∃ ch cl : ℕ, C = {ch, cl} ∧ ch ≠ cl ∧ ch ∈ C ∧ cl ∈ C ∧ M < 2 * ch := by
      rcases bad_pair_eq_double (hA_pos c₁ (hC_sub hc1C)) (hA_pos c₂ (hC_sub hc2C)) hc12
          (hA_le c₁ (hC_sub hc1C)) (hA_le c₂ (hC_sub hc2C)) hbad with ⟨_, _, h2_hi⟩ | ⟨_, _, h1_hi⟩
      · exact ⟨c₂, c₁, by rw [hC_eq, Finset.pair_comm],
          hc12.symm, hc2C, hc1C, h2_hi⟩
      · exact ⟨c₁, c₂, hC_eq, hc12, hc1C, hc2C, h1_hi⟩
    obtain ⟨ch, cl, hC_ord, hchl, hchC, hclC, hch_h⟩ := hex_half
    have huC : ∀ u ∈ U₁, ∀ c ∈ C, u ≠ c := fun u hu c hc h => Finset.disjoint_left.mp hdisj1C hu (h ▸ hc)
    have hvC : ∀ v ∈ U₂, ∀ c ∈ C, v ≠ c := fun v hv c hc h => Finset.disjoint_left.mp hdisj2C hv (h ▸ hc)
    rcases (by omega : (U₁.card = 3 ∧ U₂.card = 0) ∨ (U₁.card = 2 ∧ U₂.card = 1)) with
        ⟨hU1_3, hU2_0⟩ | ⟨hU1_2, hU2_1⟩
    · have hU2_emp : U₂ = ∅ := Finset.card_eq_zero.mp hU2_0
      obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 (by omega : 3 ≤ U₁.card)
      have hU1_eq : U₁ = {u₁, u₂, u₃} := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hno; push Not at hno
          have h4sub : insert z {u₁, u₂, u₃} ⊆ U₁ := Finset.insert_subset hz (fun w hw => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl <;> assumption)
          have h4c : (insert z ({u₁, u₂, u₃} : Finset ℕ)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hno]),
                Finset.card_insert_of_notMem (by simp [h12, h13]),
                Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
          have := Finset.card_le_card h4sub; omega
        · rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
              Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]; omega
      have hA_eq : A = {u₁, u₂, u₃, ch, cl} := by
        rw [hU_part, hU2_emp, Finset.union_empty, hU1_eq, hC_ord]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_six_of_four_half_one hA_eq h12 h13 (huC u₁ hu1 ch hchC) (huC u₁ hu1 cl hclC)
        h23 (huC u₂ hu2 ch hchC) (huC u₂ hu2 cl hclC) (huC u₃ hu3 ch hchC) (huC u₃ hu3 cl hclC) hchl
        hA_pos hA_le hAgcd hM7 (hU1_half u₁ hu1) (hU1_half u₂ hu2) (hU1_half u₃ hu3) hch_h
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1) (hU1_b1 u₂ hu2) (hU1_b1 u₃ hu3) (hC_both ch hchC).1 (hC_both cl hclC).2
    · obtain ⟨u₁, u₂, h12, hu_eq⟩ := Finset.card_eq_two.mp hU1_2
      obtain ⟨v₁, hv1_eq⟩ := Finset.card_eq_one.mp hU2_1
      have hu1U : u₁ ∈ U₁ := by rw [hu_eq]; simp
      have hu2U : u₂ ∈ U₁ := by rw [hu_eq]; simp
      have hv1U : v₁ ∈ U₂ := by rw [hv1_eq]; exact Finset.mem_singleton_self v₁
      have huv_d : ∀ u ∈ U₁, u ≠ v₁ := fun u hu h => Finset.disjoint_left.mp hdisj12 hu (h ▸ hv1U)
      have hA_eq : A = {u₁, u₂, ch, v₁, cl} := by
        rw [hU_part, hu_eq, hv1_eq, hC_ord]
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      exact cover_six_of_r2_C1_31 hA_eq h12 (huC u₁ hu1U ch hchC) (huv_d u₁ hu1U) (huC u₁ hu1U cl hclC)
        (huC u₂ hu2U ch hchC) (huv_d u₂ hu2U) (huC u₂ hu2U cl hclC)
        (hvC v₁ hv1U ch hchC).symm hchl (hvC v₁ hv1U cl hclC)
        hA_pos hA_le hAgcd hM7 (hU1_half u₁ hu1U) (hU1_half u₂ hu2U) hch_h (hU2_half v₁ hv1U)
        hb₁_I hb₂_I hb12 (hU1_b1 u₁ hu1U) (hU1_b1 u₂ hu2U) (hC_both ch hchC).1 (hC_both cl hclC).1
        (hU2_b2 v₁ hv1U) (hC_both cl hclC).2

private lemma cover_six_of_r2_two_sided_wlog {A U₁ U₂ C : Finset ℕ} {x M b₁ b₂ : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hU₁_sub : U₁ ⊆ A) (hU₂_sub : U₂ ⊆ A) (hC_sub : C ⊆ A)
    (hdisj1C : Disjoint U₁ C) (hdisj2C : Disjoint U₂ C) (hdisj12 : Disjoint U₁ U₂)
    (hU_part : A = U₁ ∪ U₂ ∪ C) (hU2_le : U₂.card ≤ U₁.card)
    (hU1_half : ∀ a ∈ U₁, M < 2 * a) (hU2_half : ∀ a ∈ U₂, M < 2 * a)
    (hU1_b1 : ∀ a ∈ U₁, a ∣ b₁) (hU2_b2 : ∀ a ∈ U₂, a ∣ b₂)
    (hC_both : ∀ a ∈ C, a ∣ b₁ ∧ a ∣ b₂) (hb2_ex : (U₂ ∪ C).Nonempty) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  by_cases hC3 : 3 ≤ C.card
  · exact cover_six_of_r2_two_sided_Cge3 hA_card hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb12
      hU₁_sub hU₂_sub hC_sub hdisj1C hdisj2C hdisj12 hU_part hC3 hU2_le hU1_b1 hU2_b2 hC_both
  · by_cases hC2 : C.card = 2
    · exact cover_six_of_r2_two_sided_C2 hA_card hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb12
        hU₁_sub hU₂_sub hC_sub hdisj1C hdisj2C hdisj12 hU_part hC2 hU2_le hU1_half hU2_half
        hU1_b1 hU2_b2 hC_both
    · exact cover_six_of_r2_two_sided_C01 hA_card hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb12
        hU₁_sub hU₂_sub hC_sub hdisj1C hdisj2C hdisj12 hU_part (by omega) hU2_le hU1_half hU2_half
        hU1_b1 hU2_b2 hC_both hb2_ex

/-- Master `r = 2` theorem for `g(5) ≤ 6`. -/
theorem erdos708_upper_five_of_matching_two {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M) (hSA : S ⊆ A) (hS_card : S.card = 2)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S)
    (hnot3 : ¬ HasMatching A x M 3) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have hmax := max_matching_two_unique_multiples hSA hf_mem hf_dvd hf_inj (by rw [hS_card]; exact hnot3)
  obtain ⟨s₁, s₂, hs12, hS_eq⟩ := Finset.card_eq_two.mp hS_card
  have hs1S : s₁ ∈ S := by rw [hS_eq]; simp
  have hs2S : s₂ ∈ S := by rw [hS_eq]; simp
  let b₁ := f s₁
  let b₂ := f s₂
  have hb₁_I : b₁ ∈ consecInterval x M := hf_mem s₁ hs1S
  have hb₂_I : b₂ ∈ consecInterval x M := hf_mem s₂ hs2S
  have hb12 : b₁ ≠ b₂ := fun h => hs12 (hf_inj hs1S hs2S h)
  have hs1_b1 : s₁ ∣ b₁ := hf_dvd s₁ hs1S
  have hs2_b2 : s₂ ∣ b₂ := hf_dvd s₂ hs2S
  have hSimg : S.image f = {b₁, b₂} := by
    rw [hS_eq, Finset.image_insert, Finset.image_singleton]
  have hdiff_c : (A \ S).card = 3 := by
    have h := Finset.card_sdiff_add_card_inter A S
    rw [Finset.inter_eq_right.mpr hSA, hA_card, hS_card] at h; omega
  obtain ⟨u₁, hu1, u₂, hu2, u₃, hu3, h12, h13, h23⟩ := extract_three_of_card_ge3 (by omega : 3 ≤ (A \ S).card)
  have hdiff_eq : A \ S = {u₁, u₂, u₃} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hno; push Not at hno
      have h4sub : insert z {u₁, u₂, u₃} ⊆ A \ S := Finset.insert_subset hz (fun w hw => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption)
      have h4c : (insert z ({u₁, u₂, u₃} : Finset ℕ)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hno]),
            Finset.card_insert_of_notMem (by simp [h12, h13]),
            Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have := Finset.card_le_card h4sub; omega
    · rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]; omega
  have hA_eq : A = {u₁, u₂, u₃, s₁, s₂} := by
    rw [← Finset.sdiff_union_of_subset hSA, hdiff_eq, hS_eq]
    ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have huS : ∀ u ∈ A \ S, u ∉ S := fun u hu => (Finset.mem_sdiff.mp hu).2
  have h1s1 : u₁ ≠ s₁ := fun h => huS u₁ hu1 (h ▸ hs1S)
  have h1s2 : u₁ ≠ s₂ := fun h => huS u₁ hu1 (h ▸ hs2S)
  have h2s1 : u₂ ≠ s₁ := fun h => huS u₂ hu2 (h ▸ hs1S)
  have h2s2 : u₂ ≠ s₂ := fun h => huS u₂ hu2 (h ▸ hs2S)
  have h3s1 : u₃ ≠ s₁ := fun h => huS u₃ hu3 (h ▸ hs1S)
  have h3s2 : u₃ ≠ s₂ := fun h => huS u₃ hu3 (h ▸ hs2S)
  have hu_all : ∀ u ∈ A \ S, ∀ b ∈ consecInterval x M, u ∣ b → b = b₁ ∨ b = b₂ := fun u hu b hb hdb => by
    have := hmax.1 u hu b hb hdb
    rw [hSimg] at this
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  by_cases hex_b2 : ∃ u ∈ A \ S, u ∣ b₂
  · by_cases hex_b1 : ∃ u ∈ A \ S, u ∣ b₁
    · -- **Two-sided:** EVERY `a ∈ A` has all multiples in `{b₁, b₂}`!
      have hs1_all : ∀ b ∈ consecInterval x M, s₁ ∣ b → b = b₁ ∨ b = b₂ := fun b hb hdb => by
        have := hmax.2 s₁ hs1S hex_b1 b hb hdb; rw [hSimg] at this; simpa using this
      have hs2_all : ∀ b ∈ consecInterval x M, s₂ ∣ b → b = b₁ ∨ b = b₂ := fun b hb hdb => by
        have := hmax.2 s₂ hs2S hex_b2 b hb hdb; rw [hSimg] at this; simpa using this
      have hall_12 : ∀ a ∈ A, ∀ b ∈ consecInterval x M, a ∣ b → b = b₁ ∨ b = b₂ := fun a ha b hb hdb => by
        by_cases haS : a ∈ S
        · rw [hS_eq] at haS; rcases Finset.mem_insert.mp haS with rfl | hmem
          · exact hs1_all b hb hdb
          · rw [Finset.mem_singleton] at hmem; subst hmem; exact hs2_all b hb hdb
        · exact hu_all a (Finset.mem_sdiff.mpr ⟨ha, haS⟩) b hb hdb
      have hall_div : ∀ a ∈ A, a ∣ b₁ ∨ a ∣ b₂ := fun a ha => by
        obtain ⟨ba, hba_I, hda⟩ := exists_multiple_in_consecInterval x a M (hA_pos a ha) (hA_le a ha)
        rcases hall_12 a ha ba hba_I hda with rfl | rfl <;> [exact Or.inl hda; exact Or.inr hda]
      let U₁ := A.filter (fun a => a ∣ b₁ ∧ ¬ (a ∣ b₂))
      let U₂ := A.filter (fun a => ¬ (a ∣ b₁) ∧ a ∣ b₂)
      let C := A.filter (fun a => a ∣ b₁ ∧ a ∣ b₂)
      have hU₁_sub : U₁ ⊆ A := Finset.filter_subset _ _
      have hU₂_sub : U₂ ⊆ A := Finset.filter_subset _ _
      have hC_sub : C ⊆ A := Finset.filter_subset _ _
      have hd1C : Disjoint U₁ C := Finset.disjoint_left.mpr fun a h1 hC =>
        (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp hC).2.2
      have hd2C : Disjoint U₂ C := Finset.disjoint_left.mpr fun a h2 hC =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp hC).2.1
      have hd12 : Disjoint U₁ U₂ := Finset.disjoint_left.mpr fun a h1 h2 =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      have hU_part : A = U₁ ∪ U₂ ∪ C := by
        ext a; simp only [U₁, U₂, C, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ha; rcases hall_div a ha with h1 | h2 <;> by_cases h1' : a ∣ b₁ <;> by_cases h2' : a ∣ b₂ <;> tauto
        · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩) <;> exact ha
      have hU1_b1 : ∀ a ∈ U₁, a ∣ b₁ := fun a ha => (Finset.mem_filter.mp ha).2.1
      have hU2_b2 : ∀ a ∈ U₂, a ∣ b₂ := fun a ha => (Finset.mem_filter.mp ha).2.2
      have hC_both : ∀ a ∈ C, a ∣ b₁ ∧ a ∣ b₂ := fun a ha => (Finset.mem_filter.mp ha).2
      have hU1_half : ∀ a ∈ U₁, M < 2 * a := fun a ha =>
        lt_two_mul_of_unique_multiple_in_consecInterval (hA_pos a (hU₁_sub ha)) hb₁_I (hU1_b1 a ha)
          (fun b hb hdb => (hall_12 a (hU₁_sub ha) b hb hdb).elim id
            (fun h => absurd (h ▸ hdb) (Finset.mem_filter.mp ha).2.2))
      have hU2_half : ∀ a ∈ U₂, M < 2 * a := fun a ha =>
        lt_two_mul_of_unique_multiple_in_consecInterval (hA_pos a (hU₂_sub ha)) hb₂_I (hU2_b2 a ha)
          (fun b hb hdb => (hall_12 a (hU₂_sub ha) b hb hdb).elim
            (fun h => absurd (h ▸ hdb) (Finset.mem_filter.mp ha).2.1) id)
      have hb1_ex : (U₁ ∪ C).Nonempty := by
        refine ⟨s₁, ?_⟩
        by_cases h2 : s₁ ∣ b₂
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSA hs1S, hs1_b1, h2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSA hs1S, hs1_b1, h2⟩)
      have hb2_ex : (U₂ ∪ C).Nonempty := by
        refine ⟨s₂, ?_⟩
        by_cases h1 : s₂ ∣ b₁
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hSA hs2S, h1, hs2_b2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hSA hs2S, h1, hs2_b2⟩)
      rcases le_or_gt U₂.card U₁.card with hle | hlt
      · exact cover_six_of_r2_two_sided_wlog hA_card hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb12
          hU₁_sub hU₂_sub hC_sub hd1C hd2C hd12 hU_part hle hU1_half hU2_half hU1_b1 hU2_b2 hC_both hb2_ex
      · have hU_part' : A = U₂ ∪ U₁ ∪ C := by
          rw [hU_part]; ext z; simp only [Finset.mem_union]; tauto
        exact cover_six_of_r2_two_sided_wlog hA_card hA_pos hA_le hAgcd hM7 hb₂_I hb₁_I hb12.symm
          hU₂_sub hU₁_sub hC_sub hd2C hd1C hd12.symm hU_part' (by omega) hU2_half hU1_half hU2_b2 hU1_b1
          (fun a ha => ⟨(hC_both a ha).2, (hC_both a ha).1⟩) hb1_ex
    · -- **One-sided (at `b₂`):** NO `u ∈ A \ S` divides `b₁`, so all 3 `u ∈ A \ S` divide `b₂`!
      have hu_only_b2 : ∀ u ∈ ({u₁, u₂, u₃} : Finset ℕ), ∀ b ∈ consecInterval x M, u ∣ b → b = b₂ := by
        intro u hu b hb hdb
        have hu' : u ∈ A \ S := by rw [hdiff_eq]; exact hu
        rcases hu_all u hu' b hb hdb with rfl | rfl
        · exact absurd ⟨u, hu', hdb⟩ hex_b1
        · rfl
      have hs2_all : ∀ b ∈ consecInterval x M, s₂ ∣ b → b = b₂ ∨ b = b₁ := fun b hb hdb => by
        have := hmax.2 s₂ hs2S hex_b2 b hb hdb; rw [hSimg] at this
        simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm] using this
      have hA_eq' : A = {u₁, u₂, u₃, s₂, s₁} := by
        rw [hA_eq]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp, by rintro (rfl|rfl|rfl|rfl|rfl) <;> simp⟩
      exact cover_six_of_r2_one_sided hA_eq' h12 h13 h1s2 h1s1 h23 h2s2 h2s1 h3s2 h3s1 hs12.symm
        hA_pos hA_le hAgcd hM7 hb₂_I hb₁_I hb12.symm hs2_b2 hs1_b1 hu_only_b2 hs2_all
  · -- **One-sided (at `b₁`):** NO `u ∈ A \ S` divides `b₂`!
    have hu_only_b1 : ∀ u ∈ ({u₁, u₂, u₃} : Finset ℕ), ∀ b ∈ consecInterval x M, u ∣ b → b = b₁ := by
      intro u hu b hb hdb
      have hu' : u ∈ A \ S := by rw [hdiff_eq]; exact hu
      rcases hu_all u hu' b hb hdb with rfl | rfl
      · rfl
      · exact absurd ⟨u, hu', hdb⟩ hex_b2
    have hex_b1 : ∃ u ∈ A \ S, u ∣ b₁ := by
      obtain ⟨bu, hbu_I, hdu⟩ := exists_multiple_in_consecInterval x u₁ M (hA_pos u₁ (hA_eq ▸ by simp))
        (hA_le u₁ (hA_eq ▸ by simp))
      have heq : bu = b₁ := hu_only_b1 u₁ (by simp) bu hbu_I hdu
      exact ⟨u₁, hu1, heq ▸ hdu⟩
    have hs1_all : ∀ b ∈ consecInterval x M, s₁ ∣ b → b = b₁ ∨ b = b₂ := fun b hb hdb => by
      have := hmax.2 s₁ hs1S hex_b1 b hb hdb; rw [hSimg] at this; simpa using this
    exact cover_six_of_r2_one_sided hA_eq h12 h13 h1s1 h1s2 h23 h2s1 h2s2 h3s1 h3s2 hs12
      hA_pos hA_le hAgcd hM7 hb₁_I hb₂_I hb12 hs1_b1 hs2_b2 hu_only_b1 hs1_all

end Erdos708

