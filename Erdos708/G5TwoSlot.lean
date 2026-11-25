import Erdos708.G4

/-!
# PPL 176 (Erdős Problem #708) — Two-Slot Closure, Chain/Type-1b, and `r = 2` for `g(5) ≤ 6`

This module builds Part 1 of the unconditional proof of `g(5) ≤ 6` (`SatisfiesBound 5 6`):
1. **Layer-Cake Deficit Bound for `|A| = 5, gcd(A) = 1`** (`layer_cake_deficit_le_of_pow_subset_five`).
2. **Master Two-Slot Residual Theorem (`exists_two_slots_for_R_le_M_five`)**:
   given a `≤ 4`-slot subset `B₁ ⊆ consecInterval x M` leaving residual `R ≤ M` (under `|A| = 5`,
   `gcd(A) = 1`, `7 ≤ M`), two extra slots in `consecInterval x M \ B₁` always suffice.
   Immediate corollary `cover_six_of_cover_four_erase`: any `≤ 4`-slot cover of `A.erase u`
   extends unconditionally to a `≤ 6`-slot cover of `A`.
3. **Unconditional 4-Slot Closures for 4 Elements Dividing `b₀`**:
   - `cover_four_of_chain4`: any 4-element chain `a₃ ∤ lcm(a₁, a₂)` and `a₄ ∤ lcm(a₁, a₂, a₃)`
     in `(M/2, M]` admits a `≤ 4`-slot cover.
   - `cover_four_of_type1b`: any pair-spanning 4-subset in `(M/2, M]` admits a `≤ 4`-slot cover.
4. **Matching Size `r = 2` Closure (`cover_six_of_r2`)**:
   complete closure of the `S.card = 2` branch using the disjoint/shared partition `(U₁, U₂, C)`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Elementary Helpers & Layer-Cake Deficit Bound (`|A| = 5, gcd = 1`) -/

lemma isCover_of_prime_factorization_5 {A B : Finset ℕ}
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    (hfac : ∀ p : ℕ, p.Prime → ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B, b.factorization p) :
    IsCover A B :=
  prod_dvd_prod_of_factorization_le hA0 hB0 hfac

lemma fac_le_of_dvd_5 {d w p : ℕ} (hw : w ≠ 0) (hdw : d ∣ w) :
    d.factorization p ≤ w.factorization p := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp at hdw; exact absurd hdw hw
  · exact (Nat.factorization_le_iff_dvd hd_pos.ne' hw).mpr hdw p

lemma fac_gcd_eq_min_5 {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.gcd a b).factorization p = min (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_gcd ha hb]
  rfl

lemma fac_lcm_eq_max_5 {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).factorization p = max (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_lcm ha hb]
  rfl

lemma coprime_factorization_zero {a b p : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) (hcop : Nat.Coprime a b) :
    a.factorization p = 0 ∨ b.factorization p = 0 := by
  by_contra hboth
  push Not at hboth
  have hd1 : p ∣ a := (hp.dvd_iff_one_le_factorization ha.ne').mpr (Nat.pos_of_ne_zero hboth.1)
  have hd2 : p ∣ b := (hp.dvd_iff_one_le_factorization hb.ne').mpr (Nat.pos_of_ne_zero hboth.2)
  have hdp : p ∣ Nat.gcd a b := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hdp
  exact hp.not_dvd_one hdp

lemma exists_avoiding_multiple_5 (x M d : ℕ) (S : Finset ℕ) (hd : 0 < d)
    (hbd : (S.card + 1) * d ≤ M) :
    ∃ w ∈ consecInterval x M, w ∉ S ∧ d ∣ w :=
  exists_avoiding_multiple_in_consecInterval x M d S hd hbd

lemma three_mul_le_of_two_gt_half_5 {d a₁ a₂ M : ℕ}
    (_hd : 0 < d) (h12 : a₁ ≠ a₂) (ha₁M : a₁ ≤ M) (ha₂M : a₂ ≤ M)
    (h1_half : M < 2 * a₁) (h2_half : M < 2 * a₂)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) :
    3 * d ≤ M := by
  rcases lt_or_gt_of_ne h12 with hlt | hgt
  · obtain ⟨q₁, hq1⟩ := hd1
    obtain ⟨q₂, hq2⟩ := hd2
    have hq1_lt : q₁ < q₂ := by
      by_contra hle
      have h21 : d * q₂ ≤ d * q₁ := Nat.mul_le_mul_left d (by omega)
      omega
    have hq1_pos : 1 ≤ q₁ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq1; omega
    have hq1_ge2 : 2 ≤ q₁ := by
      by_contra hlt1
      have hq1_le1 : q₁ ≤ 1 := by omega
      have hle : a₁ ≤ d := by
        calc a₁ = d * q₁ := hq1
          _ ≤ d * 1 := Nat.mul_le_mul_left d hq1_le1
          _ = d := mul_one d
      have hq2_ge2 : 2 ≤ q₂ := by omega
      have hd_le_a2 : 2 * d ≤ a₂ := by
        calc 2 * d = d * 2 := by ring
          _ ≤ d * q₂ := Nat.mul_le_mul_left d hq2_ge2
          _ = a₂ := hq2.symm
      omega
    have hq2_ge3 : 3 ≤ q₂ := by omega
    calc 3 * d = d * 3 := by ring
      _ ≤ d * q₂ := Nat.mul_le_mul_left d hq2_ge3
      _ = a₂ := hq2.symm
      _ ≤ M := ha₂M
  · obtain ⟨q₁, hq1⟩ := hd1
    obtain ⟨q₂, hq2⟩ := hd2
    have hq2_lt : q₂ < q₁ := by
      by_contra hle
      have h12' : d * q₁ ≤ d * q₂ := Nat.mul_le_mul_left d (by omega)
      omega
    have hq2_pos : 1 ≤ q₂ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hq2; omega
    have hq2_ge2 : 2 ≤ q₂ := by
      by_contra hlt2
      have hq2_le1 : q₂ ≤ 1 := by omega
      have hle : a₂ ≤ d := by
        calc a₂ = d * q₂ := hq2
          _ ≤ d * 1 := Nat.mul_le_mul_left d hq2_le1
          _ = d := mul_one d
      have hq1_ge2 : 2 ≤ q₁ := by omega
      have hd_le_a1 : 2 * d ≤ a₁ := by
        calc 2 * d = d * 2 := by ring
          _ ≤ d * q₁ := Nat.mul_le_mul_left d hq1_ge2
          _ = a₁ := hq1.symm
      omega
    have hq1_ge3 : 3 ≤ q₁ := by omega
    calc 3 * d = d * 3 := by ring
      _ ≤ d * q₁ := Nat.mul_le_mul_left d hq1_ge3
      _ = a₁ := hq1.symm
      _ ≤ M := ha₁M

lemma two_mul_gcd_le_5 {a b M : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haM : a ≤ M) (hbM : b ≤ M) :
    2 * Nat.gcd a b ≤ M := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a b
    have hle : Nat.gcd a b ≤ a := Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)
    have hq2 : 2 ≤ q := by
      by_contra hltq
      have hq_le1 : q ≤ 1 := by omega
      have hb_le : b ≤ Nat.gcd a b := by
        calc b = Nat.gcd a b * q := hq
          _ ≤ Nat.gcd a b * 1 := Nat.mul_le_mul_left _ hq_le1
          _ = Nat.gcd a b := mul_one _
      omega
    have h1 : 2 * Nat.gcd a b ≤ Nat.gcd a b * q := by
      rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq2
    omega
  · obtain ⟨q, hq⟩ := Nat.gcd_dvd_left a b
    have hle : Nat.gcd a b ≤ b := Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)
    have hq2 : 2 ≤ q := by
      by_contra hltq
      have hq_le1 : q ≤ 1 := by omega
      have ha_le : a ≤ Nat.gcd a b := by
        calc a = Nat.gcd a b * q := hq
          _ ≤ Nat.gcd a b * 1 := Nat.mul_le_mul_left _ hq_le1
          _ = Nat.gcd a b := mul_one _
      omega
    have h1 : 2 * Nat.gcd a b ≤ Nat.gcd a b * q := by
      rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq2
    omega

lemma card_finset_le_three_5 (a b c : ℕ) : ({a, b, c} : Finset ℕ).card ≤ 3 := by
  have h1 := Finset.card_insert_le a {b, c}
  have h2 := Finset.card_insert_le b {c}
  simp only [Finset.card_singleton] at h2
  omega

lemma card_finset_le_four_5 (a b c d : ℕ) : ({a, b, c, d} : Finset ℕ).card ≤ 4 := by
  have h1 := Finset.card_insert_le a {b, c, d}
  have h2 := card_finset_le_three_5 b c d
  omega

private lemma card_multiples_Icc_le_5 (x M d : ℕ) (hM : 1 ≤ M) (_hd : 0 < d) :
    ((consecInterval x M).filter (fun b => d ∣ b)).card ≤ (M - 1) / d + 1 := by
  let S := (consecInterval x M).filter (fun b => d ∣ b)
  change S.card ≤ (M - 1) / d + 1
  by_cases hS : S.Nonempty
  · let b₀ := S.min' hS
    have hb₀_S : b₀ ∈ S := Finset.min'_mem S hS
    have hb₀_mem := Finset.mem_filter.mp hb₀_S
    have hb₀_I := Finset.mem_Icc.mp hb₀_mem.1
    have hb₀_dvd : d ∣ b₀ := hb₀_mem.2
    let g : ℕ → ℕ := fun b => (b - b₀) / d
    have hmaps : Set.MapsTo g S (Finset.range ((M - 1) / d + 1)) := by
      intro b hb
      rw [Finset.mem_coe, Finset.mem_range]
      have hb_I := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
      have hle : b - b₀ ≤ M - 1 := by omega
      have hdiv : (b - b₀) / d ≤ (M - 1) / d := Nat.div_le_div_right hle
      dsimp [g]
      omega
    have hinj : Set.InjOn g S := by
      intro b₁ hb₁ b₂ hb₂ heq
      dsimp [g] at heq
      have hb₁_le : b₀ ≤ b₁ := Finset.min'_le S b₁ hb₁
      have hb₂_le : b₀ ≤ b₂ := Finset.min'_le S b₂ hb₂
      have hb₁_dvd : d ∣ b₁ := (Finset.mem_filter.mp hb₁).2
      have hb₂_dvd : d ∣ b₂ := (Finset.mem_filter.mp hb₂).2
      have hsub1 : d ∣ b₁ - b₀ := Nat.dvd_sub hb₁_dvd hb₀_dvd
      have hsub2 : d ∣ b₂ - b₀ := Nat.dvd_sub hb₂_dvd hb₀_dvd
      have hmul1 : d * ((b₁ - b₀) / d) = b₁ - b₀ := Nat.mul_div_cancel' hsub1
      have hmul2 : d * ((b₂ - b₀) / d) = b₂ - b₀ := Nat.mul_div_cancel' hsub2
      have hsub_eq : b₁ - b₀ = b₂ - b₀ := by rw [← hmul1, ← hmul2, heq]
      omega
    simpa [Finset.card_range] using Finset.card_le_card_of_injOn g hmaps hinj
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS, Finset.card_empty]
    exact Nat.zero_le _

private lemma sum_factorization_eq_sum_card_Icc_5 {A : Finset ℕ} {M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hp : p.Prime) :
    ∑ a ∈ A, a.factorization p =
      ∑ j ∈ Finset.Icc 1 M, (A.filter (fun a => p ^ j ∣ a)).card := by
  calc
    ∑ a ∈ A, a.factorization p
        = ∑ a ∈ A, ∑ j ∈ Finset.Icc 1 M, if p ^ j ∣ a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact factorization_eq_sum_dvd hp (hA_pos a ha) (hA_le a ha)
    _ = ∑ j ∈ Finset.Icc 1 M, ∑ a ∈ A, if p ^ j ∣ a then 1 else 0 := Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc 1 M, (A.filter (fun a => p ^ j ∣ a)).card := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_boole, Nat.cast_id]

private lemma sum_card_Icc_le_sum_factorization_5 {S : Finset ℕ} {x M K p : ℕ}
    (hS_I : S ⊆ consecInterval x M) (hp : p.Prime) :
    ∑ j ∈ Finset.Icc 1 K, (S.filter (fun b => p ^ j ∣ b)).card ≤
      ∑ b ∈ S, b.factorization p := by
  calc
    ∑ j ∈ Finset.Icc 1 K, (S.filter (fun b => p ^ j ∣ b)).card
        = ∑ j ∈ Finset.Icc 1 K, ∑ b ∈ S, if p ^ j ∣ b then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_boole, Nat.cast_id]
    _ = ∑ b ∈ S, ∑ j ∈ Finset.Icc 1 K, if p ^ j ∣ b then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ b ∈ S, b.factorization p := by
          apply Finset.sum_le_sum
          intro b hb
          exact sum_dvd_le_factorization hp (pos_of_mem_consecInterval (hS_I hb))

private lemma exists_not_dvd_of_gcd_one_5 {A : Finset ℕ} (hAgcd : A.gcd id = 1)
    {p : ℕ} (hp : p.Prime) :
    ∃ a₀ ∈ A, ¬ (p ∣ a₀) := by
  by_contra hall
  push Not at hall
  have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd (fun a ha => hall a ha)
  rw [hAgcd] at hpgcd
  exact hp.not_dvd_one hpgcd

private lemma card_filter_le_four_and_div_5 {A : Finset ℕ} {M p j : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hp : p.Prime) (hj : 1 ≤ j) :
    (A.filter (fun a => p ^ j ∣ a)).card ≤ 4 ∧
      (A.filter (fun a => p ^ j ∣ a)).card ≤ M / p ^ j := by
  obtain ⟨a₀, ha₀A, ha₀_ndvd⟩ := exists_not_dvd_of_gcd_one_5 hAgcd hp
  have hnot_pj : ¬ (p ^ j ∣ a₀) := fun h =>
    ha₀_ndvd (dvd_trans (dvd_pow_self p (by omega)) h)
  have hsub4 : A.filter (fun a => p ^ j ∣ a) ⊆ A.erase a₀ := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_erase.mpr ⟨fun heq => hnot_pj (heq ▸ ha.2), ha.1⟩
  have hcard4 : (A.filter (fun a => p ^ j ∣ a)).card ≤ 4 := by
    have h1 := Finset.card_le_card hsub4
    rw [Finset.card_erase_of_mem ha₀A, hA_card] at h1
    exact h1
  have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
  have hsubI : A.filter (fun a => p ^ j ∣ a) ⊆ (Finset.Icc 1 M).filter (fun a => p ^ j ∣ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_Icc.mpr ⟨hA_pos a ha.1, hA_le a ha.1⟩, ha.2⟩
  have hcardDiv : (A.filter (fun a => p ^ j ∣ a)).card ≤ M / p ^ j :=
    le_trans (Finset.card_le_card hsubI) (card_multiples_Icc_one_le M (p ^ j) hpj_pos)
  exact ⟨hcard4, hcardDiv⟩

/-- **Generalized Layer-Cake Deficit Bound for `|A| = 5, gcd(A) = 1`**:
    if `(consecInterval x M).filter (p ^ t ∣ ·) ⊆ B₀` (`1 ≤ t`), then
    `(∑ A, v_p) - (∑ B₀, v_p) ≤ (4 - M / p ^ t) * (t - 1)`. -/
lemma layer_cake_deficit_le_of_pow_subset_five {A B₀ : Finset ℕ} {x M p t : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (_ht : 1 ≤ t) (hsub : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀) :
    (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ (4 - M / p ^ t) * (t - 1) := by
  have hA_sum := sum_factorization_eq_sum_card_Icc_5 hA_pos hA_le hp
  have hB₀_sum := sum_card_Icc_le_sum_factorization_5 (K := M) hB₀_I hp
  let J_lo := (Finset.Icc 1 M).filter (fun j => j < t)
  let J_hi := (Finset.Icc 1 M).filter (fun j => ¬ (j < t))
  have hA_split : ∑ j ∈ Finset.Icc 1 M, (A.filter (fun a => p ^ j ∣ a)).card =
      (∑ j ∈ J_lo, (A.filter (fun a => p ^ j ∣ a)).card) +
      (∑ j ∈ J_hi, (A.filter (fun a => p ^ j ∣ a)).card) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun j => j < t)
      (fun j => (A.filter (fun a => p ^ j ∣ a)).card)).symm
  have hB₀_split : ∑ j ∈ Finset.Icc 1 M, (B₀.filter (fun b => p ^ j ∣ b)).card =
      (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) +
      (∑ j ∈ J_hi, (B₀.filter (fun b => p ^ j ∣ b)).card) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun j => j < t)
      (fun j => (B₀.filter (fun b => p ^ j ∣ b)).card)).symm
  have hlo_term : ∀ j ∈ J_lo,
      (A.filter (fun a => p ^ j ∣ a)).card ≤
        (B₀.filter (fun b => p ^ j ∣ b)).card + (4 - M / p ^ t) := by
    intro j hj
    have hj_mem := (Finset.mem_filter.mp hj).1
    have hj_lt : j < t := (Finset.mem_filter.mp hj).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
    have hA4 := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd hp hj1).1
    have hsub_j : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆
        B₀.filter (fun b => p ^ j ∣ b) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      exact ⟨hsub (Finset.mem_filter.mpr hb), dvd_trans (Nat.pow_dvd_pow p (by omega)) hb.2⟩
    have hB_ge : M / p ^ t ≤ (B₀.filter (fun b => p ^ j ∣ b)).card :=
      le_trans (card_multiples_Icc_ge x M (p ^ t) (pow_pos hp.pos t)) (Finset.card_le_card hsub_j)
    omega
  have hhi_term : ∀ j ∈ J_hi,
      (A.filter (fun a => p ^ j ∣ a)).card ≤ (B₀.filter (fun b => p ^ j ∣ b)).card := by
    intro j hj
    have hj_mem := (Finset.mem_filter.mp hj).1
    have hj_ge : t ≤ j := by have := (Finset.mem_filter.mp hj).2; omega
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
    have hAdiv := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd hp hj1).2
    have hsub_j : (consecInterval x M).filter (fun b => p ^ j ∣ b) ⊆
        B₀.filter (fun b => p ^ j ∣ b) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      have hb_t : p ^ t ∣ b := dvd_trans (Nat.pow_dvd_pow p hj_ge) hb.2
      exact ⟨hsub (Finset.mem_filter.mpr ⟨hb.1, hb_t⟩), hb.2⟩
    have hB_ge : M / p ^ j ≤ (B₀.filter (fun b => p ^ j ∣ b)).card :=
      le_trans (card_multiples_Icc_ge x M (p ^ j) (pow_pos hp.pos j)) (Finset.card_le_card hsub_j)
    exact le_trans hAdiv hB_ge
  have hJlo_card : J_lo.card ≤ t - 1 := by
    have hsub_ico : J_lo ⊆ Finset.Ico 1 t := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      exact Finset.mem_Ico.mpr ⟨hj.1.1, hj.2⟩
    calc J_lo.card ≤ (Finset.Ico 1 t).card := Finset.card_le_card hsub_ico
      _ = t - 1 := by rw [Nat.card_Ico]
  have hlo_sum : ∑ j ∈ J_lo, (A.filter (fun a => p ^ j ∣ a)).card ≤
      (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (4 - M / p ^ t) * (t - 1) := by
    calc
      ∑ j ∈ J_lo, (A.filter (fun a => p ^ j ∣ a)).card
          ≤ ∑ j ∈ J_lo, ((B₀.filter (fun b => p ^ j ∣ b)).card + (4 - M / p ^ t)) :=
            Finset.sum_le_sum hlo_term
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) +
          ∑ _j ∈ J_lo, (4 - M / p ^ t) := Finset.sum_add_distrib
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + J_lo.card * (4 - M / p ^ t) := by
          simp
      _ ≤ (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (t - 1) * (4 - M / p ^ t) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hJlo_card) _
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (4 - M / p ^ t) * (t - 1) := by
          ring
  have hhi_sum : ∑ j ∈ J_hi, (A.filter (fun a => p ^ j ∣ a)).card ≤
      ∑ j ∈ J_hi, (B₀.filter (fun b => p ^ j ∣ b)).card := Finset.sum_le_sum hhi_term
  omega

lemma exists_prime_multiple_avoiding_five {A B₀ : Finset ℕ} {x M p : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (hdef : 1 ≤ (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ b ∈ consecInterval x M, b ∉ B₀ ∧ p ∣ b := by
  by_contra hall
  push Not at hall
  have hsub : (consecInterval x M).filter (fun b => p ^ 1 ∣ b) ⊆ B₀ := by
    intro b hb
    rw [Finset.mem_filter, pow_one] at hb
    by_contra hbB₀
    exact hall b hb.1 hbB₀ hb.2
  have h0 := layer_cake_deficit_le_of_pow_subset_five hA_card hA_pos hA_le hAgcd hB₀_I hp (le_refl 1) hsub
  omega

lemma exists_pow_multiple_avoiding_of_3_le_div_five {A B₀ : Finset ℕ} {x M p t : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (ht : 1 ≤ t) (hc3 : 3 ≤ M / p ^ t)
    (hdef : t ≤ (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ b ∈ consecInterval x M, b ∉ B₀ ∧ p ^ t ∣ b := by
  by_contra hall
  push Not at hall
  have hsub : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀ := by
    intro b hb
    rw [Finset.mem_filter] at hb
    by_contra hbB₀
    exact hall b hb.1 hbB₀ hb.2
  have h0 := layer_cake_deficit_le_of_pow_subset_five hA_card hA_pos hA_le hAgcd hB₀_I hp ht hsub
  have hle : (4 - M / p ^ t) * (t - 1) ≤ 1 * (t - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Total-interval valuation dominance for `A ⊆ [1, M]` and `consecInterval x M`. -/
lemma sum_factorization_le_consecInterval {A : Finset ℕ} {x M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hp : p.Prime) :
    ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ consecInterval x M, b.factorization p := by
  let I := consecInterval x M
  have hsub : A ⊆ Finset.Icc 1 M := fun a ha => Finset.mem_Icc.mpr ⟨hA_pos a ha, hA_le a ha⟩
  have hsumA : ∑ a ∈ A, a.factorization p =
      ∑ j ∈ Finset.Icc 1 M, (A.filter (fun a => p ^ j ∣ a)).card :=
    sum_factorization_eq_sum_card_Icc_5 hA_pos hA_le hp
  have hsumI : ∑ j ∈ Finset.Icc 1 M, (I.filter (fun b => p ^ j ∣ b)).card ≤
      ∑ b ∈ I, b.factorization p :=
    sum_card_Icc_le_sum_factorization_5 (K := M) Finset.Subset.rfl hp
  have hterm : ∀ j ∈ Finset.Icc 1 M,
      (A.filter (fun a => p ^ j ∣ a)).card ≤ (I.filter (fun b => p ^ j ∣ b)).card := by
    intro j hj
    have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
    have hsubA : A.filter (fun a => p ^ j ∣ a) ⊆ (Finset.Icc 1 M).filter (fun a => p ^ j ∣ a) := by
      intro a ha; rw [Finset.mem_filter] at ha ⊢; exact ⟨hsub ha.1, ha.2⟩
    have h1 := le_trans (Finset.card_le_card hsubA) (card_multiples_Icc_one_le M (p ^ j) hpj_pos)
    exact le_trans h1 (card_multiples_Icc_ge x M (p ^ j) hpj_pos)
  change ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ I, b.factorization p
  exact le_trans (by rw [hsumA]; exact Finset.sum_le_sum hterm) hsumI

/-! ## Part 2: 2-Slot Realization Helpers & `exists_two_slots_for_R_le_M_five` -/

private lemma two_slots_of_one_dvd_5 {B₀ : Finset ℕ} {x M R w : ℕ}
    (hw_I : w ∈ consecInterval x M) (hw_notB₀ : w ∉ B₀) (hRw : R ∣ w) (hR0 : R ≠ 0) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  refine ⟨{w}, Finset.singleton_subset_iff.mpr hw_I, Finset.disjoint_singleton_right.mpr hw_notB₀,
    by simp, ?_⟩
  intro p _hp
  rw [Finset.sum_singleton]
  exact (Nat.factorization_le_iff_dvd hR0 (pos_of_mem_consecInterval hw_I).ne').mpr hRw p

private lemma two_slots_of_two_dvd_5 {B₀ : Finset ℕ} {x M R w₁ w₂ : ℕ}
    (hw₁_I : w₁ ∈ consecInterval x M) (hw₂_I : w₂ ∈ consecInterval x M)
    (hw₁_notB₀ : w₁ ∉ B₀) (hw₂_notB₀ : w₂ ∉ B₀)
    (hne : w₁ ≠ w₂) (hRw : R ∣ w₁ * w₂) (hR0 : R ≠ 0) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  refine ⟨{w₁, w₂}, Finset.insert_subset hw₁_I (Finset.singleton_subset_iff.mpr hw₂_I), ?_,
    Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
  · rw [Finset.disjoint_insert_right]
    exact ⟨hw₁_notB₀, Finset.disjoint_singleton_right.mpr hw₂_notB₀⟩
  · intro p _hp
    have hw₁_pos : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
    have hw₂_pos : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
    have hfac := (Nat.factorization_le_iff_dvd hR0 (mul_ne_zero hw₁_pos hw₂_pos)).mpr hRw p
    rw [Nat.factorization_mul hw₁_pos hw₂_pos, Finsupp.add_apply] at hfac
    rwa [Finset.sum_pair hne]

private lemma two_slots_of_coprime_dvd_5 {B₀ : Finset ℕ} {x M R d₁ d₂ w₁ w₂ : ℕ}
    (hR_eq : R = d₁ * d₂) (hcop : Nat.Coprime d₁ d₂)
    (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (hw₁_I : w₁ ∈ consecInterval x M) (hw₂_I : w₂ ∈ consecInterval x M)
    (hw₁_notB₀ : w₁ ∉ B₀) (hw₂_notB₀ : w₂ ∉ B₀)
    (hd₁_w₁ : d₁ ∣ w₁) (hd₂_w₂ : d₂ ∣ w₂) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  have hR0 : R ≠ 0 := by rw [hR_eq]; exact mul_ne_zero hd₁_pos.ne' hd₂_pos.ne'
  by_cases heq : w₁ = w₂
  · have hd₂_w₁ : d₂ ∣ w₁ := heq ▸ hd₂_w₂
    have hRw₁ : R ∣ w₁ := by rw [hR_eq]; exact hcop.mul_dvd_of_dvd_of_dvd hd₁_w₁ hd₂_w₁
    exact two_slots_of_one_dvd_5 hw₁_I hw₁_notB₀ hRw₁ hR0
  · have hRw : R ∣ w₁ * w₂ := by rw [hR_eq]; exact mul_dvd_mul hd₁_w₁ hd₂_w₂
    exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ heq hRw hR0

private lemma two_distinct_mults_five {B₀ : Finset ℕ} {x M R d : ℕ}
    (hB₀_card : B₀.card ≤ 4) (hR0 : R ≠ 0) (hd_pos : 0 < d) (h6d : 6 * d ≤ M) (hRd2 : R ∣ d * d) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  have hbd1 : (B₀.card + 1) * d ≤ M :=
    le_trans (Nat.mul_le_mul_right d (by omega : B₀.card + 1 ≤ 6)) h6d
  obtain ⟨w₁, hw₁_I, hw₁_notB₀, hdw₁⟩ := exists_avoiding_multiple_5 x M d B₀ hd_pos hbd1
  have hcard_ins : (insert w₁ B₀).card + 1 ≤ 6 := by
    have h1 := Finset.card_insert_le w₁ B₀; omega
  obtain ⟨w₂, hw₂_I, hw₂_notIns, hdw₂⟩ := exists_avoiding_multiple_5 x M d (insert w₁ B₀) hd_pos
    (le_trans (Nat.mul_le_mul_right d hcard_ins) h6d)
  have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
  have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
  exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
    (dvd_trans hRd2 (mul_dvd_mul hdw₁ hdw₂)) hR0

private lemma two_split_mults_five {B₀ : Finset ℕ} {x M R d₁ d₂ : ℕ}
    (hB₀_card : B₀.card ≤ 4) (hR0 : R ≠ 0) (hd₁_pos : 0 < d₁) (hd₂_pos : 0 < d₂)
    (h5d₁ : 5 * d₁ ≤ M) (h6d₂ : 6 * d₂ ≤ M) (hRd12 : R ∣ d₁ * d₂) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  have hbd1 : (B₀.card + 1) * d₁ ≤ M :=
    le_trans (Nat.mul_le_mul_right d₁ (by omega : B₀.card + 1 ≤ 5)) h5d₁
  obtain ⟨w₁, hw₁_I, hw₁_notB₀, hd₁_w₁⟩ := exists_avoiding_multiple_5 x M d₁ B₀ hd₁_pos hbd1
  have hcard_ins : (insert w₁ B₀).card + 1 ≤ 6 := by
    have h1 := Finset.card_insert_le w₁ B₀; omega
  obtain ⟨w₂, hw₂_I, hw₂_notIns, hd₂_w₂⟩ := exists_avoiding_multiple_5 x M d₂ (insert w₁ B₀) hd₂_pos
    (le_trans (Nat.mul_le_mul_right d₂ hcard_ins) h6d₂)
  have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
  have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
  exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
    (dvd_trans hRd12 (mul_dvd_mul hd₁_w₁ hd₂_w₂)) hR0

/-- Subcase `(R = 18, 18 ≤ M ≤ 26)` of `exists_two_slots_for_R_le_M_five`. -/
private lemma two_slots_five_R18 {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (_hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 4)
    (hM_lo : 18 ≤ M) (hM_hi : M ≤ 26) (hR_eq : R = 18)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  have hR0 : R ≠ 0 := by omega
  have hsumA_3 : ∑ a ∈ A, a.factorization 3 ≤ 6 := by
    have h1 := sum_factorization_eq_sum_card_Icc_5 hA_pos hA_le (by norm_num : Nat.Prime 3)
    have hc1 := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 3) (j := 1)
      (by norm_num) (by omega)).1
    have hc2 : (A.filter (fun a => 3 ^ 2 ∣ a)).card ≤ 2 := by
      have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 3) (j := 2)
        (by norm_num) (by omega)).2
      have hdiv : M / 3 ^ 2 ≤ 2 := by omega
      omega
    have hcz : ∀ j ∈ Finset.Icc 3 M, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 := by
      intro j hj; rw [Finset.mem_Icc] at hj
      have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 3) (j := j)
        (by norm_num) (by omega)).2
      have hpow : 27 ≤ 3 ^ j :=
        le_trans (by norm_num : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_right (by norm_num) hj.1)
      have hdiv0 : M / 3 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at h1
    have hsum0 : ∑ j ∈ Finset.Icc 3 M, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 :=
      Finset.sum_eq_zero hcz
    omega
  by_cases hsub9 : (consecInterval x M).filter (fun b => 9 ∣ b) ⊆ B₀
  · by_cases hsub6 : (consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀
    · -- All multiples of `9` and all multiples of `6` in `I` lie in `B₀`.
      -- Wait: check if deficit at `3` could still be `2`? No! `∑_{b ∈ B₀} v_3(b) ≥ 6` unless `R.factorization 3 ≤ 0`!
      let I₉ := (consecInterval x M).filter (fun b => 9 ∣ b)
      let I₆ := (consecInterval x M).filter (fun b => 6 ∣ b)
      have hI₉_2 : 2 ≤ I₉.card := by
        have h := card_multiples_Icc_ge x M 9 (by norm_num)
        change M / 9 ≤ I₉.card at h
        have hdiv : 2 ≤ M / 9 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
        omega
      have hI₆_3 : 3 ≤ I₆.card := by
        have h := card_multiples_Icc_ge x M 6 (by norm_num)
        change M / 6 ≤ I₆.card at h
        have hdiv : 3 ≤ M / 6 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
        omega
      -- Every element of `I₉` has `v_3 ≥ 2`, and every element of `I₆ \ I₉` has `v_3 ≥ 1`.
      -- Moreover `I₉ ∩ I₆ = I.filter (18 ∣ ·)`. Notice if `I₉.card ≥ 3` we get `3 * 2 = 6 ≤ ∑ B₀, v_3`;
      -- if `I₉.card = 2`, then `(I₉ ∩ I₆).card ≤ 1` (two multiples of `18` differ by `18`, so their midpoint `b₁ + 9` is also in `I₉`!),
      -- hence `(I₆ \ I₉).card ≥ 3 - 1 = 2`, giving `2 * 2 + 2 * 1 = 6 ≤ ∑ B₀, v_3`!
      have hI₁₈_le : (I₉ ∩ I₆).card ≤ 1 ∨ 3 ≤ I₉.card := by
        by_cases h3 : 3 ≤ I₉.card
        · exact Or.inr h3
        · left
          by_contra hgt
          have h2 : 2 ≤ (I₉ ∩ I₆).card := by omega
          obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
          have hu' := Finset.mem_filter.mp (Finset.mem_inter.mp hu).1
          have hv' := Finset.mem_filter.mp (Finset.mem_inter.mp hv).1
          have hu₆ := (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2
          have hv₆ := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
          have hu₁₈ : 18 ∣ u := (by norm_num : Nat.lcm 9 6 = 18) ▸ Nat.lcm_dvd hu'.2 hu₆
          have hv₁₈ : 18 ∣ v := (by norm_num : Nat.lcm 9 6 = 18) ▸ Nat.lcm_dvd hv'.2 hv₆
          rcases lt_or_gt_of_ne huv with hlt | hgt'
          · have hm_I : u + 9 ∈ consecInterval x M := by
              have huI := Finset.mem_Icc.mp hu'.1
              have hvI := Finset.mem_Icc.mp hv'.1
              have hdiff : u + 18 ≤ v := by
                obtain ⟨q₁, hq1⟩ := hu₁₈; obtain ⟨q₂, hq2⟩ := hv₁₈
                have : q₁ < q₂ := by by_contra hle; nlinarith
                omega
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hm_9 : 9 ∣ u + 9 := dvd_add (dvd_trans (by norm_num) hu₁₈) dvd_rfl
            have hmem : u + 9 ∈ I₉ := Finset.mem_filter.mpr ⟨hm_I, hm_9⟩
            have hm_ne_u : u + 9 ≠ u := by omega
            have hm_ne_v : u + 9 ≠ v := by
              obtain ⟨q₁, hq1⟩ := hu₁₈; obtain ⟨q₂, hq2⟩ := hv₁₈
              have : q₁ < q₂ := by by_contra hle; nlinarith
              omega
            have h3sub : {u, v, u + 9} ⊆ I₉ := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact (Finset.mem_inter.mp hu).1
              · exact (Finset.mem_inter.mp hv).1
              · exact hmem
            have h3c := Finset.card_le_card h3sub
            rw [Finset.card_insert_of_notMem (by simp [huv]),
                Finset.card_insert_of_notMem (by simp [hm_ne_v.symm]), Finset.card_singleton] at h3c
            omega
          · have hm_I : v + 9 ∈ consecInterval x M := by
              have huI := Finset.mem_Icc.mp hu'.1
              have hvI := Finset.mem_Icc.mp hv'.1
              have hdiff : v + 18 ≤ u := by
                obtain ⟨q₁, hq1⟩ := hu₁₈; obtain ⟨q₂, hq2⟩ := hv₁₈
                have : q₂ < q₁ := by by_contra hle; nlinarith
                omega
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hm_9 : 9 ∣ v + 9 := dvd_add (dvd_trans (by norm_num) hv₁₈) dvd_rfl
            have hmem : v + 9 ∈ I₉ := Finset.mem_filter.mpr ⟨hm_I, hm_9⟩
            have hm_ne_v : v + 9 ≠ v := by omega
            have hm_ne_u : v + 9 ≠ u := by
              obtain ⟨q₁, hq1⟩ := hu₁₈; obtain ⟨q₂, hq2⟩ := hv₁₈
              have : q₂ < q₁ := by by_contra hle; nlinarith
              omega
            have h3sub : {u, v, v + 9} ⊆ I₉ := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact (Finset.mem_inter.mp hu).1
              · exact (Finset.mem_inter.mp hv).1
              · exact hmem
            have h3c := Finset.card_le_card h3sub
            rw [Finset.card_insert_of_notMem (by simp [huv, hm_ne_u.symm]),
                Finset.card_insert_of_notMem (by simp), Finset.card_singleton] at h3c
            omega
      have hB₀_3 : 6 ≤ ∑ b ∈ B₀, b.factorization 3 := by
        have hU_sub : I₉ ∪ (I₆ \ I₉) ⊆ B₀ := Finset.union_subset hsub9 (Finset.Subset.trans Finset.sdiff_subset hsub6)
        have hsum_sub := Finset.sum_le_sum_of_subset hU_sub (f := fun b => b.factorization 3)
        rw [Finset.sum_union disjoint_sdiff_self_right] at hsum_sub
        have h9_val : ∀ b ∈ I₉, 2 ≤ b.factorization 3 := by
          intro b hb
          have hb_flt := Finset.mem_filter.mp hb
          have hb0 : b ≠ 0 := (pos_of_mem_consecInterval hb_flt.1).ne'
          exact ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hb0).mp
            (by simpa [show (3 ^ 2 : ℕ) = 9 by norm_num] using hb_flt.2)
        have h6_val : ∀ b ∈ I₆ \ I₉, 1 ≤ b.factorization 3 := by
          intro b hb
          have hb_flt := Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1
          have hb0 : b ≠ 0 := (pos_of_mem_consecInterval hb_flt.1).ne'
          exact ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hb0).mp
            (by simpa [pow_one] using dvd_trans (by norm_num : 3 ∣ 6) hb_flt.2)
        have hs9 : 2 * I₉.card ≤ ∑ b ∈ I₉, b.factorization 3 := by
          calc 2 * I₉.card = ∑ _b ∈ I₉, 2 := by simp [mul_comm]
            _ ≤ ∑ b ∈ I₉, b.factorization 3 := Finset.sum_le_sum h9_val
        have hs6 : (I₆ \ I₉).card ≤ ∑ b ∈ I₆ \ I₉, b.factorization 3 := by
          calc (I₆ \ I₉).card = ∑ _b ∈ I₆ \ I₉, 1 := by simp
            _ ≤ ∑ b ∈ I₆ \ I₉, b.factorization 3 := Finset.sum_le_sum h6_val
        rcases hI₁₈_le with h18 | h3
        · have hsd : (I₆ \ I₉).card + (I₆ ∩ I₉).card = I₆.card := Finset.card_sdiff_add_card_inter I₆ I₉
          rw [Finset.inter_comm] at hsd
          omega
        · omega
      have hfac3 := hR_fac 3 (by norm_num)
      have ht_fac3 : R.factorization 3 = 2 := by
        rw [hR_eq, show (18 : ℕ) = 2 * 3 ^ 2 by norm_num,
            Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
            Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
            (Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 ∣ 2)))]
      omega
    · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub6
      rw [Finset.mem_filter] at hw₁_flt
      have h6_pos : 0 < 6 := by norm_num
      have hbd2 : ((insert w₁ B₀).card + 1) * 3 ≤ M := by
        have h1 := Finset.card_insert_le w₁ B₀; omega
      obtain ⟨w₂, hw₂_I, hw₂_notIns, h3_w₂⟩ := exists_avoiding_multiple_5 x M 3 (insert w₁ B₀)
        (by norm_num) hbd2
      have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
      have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
      have hRw : R ∣ w₁ * w₂ := by rw [hR_eq, show (18 : ℕ) = 6 * 3 by norm_num]; exact mul_dvd_mul hw₁_flt.2 h3_w₂
      exact two_slots_of_two_dvd_5 hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR0
  · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub9
    rw [Finset.mem_filter] at hw₁_flt
    have hbd2 : (B₀.card + 1) * 2 ≤ M :=
      le_trans (Nat.mul_le_mul_right 2 (by omega : B₀.card + 1 ≤ 5)) (by omega)
    obtain ⟨w₂, hw₂_I, hw₂_notB₀, h2_w₂⟩ := exists_avoiding_multiple_5 x M 2 B₀ (by norm_num) hbd2
    exact two_slots_of_coprime_dvd_5 hR_eq (by norm_num : Nat.Coprime 9 2)
      (by norm_num) (by norm_num) hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₁_flt.2 h2_w₂

/-- Subcase `R = p ^ t` of `exists_two_slots_for_R_le_M_five` (`1 ≤ t`, `p ^ t ≤ M`). -/
private lemma two_slots_five_prime_pow {A B₀ : Finset ℕ} {x M R p t : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 4)
    (hM7 : 7 ≤ M) (hp : p.Prime) (ht1 : 1 ≤ t) (hR_eq : R = p ^ t) (hRM : R ≤ M)
    (hR_fac : ∀ q : ℕ, q.Prime →
      R.factorization q = (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ q : ℕ, q.Prime → R.factorization q ≤ ∑ b ∈ B₁, b.factorization q := by
  have hR0 : R ≠ 0 := by rw [hR_eq]; exact pow_ne_zero t hp.ne_zero
  have hR_fac_p : R.factorization p = t := by
    rw [hR_eq, hp.factorization_pow, Finsupp.single_eq_same]
  have hdef_p : (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) = t := by
    rw [← hR_fac p hp, hR_fac_p]
  by_cases ht1_eq : t = 1
  · subst ht1_eq
    obtain ⟨w, hw_I, hw_notB₀, hp_w⟩ := exists_prime_multiple_avoiding_five
      hA_card hA_pos hA_le hAgcd hB₀_I hp (by omega)
    exact two_slots_of_one_dvd_5 hw_I hw_notB₀ (by rw [hR_eq, pow_one]; exact hp_w) hR0
  · by_cases ht2_eq : t = 2
    · subst ht2_eq
      let J := (consecInterval x M \ B₀).filter (fun b => p ∣ b)
      rcases le_or_gt 2 J.card with hJ2 | hJ1
      · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hJ2
        rw [Finset.mem_filter, Finset.mem_sdiff] at hw₁ hw₂
        have hRw : R ∣ w₁ * w₂ := by
          rw [hR_eq, pow_two]; exact mul_dvd_mul hw₁.2 hw₂.2
        exact two_slots_of_two_dvd_5 hw₁.1.1 hw₂.1.1 hw₁.1.2 hw₂.1.2 hne hRw hR0
      · have hJ_subI : J ⊆ consecInterval x M :=
          Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset
        have hJ_disj : Disjoint B₀ J :=
          Finset.disjoint_left.mpr fun _ hb hj =>
            (Finset.mem_sdiff.mp (Finset.filter_subset _ _ hj)).2 hb
        have hdom := sum_factorization_le_consecInterval (x := x) hA_pos hA_le hp
        -- Partition `I` multiples of `p` into `(B₀ ∩ I_p)` and `J`: actually `I` split into `B₀ ∪ J` and `I \ (B₀ ∪ J)`:
        -- Every `b ∈ I \ (B₀ ∪ J)` has `¬ (p ∣ b)`, hence `b.factorization p = 0`!
        have hsumI_eq : ∑ b ∈ consecInterval x M, b.factorization p =
            ∑ b ∈ B₀, b.factorization p + ∑ b ∈ J, b.factorization p := by
          have hsub_BJ : B₀ ∪ J ⊆ consecInterval x M := Finset.union_subset hB₀_I hJ_subI
          rw [← Finset.sum_sdiff hsub_BJ, Finset.sum_union hJ_disj]
          have hzero : ∑ b ∈ consecInterval x M \ (B₀ ∪ J), b.factorization p = 0 := by
            apply Finset.sum_eq_zero
            intro b hb
            rw [Finset.mem_sdiff, Finset.mem_union] at hb
            have hnd : ¬ (p ∣ b) := fun hpd => hb.2 (Or.inr
              (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hb.1, fun hB => hb.2 (Or.inl hB)⟩, hpd⟩))
            exact Nat.factorization_eq_zero_of_not_dvd hnd
          omega
        refine ⟨J, hJ_subI, hJ_disj, by omega, ?_⟩
        intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hR_fac_p]; omega
        · have hnd : ¬ (q ∣ R) := fun hd => by
            rw [hR_eq] at hd
            exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
          rw [Nat.factorization_eq_zero_of_not_dvd hnd]
          exact Nat.zero_le _
    · -- `t ≥ 3`, `R = p ^ t ≤ M`.
      have ht3 : 3 ≤ t := by omega
      let e₁ := (t + 1) / 2
      let e₂ := t / 2
      have he12 : e₁ + e₂ = t := by dsimp [e₁, e₂]; omega
      by_cases h56 : 5 * p ^ e₁ ≤ M ∧ 6 * p ^ e₂ ≤ M
      · exact two_split_mults_five hB₀_card hR0 (pow_pos hp.pos e₁) (pow_pos hp.pos e₂)
          h56.1 h56.2 (by rw [hR_eq, ← pow_add, he12])
      · -- Only 4 finite `(p, t)` pairs fail `5 * p^e₁ ≤ p^t ∧ 6 * p^e₂ ≤ p^t`: `(2,3), (2,4), (2,5), (3,3)`.
        have hp_lt7 : p < 7 := by
          by_contra hp7
          have h5e1 : 5 * p ^ e₁ ≤ p ^ t := by
            have hsub_ge1 : 1 ≤ t - e₁ := by dsimp [e₁]; omega
            calc 5 * p ^ e₁ ≤ p * p ^ e₁ := Nat.mul_le_mul_right _ (by omega)
              _ = p ^ (1 + e₁) := by rw [pow_add, pow_one]
              _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos (by omega)
          have h6e2 : 6 * p ^ e₂ ≤ p ^ t := by
            have hsub_ge1 : 1 ≤ t - e₂ := by dsimp [e₂]; omega
            calc 6 * p ^ e₂ ≤ p * p ^ e₂ := Nat.mul_le_mul_right _ (by omega)
              _ = p ^ (1 + e₂) := by rw [pow_add, pow_one]
              _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos (by omega)
          exact h56 ⟨by rw [hR_eq] at hRM; omega, by rw [hR_eq] at hRM; omega⟩
        have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 := by
          have := hp.two_le
          by_contra hnone
          have hp4_or6 : p = 4 ∨ p = 6 := by omega
          rcases hp4_or6 with rfl | rfl
          · exact absurd hp (by decide)
          · exact absurd hp (by decide)
        rcases hp_cases with rfl | rfl | rfl
        · -- `p = 2`: if `t ≥ 6`, `5 * 2^e₁ ≤ 2^t ∧ 6 * 2^e₂ ≤ 2^t` holds!
          have ht_lt6 : t < 6 := by
            by_contra ht6
            have he1_sub : 3 ≤ t - e₁ := by dsimp [e₁]; omega
            have he2_sub : 3 ≤ t - e₂ := by dsimp [e₂]; omega
            have h5e1 : 5 * 2 ^ e₁ ≤ 2 ^ t := by
              calc 5 * 2 ^ e₁ ≤ 2 ^ 3 * 2 ^ e₁ := Nat.mul_le_mul_right _ (by norm_num)
                _ = 2 ^ (3 + e₁) := (pow_add 2 3 e₁).symm
                _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
            have h6e2 : 6 * 2 ^ e₂ ≤ 2 ^ t := by
              calc 6 * 2 ^ e₂ ≤ 2 ^ 3 * 2 ^ e₂ := Nat.mul_le_mul_right _ (by norm_num)
                _ = 2 ^ (3 + e₂) := (pow_add 2 3 e₂).symm
                _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact h56 ⟨by rw [hR_eq] at hRM; omega, by rw [hR_eq] at hRM; omega⟩
          have ht_cases : t = 3 ∨ t = 4 ∨ t = 5 := by omega
          rcases ht_cases with rfl | rfl | rfl
          · -- `(2, 3)`: `R = 8, 8 ≤ M`.
            have hR8 : R = 8 := by rw [hR_eq]; norm_num
            have hM8 : 8 ≤ M := by omega
            by_cases hM12 : 12 ≤ M
            · have hc3 : 3 ≤ M / 2 ^ 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
              obtain ⟨w₁, hw₁_I, hw₁_notB₀, h4_w₁⟩ := exists_pow_multiple_avoiding_of_3_le_div_five
                hA_card hA_pos hA_le hAgcd hB₀_I (p := 2) (by norm_num) (by norm_num) hc3 (by omega)
              have h4_eq : (2 ^ 2 : ℕ) = 4 := by norm_num
              rw [h4_eq] at h4_w₁
              have hbd2 : ((insert w₁ B₀).card + 1) * 2 ≤ M := by
                have h1 := Finset.card_insert_le w₁ B₀; omega
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h2_w₂⟩ :=
                exists_avoiding_multiple_5 x M 2 (insert w₁ B₀) (by norm_num) hbd2
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                (by rw [hR8, show (8 : ℕ) = 4 * 2 by norm_num]; exact mul_dvd_mul h4_w₁ h2_w₂) hR0
            · -- `8 ≤ M ≤ 11`, `R = 8`: `∑ A, v_2 ≤ 4 + 2 + 1 = 7`.
              have hM_le11 : M ≤ 11 := by omega
              have hsumA_le7 : ∑ a ∈ A, a.factorization 2 ≤ 7 := by
                have h1 := sum_factorization_eq_sum_card_Icc_5 hA_pos hA_le (by norm_num : Nat.Prime 2)
                have hc1 := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 1)
                  (by norm_num) (by omega)).1
                have hc2 : (A.filter (fun a => 2 ^ 2 ∣ a)).card ≤ 2 := by
                  have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 2)
                    (by norm_num) (by omega)).2
                  have hd : M / 2 ^ 2 ≤ 2 := by omega
                  omega
                have hc3 : (A.filter (fun a => 2 ^ 3 ∣ a)).card ≤ 1 := by
                  have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 3)
                    (by norm_num) (by omega)).2
                  have hd : M / 2 ^ 3 ≤ 1 := by omega
                  omega
                have hcz : ∀ j ∈ Finset.Icc 4 M, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 := by
                  intro j hj; rw [Finset.mem_Icc] at hj
                  have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := j)
                    (by norm_num) (by omega)).2
                  have hpow : 16 ≤ 2 ^ j :=
                    le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hj.1)
                  have hd0 : M / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                  omega
                have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (Finset.Icc 4 M))) := by
                  ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
                    Finset.sum_insert (by simp)] at h1
                have hsum0 : ∑ j ∈ Finset.Icc 4 M, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 :=
                  Finset.sum_eq_zero hcz
                omega
              by_cases hsub4 : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆ B₀
              · have hB₀_4 : 2 ≤ (B₀.filter (fun b => 2 ^ 2 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 2 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hsub4 (Finset.mem_filter.mpr hb), by simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 4 (by norm_num)
                  have hd : 2 ≤ M / 4 := by omega
                  exact le_trans hd (le_trans h2 (Finset.card_le_card h1))
                have hB₀_2 : 2 ≤ (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by
                  have hsub24 : B₀.filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 1 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hb.1, dvd_trans (by norm_num) hb.2⟩
                  exact le_trans hB₀_4 (Finset.card_le_card hsub24)
                have hB₀_8 : 1 ≤ (B₀.filter (fun b => 2 ^ 3 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 3 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hsub4 (Finset.mem_filter.mpr ⟨hb.1, dvd_trans (by norm_num) hb.2⟩),
                      by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 8 (by norm_num)
                  have hd : 1 ≤ M / 8 := by omega
                  exact le_trans hd (le_trans h2 (Finset.card_le_card h1))
                have hB₀_sum5 : 5 ≤ ∑ b ∈ B₀, b.factorization 2 := by
                  have h1 := sum_card_Icc_le_sum_factorization_5 (K := 3) hB₀_I (by norm_num : Nat.Prime 2)
                  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
                  rw [hIcc3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                      Finset.sum_singleton] at h1
                  omega
                omega
              · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub4
                rw [Finset.mem_filter] at hw₁_flt
                by_cases h8_w1 : 8 ∣ w₁
                · exact two_slots_of_one_dvd_5 hw₁_flt.1 hw₁_notB₀ (hR8 ▸ h8_w1) hR0
                · have hw₁_pos : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_flt.1).ne'
                  have hw1_v2 : w₁.factorization 2 = 2 := by
                    have hge2 : 2 ≤ w₁.factorization 2 :=
                      ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hw₁_pos).mp
                        (by simpa [show (2 ^ 2 : ℕ) = 4 by norm_num] using hw₁_flt.2)
                    have hlt3 : w₁.factorization 2 < 3 := by
                      by_contra h3
                      have h8w : 8 ∣ w₁ := (by norm_num : (8 : ℕ) = 2 ^ 3) ▸
                        (((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hw₁_pos).mpr (by omega))
                      exact h8_w1 h8w
                    omega
                  have hB1_I : insert w₁ B₀ ⊆ consecInterval x M := Finset.insert_subset hw₁_flt.1 hB₀_I
                  have hdef_ins : 1 ≤ (∑ a ∈ A, a.factorization 2) -
                      (∑ b ∈ insert w₁ B₀, b.factorization 2) := by
                    rw [Finset.sum_insert hw₁_notB₀]
                    omega
                  obtain ⟨w₂, hw₂_I, hw₂_notIns, h2_w₂⟩ := exists_prime_multiple_avoiding_five
                    hA_card hA_pos hA_le hAgcd hB1_I (by norm_num : Nat.Prime 2) hdef_ins
                  have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
                  have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
                  exact two_slots_of_two_dvd_5 hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                    (by rw [hR8, show (8 : ℕ) = 4 * 2 by norm_num]; exact mul_dvd_mul hw₁_flt.2 h2_w₂) hR0
          · -- `(2, 4)`: `R = 16, 16 ≤ M`.
            have hR16 : R = 16 := by rw [hR_eq]; norm_num
            have hM16 : 16 ≤ M := by omega
            by_cases hsub8 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀
            · by_cases hM24 : 24 ≤ M
              · exact two_distinct_mults_five hB₀_card hR0 (by norm_num) (by omega : 6 * 4 ≤ M)
                  (hR16 ▸ dvd_rfl)
              · -- `16 ≤ M ≤ 23`: `∑ A, v_2 ≤ 11`, and `B₀` already covers all `≥ 2` multiples of `8`,
                -- leaving `≥ 2` multiples of `4` outside `B₀` (or `v_2(B₀) ≥ 9`, contradicting `v_2(R) = 4`).
                have hM_lt24 : M ≤ 23 := by omega
                let J4 := (consecInterval x M \ B₀).filter (fun b => 4 ∣ b)
                rcases le_or_gt 2 J4.card with hJ4_2 | hJ4_1
                · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hJ4_2
                  rw [Finset.mem_filter, Finset.mem_sdiff] at hw₁ hw₂
                  exact two_slots_of_two_dvd_5 hw₁.1.1 hw₂.1.1 hw₁.1.2 hw₂.1.2 hne
                    (by rw [hR16, show (16 : ℕ) = 4 * 4 by norm_num]; exact mul_dvd_mul hw₁.2 hw₂.2) hR0
                · have hI4_4 : 4 ≤ ((consecInterval x M).filter (fun b => 4 ∣ b)).card := by
                    have h := card_multiples_Icc_ge x M 4 (by norm_num)
                    change M / 4 ≤ ((consecInterval x M).filter (fun b => 4 ∣ b)).card at h
                    have hd : 4 ≤ M / 4 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
                    omega
                  have hB₀_4 : 3 ≤ (B₀.filter (fun b => 2 ^ 2 ∣ b)).card := by
                    have hsub_u : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆
                        B₀.filter (fun b => 4 ∣ b) ∪ J4 := by
                      intro b hb; rw [Finset.mem_filter] at hb
                      by_cases hbB₀ : b ∈ B₀
                      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbB₀, hb.2⟩)
                      · exact Finset.mem_union_right _
                          (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩, hb.2⟩)
                    have h1 := Finset.card_le_card hsub_u
                    have h2 := Finset.card_union_le (B₀.filter (fun b => 4 ∣ b)) J4
                    have heq4 : B₀.filter (fun b => 4 ∣ b) = B₀.filter (fun b => 2 ^ 2 ∣ b) := by
                      ext b; simp [show (4 : ℕ) = 2 ^ 2 by norm_num]
                    rw [heq4] at h1 h2
                    omega
                  have hB₀_2 : 3 ≤ (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by
                    have hsub24 : B₀.filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 1 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hb.1, dvd_trans (by norm_num) hb.2⟩
                    exact le_trans hB₀_4 (Finset.card_le_card hsub24)
                  have hB₀_8 : 2 ≤ (B₀.filter (fun b => 2 ^ 3 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 3 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub8 (Finset.mem_filter.mpr hb),
                        by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 8 (by norm_num)
                    have hd : 2 ≤ M / 8 := by omega
                    exact le_trans hd (le_trans h2 (Finset.card_le_card h1))
                  have hB₀_16 : 1 ≤ (B₀.filter (fun b => 2 ^ 4 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 16 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 4 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub8 (Finset.mem_filter.mpr ⟨hb.1, dvd_trans (by norm_num) hb.2⟩),
                        by simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 16 (by norm_num)
                    have hd : 1 ≤ M / 16 := by omega
                    exact le_trans hd (le_trans h2 (Finset.card_le_card h1))
                  have hB₀_sum9 : 9 ≤ ∑ b ∈ B₀, b.factorization 2 := by
                    have h1 := sum_card_Icc_le_sum_factorization_5 (K := 4) hB₀_I (by norm_num : Nat.Prime 2)
                    have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
                    rw [hIcc4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                        Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                    omega
                  have hA_sum11 : ∑ a ∈ A, a.factorization 2 ≤ 11 := by
                    have h1 := sum_factorization_eq_sum_card_Icc_5 hA_pos hA_le (by norm_num : Nat.Prime 2)
                    have hc1 := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 1)
                      (by norm_num) (by omega)).1
                    have hc2 := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 2)
                      (by norm_num) (by omega)).1
                    have hc3 : (A.filter (fun a => 2 ^ 3 ∣ a)).card ≤ 2 := by
                      have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 3)
                        (by norm_num) (by omega)).2
                      have hd : M / 2 ^ 3 ≤ 2 := by omega
                      omega
                    have hc4 : (A.filter (fun a => 2 ^ 4 ∣ a)).card ≤ 1 := by
                      have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := 4)
                        (by norm_num) (by omega)).2
                      have hd : M / 2 ^ 4 ≤ 1 := by omega
                      omega
                    have hcz : ∀ j ∈ Finset.Icc 5 M, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 := by
                      intro j hj; rw [Finset.mem_Icc] at hj
                      have h := (card_filter_le_four_and_div_5 hA_card hA_pos hA_le hAgcd (p := 2) (j := j)
                        (by norm_num) (by omega)).2
                      have hpow : 32 ≤ 2 ^ j :=
                        le_trans (by norm_num : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) hj.1)
                      have hd0 : M / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                      omega
                    have hsplit : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (insert 4 (Finset.Icc 5 M)))) := by
                      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
                        Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at h1
                    have hsum0 : ∑ j ∈ Finset.Icc 5 M, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 :=
                      Finset.sum_eq_zero hcz
                    omega
                  omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub8
              rw [Finset.mem_filter] at hw₁_flt
              have hbd2 : ((insert w₁ B₀).card + 1) * 2 ≤ M := by
                have h1 := Finset.card_insert_le w₁ B₀; omega
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h2_w₂⟩ :=
                exists_avoiding_multiple_5 x M 2 (insert w₁ B₀) (by norm_num) hbd2
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              exact two_slots_of_two_dvd_5 hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                (by rw [hR16, show (16 : ℕ) = 8 * 2 by norm_num]; exact mul_dvd_mul hw₁_flt.2 h2_w₂) hR0
          · -- `(2, 5)`: `R = 32, 32 ≤ M`.
            have hR32 : R = 32 := by rw [hR_eq]; norm_num
            have hM32 : 32 ≤ M := by omega
            by_cases hM40 : 40 ≤ M
            · exact two_split_mults_five hB₀_card hR0 (by norm_num) (by norm_num)
                (by omega : 5 * 8 ≤ M) (by omega : 6 * 4 ≤ M) (hR32 ▸ dvd_rfl)
            · have hc3 : 3 ≤ M / 2 ^ 3 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
              obtain ⟨w₁, hw₁_I, hw₁_notB₀, h8_w₁⟩ := exists_pow_multiple_avoiding_of_3_le_div_five
                hA_card hA_pos hA_le hAgcd hB₀_I (p := 2) (by norm_num) (by norm_num) hc3 (by omega)
              rw [show (2 ^ 3 : ℕ) = 8 by norm_num] at h8_w₁
              have hbd2 : ((insert w₁ B₀).card + 1) * 4 ≤ M := by
                have h1 := Finset.card_insert_le w₁ B₀; omega
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h4_w₂⟩ :=
                exists_avoiding_multiple_5 x M 4 (insert w₁ B₀) (by norm_num) hbd2
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                (by rw [hR32, show (32 : ℕ) = 8 * 4 by norm_num]; exact mul_dvd_mul h8_w₁ h4_w₂) hR0
        · -- `p = 3`: if `t ≥ 4`, `5 * 3^e₁ ≤ 3^t ∧ 6 * 3^e₂ ≤ 3^t` holds!
          have ht_lt4 : t < 4 := by
            by_contra ht4
            have he1_sub : 2 ≤ t - e₁ := by dsimp [e₁]; omega
            have he2_sub : 2 ≤ t - e₂ := by dsimp [e₂]; omega
            have h5e1 : 5 * 3 ^ e₁ ≤ 3 ^ t := by
              calc 5 * 3 ^ e₁ ≤ 3 ^ 2 * 3 ^ e₁ := Nat.mul_le_mul_right _ (by norm_num)
                _ = 3 ^ (2 + e₁) := (pow_add 3 2 e₁).symm
                _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
            have h6e2 : 6 * 3 ^ e₂ ≤ 3 ^ t := by
              calc 6 * 3 ^ e₂ ≤ 3 ^ 2 * 3 ^ e₂ := Nat.mul_le_mul_right _ (by norm_num)
                _ = 3 ^ (2 + e₂) := (pow_add 3 2 e₂).symm
                _ ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact h56 ⟨by rw [hR_eq] at hRM; omega, by rw [hR_eq] at hRM; omega⟩
          have ht3_eq : t = 3 := by omega
          subst ht3_eq
          have hR27 : R = 27 := by rw [hR_eq]; norm_num
          have hM27 : 27 ≤ M := by omega
          have hc3 : 3 ≤ M / 3 ^ 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
          obtain ⟨w₁, hw₁_I, hw₁_notB₀, h9_w₁⟩ := exists_pow_multiple_avoiding_of_3_le_div_five
            hA_card hA_pos hA_le hAgcd hB₀_I (p := 3) (by norm_num) (by norm_num) hc3 (by omega)
          rw [show (3 ^ 2 : ℕ) = 9 by norm_num] at h9_w₁
          have hbd2 : ((insert w₁ B₀).card + 1) * 3 ≤ M := by
            have h1 := Finset.card_insert_le w₁ B₀; omega
          obtain ⟨w₂, hw₂_I, hw₂_notIns, h3_w₂⟩ :=
            exists_avoiding_multiple_5 x M 3 (insert w₁ B₀) (by norm_num) hbd2
          have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
          have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
          exact two_slots_of_two_dvd_5 hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
            (by rw [hR27, show (27 : ℕ) = 9 * 3 by norm_num]; exact mul_dvd_mul h9_w₁ h3_w₂) hR0
        · -- `p = 5`: for all `t ≥ 3`, `5 * 5^e₁ ≤ 5^t ∧ 6 * 5^e₂ ≤ 5^t` holds!
          exfalso
          have he1_sub : 1 ≤ t - e₁ := by dsimp [e₁]; omega
          have he2_sub : 2 ≤ t - e₂ := by dsimp [e₂]; omega
          have h5e1 : 5 * 5 ^ e₁ ≤ 5 ^ t := by
            calc 5 * 5 ^ e₁ = 5 ^ (1 + e₁) := by rw [pow_add, pow_one]
              _ ≤ 5 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h6e2 : 6 * 5 ^ e₂ ≤ 5 ^ t := by
            calc 6 * 5 ^ e₂ ≤ 5 ^ 2 * 5 ^ e₂ := Nat.mul_le_mul_right _ (by norm_num)
              _ = 5 ^ (2 + e₂) := (pow_add 5 2 e₂).symm
              _ ≤ 5 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact h56 ⟨by rw [hR_eq] at hRM; omega, by rw [hR_eq] at hRM; omega⟩

/-- **Master Two-Slot Residual Theorem (`R ≤ M` for `|A| = 5`)**:
    assuming `A.card = 5`, `A.gcd id = 1`, `7 ≤ M`, `B₀ ⊆ consecInterval x M` with
    `B₀.card ≤ 4`, `0 < R ≤ M`, and `R.factorization p = (∑ A, v_p) - (∑ B₀, v_p)`,
    there exists `B₁ ⊆ consecInterval x M` disjoint from `B₀` with `B₁.card ≤ 2`
    absorbing `R`. -/
theorem exists_two_slots_for_R_le_M_five {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 4)
    (hM7 : 7 ≤ M) (hR_pos : 0 < R) (hRM : R ≤ M)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  by_cases hR1 : R = 1
  · refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp, ?_⟩
    intro p _hp
    simp [hR1]
  · have hR_gt1 : 1 < R := by omega
    have hR_pf_ne : R.primeFactors.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by
        intro he
        have h := Nat.prod_factorization_pow_eq_self hR_pos.ne'
        rw [Finsupp.prod, Nat.support_factorization, he, Finset.prod_empty] at h
        omega)
    by_cases hpf1 : R.primeFactors.card = 1
    · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hpf1
      have hp_mem : p ∈ R.primeFactors := by rw [hp_eq]; exact Finset.mem_singleton_self p
      have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpd : p ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp_mem).2
      have ht1 : 1 ≤ R.factorization p :=
        (hp_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hpd)
      have hR_pp : R = p ^ (R.factorization p) := by
        calc R = R.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hR_pos.ne').symm
          _ = ∏ q ∈ R.primeFactors, q ^ (R.factorization q) := by rw [Finsupp.prod, Nat.support_factorization]
          _ = p ^ (R.factorization p) := by rw [hp_eq, Finset.prod_singleton]
      exact two_slots_five_prime_pow hA_card hA_pos hA_le hAgcd hB₀_I hB₀_card hM7
        hp_pr ht1 hR_pp hRM hR_fac
    · -- `R` has `≥ 2` distinct prime factors.
      -- Let `p` maximize `q = p ^ R.factorization p` over `p ∈ R.primeFactors`.
      let g : ℕ → ℕ := fun p => p ^ (R.factorization p)
      obtain ⟨p, hp_mem, hp_max⟩ := Finset.exists_max_image R.primeFactors g hR_pf_ne
      let e := R.factorization p
      let q := g p
      have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have he1 : 1 ≤ e := by
        have hpd := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp_mem).2
        exact (hp_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hpd)
      have hq_pos : 0 < q := pow_pos hp_pr.pos e
      let P_rest := R.primeFactors.erase p
      have hP_rest_ne : P_rest.Nonempty := by
        have hc : 1 < R.primeFactors.card := by
          have := Finset.card_pos.mpr hR_pf_ne; omega
        have : 0 < P_rest.card := by rw [Finset.card_erase_of_mem hp_mem]; omega
        exact Finset.card_pos.mp this
      let D₁ : ℕ := ∏ r ∈ P_rest, r ^ (R.factorization r)
      have hD₁_pos : 0 < D₁ := Finset.prod_pos (fun r hr =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hr).2).pos _)
      have hD₁_ge2 : 2 ≤ D₁ := by
        obtain ⟨r, hr⟩ := hP_rest_ne
        have hr_mem := (Finset.mem_erase.mp hr).2
        have hr_pr := Nat.prime_of_mem_primeFactors hr_mem
        have hrd := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hr_mem).2
        have h1 : 1 ≤ R.factorization r :=
          (hr_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hrd)
        have h2 : r ∣ D₁ := dvd_trans (dvd_pow_self r (by omega))
          (Finset.dvd_prod_of_mem (fun x => x ^ R.factorization x) hr)
        exact le_trans hr_pr.two_le (Nat.le_of_dvd hD₁_pos h2)
      have hR_split : R = D₁ * q := by
        calc R = R.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hR_pos.ne').symm
          _ = ∏ r ∈ R.primeFactors, r ^ (R.factorization r) := by rw [Finsupp.prod, Nat.support_factorization]
          _ = q * D₁ := (Finset.mul_prod_erase R.primeFactors (fun x => x ^ R.factorization x) hp_mem).symm
          _ = D₁ * q := mul_comm q D₁
      have hcop_D1_q : Nat.Coprime D₁ q := by
        apply Nat.Coprime.prod_left
        intro r hr
        have hmem := Finset.mem_erase.mp hr
        have hr_pr := Nat.prime_of_mem_primeFactors hmem.2
        exact ((Nat.coprime_primes hr_pr hp_pr).mpr hmem.1).pow _ _
      by_cases hq5 : 5 ≤ q
      · -- **Case A (`5 ≤ q`)**: `5 * D₁ ≤ D₁ * q = R ≤ M`.
        have h5D1 : 5 * D₁ ≤ M := by
          have : 5 * D₁ ≤ q * D₁ := Nat.mul_le_mul_right D₁ hq5
          have hqD : q * D₁ = R := by rw [hR_split, mul_comm]
          omega
        obtain ⟨w₁, hw₁_I, hw₁_notB₀, hD₁_w₁⟩ := exists_avoiding_multiple_5 x M D₁ B₀ hD₁_pos
          (le_trans (Nat.mul_le_mul_right D₁ (by omega : B₀.card + 1 ≤ 5)) h5D1)
        by_cases hsub_q : (consecInterval x M).filter (fun b => q ∣ b) ⊆ B₀
        · -- Layer-cake at `p^e`: since `q = p^e` avoids no elements outside `B₀`, deficit `≤ (4 - M/q) * (e - 1)`.
          have hdef_le := layer_cake_deficit_le_of_pow_subset_five hA_card hA_pos hA_le hAgcd hB₀_I
            hp_pr he1 (by simpa [q, g, e] using hsub_q)
          have hfac_p := hR_fac p hp_pr
          have he_ge2 : 2 ≤ e := by
            by_contra hlt2
            have he1_eq : e = 1 := by omega
            rw [he1_eq] at hdef_le
            simp only [Nat.sub_self, mul_zero] at hdef_le
            change e = ∑ a ∈ A, a.factorization p - ∑ b ∈ B₀, b.factorization p at hfac_p
            omega
          have hMq_lt3 : M / (p ^ e) < 3 := by
            by_contra hge3
            have h1 : (4 - M / p ^ e) * (e - 1) ≤ 1 * (e - 1) := Nat.mul_le_mul_right _ (by omega)
            rw [one_mul] at h1
            change e = ∑ a ∈ A, a.factorization p - ∑ b ∈ B₀, b.factorization p at hfac_p
            omega
          have hD1_eq2 : D₁ = 2 := by
            have h2q_le : 2 * q ≤ M := by
              have : 2 * q ≤ D₁ * q := Nat.mul_le_mul_right q hD₁_ge2
              omega
            have hD1_lt3 : D₁ < 3 := by
              by_contra h3
              have h3p_le : 3 * (p ^ e) ≤ M := by
                calc 3 * (p ^ e) = q * 3 := by rw [mul_comm]
                  _ ≤ q * D₁ := Nat.mul_le_mul_left q (by omega)
                  _ = R := by rw [hR_split, mul_comm]
                  _ ≤ M := hRM
              have hdiv3 : 3 ≤ M / (p ^ e) := (Nat.le_div_iff_mul_le hq_pos).mpr h3p_le
              omega
            omega
          have hp_ge3 : 3 ≤ p := by
            have := hp_pr.two_le
            by_contra hlt3
            have hp2 : p = 2 := by omega
            have h2_q : 2 ∣ q := by
              have h2e : 1 ≤ R.factorization 2 := by rw [← hp2]; exact he1
              dsimp [q]; rw [hp2]; exact dvd_pow_self 2 (by omega)
            have h2_D1 : 2 ∣ D₁ := by rw [hD1_eq2]
            have h2_cop : 2 ∣ Nat.gcd D₁ q := Nat.dvd_gcd h2_D1 h2_q
            rw [hcop_D1_q.gcd_eq_one] at h2_cop
            omega
          have hR_2pe : R = 2 * p ^ e := by rw [hR_split, hD1_eq2]
          by_cases he3 : 3 ≤ e
          · -- Split `2 * p^(e/2)` and `p^(e - e/2)`.
            let a := e / 2
            let b := e - e / 2
            have hab : a + b = e := by dsimp [a, b]; omega
            have ha1 : 1 ≤ a := by dsimp [a]; omega
            have hb2 : 2 ≤ b := by dsimp [b]; omega
            have ha2_or_b2 : 2 ≤ b ∧ 1 ≤ a := ⟨hb2, ha1⟩
            have hp2_ge9 : 9 ≤ p ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hp_ge3 2)
            have h5_d1 : 5 * (2 * p ^ a) ≤ M := by
              have h10p : 10 * p ^ a ≤ 2 * p ^ e := by
                have h5pb : 5 ≤ p ^ b := le_trans (by omega : 5 ≤ p ^ 2)
                  (Nat.pow_le_pow_right hp_pr.pos hb2)
                calc 10 * p ^ a = 2 * (5 * p ^ a) := by ring
                  _ ≤ 2 * (p ^ b * p ^ a) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h5pb)
                  _ = 2 * p ^ (b + a) := by rw [pow_add]
                  _ = 2 * p ^ e := by rw [add_comm, hab]
              omega
            have h6_d2 : 6 * p ^ b ≤ M := by
              have h3pa : 3 ≤ p ^ a := le_trans hp_ge3 (Nat.le_self_pow (by omega) p)
              have h6pb : 6 * p ^ b ≤ 2 * p ^ e := by
                calc 6 * p ^ b = 2 * (3 * p ^ b) := by ring
                  _ ≤ 2 * (p ^ a * p ^ b) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h3pa)
                  _ = 2 * p ^ (a + b) := by rw [pow_add]
                  _ = 2 * p ^ e := by rw [hab]
              omega
            exact two_split_mults_five hB₀_card hR_pos.ne' (mul_pos (by norm_num) (pow_pos hp_pr.pos a))
              (pow_pos hp_pr.pos b) h5_d1 h6_d2 (by rw [hR_2pe, ← hab, pow_add]; ring_nf; exact dvd_rfl)
          · -- `e = 2`, `R = 2 * p^2`.
            have he_eq2 : e = 2 := by omega
            by_cases hp5 : 5 ≤ p
            · have h5_d1 : 5 * (2 * p) ≤ M := by
                have : 10 * p ≤ 2 * p ^ 2 := by nlinarith
                rw [hR_2pe, he_eq2] at hRM; omega
              have h6_d2 : 6 * p ≤ M := by
                have : 6 * p ≤ 2 * p ^ 2 := by nlinarith
                rw [hR_2pe, he_eq2] at hRM; omega
              exact two_split_mults_five hB₀_card hR_pos.ne' (by omega) hp_pr.pos
                h5_d1 h6_d2 (by rw [hR_2pe, he_eq2, pow_two]; ring_nf; exact dvd_rfl)
            · have hp_ne4 : p ≠ 4 := fun h => by rw [h] at hp_pr; exact absurd hp_pr (by decide)
              have hp3 : p = 3 := by omega
              have hR18 : R = 18 := by rw [hR_2pe, he_eq2, hp3]; norm_num
              have hM_lo : 18 ≤ M := by omega
              have hM_hi : M ≤ 26 := by
                have hq9 : p ^ e = 9 := by rw [hp3, he_eq2]; norm_num
                have : M / 9 < 3 := hq9 ▸ hMq_lt3
                omega
              exact two_slots_five_R18 hA_card hA_pos hA_le hAgcd hB₀_I hB₀_card hM_lo hM_hi hR18 hR_fac
        · obtain ⟨w₂, hw₂_flt, hw₂_notB₀⟩ := Finset.not_subset.mp hsub_q
          rw [Finset.mem_filter] at hw₂_flt
          exact two_slots_of_coprime_dvd_5 hR_split hcop_D1_q hD₁_pos hq_pos
            hw₁_I hw₂_flt.1 hw₁_notB₀ hw₂_notB₀ hD₁_w₁ hw₂_flt.2
      · -- **Case B (`q ≤ 4`)**: every prime-power component of `R` is `≤ 4` (`∈ {2, 3, 4}`),
        -- and `R` has `≥ 2` distinct prime factors, so `R ∈ {6, 12}`!
        have hcomp_le4 : ∀ r ∈ R.primeFactors, r ^ (R.factorization r) ≤ 4 := fun r hr =>
          le_trans (hp_max r hr) (by omega)
        have hpf_sub : R.primeFactors ⊆ {2, 3} := by
          intro r hr
          have hr_pr := Nat.prime_of_mem_primeFactors hr
          have hrd := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hr).2
          have hr1 : 1 ≤ R.factorization r :=
            (hr_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hrd)
          have hr_le : r ≤ r ^ (R.factorization r) := Nat.le_self_pow (by omega) r
          have hr4 : r ≤ 4 := le_trans hr_le (hcomp_le4 r hr)
          have hr2 := hr_pr.two_le
          have hr_ne4 : r ≠ 4 := fun h => by rw [h] at hr_pr; norm_num at hr_pr
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        have hc_ge2 : 2 ≤ R.primeFactors.card := by
          have := Finset.card_pos.mpr hR_pf_ne; omega
        have hpf_eq : R.primeFactors = {2, 3} :=
          Finset.eq_of_subset_of_card_le hpf_sub (by simp; omega)
        have h2_mem : 2 ∈ R.primeFactors := by rw [hpf_eq]; simp
        have h3_mem : 3 ∈ R.primeFactors := by rw [hpf_eq]; simp
        have he2_pos : 1 ≤ R.factorization 2 := by
          have h := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp h2_mem).2
          exact ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hR_pos.ne').mp
            (by simpa only [pow_one] using h)
        have he3_pos : 1 ≤ R.factorization 3 := by
          have h := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp h3_mem).2
          exact ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hR_pos.ne').mp
            (by simpa only [pow_one] using h)
        have h2_bnd : 2 ^ (R.factorization 2) ≤ 4 := hcomp_le4 2 h2_mem
        have h3_bnd : 3 ^ (R.factorization 3) ≤ 4 := hcomp_le4 3 h3_mem
        have he3_eq1 : R.factorization 3 = 1 := by
          by_contra hne1
          have hge2 : 2 ≤ R.factorization 3 := by omega
          have : 9 ≤ 3 ^ (R.factorization 3) :=
            le_trans (by norm_num : 9 ≤ 3 ^ 2) (Nat.pow_le_pow_right (by norm_num) hge2)
          omega
        have he2_le2 : R.factorization 2 ≤ 2 := by
          by_contra hgt2
          have hge3 : 3 ≤ R.factorization 2 := by omega
          have : 8 ≤ 2 ^ (R.factorization 2) :=
            le_trans (by norm_num : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) hge3)
          omega
        have hR_prod : R = 2 ^ (R.factorization 2) * 3 ^ (R.factorization 3) := by
          calc R = R.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self hR_pos.ne').symm
            _ = ∏ r ∈ R.primeFactors, r ^ (R.factorization r) := by rw [Finsupp.prod, Nat.support_factorization]
            _ = 2 ^ (R.factorization 2) * 3 ^ (R.factorization 3) := by rw [hpf_eq, Finset.prod_pair (by norm_num)]
        have he2_cases : R.factorization 2 = 1 ∨ R.factorization 2 = 2 := by omega
        rcases he2_cases with he2 | he2
        · have hR6 : R = 6 := by rw [hR_prod, he2, he3_eq1]; norm_num
          obtain ⟨w₁, hw₁_I, hw₁_notB₀, h2_w₁⟩ := exists_prime_multiple_avoiding_five
            hA_card hA_pos hA_le hAgcd hB₀_I (by norm_num : Nat.Prime 2)
            (by rw [← hR_fac 2 (by norm_num)]; omega)
          obtain ⟨w₂, hw₂_I, hw₂_notB₀, h3_w₂⟩ := exists_prime_multiple_avoiding_five
            hA_card hA_pos hA_le hAgcd hB₀_I (by norm_num : Nat.Prime 3)
            (by rw [← hR_fac 3 (by norm_num)]; omega)
          exact two_slots_of_coprime_dvd_5 hR6 (by norm_num) (by norm_num) (by norm_num)
            hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ h2_w₁ h3_w₂
        · have hR12 : R = 12 := by rw [hR_prod, he2, he3_eq1]; norm_num
          have hM12 : 12 ≤ M := by omega
          have hc3 : 3 ≤ M / 2 ^ 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
          obtain ⟨w₁, hw₁_I, hw₁_notB₀, h4_w₁⟩ := exists_pow_multiple_avoiding_of_3_le_div_five
            hA_card hA_pos hA_le hAgcd hB₀_I (p := 2) (by norm_num) (by norm_num) hc3
            (by rw [← hR_fac 2 (by norm_num)]; omega)
          rw [show (2 ^ 2 : ℕ) = 4 by norm_num] at h4_w₁
          obtain ⟨w₂, hw₂_I, hw₂_notB₀, h3_w₂⟩ := exists_prime_multiple_avoiding_five
            hA_card hA_pos hA_le hAgcd hB₀_I (by norm_num : Nat.Prime 3)
            (by rw [← hR_fac 3 (by norm_num)]; omega)
          exact two_slots_of_coprime_dvd_5 hR12 (by norm_num) (by norm_num) (by norm_num)
            hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ h4_w₁ h3_w₂

/-- **Immediate Two-Slot Extension Corollary**:
    for ANY `u ∈ A`, if `A.erase u` admits a `≤ 4`-slot cover in `consecInterval x M`,
    then `A` admits a `≤ 6`-slot cover in `consecInterval x M`. -/
lemma cover_six_of_cover_four_erase {A : Finset ℕ} {x M u : ℕ}
    (hA_card : A.card = 5) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M) (huA : u ∈ A)
    (hcov4 : ∃ B₀ ⊆ consecInterval x M, B₀.card ≤ 4 ∧ IsCover (A.erase u) B₀) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  obtain ⟨B₀, hB₀_I, hB₀_card, hB₀_cov⟩ := hcov4
  have hA'0 : ∀ a ∈ A.erase u, a ≠ 0 := fun a ha => (hA_pos a (Finset.mem_erase.mp ha).2).ne'
  have hB₀0 : ∀ b ∈ B₀, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hB₀_I hb)).ne'
  have hA_eq : A = insert u (A.erase u) := (Finset.insert_erase huA).symm
  have hu_not : u ∉ A.erase u := Finset.notMem_erase u A
  have hu_pos : 0 < u := hA_pos u huA
  have hu_le : u ≤ M := hA_le u huA
  have hdef_le : ∀ p : ℕ, (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤
      u.factorization p := by
    intro p
    have h1 : ∑ a ∈ A, a.factorization p = u.factorization p + ∑ a ∈ A.erase u, a.factorization p :=
      (Finset.add_sum_erase A (fun a => a.factorization p) huA).symm
    have h2 := sum_factorization_le_of_isCover hA'0 hB₀0 hB₀_cov p
    omega
  let R : ℕ := ∏ p ∈ u.primeFactors,
    p ^ ((∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p))
  have hR_pos : 0 < R := Finset.prod_pos (fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  have hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) := by
    intro p hp
    have hterm_ne : ∀ q ∈ u.primeFactors,
        q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q)) ≠ 0 :=
      fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
    rw [Nat.factorization_prod hterm_ne]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ q ∈ u.primeFactors,
        (q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q))).factorization p =
          if q = p then (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q) else 0 := by
      intro q hq
      rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hq), Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hp_mem
    · rfl
    · have hfac0 : u.factorization p = 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hp_mem
        exact hp_mem
      have hle := hdef_le p
      rw [hfac0] at hle
      omega
  have hRu : R ∣ u := by
    rw [← Nat.factorization_le_iff_dvd hR_pos.ne' hu_pos.ne']
    intro p
    by_cases hp : p.Prime
    · rw [hR_fac p hp]; exact hdef_le p
    · rw [Nat.factorization_eq_zero_of_not_prime R hp]; exact Nat.zero_le _
  have hRM : R ≤ M := le_trans (Nat.le_of_dvd hu_pos hRu) hu_le
  obtain ⟨B₁, hB₁_I, hdisj, hB₁_card, hB₁_val⟩ := exists_two_slots_for_R_le_M_five
    hA_card hA_pos hA_le hAgcd hB₀_I hB₀_card hM7 hR_pos hRM hR_fac
  refine ⟨B₀ ∪ B₁, Finset.union_subset hB₀_I hB₁_I, ?_, ?_⟩
  · have h1 := Finset.card_union_le B₀ B₁
    omega
  · apply isCover_union_of_disjoint_factorization (fun a ha => (hA_pos a ha).ne') hB₀0
      (fun b hb => (pos_of_mem_consecInterval (hB₁_I hb)).ne') hdisj
    intro p hp
    have h1 := hR_fac p hp
    have h2 := hB₁_val p hp
    omega

/-! ## Part 3: Unconditional 4-Slot Closures (`cover_four_of_chain4` and `cover_four_of_type1b`) -/

private lemma chain4_val_ineq_diff (a b c d : ℕ) :
    a + b + c + d ≤ max (max (max a b) c) d + min (max a b) c + min (max (max a b) c) d +
      min a b := by
  omega

private lemma chain4_val_ineq_merged (a b c d : ℕ) :
    a + b + c + d ≤ max (max (max a b) c) d + max (min a b) (min (max a b) c) +
      max (min a b) (min (max (max a b) c) d) +
      min (min a b) (min (min (max a b) c) (min (max (max a b) c) d)) := by
  rcases le_total a b with h1 | h1 <;>
  rcases le_total c (max a b) with h2 | h2 <;>
  rcases le_total d (max (max a b) c) with h3 | h3 <;>
  omega

private lemma finset_lcm_pos_5 {T : Finset ℕ} (hT : ∀ a ∈ T, 0 < a) : 0 < T.lcm id := by
  refine Nat.pos_of_ne_zero ?_
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s _ ih =>
    rw [Finset.lcm_insert]
    simp only [id_eq]
    exact Nat.lcm_ne_zero (hT a (Finset.mem_insert_self a s)).ne'
      (ih fun b hb => hT b (Finset.mem_insert_of_mem hb))

lemma gcd_not_dvd_mul_le {a b M : ℕ} (_ha : 0 < a) (hb : 0 < b)
    (hbM : b ≤ M) (hnd : ¬ (b ∣ a)) :
    2 * Nat.gcd a b ≤ M := by
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a b
  have hq2 : 2 ≤ q := by
    by_contra hlt
    have hq1 : q ≤ 1 := by omega
    have hq_pos : 0 < q := by
      by_contra h0
      have h0' : q = 0 := by omega
      rw [h0', mul_zero] at hq
      omega
    have hq_eq1 : q = 1 := by omega
    rw [hq_eq1, mul_one] at hq
    have : b ∣ a := hq ▸ Nat.gcd_dvd_left a b
    exact hnd this
  have h1 : 2 * Nat.gcd a b ≤ Nat.gcd a b * q := by rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hq2
  omega

/-- **Unconditional Chain-of-4 Closure**: if `{a₁, a₂, a₃, a₄} ⊆ (M/2, M]` are 4 distinct
    divisors of `b₀ ∈ consecInterval x M` with `¬ (a₃ ∣ lcm a₁ a₂)` and
    `¬ (a₄ ∣ lcm (lcm a₁ a₂) a₃)`, then `{a₁, a₂, a₃, a₄}` has a `≤ 4`-slot cover in
    `consecInterval x M`. -/
lemma cover_four_of_chain4 {A4 : Finset ℕ} {x M b₀ a₁ a₂ a₃ a₄ : ℕ}
    (hA4_eq : A4 = {a₁, a₂, a₃, a₄})
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (hpos : ∀ a ∈ A4, 0 < a) (hle : ∀ a ∈ A4, a ≤ M) (hhalf : ∀ a ∈ A4, M < 2 * a)
    (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A4, a ∣ b₀)
    (h3 : ¬ (a₃ ∣ Nat.lcm a₁ a₂)) (h4 : ¬ (a₄ ∣ Nat.lcm (Nat.lcm a₁ a₂) a₃)) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover A4 B := by
  have ha₁_pos : 0 < a₁ := hpos a₁ (by rw [hA4_eq]; simp)
  have ha₂_pos : 0 < a₂ := hpos a₂ (by rw [hA4_eq]; simp)
  have ha₃_pos : 0 < a₃ := hpos a₃ (by rw [hA4_eq]; simp)
  have ha₄_pos : 0 < a₄ := hpos a₄ (by rw [hA4_eq]; simp)
  have ha₁_M : a₁ ≤ M := hle a₁ (by rw [hA4_eq]; simp)
  have ha₂_M : a₂ ≤ M := hle a₂ (by rw [hA4_eq]; simp)
  have ha₃_M : a₃ ≤ M := hle a₃ (by rw [hA4_eq]; simp)
  have ha₄_M : a₄ ≤ M := hle a₄ (by rw [hA4_eq]; simp)
  have ha₁_h : M < 2 * a₁ := hhalf a₁ (by rw [hA4_eq]; simp)
  have ha₂_h : M < 2 * a₂ := hhalf a₂ (by rw [hA4_eq]; simp)
  have ha₃_h : M < 2 * a₃ := hhalf a₃ (by rw [hA4_eq]; simp)
  have ha₄_h : M < 2 * a₄ := hhalf a₄ (by rw [hA4_eq]; simp)
  have hA4_0 : ∀ a ∈ A4, a ≠ 0 := fun a ha => (hpos a ha).ne'
  have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  let L₁₂ := Nat.lcm a₁ a₂
  let L₁₂₃ := Nat.lcm L₁₂ a₃
  have hL12_pos : 0 < L₁₂ := Nat.lcm_pos ha₁_pos ha₂_pos
  have hL123_pos : 0 < L₁₂₃ := Nat.lcm_pos hL12_pos ha₃_pos
  let d₂ := Nat.gcd a₁ a₂
  let d₃ := Nat.gcd L₁₂ a₃
  let d₄ := Nat.gcd L₁₂₃ a₄
  have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_left a₂ ha₁_pos
  have hd₃_pos : 0 < d₃ := Nat.gcd_pos_of_pos_left a₃ hL12_pos
  have hd₄_pos : 0 < d₄ := Nat.gcd_pos_of_pos_left a₄ hL123_pos
  have h3d₂ : 3 * d₂ ≤ M := three_mul_le_of_two_gt_half_5 hd₂_pos h12 ha₁_M ha₂_M ha₁_h ha₂_h
    (Nat.gcd_dvd_left a₁ a₂) (Nat.gcd_dvd_right a₁ a₂)
  have h2d₃ : 2 * d₃ ≤ M := gcd_not_dvd_mul_le hL12_pos ha₃_pos ha₃_M h3
  have h2d₄ : 2 * d₄ ≤ M := gcd_not_dvd_mul_le hL123_pos ha₄_pos ha₄_M h4
  obtain ⟨w₃, hw₃_I, hw₃_nb0, hd₃_w₃⟩ := exists_avoiding_multiple_5 x M d₃ {b₀}
    hd₃_pos (by simpa using h2d₃)
  have hw3_b0 : w₃ ≠ b₀ := by simpa using hw₃_nb0
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A4, a.factorization p =
      a₁.factorization p + a₂.factorization p + a₃.factorization p + a₄.factorization p := by
    intro p
    rw [hA4_eq, Finset.sum_insert (by simp [h12, h13, h14]),
        Finset.sum_insert (by simp [h23, h24]), Finset.sum_insert (by simp [h34]),
        Finset.sum_singleton]
    ring
  have hb0_1 := fun p => fac_le_of_dvd_5 hb₀0 (hdiv_b0 a₁ (by rw [hA4_eq]; simp)) (p := p)
  have hb0_2 := fun p => fac_le_of_dvd_5 hb₀0 (hdiv_b0 a₂ (by rw [hA4_eq]; simp)) (p := p)
  have hb0_3 := fun p => fac_le_of_dvd_5 hb₀0 (hdiv_b0 a₃ (by rw [hA4_eq]; simp)) (p := p)
  have hb0_4 := fun p => fac_le_of_dvd_5 hb₀0 (hdiv_b0 a₄ (by rw [hA4_eq]; simp)) (p := p)
  by_cases h34_eq : d₃ = d₄
  · have hd₄_a3 : d₄ ∣ a₃ := h34_eq ▸ Nat.gcd_dvd_right L₁₂ a₃
    have h3d₄ : 3 * d₄ ≤ M := three_mul_le_of_two_gt_half_5 hd₄_pos h34 ha₃_M ha₄_M ha₃_h ha₄_h
      hd₄_a3 (Nat.gcd_dvd_right L₁₂₃ a₄)
    have hbd2 : ({b₀, w₃} : Finset ℕ).card + 1 ≤ 3 := by
      have := Finset.card_insert_le b₀ {w₃}; simp at this ⊢; omega
    obtain ⟨w₄, hw₄_I, hw₄_not, hd₄_w₄⟩ := exists_avoiding_multiple_5 x M d₄ {b₀, w₃}
      hd₄_pos (le_trans (Nat.mul_le_mul_right d₄ hbd2) h3d₄)
    have hw4_b0 : w₄ ≠ b₀ := fun h => hw₄_not (by simp [h])
    have hw4_w3 : w₄ ≠ w₃ := fun h => hw₄_not (by simp [h])
    have hbd3 : ({b₀, w₃, w₄} : Finset ℕ).card + 1 ≤ 4 := by
      have h1 := Finset.card_insert_le b₀ {w₃, w₄}
      have h2 := Finset.card_insert_le w₃ {w₄}
      simp only [Finset.card_singleton] at h2; omega
    by_cases h4d2 : 4 * d₂ ≤ M
    · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := exists_avoiding_multiple_5 x M d₂ {b₀, w₃, w₄}
        hd₂_pos (le_trans (Nat.mul_le_mul_right d₂ hbd3) h4d2)
      have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
      have hw2_w3 : w₂ ≠ w₃ := fun h => hw₂_not (by simp [h])
      have hw2_w4 : w₂ ≠ w₄ := fun h => hw₂_not (by simp [h])
      let B : Finset ℕ := {b₀, w₃, w₄, w₂}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
      intro p _hp
      rw [hsumA_eq p]
      have hsumB : b₀.factorization p + w₃.factorization p + w₄.factorization p + w₂.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hw3_b0.symm, hw4_b0.symm, hw2_b0.symm]),
            Finset.sum_insert (by simp [hw4_w3.symm, hw2_w3.symm]),
            Finset.sum_insert (by simp [hw2_w4.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
      have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
      have hvd4 := fac_le_of_dvd_5 hw40 hd₄_w₄ (p := p)
      have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
      rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
      rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
          fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
      rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2
      have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
          (a₄.factorization p) ≤ b₀.factorization p := by
        have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
      have hvi := chain4_val_ineq_diff (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
      omega
    · -- `M < 4 * d₂`, so `d₂` has at most `3` multiples in `I` — actually if `d₂` has a multiple outside `{b₀, w₃, w₄}` we're done!
      -- Otherwise `d₂ ∣ w₃` or `d₂ ∣ w₄`, in which case `{w₃, w₄}` gives ONE extra copy of `d₂` AND `b₀` already has `max ≥ d₂`!
      by_cases hex2 : ∃ w₂ ∈ consecInterval x M, w₂ ∉ ({b₀, w₃, w₄} : Finset ℕ) ∧ d₂ ∣ w₂
      · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := hex2
        have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
        have hw2_w3 : w₂ ≠ w₃ := fun h => hw₂_not (by simp [h])
        have hw2_w4 : w₂ ≠ w₄ := fun h => hw₂_not (by simp [h])
        let B : Finset ℕ := {b₀, w₃, w₄, w₂}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p _hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₃.factorization p + w₄.factorization p + w₂.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hw3_b0.symm, hw4_b0.symm, hw2_b0.symm]),
              Finset.sum_insert (by simp [hw4_w3.symm, hw2_w3.symm]),
              Finset.sum_insert (by simp [hw2_w4.symm]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
        have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
        have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
        have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
        have hvd4 := fac_le_of_dvd_5 hw40 hd₄_w₄ (p := p)
        have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
        rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
        rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
        rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2
        have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
            (a₄.factorization p) ≤ b₀.factorization p := by
          have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
        have hvi := chain4_val_ineq_diff (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
        omega
      · -- All `≥ 3` multiples of `d₂` in `I` lie in `{b₀, w₃, w₄}`, which has size `3`, so `d₂ ∣ w₃` AND `d₂ ∣ w₄`!
        push Not at hex2
        have hsub : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ ({b₀, w₃, w₄} : Finset ℕ) := by
          intro b hb; rw [Finset.mem_filter] at hb
          by_contra hnot; exact hex2 b hb.1 hnot hb.2
        have hge3 : 3 ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card := by
          have h1 := card_multiples_Icc_ge x M d₂ hd₂_pos
          change M / d₂ ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card at h1
          have h2 : 3 ≤ M / d₂ := (Nat.le_div_iff_mul_le hd₂_pos).mpr h3d₂
          omega
        have hcard3 : ({b₀, w₃, w₄} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hw3_b0.symm, hw4_b0.symm]),
              Finset.card_insert_of_notMem (by simp [hw4_w3.symm]), Finset.card_singleton]
        have heq_sub : (consecInterval x M).filter (fun b => d₂ ∣ b) = {b₀, w₃, w₄} :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hd₂_w₃ : d₂ ∣ w₃ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : w₃ ∈ ({b₀, w₃, w₄} : Finset ℕ)))).2
        have hd₂_w₄ : d₂ ∣ w₄ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : w₄ ∈ ({b₀, w₃, w₄} : Finset ℕ)))).2
        -- Now wait: `b₀` has `max`, `w₃` has `lcm(d₂, d₃)`, `w₄` has `lcm(d₂, d₄)`.
        -- Residual is `gcd(d₂, d₃)` (Wait: `d₃ = d₄`, and `d₂ ∣ d₃`? Not necessarily, residual divides `gcd(d₂, d₃) ≤ d₂` AND divides `a₁, a₂, a₃`, so `3 * D' ≤ M`... wait `4`th element `w'` needs `4 * D' ≤ M`!)
        -- Check: `D' = Nat.gcd d₂ d₃` divides `a₁, a₂, a₃`, AND since `d₃ = d₄ ∣ a₄`, `D'` divides ALL FOUR `a₁, a₂, a₃, a₄`!
        -- Four distinct elements in `(M/2, M]` divisible by `D'` force `4 * D' ≤ M` (in fact `D' ≤ M/4`)!
        let D' := Nat.gcd d₂ d₃
        have hD'_pos : 0 < D' := Nat.gcd_pos_of_pos_left d₃ hd₂_pos
        have hD'_1 : D' ∣ a₁ := dvd_trans (Nat.gcd_dvd_left d₂ d₃) (Nat.gcd_dvd_left a₁ a₂)
        have hD'_2 : D' ∣ a₂ := dvd_trans (Nat.gcd_dvd_left d₂ d₃) (Nat.gcd_dvd_right a₁ a₂)
        have hD'_3 : D' ∣ a₃ := dvd_trans (Nat.gcd_dvd_right d₂ d₃) (Nat.gcd_dvd_right L₁₂ a₃)
        have hD'_4 : D' ∣ a₄ := dvd_trans (Nat.gcd_dvd_right d₂ d₃) (h34_eq ▸ Nat.gcd_dvd_right L₁₂₃ a₄)
        have h4D' : 4 * D' ≤ M := by
          have hT := card_mul_le_of_forall_dvd (T := A4) (d := D') (M := M) hD'_pos (fun a ha => by
            rw [hA4_eq] at ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · exact ⟨ha₁_pos, ha₁_M, hD'_1⟩
            · exact ⟨ha₂_pos, ha₂_M, hD'_2⟩
            · exact ⟨ha₃_pos, ha₃_M, hD'_3⟩
            · exact ⟨ha₄_pos, ha₄_M, hD'_4⟩)
          have hA4_c : A4.card = 4 := by
            rw [hA4_eq, Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
                Finset.card_insert_of_notMem (by simp [h23, h24]),
                Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
          rwa [hA4_c] at hT
        obtain ⟨w', hw'_I, hw'_not, hD'_w'⟩ := exists_avoiding_multiple_5 x M D' {b₀, w₃, w₄}
          hD'_pos (le_trans (Nat.mul_le_mul_right D' (by omega : ({b₀, w₃, w₄} : Finset ℕ).card + 1 ≤ 4)) h4D')
        have hw'_b0 : w' ≠ b₀ := fun h => hw'_not (by simp [h])
        have hw'_w3 : w' ≠ w₃ := fun h => hw'_not (by simp [h])
        have hw'_w4 : w' ≠ w₄ := fun h => hw'_not (by simp [h])
        let B : Finset ℕ := {b₀, w₃, w₄, w'}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p _hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₃.factorization p + w₄.factorization p + w'.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hw3_b0.symm, hw4_b0.symm, hw'_b0.symm]),
              Finset.sum_insert (by simp [hw4_w3.symm, hw'_w3.symm]),
              Finset.sum_insert (by simp [hw'_w4.symm]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
        have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
        have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
        have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
        have hvd2_3 := fac_le_of_dvd_5 hw30 hd₂_w₃ (p := p)
        have hvd4 := fac_le_of_dvd_5 hw40 hd₄_w₄ (p := p)
        have hvd2_4 := fac_le_of_dvd_5 hw40 hd₂_w₄ (p := p)
        have hvdD := fac_le_of_dvd_5 hw'0 hD'_w' (p := p)
        rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
        rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2_3 hvd2_4
        rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
        rw [fac_gcd_eq_min_5 hd₂_pos.ne' hd₃_pos.ne', fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne',
            fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvdD
        have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
            (a₄.factorization p) ≤ b₀.factorization p := by
          have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
        have hvi := chain4_val_ineq_merged (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
        have heq34p : d₃.factorization p = d₄.factorization p := congrArg (fun n => n.factorization p) h34_eq
        rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne',
            fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at heq34p
        omega
  · -- `d₃ ≠ d₄`.
    obtain ⟨w₄, hw₄_I, hw₄_nb0, hd₄_w₄⟩ := exists_avoiding_multiple_5 x M d₄ {b₀}
      hd₄_pos (by simpa using h2d₄)
    have hw4_b0 : w₄ ≠ b₀ := by simpa using hw₄_nb0
    by_cases hw34 : w₃ = w₄
    · -- `w₃ = w₄`: `lcm(d₃, d₄) ∣ w₃`, and `g = gcd d₃ d₄` satisfies `4 * g ≤ M` (since `d₃ ≠ d₄`,
      -- WLOG `2 * g ≤ d₃` and `2 * d₃ ≤ a₃ ≤ M`, or `2 * g ≤ d₄` and `2 * d₄ ≤ a₄ ≤ M`).
      have hd₄_w₃ : d₄ ∣ w₃ := hw34 ▸ hd₄_w₄
      let g := Nat.gcd d₃ d₄
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d₄ hd₃_pos
      have h4g : 4 * g ≤ M := by
        have hlt_or_gt : g < d₃ ∨ g < d₄ := by
          by_contra hnone
          have h1 : d₃ ≤ g := by omega
          have h2 : d₄ ≤ g := by omega
          have h3 : g ≤ d₃ := Nat.le_of_dvd hd₃_pos (Nat.gcd_dvd_left d₃ d₄)
          have h4' : g ≤ d₄ := Nat.le_of_dvd hd₄_pos (Nat.gcd_dvd_right d₃ d₄)
          exact h34_eq (by omega)
        rcases hlt_or_gt with hgd3 | hgd4
        · obtain ⟨q, hq⟩ := Nat.gcd_dvd_left d₃ d₄
          have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
          have hq2 : 2 ≤ q := by
            by_contra hlt; have hq1 : q ≤ 1 := by omega
            have hle : d₃ ≤ g := by nlinarith
            omega
          have h2gd3 : 2 * g ≤ d₃ := by nlinarith
          omega
        · obtain ⟨q, hq⟩ := Nat.gcd_dvd_right d₃ d₄
          have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
          have hq2 : 2 ≤ q := by
            by_contra hlt; have hq1 : q ≤ 1 := by omega
            have hle : d₄ ≤ g := by nlinarith
            omega
          have h2gd4 : 2 * g ≤ d₄ := by nlinarith
          omega
      have hbd2 : ({b₀, w₃} : Finset ℕ).card + 1 ≤ 3 := by
        have := Finset.card_insert_le b₀ {w₃}; simp at this ⊢; omega
      obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := exists_avoiding_multiple_5 x M d₂ {b₀, w₃}
        hd₂_pos (le_trans (Nat.mul_le_mul_right d₂ hbd2) h3d₂)
      have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
      have hw2_w3 : w₂ ≠ w₃ := fun h => hw₂_not (by simp [h])
      have hbd3 : ({b₀, w₃, w₂} : Finset ℕ).card + 1 ≤ 4 := by
        have h1 := Finset.card_insert_le b₀ {w₃, w₂}
        have h2 := Finset.card_insert_le w₃ {w₂}
        simp only [Finset.card_singleton] at h2; omega
      obtain ⟨w', hw'_I, hw'_not, hg_w'⟩ := exists_avoiding_multiple_5 x M g {b₀, w₃, w₂}
        hg_pos (le_trans (Nat.mul_le_mul_right g hbd3) h4g)
      have hw'_b0 : w' ≠ b₀ := fun h => hw'_not (by simp [h])
      have hw'_w3 : w' ≠ w₃ := fun h => hw'_not (by simp [h])
      have hw'_w2 : w' ≠ w₂ := fun h => hw'_not (by simp [h])
      let B : Finset ℕ := {b₀, w₃, w₂, w'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
      intro p _hp
      rw [hsumA_eq p]
      have hsumB : b₀.factorization p + w₃.factorization p + w₂.factorization p + w'.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hw3_b0.symm, hw2_b0.symm, hw'_b0.symm]),
            Finset.sum_insert (by simp [hw2_w3.symm, hw'_w3.symm]),
            Finset.sum_insert (by simp [hw'_w2.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
      have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
      have hvd4 := fac_le_of_dvd_5 hw30 hd₄_w₃ (p := p)
      have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
      have hvg := fac_le_of_dvd_5 hw'0 hg_w' (p := p)
      rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
      rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
          fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
      rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2
      rw [fac_gcd_eq_min_5 hd₃_pos.ne' hd₄_pos.ne',
          fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne',
          fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
          fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvg
      have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
          (a₄.factorization p) ≤ b₀.factorization p := by
        have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
      have hvi := chain4_val_ineq_diff (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
      omega
    · -- `w₃ ≠ w₄`.
      by_cases hex2 : ∃ w₂ ∈ consecInterval x M, w₂ ∉ ({b₀, w₃, w₄} : Finset ℕ) ∧ d₂ ∣ w₂
      · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := hex2
        have hw2_b0 : w₂ ≠ b₀ := fun h => hw₂_not (by simp [h])
        have hw2_w3 : w₂ ≠ w₃ := fun h => hw₂_not (by simp [h])
        have hw2_w4 : w₂ ≠ w₄ := fun h => hw₂_not (by simp [h])
        let B : Finset ℕ := {b₀, w₃, w₄, w₂}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p _hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₃.factorization p + w₄.factorization p + w₂.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hw3_b0.symm, hw4_b0.symm, hw2_b0.symm]),
              Finset.sum_insert (by simp [hw34, hw2_w3.symm]),
              Finset.sum_insert (by simp [hw2_w4.symm]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
        have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
        have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
        have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
        have hvd4 := fac_le_of_dvd_5 hw40 hd₄_w₄ (p := p)
        have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
        rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
        rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
        rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2
        have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
            (a₄.factorization p) ≤ b₀.factorization p := by
          have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
        have hvi := chain4_val_ineq_diff (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
        omega
      · -- `d₂` divides both `w₃` and `w₄`, so pick `w' ∣ D' = gcd d₂ (gcd d₃ d₄)`.
        push Not at hex2
        have hsub : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ ({b₀, w₃, w₄} : Finset ℕ) := by
          intro b hb; rw [Finset.mem_filter] at hb
          by_contra hnot; exact hex2 b hb.1 hnot hb.2
        have hge3 : 3 ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card := by
          have h1 := card_multiples_Icc_ge x M d₂ hd₂_pos
          change M / d₂ ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card at h1
          have h2 : 3 ≤ M / d₂ := (Nat.le_div_iff_mul_le hd₂_pos).mpr h3d₂
          omega
        have hcard3 : ({b₀, w₃, w₄} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hw3_b0.symm, hw4_b0.symm]),
              Finset.card_insert_of_notMem (by simp [hw34]), Finset.card_singleton]
        have heq_sub : (consecInterval x M).filter (fun b => d₂ ∣ b) = {b₀, w₃, w₄} :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hd₂_w₃ : d₂ ∣ w₃ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : w₃ ∈ ({b₀, w₃, w₄} : Finset ℕ)))).2
        have hd₂_w₄ : d₂ ∣ w₄ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : w₄ ∈ ({b₀, w₃, w₄} : Finset ℕ)))).2
        let D' := Nat.gcd d₂ (Nat.gcd d₃ d₄)
        have hg34_pos : 0 < Nat.gcd d₃ d₄ := Nat.gcd_pos_of_pos_left d₄ hd₃_pos
        have hD'_pos : 0 < D' := Nat.gcd_pos_of_pos_left (Nat.gcd d₃ d₄) hd₂_pos
        have hD'_1 : D' ∣ a₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left a₁ a₂)
        have hD'_2 : D' ∣ a₂ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right a₁ a₂)
        have hD'_3 : D' ∣ a₃ := dvd_trans (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left d₃ d₄))
          (Nat.gcd_dvd_right L₁₂ a₃)
        have hD'_4 : D' ∣ a₄ := dvd_trans (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right d₃ d₄))
          (Nat.gcd_dvd_right L₁₂₃ a₄)
        have h4D' : 4 * D' ≤ M := by
          have hT := card_mul_le_of_forall_dvd (T := A4) (d := D') (M := M) hD'_pos (fun a ha => by
            rw [hA4_eq] at ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · exact ⟨ha₁_pos, ha₁_M, hD'_1⟩
            · exact ⟨ha₂_pos, ha₂_M, hD'_2⟩
            · exact ⟨ha₃_pos, ha₃_M, hD'_3⟩
            · exact ⟨ha₄_pos, ha₄_M, hD'_4⟩)
          have hA4_c : A4.card = 4 := by
            rw [hA4_eq, Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
                Finset.card_insert_of_notMem (by simp [h23, h24]),
                Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
          rwa [hA4_c] at hT
        obtain ⟨w', hw'_I, hw'_not, hD'_w'⟩ := exists_avoiding_multiple_5 x M D' {b₀, w₃, w₄}
          hD'_pos (le_trans (Nat.mul_le_mul_right D' (by omega : ({b₀, w₃, w₄} : Finset ℕ).card + 1 ≤ 4)) h4D')
        have hw'_b0 : w' ≠ b₀ := fun h => hw'_not (by simp [h])
        have hw'_w3 : w' ≠ w₃ := fun h => hw'_not (by simp [h])
        have hw'_w4 : w' ≠ w₄ := fun h => hw'_not (by simp [h])
        let B : Finset ℕ := {b₀, w₃, w₄, w'}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p _hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₃.factorization p + w₄.factorization p + w'.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hw3_b0.symm, hw4_b0.symm, hw'_b0.symm]),
              Finset.sum_insert (by simp [hw34, hw'_w3.symm]),
              Finset.sum_insert (by simp [hw'_w4.symm]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hw30 : w₃ ≠ 0 := (pos_of_mem_consecInterval hw₃_I).ne'
        have hw40 : w₄ ≠ 0 := (pos_of_mem_consecInterval hw₄_I).ne'
        have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
        have hvd3 := fac_le_of_dvd_5 hw30 hd₃_w₃ (p := p)
        have hvd2_3 := fac_le_of_dvd_5 hw30 hd₂_w₃ (p := p)
        have hvd4 := fac_le_of_dvd_5 hw40 hd₄_w₄ (p := p)
        have hvd2_4 := fac_le_of_dvd_5 hw40 hd₂_w₄ (p := p)
        have hvdD := fac_le_of_dvd_5 hw'0 hD'_w' (p := p)
        rw [fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd3
        rw [fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd2_3 hvd2_4
        rw [fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvd4
        rw [fac_gcd_eq_min_5 hd₂_pos.ne' hg34_pos.ne', fac_gcd_eq_min_5 hd₃_pos.ne' hd₄_pos.ne',
            fac_gcd_eq_min_5 ha₁_pos.ne' ha₂_pos.ne',
            fac_gcd_eq_min_5 hL12_pos.ne' ha₃_pos.ne', fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne',
            fac_gcd_eq_min_5 hL123_pos.ne' ha₄_pos.ne', fac_lcm_eq_max_5 hL12_pos.ne' ha₃_pos.ne',
            fac_lcm_eq_max_5 ha₁_pos.ne' ha₂_pos.ne'] at hvdD
        have hb0p : max (max (max (a₁.factorization p) (a₂.factorization p)) (a₃.factorization p))
            (a₄.factorization p) ≤ b₀.factorization p := by
          have := hb0_1 p; have := hb0_2 p; have := hb0_3 p; have := hb0_4 p; omega
        have hvi := chain4_val_ineq_merged (a₁.factorization p) (a₂.factorization p) (a₃.factorization p) (a₄.factorization p)
        omega

private lemma decide_type1b_Q1 :
    ∀ a ∈ Finset.Icc 1 4, ∀ b ∈ Finset.Icc 1 7, ∀ c ∈ Finset.Icc 1 7, ∀ d ∈ Finset.Icc 1 7,
      a < b → b < c → c < d → d < 2 * a →
      Nat.gcd a b = 1 → Nat.gcd a c = 1 → Nat.gcd a d = 1 →
      Nat.gcd b c = 1 → Nat.gcd b d = 1 → Nat.gcd c d = 1 → False := by
  decide

private lemma decide_type1b_Q2 :
    ∀ c ∈ Finset.Icc 7 9, ∀ d ∈ Finset.Icc 7 9,
      c < d → Nat.gcd 5 c = 1 → Nat.gcd 5 d = 1 →
      Nat.gcd 6 c = 1 → Nat.gcd 6 d = 1 → Nat.gcd c d = 1 → False := by
  decide

/-- Helper: for any 4 distinct elements in `(M/2, M]` where every pair spans `L₄`,
    write `xᵢ = L₄ / Qᵢ`, check `Qᵢ` pairwise coprime and bounds. -/
private lemma type1b_quotients_props {A4 : Finset ℕ} {M x₁ x₂ x₃ x₄ : ℕ}
    (hA4_eq : A4 = {x₁, x₂, x₃, x₄})
    (hx12 : x₁ > x₂) (hx23 : x₂ > x₃) (hx34 : x₃ > x₄)
    (hpos : ∀ a ∈ A4, 0 < a) (hle : ∀ a ∈ A4, a ≤ M) (hhalf : ∀ a ∈ A4, M < 2 * a)
    (hpair : ∀ a ∈ A4, ∀ b ∈ A4, a ≠ b → Nat.lcm a b = A4.lcm id) :
    let L4 := A4.lcm id
    let Q₁ := L4 / x₁
    let Q₂ := L4 / x₂
    let Q₃ := L4 / x₃
    let Q₄ := L4 / x₄
    Q₁ < Q₂ ∧ Q₂ < Q₃ ∧ Q₃ < Q₄ ∧ Q₄ < 2 * Q₁ ∧
    5 ≤ Q₁ ∧ 7 ≤ Q₂ ∧ 8 ≤ Q₃ ∧ 9 ≤ Q₄ ∧
    Nat.Coprime Q₁ Q₂ ∧ Nat.Coprime Q₁ Q₃ ∧ Nat.Coprime Q₁ Q₄ ∧
    Nat.Coprime Q₂ Q₃ ∧ Nat.Coprime Q₂ Q₄ ∧ Nat.Coprime Q₃ Q₄ ∧
    (Q₁ * Q₂ * Q₃ * Q₄) ∣ L4 := by
  intro L4 Q₁ Q₂ Q₃ Q₄
  have hx₁_pos : 0 < x₁ := hpos x₁ (by rw [hA4_eq]; simp)
  have hx₂_pos : 0 < x₂ := hpos x₂ (by rw [hA4_eq]; simp)
  have hx₃_pos : 0 < x₃ := hpos x₃ (by rw [hA4_eq]; simp)
  have hx₄_pos : 0 < x₄ := hpos x₄ (by rw [hA4_eq]; simp)
  have hL4_pos : 0 < L4 := finset_lcm_pos_5 hpos
  have hd1 : x₁ ∣ L4 := Finset.dvd_lcm (by rw [hA4_eq]; simp)
  have hd2 : x₂ ∣ L4 := Finset.dvd_lcm (by rw [hA4_eq]; simp)
  have hd3 : x₃ ∣ L4 := Finset.dvd_lcm (by rw [hA4_eq]; simp)
  have hd4 : x₄ ∣ L4 := Finset.dvd_lcm (by rw [hA4_eq]; simp)
  have hmul1 : x₁ * Q₁ = L4 := Nat.mul_div_cancel' hd1
  have hmul2 : x₂ * Q₂ = L4 := Nat.mul_div_cancel' hd2
  have hmul3 : x₃ * Q₃ = L4 := Nat.mul_div_cancel' hd3
  have hmul4 : x₄ * Q₄ = L4 := Nat.mul_div_cancel' hd4
  have hQ₁_pos : 0 < Q₁ := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hmul1; omega)
  have hQ₂_pos : 0 < Q₂ := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hmul2; omega)
  have hQ₃_pos : 0 < Q₃ := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hmul3; omega)
  have hQ₄_pos : 0 < Q₄ := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hmul4; omega)
  have hQ12 : Q₁ < Q₂ := by nlinarith
  have hQ23 : Q₂ < Q₃ := by nlinarith
  have hQ34 : Q₃ < Q₄ := by nlinarith
  have hx1_M : x₁ ≤ M := hle x₁ (by rw [hA4_eq]; simp)
  have hx4_h : M < 2 * x₄ := hhalf x₄ (by rw [hA4_eq]; simp)
  have hx1_lt : x₁ < 2 * x₄ := by omega
  have hQ4_lt : Q₄ < 2 * Q₁ := by nlinarith
  -- Pairwise coprimality: if prime `p ∣ gcd Q_i Q_j`, then `v_p(x_i) < v_p(L4)` and `v_p(x_j) < v_p(L4)`,
  -- contradicting `lcm x_i x_j = L4`!
  have hcop_pair : ∀ {a b Qa Qb : ℕ}, a ∈ A4 → b ∈ A4 → a ≠ b →
      a * Qa = L4 → b * Qb = L4 → Nat.Coprime Qa Qb := by
    intro a b Qa Qb haA hbA hab haQ hbQ
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne1
    have hgt1 : 1 < Nat.gcd Qa Qb := by
      have hg_pos : 0 < Nat.gcd Qa Qb := Nat.gcd_pos_of_pos_left Qb (Nat.pos_of_ne_zero (fun h => by
        rw [h, mul_zero] at haQ; omega))
      omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
    have hpQa : p ∣ Qa := dvd_trans hpd (Nat.gcd_dvd_left Qa Qb)
    have hpQb : p ∣ Qb := dvd_trans hpd (Nat.gcd_dvd_right Qa Qb)
    have ha0 : a ≠ 0 := (hpos a haA).ne'
    have hb0 : b ≠ 0 := (hpos b hbA).ne'
    have hQa0 : Qa ≠ 0 := fun h => by rw [h, mul_zero] at haQ; omega
    have hQb0 : Qb ≠ 0 := fun h => by rw [h, mul_zero] at hbQ; omega
    have hva : a.factorization p < L4.factorization p := by
      have h1 : 1 ≤ Qa.factorization p := (hp.pow_dvd_iff_le_factorization hQa0).mp (by simpa using hpQa)
      have h2 : L4.factorization p = a.factorization p + Qa.factorization p := by
        rw [← haQ, Nat.factorization_mul ha0 hQa0, Finsupp.add_apply]
      omega
    have hvb : b.factorization p < L4.factorization p := by
      have h1 : 1 ≤ Qb.factorization p := (hp.pow_dvd_iff_le_factorization hQb0).mp (by simpa using hpQb)
      have h2 : L4.factorization p = b.factorization p + Qb.factorization p := by
        rw [← hbQ, Nat.factorization_mul hb0 hQb0, Finsupp.add_apply]
      omega
    have hlcm : Nat.lcm a b = L4 := hpair a haA b hbA hab
    have hlcm_p := congrArg (fun n => n.factorization p) hlcm
    rw [fac_lcm_eq_max_5 ha0 hb0] at hlcm_p
    omega
  have hc12 : Nat.Coprime Q₁ Q₂ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul1 hmul2
  have hc13 : Nat.Coprime Q₁ Q₃ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul1 hmul3
  have hc14 : Nat.Coprime Q₁ Q₄ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul1 hmul4
  have hc23 : Nat.Coprime Q₂ Q₃ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul2 hmul3
  have hc24 : Nat.Coprime Q₂ Q₄ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul2 hmul4
  have hc34 : Nat.Coprime Q₃ Q₄ := hcop_pair (by rw [hA4_eq]; simp) (by rw [hA4_eq]; simp) (by omega) hmul3 hmul4
  -- `Q₁ ≥ 5`: if `Q₁ ≤ 4`, 4 pairwise coprime numbers in `[Q₁, 2*Q₁ - 1]` cannot exist!
  have hQ1_ge5 : 5 ≤ Q₁ := by
    by_contra hlt5
    have hQ1_le4 : Q₁ ≤ 4 := by omega
    -- At least 2 of Q₁..Q₄ must be ≥ 5? No, Q₄ < 2 * Q₁ ≤ 8, so Q₁ < Q₂ < Q₃ < Q₄ ≤ 7!
    -- Wait: if Q₁ ≤ 4 then 2 * Q₁ ≤ 8 so Q₁..Q₄ ∈ [1, 7], among [1,7] no 4 pairwise coprime in [a, 2a-1]:
    -- Wait: `{1,3,5,7}` fails `Q₄ < 2 Q₁`; `{2,3,5,7}` fails `Q₄ < 2 Q₁` (`7 < 4` false);
    -- `{3,4,5,7}` fails `Q₄ < 2 Q₁` (`7 < 6` false); `{4,5,6,7}` fails `gcd(4,6) = 2`!
    have h4_le7 : Q₄ ≤ 7 := by omega
    have hgcd_eq : Nat.gcd Q₁ Q₂ = 1 ∧ Nat.gcd Q₁ Q₃ = 1 ∧ Nat.gcd Q₁ Q₄ = 1 ∧
        Nat.gcd Q₂ Q₃ = 1 ∧ Nat.gcd Q₂ Q₄ = 1 ∧ Nat.gcd Q₃ Q₄ = 1 :=
      ⟨hc12.gcd_eq_one, hc13.gcd_eq_one, hc14.gcd_eq_one, hc23.gcd_eq_one, hc24.gcd_eq_one, hc34.gcd_eq_one⟩
    exact decide_type1b_Q1 Q₁ (Finset.mem_Icc.mpr ⟨hQ₁_pos, hQ1_le4⟩)
      Q₂ (Finset.mem_Icc.mpr ⟨hQ₂_pos, by omega⟩)
      Q₃ (Finset.mem_Icc.mpr ⟨hQ₃_pos, by omega⟩)
      Q₄ (Finset.mem_Icc.mpr ⟨hQ₄_pos, h4_le7⟩)
      hQ12 hQ23 hQ34 hQ4_lt hgcd_eq.1 hgcd_eq.2.1 hgcd_eq.2.2.1 hgcd_eq.2.2.2.1 hgcd_eq.2.2.2.2.1 hgcd_eq.2.2.2.2.2
  have hQ2_ge7 : 7 ≤ Q₂ := by
    by_contra hlt7
    have hQ1_eq5 : Q₁ = 5 := by omega
    have hQ2_eq6 : Q₂ = 6 := by omega
    have hQ4_le9 : Q₄ ≤ 9 := by omega
    exact decide_type1b_Q2 Q₃ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) Q₄ (Finset.mem_Icc.mpr ⟨by omega, hQ4_le9⟩)
      hQ34 (hQ1_eq5 ▸ hc13.gcd_eq_one) (hQ1_eq5 ▸ hc14.gcd_eq_one)
      (hQ2_eq6 ▸ hc23.gcd_eq_one) (hQ2_eq6 ▸ hc24.gcd_eq_one) hc34.gcd_eq_one
  have hQ3_ge8 : 8 ≤ Q₃ := by omega
  have hQ4_ge9 : 9 ≤ Q₄ := by omega
  have hQ12_dvd : Q₁ * Q₂ ∣ L4 := hc12.mul_dvd_of_dvd_of_dvd ⟨x₁, by rw [mul_comm]; exact hmul1.symm⟩
    ⟨x₂, by rw [mul_comm]; exact hmul2.symm⟩
  have hQ123_dvd : Q₁ * Q₂ * Q₃ ∣ L4 := (Nat.Coprime.mul_left hc13 hc23).mul_dvd_of_dvd_of_dvd hQ12_dvd
    ⟨x₃, by rw [mul_comm]; exact hmul3.symm⟩
  have hQ1234_dvd : Q₁ * Q₂ * Q₃ * Q₄ ∣ L4 :=
    ((Nat.Coprime.mul_left (Nat.Coprime.mul_left hc14 hc24) hc34)).mul_dvd_of_dvd_of_dvd hQ123_dvd
      ⟨x₄, by rw [mul_comm]; exact hmul4.symm⟩
  exact ⟨hQ12, hQ23, hQ34, hQ4_lt, hQ1_ge5, hQ2_ge7, hQ3_ge8, hQ4_ge9,
    hc12, hc13, hc14, hc23, hc24, hc34, hQ1234_dvd⟩

private lemma type1b_val_ineq_main (d q1 q2 q3 q4 : ℕ) :
    (d + q2 + q3 + q4) + (d + q1 + q3 + q4) + (d + q1 + q2 + q4) + (d + q1 + q2 + q3) ≤
    (d + q1 + q2 + q3 + q4) + (d + 2 * q1 + q2) + (d + q2 + 2 * q3) + (d + 2 * q4) := by omega

private lemma type1b_val_ineq_hit1 (d q1 q2 q3 q4 : ℕ) :
    (d + q2 + q3 + q4) + (d + q1 + q3 + q4) + (d + q1 + q2 + q4) + (d + q1 + q2 + q3) ≤
    (d + 2 * q1 + q2 + q3 + q4) + (d + q1 + q2) + (d + q2 + 2 * q3) + (d + 2 * q4) := by omega

private lemma type1b_val_ineq_hit2 (d q1 q2 q3 q4 : ℕ) :
    (d + q2 + q3 + q4) + (d + q1 + q3 + q4) + (d + q1 + q2 + q4) + (d + q1 + q2 + q3) ≤
    (d + q1 + q2 + 2 * q3 + q4) + (d + 2 * q1 + q2) + (d + q2 + q3) + (d + 2 * q4) := by omega

private lemma type1b_val_ineq_hit12 (d q1 q2 q3 q4 : ℕ) :
    (d + q2 + q3 + q4) + (d + q1 + q3 + q4) + (d + q1 + q2 + q4) + (d + q1 + q2 + q3) ≤
    (d + 2 * q1 + q2 + 2 * q3 + q4) + (d + q1 + q2) + (d + q2 + q3) + (d + 2 * q4) := by omega

private lemma type1b_val_ineq_eq (d q1 q2 q3 q4 : ℕ) :
    (d + q2 + q3 + q4) + (d + q1 + q3 + q4) + (d + q1 + q2 + q4) + (d + q1 + q2 + q3) ≤
    (d + q1 + q2 + q3 + q4) + (d + 2 * q1 + q2 + 2 * q3) + (d + q2) + (d + 2 * q4) := by omega

private lemma type1b_fac_decomp {L4 D Q₁ Q₂ Q₃ Q₄ p : ℕ} (_hp : p.Prime)
    (hL4 : L4 = D * Q₁ * Q₂ * Q₃ * Q₄) (hL4_0 : L4 ≠ 0)
    (_hc12 : Nat.Coprime Q₁ Q₂) (_hc13 : Nat.Coprime Q₁ Q₃) (_hc14 : Nat.Coprime Q₁ Q₄)
    (_hc23 : Nat.Coprime Q₂ Q₃) (_hc24 : Nat.Coprime Q₂ Q₄) (_hc34 : Nat.Coprime Q₃ Q₄) :
    L4.factorization p = D.factorization p + Q₁.factorization p + Q₂.factorization p +
      Q₃.factorization p + Q₄.factorization p ∧
    (L4 / Q₁).factorization p = D.factorization p + Q₂.factorization p + Q₃.factorization p + Q₄.factorization p ∧
    (L4 / Q₂).factorization p = D.factorization p + Q₁.factorization p + Q₃.factorization p + Q₄.factorization p ∧
    (L4 / Q₃).factorization p = D.factorization p + Q₁.factorization p + Q₂.factorization p + Q₄.factorization p ∧
    (L4 / Q₄).factorization p = D.factorization p + Q₁.factorization p + Q₂.factorization p + Q₃.factorization p := by
  have hD0 : D ≠ 0 := fun h => by rw [h] at hL4; simp at hL4; exact hL4_0 hL4
  have hQ₁0 : Q₁ ≠ 0 := fun h => by rw [h] at hL4; simp at hL4; exact hL4_0 hL4
  have hQ₂0 : Q₂ ≠ 0 := fun h => by rw [h] at hL4; simp at hL4; exact hL4_0 hL4
  have hQ₃0 : Q₃ ≠ 0 := fun h => by rw [h] at hL4; simp at hL4; exact hL4_0 hL4
  have hQ₄0 : Q₄ ≠ 0 := fun h => by rw [h] at hL4; simp at hL4; exact hL4_0 hL4
  have hL : L4.factorization p = D.factorization p + Q₁.factorization p + Q₂.factorization p +
      Q₃.factorization p + Q₄.factorization p := by
    rw [hL4, Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0) hQ₄0,
        Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0,
        Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
        Nat.factorization_mul hD0 hQ₁0]
    simp only [Finsupp.add_apply]
  have hdiv1 : L4 / Q₁ = D * Q₂ * Q₃ * Q₄ := by
    rw [hL4, show D * Q₁ * Q₂ * Q₃ * Q₄ = (D * Q₂ * Q₃ * Q₄) * Q₁ by ring,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hQ₁0)]
  have hdiv2 : L4 / Q₂ = D * Q₁ * Q₃ * Q₄ := by
    rw [hL4, show D * Q₁ * Q₂ * Q₃ * Q₄ = (D * Q₁ * Q₃ * Q₄) * Q₂ by ring,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hQ₂0)]
  have hdiv3 : L4 / Q₃ = D * Q₁ * Q₂ * Q₄ := by
    rw [hL4, show D * Q₁ * Q₂ * Q₃ * Q₄ = (D * Q₁ * Q₂ * Q₄) * Q₃ by ring,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hQ₃0)]
  have hdiv4 : L4 / Q₄ = D * Q₁ * Q₂ * Q₃ := by
    rw [hL4, show D * Q₁ * Q₂ * Q₃ * Q₄ = (D * Q₁ * Q₂ * Q₃) * Q₄ by ring,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hQ₄0)]
  refine ⟨hL, ?_, ?_, ?_, ?_⟩
  · rw [hdiv1, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₂0) hQ₃0) hQ₄0,
        Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) hQ₃0, Nat.factorization_mul hD0 hQ₂0]
    simp only [Finsupp.add_apply]
  · rw [hdiv2, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₃0) hQ₄0,
        Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₃0, Nat.factorization_mul hD0 hQ₁0]
    simp only [Finsupp.add_apply]
  · rw [hdiv3, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₄0,
        Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0, Nat.factorization_mul hD0 hQ₁0]
    simp only [Finsupp.add_apply]
  · rw [hdiv4, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0,
        Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0, Nat.factorization_mul hD0 hQ₁0]
    simp only [Finsupp.add_apply]

private lemma sort3_dec {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z₁ z₂ z₃ : ℕ, ({a, b, c} : Finset ℕ) = {z₁, z₂, z₃} ∧ z₃ < z₂ ∧ z₂ < z₁ := by
  have hset : ∀ x y z : ℕ, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
      (z = a ∨ z = b ∨ z = c) → (a = x ∨ a = y ∨ a = z) → (b = x ∨ b = y ∨ b = z) →
      (c = x ∨ c = y ∨ c = z) → ({a, b, c} : Finset ℕ) = {x, y, z} := by
    intro x y z hx hy hz ha hb hc
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨by rintro (rfl | rfl | rfl) <;> assumption, by rintro (rfl | rfl | rfl) <;> assumption⟩
  rcases lt_or_gt_of_ne hab with h1 | h1
  · rcases lt_or_gt_of_ne hac with h2 | h2
    · rcases lt_or_gt_of_ne hbc with h3 | h3
      · exact ⟨c, b, a, hset _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h1, h3⟩
      · exact ⟨b, c, a, hset _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h2, h3⟩
    · exact ⟨b, a, c, hset _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h2, h1⟩
  · rcases lt_or_gt_of_ne hac with h2 | h2
    · exact ⟨c, a, b, hset _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h1, h2⟩
    · rcases lt_or_gt_of_ne hbc with h3 | h3
      · exact ⟨a, c, b, hset _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h3, h2⟩
      · exact ⟨a, b, c, rfl, h3, h1⟩

private lemma sort4_dec {x₁ x₂ x₃ x₄ : ℕ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄) :
    ∃ y₁ y₂ y₃ y₄ : ℕ, ({x₁, x₂, x₃, x₄} : Finset ℕ) = {y₁, y₂, y₃, y₄} ∧
      y₄ < y₃ ∧ y₃ < y₂ ∧ y₂ < y₁ := by
  obtain ⟨z₁, z₂, z₃, hz_eq, hz32, hz21⟩ := sort3_dec h12 h13 h23
  have hz1_m : z₁ = x₁ ∨ z₁ = x₂ ∨ z₁ = x₃ := by
    have h : z₁ ∈ ({x₁, x₂, x₃} : Finset ℕ) := by rw [hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hz2_m : z₂ = x₁ ∨ z₂ = x₂ ∨ z₂ = x₃ := by
    have h : z₂ ∈ ({x₁, x₂, x₃} : Finset ℕ) := by rw [hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hz3_m : z₃ = x₁ ∨ z₃ = x₂ ∨ z₃ = x₃ := by
    have h : z₃ ∈ ({x₁, x₂, x₃} : Finset ℕ) := by rw [hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hx1_m : x₁ = z₁ ∨ x₁ = z₂ ∨ x₁ = z₃ := by
    have h : x₁ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hx2_m : x₂ = z₁ ∨ x₂ = z₂ ∨ x₂ = z₃ := by
    have h : x₂ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hx3_m : x₃ = z₁ ∨ x₃ = z₂ ∨ x₃ = z₃ := by
    have h : x₃ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hx4_ne_z : x₄ ≠ z₁ ∧ x₄ ≠ z₂ ∧ x₄ ≠ z₃ := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases hz1_m with heq | heq | heq
      · exact h14 (h.trans heq).symm
      · exact h24 (h.trans heq).symm
      · exact h34 (h.trans heq).symm
    · rcases hz2_m with heq | heq | heq
      · exact h14 (h.trans heq).symm
      · exact h24 (h.trans heq).symm
      · exact h34 (h.trans heq).symm
    · rcases hz3_m with heq | heq | heq
      · exact h14 (h.trans heq).symm
      · exact h24 (h.trans heq).symm
      · exact h34 (h.trans heq).symm
  have hpush : ({x₁, x₂, x₃, x₄} : Finset ℕ) = {x₄, z₁, z₂, z₃} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · rcases hx1_m with h | h | h <;> simp [h]
      · rcases hx2_m with h | h | h <;> simp [h]
      · rcases hx3_m with h | h | h <;> simp [h]
      · exact Or.inl rfl
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · rcases hz1_m with h | h | h <;> simp [h]
      · rcases hz2_m with h | h | h <;> simp [h]
      · rcases hz3_m with h | h | h <;> simp [h]
  have hperm : ∀ p₁ p₂ p₃ p₄ : ℕ, (p₁ = x₄ ∨ p₁ = z₁ ∨ p₁ = z₂ ∨ p₁ = z₃) →
      (p₂ = x₄ ∨ p₂ = z₁ ∨ p₂ = z₂ ∨ p₂ = z₃) → (p₃ = x₄ ∨ p₃ = z₁ ∨ p₃ = z₂ ∨ p₃ = z₃) →
      (p₄ = x₄ ∨ p₄ = z₁ ∨ p₄ = z₂ ∨ p₄ = z₃) →
      (x₄ = p₁ ∨ x₄ = p₂ ∨ x₄ = p₃ ∨ x₄ = p₄) → (z₁ = p₁ ∨ z₁ = p₂ ∨ z₁ = p₃ ∨ z₁ = p₄) →
      (z₂ = p₁ ∨ z₂ = p₂ ∨ z₂ = p₃ ∨ z₂ = p₄) → (z₃ = p₁ ∨ z₃ = p₂ ∨ z₃ = p₃ ∨ z₃ = p₄) →
      ({x₁, x₂, x₃, x₄} : Finset ℕ) = {p₁, p₂, p₃, p₄} := by
    intro p₁ p₂ p₃ p₄ hp1 hp2 hp3 hp4 hq4 hq1 hq2 hq3
    rw [hpush]; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨by rintro (rfl | rfl | rfl | rfl) <;> assumption, by rintro (rfl | rfl | rfl | rfl) <;> assumption⟩
  rcases lt_or_gt_of_ne hx4_ne_z.1 with h41 | h41
  · rcases lt_or_gt_of_ne hx4_ne_z.2.1 with h42 | h42
    · rcases lt_or_gt_of_ne hx4_ne_z.2.2 with h43 | h43
      · exact ⟨z₁, z₂, z₃, x₄, hperm _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h43, hz32, hz21⟩
      · exact ⟨z₁, z₂, x₄, z₃, hperm _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h43, h42, hz21⟩
    · exact ⟨z₁, x₄, z₂, z₃, hperm _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), hz32, h42, h41⟩
  · exact ⟨x₄, z₁, z₂, z₃, hpush, hz32, hz21, h41⟩

/-- **Unconditional Type 1b 4-Slot Closure**: if `{x₁, x₂, x₃, x₄} ⊆ (M/2, M]` are 4 distinct
    divisors of `b₀ ∈ consecInterval x M` such that EVERY pair spans `A4.lcm id`, then `A4` has
    a `≤ 4`-slot cover in `consecInterval x M`. -/
lemma cover_four_of_type1b {A4 : Finset ℕ} {x M b₀ x₁ x₂ x₃ x₄ : ℕ}
    (hA4_eq : A4 = {x₁, x₂, x₃, x₄})
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄)
    (hpos : ∀ a ∈ A4, 0 < a) (hle : ∀ a ∈ A4, a ≤ M) (hhalf : ∀ a ∈ A4, M < 2 * a)
    (hb₀_I : b₀ ∈ consecInterval x M) (hdiv_b0 : ∀ a ∈ A4, a ∣ b₀)
    (hpair : ∀ a ∈ A4, ∀ b ∈ A4, a ≠ b → Nat.lcm a b = A4.lcm id) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover A4 B := by
  suffices hsorted : ∀ y₁ y₂ y₃ y₄ : ℕ, A4 = {y₁, y₂, y₃, y₄} →
      y₄ < y₃ → y₃ < y₂ → y₂ < y₁ → ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover A4 B by
    obtain ⟨y₁, y₂, y₃, y₄, hy_eq, h43, h32, h21⟩ := sort4_dec h12 h13 h14 h23 h24 h34
    exact hsorted y₁ y₂ y₃ y₄ (hA4_eq.trans hy_eq) h43 h32 h21
  intro y₁ y₂ y₃ y₄ hA4_s hy43 hy32 hy21
  have hy₁_pos : 0 < y₁ := hpos y₁ (by rw [hA4_s]; simp)
  have hy₁_M : y₁ ≤ M := hle y₁ (by rw [hA4_s]; simp)
  let L4 := A4.lcm id
  let Q₁ := L4 / y₁
  let Q₂ := L4 / y₂
  let Q₃ := L4 / y₃
  let Q₄ := L4 / y₄
  obtain ⟨hQ12, hQ23, hQ34, hQ4_lt, hQ1_5, hQ2_7, hQ3_8, hQ4_9,
    hc12, hc13, hc14, hc23, hc24, hc34, hQ1234⟩ :=
    type1b_quotients_props hA4_s hy21 hy32 hy43 hpos hle hhalf hpair
  change Q₁ < Q₂ at hQ12
  change Q₂ < Q₃ at hQ23
  change Q₃ < Q₄ at hQ34
  change Q₄ < 2 * Q₁ at hQ4_lt
  change 5 ≤ Q₁ at hQ1_5
  change 7 ≤ Q₂ at hQ2_7
  change 8 ≤ Q₃ at hQ3_8
  change 9 ≤ Q₄ at hQ4_9
  change Nat.Coprime Q₁ Q₂ at hc12
  change Nat.Coprime Q₁ Q₃ at hc13
  change Nat.Coprime Q₁ Q₄ at hc14
  change Nat.Coprime Q₂ Q₃ at hc23
  change Nat.Coprime Q₂ Q₄ at hc24
  change Nat.Coprime Q₃ Q₄ at hc34
  obtain ⟨D, hD_eq⟩ := hQ1234
  change L4 = Q₁ * Q₂ * Q₃ * Q₄ * D at hD_eq
  have hL4_eq : L4 = D * Q₁ * Q₂ * Q₃ * Q₄ := by rw [hD_eq]; ring
  have hL4_pos : 0 < L4 := finset_lcm_pos_5 hpos
  have hD_pos : 0 < D := Nat.pos_of_ne_zero fun h => by rw [h] at hL4_eq; simp at hL4_eq; omega
  have hy₁_eq : y₁ = D * Q₂ * Q₃ * Q₄ := by
    have hd1 : y₁ ∣ L4 := Finset.dvd_lcm (by rw [hA4_s]; simp)
    have hmul : y₁ * Q₁ = L4 := Nat.mul_div_cancel' hd1
    rw [hL4_eq] at hmul
    have hQ1_pos : 0 < Q₁ := by omega
    have hmul' : y₁ * Q₁ = (D * Q₂ * Q₃ * Q₄) * Q₁ := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_right hQ1_pos hmul'
  have hy₂_eq : y₂ = L4 / Q₂ := by
    have hd2 : y₂ ∣ L4 := Finset.dvd_lcm (by rw [hA4_s]; simp)
    have hmul : y₂ * Q₂ = L4 := Nat.mul_div_cancel' hd2
    rw [← hmul, Nat.mul_div_cancel _ (by omega)]
  have hy₃_eq : y₃ = L4 / Q₃ := by
    have hd3 : y₃ ∣ L4 := Finset.dvd_lcm (by rw [hA4_s]; simp)
    have hmul : y₃ * Q₃ = L4 := Nat.mul_div_cancel' hd3
    rw [← hmul, Nat.mul_div_cancel _ (by omega)]
  have hy₄_eq : y₄ = L4 / Q₄ := by
    have hd4 : y₄ ∣ L4 := Finset.dvd_lcm (by rw [hA4_s]; simp)
    have hmul : y₄ * Q₄ = L4 := Nat.mul_div_cancel' hd4
    rw [← hmul, Nat.mul_div_cancel _ (by omega)]
  have hy₁_eq' : y₁ = L4 / Q₁ := by
    have hd1 : y₁ ∣ L4 := Finset.dvd_lcm (by rw [hA4_s]; simp)
    have hmul : y₁ * Q₁ = L4 := Nat.mul_div_cancel' hd1
    rw [← hmul, Nat.mul_div_cancel _ (by omega)]
  let G₁ := D * Q₁ ^ 2 * Q₂
  let G₂ := D * Q₂ * Q₃ ^ 2
  let G₃ := D * Q₄ ^ 2
  let G₁' := D * Q₁ * Q₂
  let G₂' := D * Q₂ * Q₃
  let G₀ := D * Q₂
  have hG₁_M : G₁ ≤ M := by
    have h1 : Q₁ * Q₁ ≤ Q₃ * Q₄ := Nat.mul_le_mul (by omega) (by omega)
    calc D * Q₁ ^ 2 * Q₂ = D * Q₂ * (Q₁ * Q₁) := by ring
      _ ≤ D * Q₂ * (Q₃ * Q₄) := Nat.mul_le_mul_left _ h1
      _ = y₁ := by rw [hy₁_eq]; ring
      _ ≤ M := hy₁_M
  have hG₂_M : G₂ ≤ M := by
    calc D * Q₂ * Q₃ ^ 2 = D * Q₂ * Q₃ * Q₃ := by ring
      _ ≤ D * Q₂ * Q₃ * Q₄ := Nat.mul_le_mul_left _ (by omega)
      _ = y₁ := hy₁_eq.symm
      _ ≤ M := hy₁_M
  have h4G₃_M : 4 * G₃ ≤ M := by
    have h4Q4 : 4 * Q₄ ≤ Q₂ * Q₃ := by
      have : 4 * Q₄ ≤ 8 * Q₂ := by omega
      exact le_trans this (Nat.mul_le_mul_left Q₂ hQ3_8 |> fun h => by linarith)
    calc 4 * G₃ = D * Q₄ * (4 * Q₄) := by dsimp [G₃]; ring
      _ ≤ D * Q₄ * (Q₂ * Q₃) := Nat.mul_le_mul_left _ h4Q4
      _ = y₁ := by rw [hy₁_eq]; ring
      _ ≤ M := hy₁_M
  have h4G₁'_M : 4 * G₁' ≤ M := by
    have : 4 * Q₁ ≤ Q₃ * Q₄ := by
      have h4q3 : 4 ≤ Q₃ := by omega
      have hq14 : Q₁ ≤ Q₄ := by omega
      nlinarith
    calc 4 * G₁' = D * Q₂ * (4 * Q₁) := by dsimp [G₁']; ring
      _ ≤ D * Q₂ * (Q₃ * Q₄) := Nat.mul_le_mul_left _ this
      _ = y₁ := by rw [hy₁_eq]; ring
      _ ≤ M := hy₁_M
  have h4G₂'_M : 4 * G₂' ≤ M := by
    calc 4 * G₂' = D * Q₂ * Q₃ * 4 := by dsimp [G₂']; ring
      _ ≤ D * Q₂ * Q₃ * Q₄ := Nat.mul_le_mul_left _ (by omega)
      _ = y₁ := hy₁_eq.symm
      _ ≤ M := hy₁_M
  have h4G₀_M : 4 * G₀ ≤ M := by
    calc 4 * G₀ ≤ 4 * (G₀ * Q₃) := Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_right G₀ (by omega))
      _ = 4 * G₂' := by dsimp [G₀, G₂']
      _ ≤ M := h4G₂'_M
  have hA4_0 : ∀ a ∈ A4, a ≠ 0 := fun a ha => (hpos a ha).ne'
  have hb₀0 : b₀ ≠ 0 := (pos_of_mem_consecInterval hb₀_I).ne'
  have hsumA_eq : ∀ p : ℕ, ∑ a ∈ A4, a.factorization p =
      y₁.factorization p + y₂.factorization p + y₃.factorization p + y₄.factorization p := by
    intro p
    rw [hA4_s, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
        Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  have hb₀_L4 : L4 ∣ b₀ := Finset.lcm_dvd (fun a ha => hdiv_b0 a ha)
  have hG1_pos : 0 < G₁ := by dsimp [G₁]; positivity
  have hG2_pos : 0 < G₂ := by dsimp [G₂]; positivity
  have hG3_pos : 0 < G₃ := by dsimp [G₃]; positivity
  have hG1'_pos : 0 < G₁' := by dsimp [G₁']; positivity
  have hG2'_pos : 0 < G₂' := by dsimp [G₂']; positivity
  have hG0_pos : 0 < G₀ := by dsimp [G₀]; positivity
  -- Pick `w₁` multiple of `G₁` and `w₂` multiple of `G₂`.
  obtain ⟨w₁, hw₁_I, hG1_w1⟩ := exists_multiple_in_consecInterval x G₁ M hG1_pos hG₁_M
  obtain ⟨w₂, hw₂_I, hG2_w2⟩ := exists_multiple_in_consecInterval x G₂ M hG2_pos hG₂_M
  -- Helper: when `b₀` is divisible by `G₁`, then `b₀` absorbs extra `Q₁` (`b₀` has `lcm(L4, G₁) = D * Q₁^2 * Q₂ * Q₃ * Q₄`).
  have b0_has_G1 : G₁ ∣ b₀ → ∀ p : ℕ, p.Prime →
      D.factorization p + 2 * Q₁.factorization p + Q₂.factorization p +
        Q₃.factorization p + Q₄.factorization p ≤ b₀.factorization p := by
    intro hG1b p hp
    have hlcm : Nat.lcm L4 G₁ ∣ b₀ := Nat.lcm_dvd hb₀_L4 hG1b
    have hL4G1 : Nat.lcm L4 G₁ = D * Q₁ ^ 2 * Q₂ * Q₃ * Q₄ := by
      -- Since `L4 = (D * Q₁ * Q₂) * (Q₃ * Q₄)` and `G₁ = (D * Q₁ * Q₂) * Q₁` with `Coprime Q₁ (Q₃ * Q₄)`!
      apply Nat.dvd_antisymm
      · apply Nat.lcm_dvd
        · exact ⟨Q₁, by rw [hL4_eq]; ring⟩
        · exact ⟨Q₃ * Q₄, by dsimp [G₁]; ring⟩
      · have hd1 : D * Q₁ * Q₂ * Q₃ * Q₄ ∣ Nat.lcm L4 G₁ := hL4_eq ▸ Nat.dvd_lcm_left L4 G₁
        have hd2 : D * Q₁ ^ 2 * Q₂ ∣ Nat.lcm L4 G₁ := Nat.dvd_lcm_right L4 G₁
        -- Factorizations at prime `p`
        rw [← Nat.factorization_le_iff_dvd (by dsimp [G₁]; positivity)
          (Nat.lcm_ne_zero hL4_pos.ne' hG1_pos.ne')]
        intro q
        by_cases hq : q = 0
        · subst hq; simp
        · by_cases hqp : q.Prime
          · have h1 := fac_le_of_dvd_5 (Nat.lcm_ne_zero hL4_pos.ne' hG1_pos.ne') hd1 (p := q)
            have h2 := fac_le_of_dvd_5 (Nat.lcm_ne_zero hL4_pos.ne' hG1_pos.ne') hd2 (p := q)
            have hQ₁0 : Q₁ ≠ 0 := by omega
            have hQ₂0 : Q₂ ≠ 0 := by omega
            have hQ₃0 : Q₃ ≠ 0 := by omega
            have hQ₄0 : Q₄ ≠ 0 := by omega
            have hD0 : D ≠ 0 := hD_pos.ne'
            have hd_13 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₃) hqp hc13
            have hd_14 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₄) hqp hc14
            have hd_12 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₂) hqp hc12
            rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0) hQ₄0,
                Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0,
                Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
                Nat.factorization_mul hD0 hQ₁0] at h1
            rw [Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
                Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow] at h2
            have heq_target : D * Q₁ ^ 2 * Q₂ * Q₃ * Q₄ = D * Q₁ ^ 2 * Q₂ * Q₃ * Q₄ := rfl
            rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0) hQ₃0) hQ₄0,
                Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0) hQ₃0,
                Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
                Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow]
            simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1 h2 ⊢
            omega
          · simp [Nat.factorization_eq_zero_of_not_prime _ hqp]
    have hb0_fac := fac_le_of_dvd_5 hb₀0 (hL4G1 ▸ hlcm) (p := p)
    have hD0 : D ≠ 0 := hD_pos.ne'
    have hQ₁0 : Q₁ ≠ 0 := by omega
    have hQ₂0 : Q₂ ≠ 0 := by omega
    have hQ₃0 : Q₃ ≠ 0 := by omega
    have hQ₄0 : Q₄ ≠ 0 := by omega
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0) hQ₃0) hQ₄0,
        Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0) hQ₃0,
        Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
        Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow] at hb0_fac
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hb0_fac
    omega
  have b0_has_G2 : G₂ ∣ b₀ → ∀ p : ℕ, p.Prime →
      D.factorization p + Q₁.factorization p + Q₂.factorization p +
        2 * Q₃.factorization p + Q₄.factorization p ≤ b₀.factorization p := by
    intro hG2b p hp
    have hlcm : Nat.lcm L4 G₂ ∣ b₀ := Nat.lcm_dvd hb₀_L4 hG2b
    have hL4G2 : Nat.lcm L4 G₂ = D * Q₁ * Q₂ * Q₃ ^ 2 * Q₄ := by
      apply Nat.dvd_antisymm
      · apply Nat.lcm_dvd
        · exact ⟨Q₃, by rw [hL4_eq]; ring⟩
        · exact ⟨Q₁ * Q₄, by dsimp [G₂]; ring⟩
      · have hd1 : D * Q₁ * Q₂ * Q₃ * Q₄ ∣ Nat.lcm L4 G₂ := hL4_eq ▸ Nat.dvd_lcm_left L4 G₂
        have hd2 : D * Q₂ * Q₃ ^ 2 ∣ Nat.lcm L4 G₂ := Nat.dvd_lcm_right L4 G₂
        rw [← Nat.factorization_le_iff_dvd (by dsimp [G₂]; positivity)
          (Nat.lcm_ne_zero hL4_pos.ne' hG2_pos.ne')]
        intro q
        by_cases hqp : q.Prime
        · have h1 := fac_le_of_dvd_5 (Nat.lcm_ne_zero hL4_pos.ne' hG2_pos.ne') hd1 (p := q)
          have h2 := fac_le_of_dvd_5 (Nat.lcm_ne_zero hL4_pos.ne' hG2_pos.ne') hd2 (p := q)
          have hQ₁0 : Q₁ ≠ 0 := by omega
          have hQ₂0 : Q₂ ≠ 0 := by omega
          have hQ₃0 : Q₃ ≠ 0 := by omega
          have hQ₄0 : Q₄ ≠ 0 := by omega
          have hD0 : D ≠ 0 := hD_pos.ne'
          have hd_13 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₃) hqp hc13
          have hd_23 := coprime_factorization_zero (by omega : 0 < Q₂) (by omega : 0 < Q₃) hqp hc23
          have hd_34 := coprime_factorization_zero (by omega : 0 < Q₃) (by omega : 0 < Q₄) hqp hc34
          rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0) hQ₄0,
              Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) hQ₃0,
              Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
              Nat.factorization_mul hD0 hQ₁0] at h1
          rw [Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) (pow_ne_zero 2 hQ₃0),
              Nat.factorization_mul hD0 hQ₂0, Nat.factorization_pow] at h2
          rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) (pow_ne_zero 2 hQ₃0)) hQ₄0,
              Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) (pow_ne_zero 2 hQ₃0),
              Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
              Nat.factorization_mul hD0 hQ₁0, Nat.factorization_pow]
          simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1 h2 ⊢
          omega
        · simp [Nat.factorization_eq_zero_of_not_prime _ hqp]
    have hb0_fac := fac_le_of_dvd_5 hb₀0 (hL4G2 ▸ hlcm) (p := p)
    have hD0 : D ≠ 0 := hD_pos.ne'
    have hQ₁0 : Q₁ ≠ 0 := by omega
    have hQ₂0 : Q₂ ≠ 0 := by omega
    have hQ₃0 : Q₃ ≠ 0 := by omega
    have hQ₄0 : Q₄ ≠ 0 := by omega
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) (pow_ne_zero 2 hQ₃0)) hQ₄0,
        Nat.factorization_mul (mul_ne_zero (mul_ne_zero hD0 hQ₁0) hQ₂0) (pow_ne_zero 2 hQ₃0),
        Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
        Nat.factorization_mul hD0 hQ₁0, Nat.factorization_pow] at hb0_fac
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hb0_fac
    omega
  -- Now split on `w₁ = b₀` and `w₂ = b₀` and `w₁ = w₂`!
  by_cases hw1_b0 : w₁ = b₀
  · by_cases hw2_b0 : w₂ = b₀
    · -- Both `G₁ ∣ b₀` and `G₂ ∣ b₀`: pick 3 distinct multiples for `G₁', G₂', G₃` outside `b₀`!
      obtain ⟨w₁', hw₁'_I, hw₁'_not, hG1'_w⟩ := exists_avoiding_multiple_5 x M G₁' {b₀}
        hG1'_pos (le_trans (Nat.mul_le_mul_right G₁' (by simp : ({b₀} : Finset ℕ).card + 1 ≤ 4)) h4G₁'_M)
      obtain ⟨w₂', hw₂'_I, hw₂'_not, hG2'_w⟩ := exists_avoiding_multiple_5 x M G₂' {b₀, w₁'}
        hG2'_pos (le_trans (Nat.mul_le_mul_right G₂' (by
          have := Finset.card_insert_le b₀ {w₁'}; simp at this ⊢; omega)) h4G₂'_M)
      obtain ⟨w₃', hw₃'_I, hw₃'_not, hG3_w⟩ := exists_avoiding_multiple_5 x M G₃ {b₀, w₁', w₂'}
        hG3_pos (le_trans (Nat.mul_le_mul_right G₃ (by
          have h1 := Finset.card_insert_le b₀ {w₁', w₂'}
          have h2 := Finset.card_insert_le w₁' {w₂'}; simp at h2 ⊢; omega)) h4G₃_M)
      have hw1'_b0 : w₁' ≠ b₀ := by simpa using hw₁'_not
      have hw2'_b0 : w₂' ≠ b₀ := fun h => hw₂'_not (by simp [h])
      have hw2'_w1 : w₂' ≠ w₁' := fun h => hw₂'_not (by simp [h])
      have hw3'_b0 : w₃' ≠ b₀ := fun h => hw₃'_not (by simp [h])
      have hw3'_w1 : w₃' ≠ w₁' := fun h => hw₃'_not (by simp [h])
      have hw3'_w2 : w₃' ≠ w₂' := fun h => hw₃'_not (by simp [h])
      let B : Finset ℕ := {b₀, w₁', w₂', w₃'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
      intro p hp
      rw [hsumA_eq p]
      have hsumB : b₀.factorization p + w₁'.factorization p + w₂'.factorization p + w₃'.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hw1'_b0.symm, hw2'_b0.symm, hw3'_b0.symm]),
            Finset.sum_insert (by simp [hw2'_w1.symm, hw3'_w1.symm]),
            Finset.sum_insert (by simp [hw3'_w2.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hdec := type1b_fac_decomp hp hL4_eq hL4_pos.ne' hc12 hc13 hc14 hc23 hc24 hc34
      rw [hy₁_eq', hy₂_eq, hy₃_eq, hy₄_eq]
      rw [hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2]
      have hb01 := b0_has_G1 (hw1_b0 ▸ hG1_w1) p hp
      have hb02 := b0_has_G2 (hw2_b0 ▸ hG2_w2) p hp
      have hw10' : w₁' ≠ 0 := (pos_of_mem_consecInterval hw₁'_I).ne'
      have hw20' : w₂' ≠ 0 := (pos_of_mem_consecInterval hw₂'_I).ne'
      have hw30' : w₃' ≠ 0 := (pos_of_mem_consecInterval hw₃'_I).ne'
      have hvg1 := fac_le_of_dvd_5 hw10' hG1'_w (p := p)
      have hvg2 := fac_le_of_dvd_5 hw20' hG2'_w (p := p)
      have hvg3 := fac_le_of_dvd_5 hw30' hG3_w (p := p)
      have hQ₁0 : Q₁ ≠ 0 := by omega
      have hQ₂0 : Q₂ ≠ 0 := by omega
      have hQ₃0 : Q₃ ≠ 0 := by omega
      have hQ₄0 : Q₄ ≠ 0 := by omega
      have hD0 : D ≠ 0 := hD_pos.ne'
      rw [show G₁' = D * Q₁ * Q₂ from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
          Nat.factorization_mul hD0 hQ₁0] at hvg1
      rw [show G₂' = D * Q₂ * Q₃ from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) hQ₃0,
          Nat.factorization_mul hD0 hQ₂0] at hvg2
      rw [show G₃ = D * Q₄ ^ 2 from rfl, Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₄0),
          Nat.factorization_pow] at hvg3
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hvg1 hvg2 hvg3
      have hineq := type1b_val_ineq_hit12 (D.factorization p) (Q₁.factorization p) (Q₂.factorization p)
        (Q₃.factorization p) (Q₄.factorization p)
      have hcop_13 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₃) hp hc13
      rcases hcop_13 with hq1z | hq3z
      · rw [hq1z] at hb02 hineq ⊢; omega
      · rw [hq3z] at hb01 hineq ⊢; omega
    · -- `w₁ = b₀, w₂ ≠ b₀`: pick `w₁' ∉ {b₀, w₂}` (`G₁'`), `w₃' ∉ {b₀, w₂, w₁'}` (`G₃`).
      obtain ⟨w₁', hw₁'_I, hw₁'_not, hG1'_w⟩ := exists_avoiding_multiple_5 x M G₁' {b₀, w₂}
        hG1'_pos (le_trans (Nat.mul_le_mul_right G₁' (by
          have := Finset.card_insert_le b₀ {w₂}; simp at this ⊢; omega)) h4G₁'_M)
      obtain ⟨w₃', hw₃'_I, hw₃'_not, hG3_w⟩ := exists_avoiding_multiple_5 x M G₃ {b₀, w₂, w₁'}
        hG3_pos (le_trans (Nat.mul_le_mul_right G₃ (by
          have h1 := Finset.card_insert_le b₀ {w₂, w₁'}
          have h2 := Finset.card_insert_le w₂ {w₁'}; simp at h2 ⊢; omega)) h4G₃_M)
      have hw1'_b0 : w₁' ≠ b₀ := fun h => hw₁'_not (by simp [h])
      have hw1'_w2 : w₁' ≠ w₂ := fun h => hw₁'_not (by simp [h])
      have hw3'_b0 : w₃' ≠ b₀ := fun h => hw₃'_not (by simp [h])
      have hw3'_w2 : w₃' ≠ w₂ := fun h => hw₃'_not (by simp [h])
      have hw3'_w1 : w₃' ≠ w₁' := fun h => hw₃'_not (by simp [h])
      let B : Finset ℕ := {b₀, w₁', w₂, w₃'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
      intro p hp
      rw [hsumA_eq p]
      have hsumB : b₀.factorization p + w₁'.factorization p + w₂.factorization p + w₃'.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [Ne.symm hw1'_b0, Ne.symm hw2_b0, Ne.symm hw3'_b0]),
            Finset.sum_insert (by simp [hw1'_w2, Ne.symm hw3'_w1]),
            Finset.sum_insert (by simp [Ne.symm hw3'_w2]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hdec := type1b_fac_decomp hp hL4_eq hL4_pos.ne' hc12 hc13 hc14 hc23 hc24 hc34
      rw [hy₁_eq', hy₂_eq, hy₃_eq, hy₄_eq]
      rw [hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2]
      have hb01 := b0_has_G1 (hw1_b0 ▸ hG1_w1) p hp
      have hw10' : w₁' ≠ 0 := (pos_of_mem_consecInterval hw₁'_I).ne'
      have hw20' : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hw30' : w₃' ≠ 0 := (pos_of_mem_consecInterval hw₃'_I).ne'
      have hvg1 := fac_le_of_dvd_5 hw10' hG1'_w (p := p)
      have hvg2 := fac_le_of_dvd_5 hw20' hG2_w2 (p := p)
      have hvg3 := fac_le_of_dvd_5 hw30' hG3_w (p := p)
      have hQ₁0 : Q₁ ≠ 0 := by omega
      have hQ₂0 : Q₂ ≠ 0 := by omega
      have hQ₃0 : Q₃ ≠ 0 := by omega
      have hQ₄0 : Q₄ ≠ 0 := by omega
      have hD0 : D ≠ 0 := hD_pos.ne'
      rw [show G₁' = D * Q₁ * Q₂ from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₁0) hQ₂0,
          Nat.factorization_mul hD0 hQ₁0] at hvg1
      rw [show G₂ = D * Q₂ * Q₃ ^ 2 from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) (pow_ne_zero 2 hQ₃0),
          Nat.factorization_mul hD0 hQ₂0, Nat.factorization_pow] at hvg2
      rw [show G₃ = D * Q₄ ^ 2 from rfl, Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₄0),
          Nat.factorization_pow] at hvg3
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hvg1 hvg2 hvg3
      have hineq := type1b_val_ineq_hit1 (D.factorization p) (Q₁.factorization p) (Q₂.factorization p)
        (Q₃.factorization p) (Q₄.factorization p)
      omega
  · by_cases hw2_b0 : w₂ = b₀
    · -- `w₁ ≠ b₀, w₂ = b₀`: pick `w₂' ∉ {b₀, w₁}` (`G₂'`), `w₃' ∉ {b₀, w₁, w₂'}` (`G₃`).
      obtain ⟨w₂', hw₂'_I, hw₂'_not, hG2'_w⟩ := exists_avoiding_multiple_5 x M G₂' {b₀, w₁}
        hG2'_pos (le_trans (Nat.mul_le_mul_right G₂' (by
          have := Finset.card_insert_le b₀ {w₁}; simp at this ⊢; omega)) h4G₂'_M)
      obtain ⟨w₃', hw₃'_I, hw₃'_not, hG3_w⟩ := exists_avoiding_multiple_5 x M G₃ {b₀, w₁, w₂'}
        hG3_pos (le_trans (Nat.mul_le_mul_right G₃ (by
          have h1 := Finset.card_insert_le b₀ {w₁, w₂'}
          have h2 := Finset.card_insert_le w₁ {w₂'}; simp at h2 ⊢; omega)) h4G₃_M)
      have hw2'_b0 : w₂' ≠ b₀ := fun h => hw₂'_not (by simp [h])
      have hw2'_w1 : w₂' ≠ w₁ := fun h => hw₂'_not (by simp [h])
      have hw3'_b0 : w₃' ≠ b₀ := fun h => hw₃'_not (by simp [h])
      have hw3'_w1 : w₃' ≠ w₁ := fun h => hw₃'_not (by simp [h])
      have hw3'_w2 : w₃' ≠ w₂' := fun h => hw₃'_not (by simp [h])
      let B : Finset ℕ := {b₀, w₁, w₂', w₃'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
      intro p hp
      rw [hsumA_eq p]
      have hsumB : b₀.factorization p + w₁.factorization p + w₂'.factorization p + w₃'.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [Ne.symm hw1_b0, Ne.symm hw2'_b0, Ne.symm hw3'_b0]),
            Finset.sum_insert (by simp [Ne.symm hw2'_w1, Ne.symm hw3'_w1]),
            Finset.sum_insert (by simp [Ne.symm hw3'_w2]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hdec := type1b_fac_decomp hp hL4_eq hL4_pos.ne' hc12 hc13 hc14 hc23 hc24 hc34
      rw [hy₁_eq', hy₂_eq, hy₃_eq, hy₄_eq]
      rw [hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2]
      have hb02 := b0_has_G2 (hw2_b0 ▸ hG2_w2) p hp
      have hw10' : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
      have hw20' : w₂' ≠ 0 := (pos_of_mem_consecInterval hw₂'_I).ne'
      have hw30' : w₃' ≠ 0 := (pos_of_mem_consecInterval hw₃'_I).ne'
      have hvg1 := fac_le_of_dvd_5 hw10' hG1_w1 (p := p)
      have hvg2 := fac_le_of_dvd_5 hw20' hG2'_w (p := p)
      have hvg3 := fac_le_of_dvd_5 hw30' hG3_w (p := p)
      have hQ₁0 : Q₁ ≠ 0 := by omega
      have hQ₂0 : Q₂ ≠ 0 := by omega
      have hQ₃0 : Q₃ ≠ 0 := by omega
      have hQ₄0 : Q₄ ≠ 0 := by omega
      have hD0 : D ≠ 0 := hD_pos.ne'
      rw [show G₁ = D * Q₁ ^ 2 * Q₂ from rfl, Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
          Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow] at hvg1
      rw [show G₂' = D * Q₂ * Q₃ from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) hQ₃0,
          Nat.factorization_mul hD0 hQ₂0] at hvg2
      rw [show G₃ = D * Q₄ ^ 2 from rfl, Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₄0),
          Nat.factorization_pow] at hvg3
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hvg1 hvg2 hvg3
      have hineq := type1b_val_ineq_hit2 (D.factorization p) (Q₁.factorization p) (Q₂.factorization p)
        (Q₃.factorization p) (Q₄.factorization p)
      omega
    · by_cases hw12 : w₁ = w₂
      · -- `w₁ = w₂ ≠ b₀`: pick `w₀' ∉ {b₀, w₁}` (`G₀ = D * Q₂`) and `w₃' ∉ {b₀, w₁, w₀'}` (`G₃`).
        obtain ⟨w₀', hw₀'_I, hw₀'_not, hG0_w⟩ := exists_avoiding_multiple_5 x M G₀ {b₀, w₁}
          hG0_pos (le_trans (Nat.mul_le_mul_right G₀ (by
            have := Finset.card_insert_le b₀ {w₁}; simp at this ⊢; omega)) h4G₀_M)
        obtain ⟨w₃', hw₃'_I, hw₃'_not, hG3_w⟩ := exists_avoiding_multiple_5 x M G₃ {b₀, w₁, w₀'}
          hG3_pos (le_trans (Nat.mul_le_mul_right G₃ (by
            have h1 := Finset.card_insert_le b₀ {w₁, w₀'}
            have h2 := Finset.card_insert_le w₁ {w₀'}; simp at h2 ⊢; omega)) h4G₃_M)
        have hw0'_b0 : w₀' ≠ b₀ := fun h => hw₀'_not (by simp [h])
        have hw0'_w1 : w₀' ≠ w₁ := fun h => hw₀'_not (by simp [h])
        have hw3'_b0 : w₃' ≠ b₀ := fun h => hw₃'_not (by simp [h])
        have hw3'_w1 : w₃' ≠ w₁ := fun h => hw₃'_not (by simp [h])
        have hw3'_w0 : w₃' ≠ w₀' := fun h => hw₃'_not (by simp [h])
        let B : Finset ℕ := {b₀, w₁, w₀', w₃'}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₁.factorization p + w₀'.factorization p + w₃'.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [Ne.symm hw1_b0, Ne.symm hw0'_b0, Ne.symm hw3'_b0]),
              Finset.sum_insert (by simp [Ne.symm hw0'_w1, Ne.symm hw3'_w1]),
              Finset.sum_insert (by simp [Ne.symm hw3'_w0]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hdec := type1b_fac_decomp hp hL4_eq hL4_pos.ne' hc12 hc13 hc14 hc23 hc24 hc34
        rw [hy₁_eq', hy₂_eq, hy₃_eq, hy₄_eq]
        rw [hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2]
        have hb0_L := fac_le_of_dvd_5 hb₀0 hb₀_L4 (p := p)
        rw [hdec.1] at hb0_L
        have hw10' : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
        have hw00' : w₀' ≠ 0 := (pos_of_mem_consecInterval hw₀'_I).ne'
        have hw30' : w₃' ≠ 0 := (pos_of_mem_consecInterval hw₃'_I).ne'
        have hvg1 := fac_le_of_dvd_5 hw10' hG1_w1 (p := p)
        have hvg2 := fac_le_of_dvd_5 hw10' (hw12 ▸ hG2_w2) (p := p)
        have hvg0 := fac_le_of_dvd_5 hw00' hG0_w (p := p)
        have hvg3 := fac_le_of_dvd_5 hw30' hG3_w (p := p)
        have hQ₁0 : Q₁ ≠ 0 := by omega
        have hQ₂0 : Q₂ ≠ 0 := by omega
        have hQ₃0 : Q₃ ≠ 0 := by omega
        have hQ₄0 : Q₄ ≠ 0 := by omega
        have hD0 : D ≠ 0 := hD_pos.ne'
        rw [show G₁ = D * Q₁ ^ 2 * Q₂ from rfl, Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
            Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow] at hvg1
        rw [show G₂ = D * Q₂ * Q₃ ^ 2 from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) (pow_ne_zero 2 hQ₃0),
            Nat.factorization_mul hD0 hQ₂0, Nat.factorization_pow] at hvg2
        rw [show G₀ = D * Q₂ from rfl, Nat.factorization_mul hD0 hQ₂0] at hvg0
        rw [show G₃ = D * Q₄ ^ 2 from rfl, Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₄0),
            Nat.factorization_pow] at hvg3
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hvg1 hvg2 hvg0 hvg3
        have hcop_13 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₃) hp hc13
        have hcop_12 := coprime_factorization_zero (by omega : 0 < Q₁) (by omega : 0 < Q₂) hp hc12
        have hcop_23 := coprime_factorization_zero (by omega : 0 < Q₂) (by omega : 0 < Q₃) hp hc23
        have hineq := type1b_val_ineq_eq (D.factorization p) (Q₁.factorization p) (Q₂.factorization p)
          (Q₃.factorization p) (Q₄.factorization p)
        rcases hcop_13 with hq1z | hq3z
        · rw [hq1z] at hvg1 hineq hb0_L ⊢; omega
        · rw [hq3z] at hvg2 hineq hb0_L ⊢; omega
      · -- `b₀, w₁, w₂` pairwise distinct: pick `w₃' ∉ {b₀, w₁, w₂}` (`G₃`).
        obtain ⟨w₃', hw₃'_I, hw₃'_not, hG3_w⟩ := exists_avoiding_multiple_5 x M G₃ {b₀, w₁, w₂}
          hG3_pos (le_trans (Nat.mul_le_mul_right G₃ (by
            have h1 := Finset.card_insert_le b₀ {w₁, w₂}
            have h2 := Finset.card_insert_le w₁ {w₂}; simp at h2 ⊢; omega)) h4G₃_M)
        have hw3'_b0 : w₃' ≠ b₀ := fun h => hw₃'_not (by simp [h])
        have hw3'_w1 : w₃' ≠ w₁ := fun h => hw₃'_not (by simp [h])
        have hw3'_w2 : w₃' ≠ w₂ := fun h => hw₃'_not (by simp [h])
        let B : Finset ℕ := {b₀, w₁, w₂, w₃'}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
        intro p hp
        rw [hsumA_eq p]
        have hsumB : b₀.factorization p + w₁.factorization p + w₂.factorization p + w₃'.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [Ne.symm hw1_b0, Ne.symm hw2_b0, Ne.symm hw3'_b0]),
              Finset.sum_insert (by simp [hw12, Ne.symm hw3'_w1]),
              Finset.sum_insert (by simp [Ne.symm hw3'_w2]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hdec := type1b_fac_decomp hp hL4_eq hL4_pos.ne' hc12 hc13 hc14 hc23 hc24 hc34
        rw [hy₁_eq', hy₂_eq, hy₃_eq, hy₄_eq]
        rw [hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2]
        have hb0_L := fac_le_of_dvd_5 hb₀0 hb₀_L4 (p := p)
        rw [hdec.1] at hb0_L
        have hw10' : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
        have hw20' : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
        have hw30' : w₃' ≠ 0 := (pos_of_mem_consecInterval hw₃'_I).ne'
        have hvg1 := fac_le_of_dvd_5 hw10' hG1_w1 (p := p)
        have hvg2 := fac_le_of_dvd_5 hw20' hG2_w2 (p := p)
        have hvg3 := fac_le_of_dvd_5 hw30' hG3_w (p := p)
        have hQ₁0 : Q₁ ≠ 0 := by omega
        have hQ₂0 : Q₂ ≠ 0 := by omega
        have hQ₃0 : Q₃ ≠ 0 := by omega
        have hQ₄0 : Q₄ ≠ 0 := by omega
        have hD0 : D ≠ 0 := hD_pos.ne'
        rw [show G₁ = D * Q₁ ^ 2 * Q₂ from rfl, Nat.factorization_mul (mul_ne_zero hD0 (pow_ne_zero 2 hQ₁0)) hQ₂0,
            Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₁0), Nat.factorization_pow] at hvg1
        rw [show G₂ = D * Q₂ * Q₃ ^ 2 from rfl, Nat.factorization_mul (mul_ne_zero hD0 hQ₂0) (pow_ne_zero 2 hQ₃0),
            Nat.factorization_mul hD0 hQ₂0, Nat.factorization_pow] at hvg2
        rw [show G₃ = D * Q₄ ^ 2 from rfl, Nat.factorization_mul hD0 (pow_ne_zero 2 hQ₄0),
            Nat.factorization_pow] at hvg3
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hvg1 hvg2 hvg3
        have hineq := type1b_val_ineq_main (D.factorization p) (Q₁.factorization p) (Q₂.factorization p)
          (Q₃.factorization p) (Q₄.factorization p)
        rw [← hdec.1] at hb0_L
        omega

/-! ## Part 4: Matching Size `r = 2` Closure (`cover_six_of_r2`) -/

private lemma r2_22_val_ineq (a b c d : ℕ) :
    a + b + c + d ≤ max (a + c - min a c) (max a b) + max (b + d - min b d) (max c d) +
      min a b + min c d := by
  omega

private lemma r2_22_merged_ineq (a b c d : ℕ) :
    a + b + c + d ≤ max a b + max c d + max (min a b) (min c d) + min (min a b) (min c d) := by
  omega

lemma r2_nonspan3_val_ineq (a b c d : ℕ) :
    a + b + c + d ≤ max (max a b) c + d + min a b + min (max a b) c := by
  omega

lemma r2_nonspan3_w2_b2_ineq (a b c d : ℕ) :
    a + b + c + d ≤ max (max a b) c + max (min (max a b) c) d + min a b + min (min (max a b) c) d := by
  omega

lemma r2_31_val_ineq (u1 u2 c v1 : ℕ) :
    u1 + u2 + c + v1 ≤ max u1 u2 + max c v1 + min u1 u2 + min c v1 := by
  omega

lemma r2_31_merged_ineq (u1 u2 c v1 : ℕ) :
    u1 + u2 + c + v1 ≤ max u1 u2 + max c v1 + max (min u1 u2) (min c v1) +
      min (min u1 u2) (min c v1) := by
  omega

lemma four_mul_le_of_four_dvd_distinct {d a₁ a₂ a₃ a₄ M : ℕ}
    (hd : 0 < d) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄)
    (h1p : 0 < a₁) (h2p : 0 < a₂) (h3p : 0 < a₃) (h4p : 0 < a₄)
    (h1M : a₁ ≤ M) (h2M : a₂ ≤ M) (h3M : a₃ ≤ M) (h4M : a₄ ≤ M)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) (hd4 : d ∣ a₄) :
    4 * d ≤ M := by
  let T : Finset ℕ := {a₁, a₂, a₃, a₄}
  have hT := card_mul_le_of_forall_dvd (T := T) (d := d) (M := M) hd (by
    intro a ha; simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨h1p, h1M, hd1⟩
    · exact ⟨h2p, h2M, hd2⟩
    · exact ⟨h3p, h3M, hd3⟩
    · exact ⟨h4p, h4M, hd4⟩)
  have hc : T.card = 4 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
        Finset.card_insert_of_notMem (by simp [h23, h24]),
        Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  rwa [hc] at hT

/-- Helper: non-spanning triple `{y₁, y₂, y₃} ∣ b₁` in `(M/2, M]` plus `v₁ ∣ b₂` (`b₁ ≠ b₂`)
    yields a `≤ 4`-slot cover of `{y₁, y₂, y₃, v₁}` whenever `¬ (v₁ = gcd (lcm y₁ y₂) y₃ ∧ y₃ = 2 * v₁)`. -/
lemma cover_four_of_nonspan3 {x M b₁ b₂ y₁ y₂ y₃ v₁ : ℕ}
    (hy1v : y₁ ≠ v₁) (hy2v : y₂ ≠ v₁) (hy3v : y₃ ≠ v₁)
    (hy12 : y₁ ≠ y₂) (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (hy1p : 0 < y₁) (hy2p : 0 < y₂) (hy3p : 0 < y₃) (hv1p : 0 < v₁)
    (hy1M : y₁ ≤ M) (hy2M : y₂ ≤ M) (hy3M : y₃ ≤ M) (hv1M : v₁ ≤ M)
    (hy1h : M < 2 * y₁) (hy2h : M < 2 * y₂) (hy3h : M < 2 * y₃)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb1_y1 : y₁ ∣ b₁) (hb1_y2 : y₂ ∣ b₁) (hb1_y3 : y₃ ∣ b₁) (hb₂_v1 : v₁ ∣ b₂)
    (hns : ¬ (y₃ ∣ Nat.lcm y₁ y₂))
    (hnot_eq2 : ¬ (v₁ = Nat.gcd (Nat.lcm y₁ y₂) y₃ ∧ y₃ = 2 * v₁)) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover ({y₁, y₂, y₃, v₁} : Finset ℕ) B := by
  let L₁₂ := Nat.lcm y₁ y₂
  have hL12_pos : 0 < L₁₂ := Nat.lcm_pos hy1p hy2p
  let d₂ := Nat.gcd y₁ y₂
  let h := Nat.gcd L₁₂ y₃
  have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_left y₂ hy1p
  have hh_pos : 0 < h := Nat.gcd_pos_of_pos_left y₃ hL12_pos
  have h3d₂ : 3 * d₂ ≤ M := three_mul_le_of_two_gt_half_5 hd₂_pos hy12 hy1M hy2M hy1h hy2h
    (Nat.gcd_dvd_left y₁ y₂) (Nat.gcd_dvd_right y₁ y₂)
  have h2h : 2 * h ≤ M := gcd_not_dvd_mul_le hL12_pos hy3p hy3M hns
  obtain ⟨wh, hwh_I, hwh_nb1, hh_wh⟩ := exists_avoiding_multiple_5 x M h {b₁}
    hh_pos (by simpa using h2h)
  have hwh_b1 : wh ≠ b₁ := by simpa using hwh_nb1
  have hsum_target : ∀ p : ℕ, ∑ a ∈ ({y₁, y₂, y₃, v₁} : Finset ℕ), a.factorization p =
      y₁.factorization p + y₂.factorization p + y₃.factorization p + v₁.factorization p := by
    intro p
    rw [Finset.sum_insert (by simp [hy12, hy13, hy1v]),
        Finset.sum_insert (by simp [hy23, hy2v]),
        Finset.sum_insert (by simp [hy3v]), Finset.sum_singleton]
    ring
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hA_0 : ∀ a ∈ ({y₁, y₂, y₃, v₁} : Finset ℕ), a ≠ 0 := by
    intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  by_cases h3h : 3 * h ≤ M
  · obtain ⟨wh', hwh'_I, hwh'_not, hh_wh'⟩ := exists_avoiding_multiple_5 x M h {b₁, b₂}
      hh_pos (le_trans (Nat.mul_le_mul_right h (by
        have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3h)
    have hwh'_b1 : wh' ≠ b₁ := fun heq => hwh'_not (by simp [heq])
    have hwh'_b2 : wh' ≠ b₂ := fun heq => hwh'_not (by simp [heq])
    by_cases hex2 : ∃ w₂ ∈ consecInterval x M, w₂ ∉ ({b₁, b₂, wh'} : Finset ℕ) ∧ d₂ ∣ w₂
    · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := hex2
      have hw2_b1 : w₂ ≠ b₁ := fun heq => hw₂_not (by simp [heq])
      have hw2_b2 : w₂ ≠ b₂ := fun heq => hw₂_not (by simp [heq])
      have hw2_wh : w₂ ≠ wh' := fun heq => hw₂_not (by simp [heq])
      let B : Finset ℕ := {b₁, b₂, wh', w₂}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA_0 hB0 ?_⟩
      intro p _hp
      rw [hsum_target p]
      have hsumB : b₁.factorization p + b₂.factorization p + wh'.factorization p + w₂.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hb12, hwh'_b1.symm, hw2_b1.symm]),
            Finset.sum_insert (by simp [hwh'_b2.symm, hw2_b2.symm]),
            Finset.sum_insert (by simp [hw2_wh.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hwh0 : wh' ≠ 0 := (pos_of_mem_consecInterval hwh'_I).ne'
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
      have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
      have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
      have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
      have hvh := fac_le_of_dvd_5 hwh0 hh_wh' (p := p)
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
      have hsub : (consecInterval x M).filter (fun b => d₂ ∣ b) ⊆ ({b₁, b₂, wh'} : Finset ℕ) := by
        intro b hb; rw [Finset.mem_filter] at hb
        by_contra hnot; exact hex2 b hb.1 hnot hb.2
      have hge3 : 3 ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card := by
        have h1 := card_multiples_Icc_ge x M d₂ hd₂_pos
        change M / d₂ ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card at h1
        have h2 : 3 ≤ M / d₂ := (Nat.le_div_iff_mul_le hd₂_pos).mpr h3d₂
        omega
      have hcard3 : ({b₁, b₂, wh'} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hb12, hwh'_b1.symm]),
            Finset.card_insert_of_notMem (by simp [hwh'_b2.symm]), Finset.card_singleton]
      have heq_sub : (consecInterval x M).filter (fun b => d₂ ∣ b) = {b₁, b₂, wh'} :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hd₂_b₂ : d₂ ∣ b₂ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : b₂ ∈ ({b₁, b₂, wh'} : Finset ℕ)))).2
      have hd₂_wh : d₂ ∣ wh' := (Finset.mem_filter.mp (heq_sub ▸ (by simp : wh' ∈ ({b₁, b₂, wh'} : Finset ℕ)))).2
      let D' := Nat.gcd d₂ (Nat.gcd h v₁)
      have hg_hv_pos : 0 < Nat.gcd h v₁ := Nat.gcd_pos_of_pos_left v₁ hh_pos
      have hD'_pos : 0 < D' := Nat.gcd_pos_of_pos_left _ hd₂_pos
      have hD'_1 : D' ∣ y₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left y₁ y₂)
      have hD'_2 : D' ∣ y₂ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right y₁ y₂)
      have hD'_3 : D' ∣ y₃ := dvd_trans (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left h v₁))
        (Nat.gcd_dvd_right L₁₂ y₃)
      have hD'_v : D' ∣ v₁ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right h v₁)
      have h4D' : 4 * D' ≤ M := four_mul_le_of_four_dvd_distinct hD'_pos hy12 hy13 hy1v hy23 hy2v hy3v
        hy1p hy2p hy3p hv1p hy1M hy2M hy3M hv1M hD'_1 hD'_2 hD'_3 hD'_v
      obtain ⟨w', hw'_I, hw'_not, hD'_w'⟩ := exists_avoiding_multiple_5 x M D' {b₁, b₂, wh'}
        hD'_pos (le_trans (Nat.mul_le_mul_right D' (by omega : ({b₁, b₂, wh'} : Finset ℕ).card + 1 ≤ 4)) h4D')
      have hw'_b1 : w' ≠ b₁ := fun heq => hw'_not (by simp [heq])
      have hw'_b2 : w' ≠ b₂ := fun heq => hw'_not (by simp [heq])
      have hw'_wh : w' ≠ wh' := fun heq => hw'_not (by simp [heq])
      let B : Finset ℕ := {b₁, b₂, wh', w'}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA_0 hB0 ?_⟩
      intro p _hp
      rw [hsum_target p]
      have hsumB : b₁.factorization p + b₂.factorization p + wh'.factorization p + w'.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hb12, hwh'_b1.symm, hw'_b1.symm]),
            Finset.sum_insert (by simp [hwh'_b2.symm, hw'_b2.symm]),
            Finset.sum_insert (by simp [hw'_wh.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hwh0 : wh' ≠ 0 := (pos_of_mem_consecInterval hwh'_I).ne'
      have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
      have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
      have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
      have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
      have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
      have hb2_d2 := fac_le_of_dvd_5 hb₂0 hd₂_b₂ (p := p)
      have hvh := fac_le_of_dvd_5 hwh0 hh_wh' (p := p)
      have hvd2_wh := fac_le_of_dvd_5 hwh0 hd₂_wh (p := p)
      have hvdD := fac_le_of_dvd_5 hw'0 hD'_w' (p := p)
      rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hb2_d2 hvd2_wh
      rw [fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvh
      rw [fac_gcd_eq_min_5 hd₂_pos.ne' hg_hv_pos.ne', fac_gcd_eq_min_5 hh_pos.ne' hv1p.ne',
          fac_gcd_eq_min_5 hy1p.ne' hy2p.ne',
          fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvdD
      have hb1p : max (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) ≤ b₁.factorization p := by omega
      omega
  · by_cases hwh_b2 : wh = b₂
    · have hh_b2 : h ∣ b₂ := hwh_b2 ▸ hh_wh
      have hnd_hv1 : ¬ (h ∣ v₁) := by
        intro hdv1
        obtain ⟨q₁, hq1⟩ := Nat.gcd_dvd_right L₁₂ y₃
        obtain ⟨q₂, hq2⟩ := hdv1
        have hq1_2 : 2 ≤ q₁ := by
          by_contra hlt; have : q₁ ≤ 1 := by omega
          have h0 : q₁ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hq1; omega
          have : q₁ = 1 := by omega
          rw [this, mul_one] at hq1
          exact hns (hq1 ▸ Nat.gcd_dvd_left L₁₂ y₃)
        have hq1_eq2 : q₁ = 2 := by
          by_contra hne2; have hq1_ge3 : 3 ≤ q₁ := by omega
          have : 3 * h ≤ y₃ := by nlinarith
          omega
        have hq2_pos : 1 ≤ q₂ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq2; omega
        by_cases hq2_1 : q₂ = 1
        · exact hnot_eq2 ⟨by rw [hq2, hq2_1, mul_one], by rw [hq1, hq1_eq2, hq2, hq2_1, mul_one, mul_comm]⟩
        · have hq2_2 : 2 ≤ q₂ := by omega
          have hq2_eq2 : q₂ = 2 := by
            by_contra hne2; have hq2_ge3 : 3 ≤ q₂ := by omega
            have : 3 * h ≤ v₁ := by nlinarith
            omega
          exact hy3v (by rw [hq1, hq2, hq1_eq2, hq2_eq2])
      let g' := Nat.gcd h v₁
      have hg'_pos : 0 < g' := Nat.gcd_pos_of_pos_left v₁ hh_pos
      have h4g' : 4 * g' ≤ M := by
        have h2gh : 2 * Nat.gcd v₁ h ≤ h := gcd_not_dvd_mul_le hv1p hh_pos (le_refl h) hnd_hv1
        have : 2 * g' ≤ h := by simpa only [g', Nat.gcd_comm] using h2gh
        omega
      obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := exists_avoiding_multiple_5 x M d₂ {b₁, b₂}
        hd₂_pos (le_trans (Nat.mul_le_mul_right d₂ (by
          have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3d₂)
      obtain ⟨wg, hwg_I, hwg_not, hg'_wg⟩ := exists_avoiding_multiple_5 x M g' {b₁, b₂, w₂}
        hg'_pos (le_trans (Nat.mul_le_mul_right g' (by
          have h1 := Finset.card_insert_le b₁ {b₂, w₂}
          have h2 := Finset.card_insert_le b₂ {w₂}; simp at h2 ⊢; omega)) h4g')
      have hw2_b1 : w₂ ≠ b₁ := fun heq => hw₂_not (by simp [heq])
      have hw2_b2 : w₂ ≠ b₂ := fun heq => hw₂_not (by simp [heq])
      have hwg_b1 : wg ≠ b₁ := fun heq => hwg_not (by simp [heq])
      have hwg_b2 : wg ≠ b₂ := fun heq => hwg_not (by simp [heq])
      have hwg_w2 : wg ≠ w₂ := fun heq => hwg_not (by simp [heq])
      let B : Finset ℕ := {b₁, b₂, w₂, wg}
      have hBI : B ⊆ consecInterval x M := by
        intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> assumption
      have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
      refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
        isCover_of_prime_factorization_5 hA_0 hB0 ?_⟩
      intro p _hp
      rw [hsum_target p]
      have hsumB : b₁.factorization p + b₂.factorization p + w₂.factorization p + wg.factorization p =
          ∑ b ∈ B, b.factorization p := by
        dsimp [B]
        rw [Finset.sum_insert (by simp [hb12, hw2_b1.symm, hwg_b1.symm]),
            Finset.sum_insert (by simp [hw2_b2.symm, hwg_b2.symm]),
            Finset.sum_insert (by simp [hwg_w2.symm]), Finset.sum_singleton]
        ring
      rw [← hsumB]
      have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
      have hwg0 : wg ≠ 0 := (pos_of_mem_consecInterval hwg_I).ne'
      have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
      have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
      have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
      have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
      have hb2_h := fac_le_of_dvd_5 hb₂0 hh_b2 (p := p)
      have hvd2 := fac_le_of_dvd_5 hw20 hd₂_w₂ (p := p)
      have hvg' := fac_le_of_dvd_5 hwg0 hg'_wg (p := p)
      rw [fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hb2_h
      rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hvd2
      rw [fac_gcd_eq_min_5 hh_pos.ne' hv1p.ne',
          fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvg'
      have hvi := r2_nonspan3_w2_b2_ineq (y₁.factorization p) (y₂.factorization p)
        (y₃.factorization p) (v₁.factorization p)
      change y₁.factorization p + y₂.factorization p + y₃.factorization p + v₁.factorization p ≤
        max (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) +
        max (min (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p)) (v₁.factorization p) +
        min (y₁.factorization p) (y₂.factorization p) +
        min (min (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p)) (v₁.factorization p) at hvi
      omega
    · by_cases hex2 : ∃ w₂ ∈ consecInterval x M, w₂ ∉ ({b₁, b₂, wh} : Finset ℕ) ∧ d₂ ∣ w₂
      · obtain ⟨w₂, hw₂_I, hw₂_not, hd₂_w₂⟩ := hex2
        have hw2_b1 : w₂ ≠ b₁ := fun heq => hw₂_not (by simp [heq])
        have hw2_b2 : w₂ ≠ b₂ := fun heq => hw₂_not (by simp [heq])
        have hw2_wh : w₂ ≠ wh := fun heq => hw₂_not (by simp [heq])
        let B : Finset ℕ := {b₁, b₂, wh, w₂}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA_0 hB0 ?_⟩
        intro p _hp
        rw [hsum_target p]
        have hsumB : b₁.factorization p + b₂.factorization p + wh.factorization p + w₂.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hb12, Ne.symm hwh_b1, Ne.symm hw2_b1]),
              Finset.sum_insert (by simp [Ne.symm hwh_b2, Ne.symm hw2_b2]),
              Finset.sum_insert (by simp [Ne.symm hw2_wh]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hwh0 : wh ≠ 0 := (pos_of_mem_consecInterval hwh_I).ne'
        have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
        have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
        have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
        have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
        have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
        have hvh := fac_le_of_dvd_5 hwh0 hh_wh (p := p)
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
          intro b hb; rw [Finset.mem_filter] at hb
          by_contra hnot; exact hex2 b hb.1 hnot hb.2
        have hge3 : 3 ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card := by
          have h1 := card_multiples_Icc_ge x M d₂ hd₂_pos
          change M / d₂ ≤ ((consecInterval x M).filter (fun b => d₂ ∣ b)).card at h1
          have h2 : 3 ≤ M / d₂ := (Nat.le_div_iff_mul_le hd₂_pos).mpr h3d₂
          omega
        have hcard3 : ({b₁, b₂, wh} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hb12, Ne.symm hwh_b1]),
              Finset.card_insert_of_notMem (by simp [Ne.symm hwh_b2]), Finset.card_singleton]
        have heq_sub : (consecInterval x M).filter (fun b => d₂ ∣ b) = {b₁, b₂, wh} :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hd₂_b₂ : d₂ ∣ b₂ := (Finset.mem_filter.mp (heq_sub ▸ (by simp : b₂ ∈ ({b₁, b₂, wh} : Finset ℕ)))).2
        have hd₂_wh : d₂ ∣ wh := (Finset.mem_filter.mp (heq_sub ▸ (by simp : wh ∈ ({b₁, b₂, wh} : Finset ℕ)))).2
        let D' := Nat.gcd d₂ (Nat.gcd h v₁)
        have hg_hv_pos : 0 < Nat.gcd h v₁ := Nat.gcd_pos_of_pos_left v₁ hh_pos
        have hD'_pos : 0 < D' := Nat.gcd_pos_of_pos_left _ hd₂_pos
        have hD'_1 : D' ∣ y₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left y₁ y₂)
        have hD'_2 : D' ∣ y₂ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right y₁ y₂)
        have hD'_3 : D' ∣ y₃ := dvd_trans (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left h v₁))
          (Nat.gcd_dvd_right L₁₂ y₃)
        have hD'_v : D' ∣ v₁ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right h v₁)
        have h4D' : 4 * D' ≤ M := four_mul_le_of_four_dvd_distinct hD'_pos hy12 hy13 hy1v hy23 hy2v hy3v
          hy1p hy2p hy3p hv1p hy1M hy2M hy3M hv1M hD'_1 hD'_2 hD'_3 hD'_v
        obtain ⟨w', hw'_I, hw'_not, hD'_w'⟩ := exists_avoiding_multiple_5 x M D' {b₁, b₂, wh}
          hD'_pos (le_trans (Nat.mul_le_mul_right D' (by omega : ({b₁, b₂, wh} : Finset ℕ).card + 1 ≤ 4)) h4D')
        have hw'_b1 : w' ≠ b₁ := fun heq => hw'_not (by simp [heq])
        have hw'_b2 : w' ≠ b₂ := fun heq => hw'_not (by simp [heq])
        have hw'_wh : w' ≠ wh := fun heq => hw'_not (by simp [heq])
        let B : Finset ℕ := {b₁, b₂, wh, w'}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 hA_0 hB0 ?_⟩
        intro p _hp
        rw [hsum_target p]
        have hsumB : b₁.factorization p + b₂.factorization p + wh.factorization p + w'.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hb12, Ne.symm hwh_b1, Ne.symm hw'_b1]),
              Finset.sum_insert (by simp [Ne.symm hwh_b2, Ne.symm hw'_b2]),
              Finset.sum_insert (by simp [Ne.symm hw'_wh]), Finset.sum_singleton]
          ring
        rw [← hsumB]
        have hwh0 : wh ≠ 0 := (pos_of_mem_consecInterval hwh_I).ne'
        have hw'0 : w' ≠ 0 := (pos_of_mem_consecInterval hw'_I).ne'
        have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
        have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
        have hb1_3 := fac_le_of_dvd_5 hb₁0 hb1_y3 (p := p)
        have hb2_v := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
        have hb2_d2 := fac_le_of_dvd_5 hb₂0 hd₂_b₂ (p := p)
        have hvh := fac_le_of_dvd_5 hwh0 hh_wh (p := p)
        have hvd2_wh := fac_le_of_dvd_5 hwh0 hd₂_wh (p := p)
        have hvdD := fac_le_of_dvd_5 hw'0 hD'_w' (p := p)
        rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hb2_d2 hvd2_wh
        rw [fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvh
        rw [fac_gcd_eq_min_5 hd₂_pos.ne' hg_hv_pos.ne', fac_gcd_eq_min_5 hh_pos.ne' hv1p.ne',
            fac_gcd_eq_min_5 hy1p.ne' hy2p.ne',
            fac_gcd_eq_min_5 hL12_pos.ne' hy3p.ne', fac_lcm_eq_max_5 hy1p.ne' hy2p.ne'] at hvdD
        have hb1p : max (max (y₁.factorization p) (y₂.factorization p)) (y₃.factorization p) ≤ b₁.factorization p := by omega
        omega

private lemma bad_quad_eq_23 {a b M : ℕ} (hab : a < b) (hbM : b ≤ M) (hah : M < 2 * a)
    (h4gt : M < 4 * Nat.gcd a b) :
    2 * Nat.gcd a b = a ∧ 3 * Nat.gcd a b = b := by
  let g := Nat.gcd a b
  obtain ⟨qa, hqa⟩ := Nat.gcd_dvd_left a b
  obtain ⟨qb, hqb⟩ := Nat.gcd_dvd_right a b
  have hqa_lt : qa < qb := by
    by_contra hle
    have hmul : g * qb ≤ g * qa := Nat.mul_le_mul_left g (by omega)
    rw [← hqa, ← hqb] at hmul
    omega
  have hqa_pos : 1 ≤ qa := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hqa; omega
  have hqa_ge2 : 2 ≤ qa := by
    by_contra hlt; have hqa1 : qa ≤ 1 := by omega
    have ha_le : a ≤ g := by nlinarith
    have h2g_le : 2 * g ≤ b := by nlinarith
    omega
  have hqb_lt4 : qb < 4 := by
    by_contra hge4; have h4g_le : 4 * g ≤ b := by nlinarith
    omega
  have hqa2 : qa = 2 := by omega
  have hqb3 : qb = 3 := by omega
  exact ⟨by change 2 * g = a; rw [hqa, hqa2, mul_comm], by change 3 * g = b; rw [hqb, hqb3, mul_comm]⟩

/-- Helper: Case `(3, 2)` all elements in `(M/2, M]`, `u₁, u₂, u₃ ∣ b₁`, `v₁, v₂ ∣ b₂`. -/
lemma cover_four_of_32_half {x M b₁ b₂ u₁ u₂ u₃ v₁ v₂ : ℕ}
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h1v1 : u₁ ≠ v₁) (h1v2 : u₁ ≠ v₂)
    (h23 : u₂ ≠ u₃) (h2v1 : u₂ ≠ v₁) (h2v2 : u₂ ≠ v₂)
    (h3v1 : u₃ ≠ v₁) (h3v2 : u₃ ≠ v₂) (hv12 : v₁ ≠ v₂)
    (hpos : ∀ a ∈ ({u₁, u₂, u₃, v₁, v₂} : Finset ℕ), 0 < a)
    (hle : ∀ a ∈ ({u₁, u₂, u₃, v₁, v₂} : Finset ℕ), a ≤ M)
    (hhalf : ∀ a ∈ ({u₁, u₂, u₃, v₁, v₂} : Finset ℕ), M < 2 * a)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb₁_u1 : u₁ ∣ b₁) (hb₁_u2 : u₂ ∣ b₁) (hb₁_u3 : u₃ ∣ b₁)
    (hb₂_v1 : v₁ ∣ b₂) (hb₂_v2 : v₂ ∣ b₂) :
    ∃ u ∈ ({u₁, u₂, u₃, v₁, v₂} : Finset ℕ),
      ∃ B ⊆ consecInterval x M, B.card ≤ 4 ∧ IsCover (({u₁, u₂, u₃, v₁, v₂} : Finset ℕ).erase u) B := by
  let A : Finset ℕ := {u₁, u₂, u₃, v₁, v₂}
  have h1p : 0 < u₁ := hpos u₁ (by simp)
  have h2p : 0 < u₂ := hpos u₂ (by simp)
  have h3p : 0 < u₃ := hpos u₃ (by simp)
  have hv1p : 0 < v₁ := hpos v₁ (by simp)
  have hv2p : 0 < v₂ := hpos v₂ (by simp)
  have h1M : u₁ ≤ M := hle u₁ (by simp)
  have h2M : u₂ ≤ M := hle u₂ (by simp)
  have h3M : u₃ ≤ M := hle u₃ (by simp)
  have hv1M : v₁ ≤ M := hle v₁ (by simp)
  have hv2M : v₂ ≤ M := hle v₂ (by simp)
  have h1h : M < 2 * u₁ := hhalf u₁ (by simp)
  have h2h : M < 2 * u₂ := hhalf u₂ (by simp)
  have h3h : M < 2 * u₃ := hhalf u₃ (by simp)
  have hv1h : M < 2 * v₁ := hhalf v₁ (by simp)
  have hv2h : M < 2 * v₂ := hhalf v₂ (by simp)
  let g₂ := Nat.gcd v₁ v₂
  have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left v₂ hv1p
  have h3g₂ : 3 * g₂ ≤ M := three_mul_le_of_two_gt_half_5 hg₂_pos hv12 hv1M hv2M hv1h hv2h
    (Nat.gcd_dvd_left v₁ v₂) (Nat.gcd_dvd_right v₁ v₂)
  -- Check that some pair in `{u₁, u₂, u₃}` has `4 * gcd ≤ M`!
  -- Because all 3 are in `(M/2, M]`: take the two smallest `y₁ < y₂ < y₃`, wait: actually any two with `4 * gcd > M`:
  -- Wait: if `gcd(a, b) > M/4` with `a, b ∈ (M/2, M]`, since `M < 4*g` and `M/2 < a < b ≤ M`, quotients `q_a < q_b` satisfy `2*g ≤ M < 4*g`,
  -- so `q_a ≥ 2, q_b ≥ 3` (`q_b ≤ 3`, so `q_a = 2, q_b = 3`)!
  -- If ALL THREE pairs in `{u₁, u₂, u₃}` had `4 * gcd > M`, sorted `y₁ < y₂ < y₃` would have `y₁ = 2 g₁₂, y₂ = 3 g₁₂` AND `y₁ = 2 g₁₃, y₃ = 3 g₁₃`, forcing `y₂ = y₃`!!
  have h4g_pair : ∀ y₁ y₂ y₃ : ℕ, y₁ < y₂ → y₂ < y₃ →
      M < 2 * y₁ → y₃ ≤ M →
      4 * Nat.gcd y₁ y₂ ≤ M ∨ 4 * Nat.gcd y₁ y₃ ≤ M ∨ 4 * Nat.gcd y₂ y₃ ≤ M := by
    intro y₁ y₂ y₃ hy12 hy23 hy1h hy3M
    by_contra hnone; push Not at hnone
    rcases hnone with ⟨h12_gt, h13_gt, h23_gt⟩
    obtain ⟨ha1, hb1⟩ := bad_quad_eq_23 hy12 (by omega) hy1h h12_gt
    obtain ⟨ha2, hb2⟩ := bad_quad_eq_23 (by omega) hy3M hy1h h13_gt
    have hg_eq : Nat.gcd y₁ y₂ = Nat.gcd y₁ y₃ := by omega
    rw [hg_eq] at hb1
    omega
  have hex_pair : ∃ y₁ y₂ y₃ : ℕ, ({u₁, u₂, u₃} : Finset ℕ) = {y₁, y₂, y₃} ∧
      y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧ 4 * Nat.gcd y₁ y₂ ≤ M := by
    obtain ⟨z₁, z₂, z₃, hzeq, hz32, hz21⟩ := sort3_dec h12 h13 h23
    have hz_in : ∀ w, w ∈ ({u₁, u₂, u₃} : Finset ℕ) ↔ w = z₁ ∨ w = z₂ ∨ w = z₃ := fun w => by
      rw [hzeq]; simp only [Finset.mem_insert, Finset.mem_singleton]
    have hz3M : M < 2 * z₃ := hhalf z₃ (by
      have h := (hz_in z₃).mpr (Or.inr (Or.inr rfl))
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> simp)
    have hz1M : z₁ ≤ M := hle z₁ (by
      have h := (hz_in z₁).mpr (Or.inl rfl)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> simp)
    have hset3 : ∀ x y z : ℕ, (x = z₁ ∨ x = z₂ ∨ x = z₃) → (y = z₁ ∨ y = z₂ ∨ y = z₃) →
        (z = z₁ ∨ z = z₂ ∨ z = z₃) → (z₁ = x ∨ z₁ = y ∨ z₁ = z) → (z₂ = x ∨ z₂ = y ∨ z₂ = z) →
        (z₃ = x ∨ z₃ = y ∨ z₃ = z) → ({z₁, z₂, z₃} : Finset ℕ) = {x, y, z} := by
      intro x y z hx hy hz h1 h2 h3
      ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by rintro (rfl | rfl | rfl) <;> assumption, by rintro (rfl | rfl | rfl) <;> assumption⟩
    rcases h4g_pair z₃ z₂ z₁ hz32 hz21 hz3M hz1M with h4 | h4 | h4
    · refine ⟨z₃, z₂, z₁, ?_, by omega, by omega, by omega, h4⟩
      rw [hzeq]; exact hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · refine ⟨z₃, z₁, z₂, ?_, by omega, by omega, by omega, h4⟩
      rw [hzeq]; exact hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · refine ⟨z₂, z₁, z₃, ?_, by omega, by omega, by omega, h4⟩
      rw [hzeq]; exact hset3 _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨y₁, y₂, y₃, hy_eq, hy12, hy13, hy23, h4g1⟩ := hex_pair
  have hy_in_u : ∀ y ∈ ({y₁, y₂, y₃} : Finset ℕ), y ∈ ({u₁, u₂, u₃} : Finset ℕ) := fun y hy => by
    rw [hy_eq]; exact hy
  have hy1_u : y₁ ∈ ({u₁, u₂, u₃} : Finset ℕ) := hy_in_u y₁ (by simp)
  have hy2_u : y₂ ∈ ({u₁, u₂, u₃} : Finset ℕ) := hy_in_u y₂ (by simp)
  have hy3_u : y₃ ∈ ({u₁, u₂, u₃} : Finset ℕ) := hy_in_u y₃ (by simp)
  have hy1_mem : y₁ = u₁ ∨ y₁ = u₂ ∨ y₁ = u₃ := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy1_u
  have hy2_mem : y₂ = u₁ ∨ y₂ = u₂ ∨ y₂ = u₃ := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy2_u
  have hy3_mem : y₃ = u₁ ∨ y₃ = u₂ ∨ y₃ = u₃ := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy3_u
  have hb1_y1 : y₁ ∣ b₁ := by rcases hy1_mem with rfl | rfl | rfl <;> assumption
  have hb1_y2 : y₂ ∣ b₁ := by rcases hy2_mem with rfl | rfl | rfl <;> assumption
  have hy1v1 : y₁ ≠ v₁ := by rcases hy1_mem with rfl | rfl | rfl <;> assumption
  have hy1v2 : y₁ ≠ v₂ := by rcases hy1_mem with rfl | rfl | rfl <;> assumption
  have hy2v1 : y₂ ≠ v₁ := by rcases hy2_mem with rfl | rfl | rfl <;> assumption
  have hy2v2 : y₂ ≠ v₂ := by rcases hy2_mem with rfl | rfl | rfl <;> assumption
  have hy3v1 : y₃ ≠ v₁ := by rcases hy3_mem with rfl | rfl | rfl <;> assumption
  have hy3v2 : y₃ ≠ v₂ := by rcases hy3_mem with rfl | rfl | rfl <;> assumption
  have hy1p : 0 < y₁ := hpos y₁ (by rcases hy1_mem with rfl | rfl | rfl <;> simp)
  have hy2p : 0 < y₂ := hpos y₂ (by rcases hy2_mem with rfl | rfl | rfl <;> simp)
  have hy1M : y₁ ≤ M := hle y₁ (by rcases hy1_mem with rfl | rfl | rfl <;> simp)
  have hy2M : y₂ ≤ M := hle y₂ (by rcases hy2_mem with rfl | rfl | rfl <;> simp)
  let g₁ := Nat.gcd y₁ y₂
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left y₂ hy1p
  -- Pick `w₂ ∈ I \ {b₁, b₂}` with `g₂ ∣ w₂`, and `w₁ ∈ I \ {b₁, b₂, w₂}` with `g₁ ∣ w₁`.
  obtain ⟨w₂, hw₂_I, hw₂_not, hg₂_w₂⟩ := exists_avoiding_multiple_5 x M g₂ {b₁, b₂}
    hg₂_pos (le_trans (Nat.mul_le_mul_right g₂ (by
      have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3g₂)
  obtain ⟨w₁, hw₁_I, hw₁_not, hg₁_w₁⟩ := exists_avoiding_multiple_5 x M g₁ {b₁, b₂, w₂}
    hg₁_pos (le_trans (Nat.mul_le_mul_right g₁ (by
      have h1 := Finset.card_insert_le b₁ {b₂, w₂}
      have h2 := Finset.card_insert_le b₂ {w₂}; simp at h2 ⊢; omega)) h4g1)
  have hw2_b1 : w₂ ≠ b₁ := fun heq => hw₂_not (by simp [heq])
  have hw2_b2 : w₂ ≠ b₂ := fun heq => hw₂_not (by simp [heq])
  have hw1_b1 : w₁ ≠ b₁ := fun heq => hw₁_not (by simp [heq])
  have hw1_b2 : w₁ ≠ b₂ := fun heq => hw₁_not (by simp [heq])
  have hw1_w2 : w₁ ≠ w₂ := fun heq => hw₁_not (by simp [heq])
  refine ⟨y₃, by rcases hy3_mem with rfl | rfl | rfl <;> simp, ?_⟩
  have hu1_y : u₁ = y₁ ∨ u₁ = y₂ ∨ u₁ = y₃ := by
    have h : u₁ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hy_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hu2_y : u₂ = y₁ ∨ u₂ = y₂ ∨ u₂ = y₃ := by
    have h : u₂ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hy_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hu3_y : u₃ = y₁ ∨ u₃ = y₂ ∨ u₃ = y₃ := by
    have h : u₃ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hy_eq]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hAer : A.erase y₃ = {y₁, y₂, v₁, v₂} := by
    ext z; simp only [A, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzy3, hzA⟩
      rcases hzA with rfl | rfl | rfl | rfl | rfl
      · rcases hu1_y with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hzy3
      · rcases hu2_y with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hzy3
      · rcases hu3_y with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hzy3
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨hy13, by rcases hy1_mem with rfl | rfl | rfl <;> simp⟩
      · exact ⟨hy23, by rcases hy2_mem with rfl | rfl | rfl <;> simp⟩
      · exact ⟨hy3v1.symm, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨hy3v2.symm, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  rw [hAer]
  let B : Finset ℕ := {b₁, b₂, w₁, w₂}
  have hBI : B ⊆ consecInterval x M := by
    intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> assumption
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
  have hA4_0 : ∀ a ∈ ({y₁, y₂, v₁, v₂} : Finset ℕ), a ≠ 0 := by
    intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
    isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
  intro p _hp
  have hsumA : ∑ a ∈ ({y₁, y₂, v₁, v₂} : Finset ℕ), a.factorization p =
      y₁.factorization p + y₂.factorization p + v₁.factorization p + v₂.factorization p := by
    rw [Finset.sum_insert (by simp [hy12, hy1v1, hy1v2]),
        Finset.sum_insert (by simp [hy2v1, hy2v2]),
        Finset.sum_insert (by simp [hv12]), Finset.sum_singleton]
    ring
  have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + w₂.factorization p =
      ∑ b ∈ B, b.factorization p := by
    dsimp [B]
    rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm]),
        Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm]),
        Finset.sum_insert (by simp [hw1_w2]), Finset.sum_singleton]
    ring
  rw [hsumA, ← hsumB]
  have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
  have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
  have hw10 : w₁ ≠ 0 := (pos_of_mem_consecInterval hw₁_I).ne'
  have hw20 : w₂ ≠ 0 := (pos_of_mem_consecInterval hw₂_I).ne'
  have hb1_1 := fac_le_of_dvd_5 hb₁0 hb1_y1 (p := p)
  have hb1_2 := fac_le_of_dvd_5 hb₁0 hb1_y2 (p := p)
  have hb2_v1 := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
  have hb2_v2 := fac_le_of_dvd_5 hb₂0 hb₂_v2 (p := p)
  have hw1_g := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
  have hw2_g := fac_le_of_dvd_5 hw20 hg₂_w₂ (p := p)
  rw [fac_gcd_eq_min_5 hy1p.ne' hy2p.ne'] at hw1_g
  rw [fac_gcd_eq_min_5 hv1p.ne' hv2p.ne'] at hw2_g
  omega

private lemma decide_pairspan3_Q3 :
    ∀ a ∈ Finset.Icc 1 2, ∀ b ∈ Finset.Icc 1 3, ∀ d ∈ Finset.Icc 1 3,
      a < b → b < d → d < 2 * a →
      Nat.gcd a b = 1 → Nat.gcd a d = 1 → Nat.gcd b d = 1 → False := by
  decide

private def check457Bool (a b d : ℕ) : Bool :=
  !(decide (a = 4 ∨ a = 6 ∨ a = 8 ∨ a = 9) && decide (a < b) && decide (b < d) && decide (d < 2 * a) &&
    decide (Nat.gcd a b = 1) && decide (Nat.gcd a d = 1) && decide (Nat.gcd b d = 1) &&
    decide (b * d < 12 * a)) || (decide (a = 4) && decide (b = 5) && decide (d = 7))

private lemma check457_all :
    ((List.range 6).map (· + 4)).all (fun a => ((List.range 6).map (· + 5)).all (fun b =>
      ((List.range 6).map (· + 6)).all (fun d => check457Bool a b d))) = true := by
  decide

private lemma decide_pairspan3_457 :
    ∀ a ∈ Finset.Icc 4 9, ∀ b ∈ Finset.Icc 5 10, ∀ d ∈ Finset.Icc 6 11,
      a = 4 ∨ a = 6 ∨ a = 8 ∨ a = 9 →
      a < b → b < d → d < 2 * a →
      Nat.gcd a b = 1 → Nat.gcd a d = 1 → Nat.gcd b d = 1 →
      b * d < 12 * a → a = 4 ∧ b = 5 ∧ d = 7 := by
  intro a ha b hb d hd hcomp h1 h2 h3 h4 h5 h6 h7
  rw [Finset.mem_Icc] at ha hb hd
  have h0 := check457_all
  rw [List.all_eq_true] at h0
  have haL : a ∈ (List.range 6).map (· + 4) := List.mem_map.mpr ⟨a - 4, List.mem_range.mpr (by omega), by omega⟩
  have ha' := h0 a haL
  rw [List.all_eq_true] at ha'
  have hbL : b ∈ (List.range 6).map (· + 5) := List.mem_map.mpr ⟨b - 5, List.mem_range.mpr (by omega), by omega⟩
  have hb' := ha' b hbL
  rw [List.all_eq_true] at hb'
  have hdL : d ∈ (List.range 6).map (· + 6) := List.mem_map.mpr ⟨d - 6, List.mem_range.mpr (by omega), by omega⟩
  have hbool := hb' d hdL
  simpa [check457Bool, hcomp, h1, h2, h3, h4, h5, h6, h7, and_assoc] using hbool

/-- Helper: pair-spanning triple `u₁ < u₂ < u₃` (`uᵢ ∣ b₁`, `M < 2*uᵢ`, pair-spanning `L₃`),
    plus `c, v₁` where `v₁ = 2 * c`, `2 * c ≤ M < 3 * c`, `c ∣ L₃`, `c ∣ b₂`, `v₁ ∣ b₁ ∨ v₁ ∣ b₂`. -/
lemma cover_six_of_pairspan3_c_2c {A : Finset ℕ} {x M b₁ b₂ u₁ u₂ u₃ c v₁ : ℕ}
    (hA_eq : A = {u₁, u₂, u₃, c, v₁})
    (h12 : u₁ < u₂) (h23 : u₂ < u₃)
    (h1c : u₁ ≠ c) (h2c : u₂ ≠ c) (h3c : u₃ ≠ c)
    (h1v : u₁ ≠ v₁) (h2v : u₂ ≠ v₁) (h3v : u₃ ≠ v₁) (hcv : c ≠ v₁)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1)
    (hu1_h : M < 2 * u₁) (hu2_h : M < 2 * u₂) (hu3_h : M < 2 * u₃)
    (h2c_le : 2 * c ≤ M) (h3c_gt : M < 3 * c) (hv1_eq : v₁ = 2 * c)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb₁_u1 : u₁ ∣ b₁) (hb₁_u2 : u₂ ∣ b₁) (hb₁_u3 : u₃ ∣ b₁)
    (hb₂_c : c ∣ b₂) (hb_v1 : v₁ ∣ b₂ ∨ (v₁ ∣ b₁ ∧ ¬ (v₁ ∣ ({u₁, u₂, u₃} : Finset ℕ).lcm id)))
    (hc_L3 : c ∣ ({u₁, u₂, u₃} : Finset ℕ).lcm id)
    (hpair : ∀ a ∈ ({u₁, u₂, u₃} : Finset ℕ), ∀ b ∈ ({u₁, u₂, u₃} : Finset ℕ),
      a ≠ b → Nat.lcm a b = ({u₁, u₂, u₃} : Finset ℕ).lcm id) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  let U3 : Finset ℕ := {u₁, u₂, u₃}
  let L₃ := U3.lcm id
  have hu1p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have hu2p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have hu3p : 0 < u₃ := hA_pos u₃ (by rw [hA_eq]; simp)
  have hcp : 0 < c := hA_pos c (by rw [hA_eq]; simp)
  have hvp : 0 < v₁ := hA_pos v₁ (by rw [hA_eq]; simp)
  have hu3M : u₃ ≤ M := hA_le u₃ (by rw [hA_eq]; simp)
  have hL3_pos : 0 < L₃ := finset_lcm_pos_5 fun u hu => by
    simp only [U3, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  let Q₁ := L₃ / u₁
  let Q₂ := L₃ / u₂
  let Q₃ := L₃ / u₃
  have hd1 : u₁ ∣ L₃ := Finset.dvd_lcm (by simp [U3])
  have hd2 : u₂ ∣ L₃ := Finset.dvd_lcm (by simp [U3])
  have hd3 : u₃ ∣ L₃ := Finset.dvd_lcm (by simp [U3])
  have hmul1 : u₁ * Q₁ = L₃ := Nat.mul_div_cancel' hd1
  have hmul2 : u₂ * Q₂ = L₃ := Nat.mul_div_cancel' hd2
  have hmul3 : u₃ * Q₃ = L₃ := Nat.mul_div_cancel' hd3
  have hQ₁_pos : 0 < Q₁ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul1; omega
  have hQ₂_pos : 0 < Q₂ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul2; omega
  have hQ₃_pos : 0 < Q₃ := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul3; omega
  have hQ32 : Q₃ < Q₂ := by nlinarith
  have hQ21 : Q₂ < Q₁ := by nlinarith
  have hQ1_lt : Q₁ < 2 * Q₃ := by nlinarith
  -- Pairwise coprimality of `Q₁, Q₂, Q₃`:
  have hcop_pair : ∀ {a b Qa Qb : ℕ}, a ∈ U3 → b ∈ U3 → a ≠ b →
      a * Qa = L₃ → b * Qb = L₃ → Nat.Coprime Qa Qb := by
    intro a b Qa Qb ha hb hab haQ hbQ
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
    have ha0 : a ≠ 0 := (hA_pos a (by
      rw [hA_eq]; rcases (by simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using ha : a = u₁ ∨ a = u₂ ∨ a = u₃) with rfl | rfl | rfl <;> simp)).ne'
    have hb0 : b ≠ 0 := (hA_pos b (by
      rw [hA_eq]; rcases (by simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hb : b = u₁ ∨ b = u₂ ∨ b = u₃) with rfl | rfl | rfl <;> simp)).ne'
    have hQa0 : Qa ≠ 0 := fun h => by rw [h, mul_zero] at haQ; omega
    have hQb0 : Qb ≠ 0 := fun h => by rw [h, mul_zero] at hbQ; omega
    have h1 : 1 ≤ Qa.factorization p := (hp.pow_dvd_iff_le_factorization hQa0).mp (by simpa using dvd_trans hpd (Nat.gcd_dvd_left _ _))
    have h2 : 1 ≤ Qb.factorization p := (hp.pow_dvd_iff_le_factorization hQb0).mp (by simpa using dvd_trans hpd (Nat.gcd_dvd_right _ _))
    have ha_v : a.factorization p + Qa.factorization p = L₃.factorization p := by
      rw [← haQ, Nat.factorization_mul ha0 hQa0, Finsupp.add_apply]
    have hb_v : b.factorization p + Qb.factorization p = L₃.factorization p := by
      rw [← hbQ, Nat.factorization_mul hb0 hQb0, Finsupp.add_apply]
    have hlcm := congrArg (fun n => n.factorization p) (hpair a ha b hb hab)
    change (Nat.lcm a b).factorization p = L₃.factorization p at hlcm
    rw [fac_lcm_eq_max_5 ha0 hb0] at hlcm
    omega
  have hc12 : Nat.Coprime Q₁ Q₂ := hcop_pair (by simp [U3]) (by simp [U3]) (by omega) hmul1 hmul2
  have hc13 : Nat.Coprime Q₁ Q₃ := hcop_pair (by simp [U3]) (by simp [U3]) (by omega) hmul1 hmul3
  have hc23 : Nat.Coprime Q₂ Q₃ := hcop_pair (by simp [U3]) (by simp [U3]) (by omega) hmul2 hmul3
  have hQ3_3 : 3 ≤ Q₃ := by
    by_contra hlt3
    have hQ3_le2 : Q₃ ≤ 2 := by omega
    have hQ1_le3 : Q₁ ≤ 3 := by omega
    exact decide_pairspan3_Q3 Q₃ (Finset.mem_Icc.mpr ⟨hQ₃_pos, hQ3_le2⟩) Q₂ (Finset.mem_Icc.mpr ⟨hQ₂_pos, by omega⟩)
      Q₁ (Finset.mem_Icc.mpr ⟨hQ₁_pos, hQ1_le3⟩) hQ32 hQ21 hQ1_lt
      hc23.symm.gcd_eq_one hc13.symm.gcd_eq_one hc12.symm.gcd_eq_one
  have hQ2_4 : 4 ≤ Q₂ := by omega
  have hQ1_5 : 5 ≤ Q₁ := by omega
  have hQ123_dvd : Q₁ * Q₂ * Q₃ ∣ L₃ :=
    (Nat.Coprime.mul_left hc13 hc23).mul_dvd_of_dvd_of_dvd
      (hc12.mul_dvd_of_dvd_of_dvd ⟨u₁, by rw [mul_comm]; exact hmul1.symm⟩
        ⟨u₂, by rw [mul_comm]; exact hmul2.symm⟩)
      ⟨u₃, by rw [mul_comm]; exact hmul3.symm⟩
  obtain ⟨D, hD_eq⟩ := hQ123_dvd
  have hL3_eq : L₃ = D * Q₁ * Q₂ * Q₃ := by rw [hD_eq]; ring
  have hD_pos : 0 < D := Nat.pos_of_ne_zero fun h => by
    rw [h] at hL3_eq; simp only [zero_mul] at hL3_eq; omega
  have hu3_eq : u₃ = D * Q₁ * Q₂ := by
    have hmul : u₃ * Q₃ = (D * Q₁ * Q₂) * Q₃ := by rw [hmul3, hL3_eq]
    exact Nat.eq_of_mul_eq_mul_right hQ₃_pos hmul
  have hu2_eq : u₂ = D * Q₁ * Q₃ := by
    have hmul : u₂ * Q₂ = (D * Q₁ * Q₃) * Q₂ := by rw [hmul2, hL3_eq]; ring
    exact Nat.eq_of_mul_eq_mul_right hQ₂_pos hmul
  have hu1_eq : u₁ = D * Q₂ * Q₃ := by
    have hmul : u₁ * Q₁ = (D * Q₂ * Q₃) * Q₁ := by rw [hmul1, hL3_eq]; ring
    exact Nat.eq_of_mul_eq_mul_right hQ₁_pos hmul
  -- `c ∤ u₁, c ∤ u₂, c ∤ u₃` since `c < u₁ < u₂ < u₃ ≤ M < 3*c` and `uᵢ ≠ 2*c = v₁`!
  have hc_nd_u : ∀ u ∈ U3, ¬ (c ∣ u) := by
    intro u hu hdc
    have hu_mem : u = u₁ ∨ u = u₂ ∨ u = u₃ := by simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hu
    have hu_h : M < 2 * u := by rcases hu_mem with rfl | rfl | rfl <;> assumption
    have hu_M : u ≤ M := hA_le u (by rw [hA_eq]; rcases hu_mem with rfl | rfl | rfl <;> simp)
    have hu_ne : u ≠ v₁ := by rcases hu_mem with rfl | rfl | rfl <;> assumption
    obtain ⟨q, hq⟩ := hdc
    have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by
      have : 0 < u := hA_pos u (by rw [hA_eq]; rcases hu_mem with rfl | rfl | rfl <;> simp)
      rw [h0, mul_zero] at hq; omega
    have hq2 : 2 ≤ q := by
      by_contra hlt; have hq1 : q ≤ 1 := by omega
      have huc : u ≤ c := by rw [hq]; exact le_trans (Nat.mul_le_mul_left c hq1) (by omega)
      omega
    have hq_eq2 : q = 2 := by
      by_contra hne2; have hq3 : 3 ≤ q := by omega
      have h3c_u : 3 * c ≤ u := le_trans (Nat.mul_le_mul_right c hq3) (by rw [hq, mul_comm])
      omega
    exact hu_ne (by rw [hq, hq_eq2, hv1_eq, mul_comm])
  -- `gcd(D, c) = 1` because `D ∣ u₁, u₂, u₃` and `c ∣ v₁` and `A.gcd id = 1`!
  have hcop_Dc : Nat.Coprime D c := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne1
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
    have hpD : p ∣ D := dvd_trans hpd (Nat.gcd_dvd_left D c)
    have hpc : p ∣ c := dvd_trans hpd (Nat.gcd_dvd_right D c)
    have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd fun a ha => by
      rw [hA_eq] at ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact dvd_trans hpD ⟨Q₂ * Q₃, by dsimp only [id]; rw [hu1_eq]; ring⟩
      · exact dvd_trans hpD ⟨Q₁ * Q₃, by dsimp only [id]; rw [hu2_eq]; ring⟩
      · exact dvd_trans hpD ⟨Q₁ * Q₂, by dsimp only [id]; rw [hu3_eq]; ring⟩
      · exact hpc
      · exact dvd_trans hpc (hv1_eq ▸ dvd_mul_left c 2)
    rw [hAgcd] at hpgcd
    exact hp.not_dvd_one hpgcd
  -- Since `c ∣ L₃ = D * (Q₁ * Q₂ * Q₃)` and `Coprime c D`, `c ∣ Q₁ * Q₂ * Q₃`!
  have hc_dvd_Q : c ∣ Q₁ * Q₂ * Q₃ := by
    have h1 : c ∣ D * (Q₁ * Q₂ * Q₃) := by rw [show D * (Q₁ * Q₂ * Q₃) = L₃ by rw [hL3_eq]; ring]; exact hc_L3
    exact hcop_Dc.symm.dvd_of_dvd_mul_left h1
  -- Write `g₁ = gcd c Q₁`, `g₂ = gcd c Q₂`, `g₃ = gcd c Q₃`!
  let g₁ := Nat.gcd c Q₁
  let g₂ := Nat.gcd c Q₂
  let g₃ := Nat.gcd c Q₃
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left Q₁ hcp
  have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left Q₂ hcp
  have hg₃_pos : 0 < g₃ := Nat.gcd_pos_of_pos_left Q₃ hcp
  have hg12 : Nat.Coprime g₁ g₂ := hc12.coprime_dvd_left (Nat.gcd_dvd_right _ _) |>.coprime_dvd_right (Nat.gcd_dvd_right _ _)
  have hg13 : Nat.Coprime g₁ g₃ := hc13.coprime_dvd_left (Nat.gcd_dvd_right _ _) |>.coprime_dvd_right (Nat.gcd_dvd_right _ _)
  have hg23 : Nat.Coprime g₂ g₃ := hc23.coprime_dvd_left (Nat.gcd_dvd_right _ _) |>.coprime_dvd_right (Nat.gcd_dvd_right _ _)
  have hg1_ge2 : 2 ≤ g₁ := by
    by_contra hlt2; have : g₁ = 1 := by omega
    have hcop_c1 : Nat.Coprime c Q₁ := Nat.coprime_iff_gcd_eq_one.mpr this
    have : c ∣ D * Q₂ * Q₃ := by
      have hc1 : c ∣ (D * Q₂ * Q₃) * Q₁ := by rw [show (D * Q₂ * Q₃) * Q₁ = L₃ by rw [hL3_eq]; ring]; exact hc_L3
      exact hcop_c1.dvd_of_dvd_mul_right hc1
    exact hc_nd_u u₁ (by simp [U3]) (hu1_eq ▸ this)
  have hg2_ge2 : 2 ≤ g₂ := by
    by_contra hlt2; have : g₂ = 1 := by omega
    have hcop_c2 : Nat.Coprime c Q₂ := Nat.coprime_iff_gcd_eq_one.mpr this
    have : c ∣ D * Q₁ * Q₃ := by
      have hc2 : c ∣ (D * Q₁ * Q₃) * Q₂ := by rw [show (D * Q₁ * Q₃) * Q₂ = L₃ by rw [hL3_eq]; ring]; exact hc_L3
      exact hcop_c2.dvd_of_dvd_mul_right hc2
    exact hc_nd_u u₂ (by simp [U3]) (hu2_eq ▸ this)
  have hg3_ge2 : 2 ≤ g₃ := by
    by_contra hlt2; have : g₃ = 1 := by omega
    have hcop_c3 : Nat.Coprime c Q₃ := Nat.coprime_iff_gcd_eq_one.mpr this
    have : c ∣ D * Q₁ * Q₂ := by
      have hc3 : c ∣ (D * Q₁ * Q₂) * Q₃ := by rw [show (D * Q₁ * Q₂) * Q₃ = L₃ by rw [hL3_eq]]; exact hc_L3
      exact hcop_c3.dvd_of_dvd_mul_right hc3
    exact hc_nd_u u₃ (by simp [U3]) (hu3_eq ▸ this)
  -- Since `c ∣ Q₁ * Q₂ * Q₃` and `Q₁, Q₂, Q₃` pairwise coprime, `c = g₁ * g₂ * g₃`!
  have hc_eq_g : c = g₁ * g₂ * g₃ := by
    apply Nat.dvd_antisymm
    · rw [← Nat.factorization_le_iff_dvd hcp.ne' (by positivity)]
      intro p
      by_cases hp : p.Prime
      · rw [Nat.factorization_mul (mul_ne_zero hg₁_pos.ne' hg₂_pos.ne') hg₃_pos.ne',
            Nat.factorization_mul hg₁_pos.ne' hg₂_pos.ne', Finsupp.add_apply, Finsupp.add_apply]
        have hfp : c.factorization p ≤ (Q₁ * Q₂ * Q₃).factorization p :=
          fac_le_of_dvd_5 (by positivity) hc_dvd_Q
        rw [Nat.factorization_mul (mul_ne_zero hQ₁_pos.ne' hQ₂_pos.ne') hQ₃_pos.ne',
            Nat.factorization_mul hQ₁_pos.ne' hQ₂_pos.ne', Finsupp.add_apply, Finsupp.add_apply] at hfp
        rw [fac_gcd_eq_min_5 hcp.ne' hQ₁_pos.ne', fac_gcd_eq_min_5 hcp.ne' hQ₂_pos.ne',
            fac_gcd_eq_min_5 hcp.ne' hQ₃_pos.ne']
        have h12 := coprime_factorization_zero hQ₁_pos hQ₂_pos hp hc12
        have h13 := coprime_factorization_zero hQ₁_pos hQ₃_pos hp hc13
        have h23 := coprime_factorization_zero hQ₂_pos hQ₃_pos hp hc23
        omega
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    · exact (Nat.Coprime.mul_left hg13 hg23).mul_dvd_of_dvd_of_dvd
        (hg12.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
        (Nat.gcd_dvd_left _ _)
  -- Sort `{g₁, g₂, g₃}` as `2 ≤ s₁ < s₂ < s₃`:
  have hg12_ne : g₁ ≠ g₂ := fun h => by
    have h1 := hg12.gcd_eq_one; rw [h, Nat.gcd_self] at h1; omega
  have hg13_ne : g₁ ≠ g₃ := fun h => by
    have h1 := hg13.gcd_eq_one; rw [h, Nat.gcd_self] at h1; omega
  have hg23_ne : g₂ ≠ g₃ := fun h => by
    have h1 := hg23.gcd_eq_one; rw [h, Nat.gcd_self] at h1; omega
  have sort3 : ∀ a b d : ℕ, 2 ≤ a → 2 ≤ b → 2 ≤ d → a ≠ b → a ≠ d → b ≠ d →
      ∃ s₁ s₂ s₃ : ℕ, 2 ≤ s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ a * b * d = s₁ * s₂ * s₃ := by
    intro a b d ha hb hd hab had hbd
    rcases lt_or_gt_of_ne hab with h1 | h1
    · rcases lt_or_gt_of_ne had with h2 | h2
      · rcases lt_or_gt_of_ne hbd with h3 | h3
        · exact ⟨a, b, d, ha, h1, h3, by ring⟩
        · exact ⟨a, d, b, ha, h2, h3, by ring⟩
      · exact ⟨d, a, b, hd, h2, h1, by ring⟩
    · rcases lt_or_gt_of_ne hbd with h3 | h3
      · rcases lt_or_gt_of_ne had with h2 | h2
        · exact ⟨b, a, d, hb, h1, h2, by ring⟩
        · exact ⟨b, d, a, hb, h3, h2, by ring⟩
      · exact ⟨d, b, a, hd, h3, h1, by ring⟩
  obtain ⟨s₁, s₂, s₃, hs1_ge2, hs12, hs23, hg_prod_s⟩ :=
    sort3 g₁ g₂ g₃ hg1_ge2 hg2_ge2 hg3_ge2 hg12_ne hg13_ne hg23_ne
  have hc_s : c = s₁ * s₂ * s₃ := by rw [hc_eq_g, hg_prod_s]
  have hs3_ge5 : 5 ≤ s₃ := by
    by_contra hlt5
    have hs234 : s₁ = 2 ∧ s₂ = 3 ∧ s₃ = 4 := by omega
    have h2_or : 2 ∣ g₁ ∨ 2 ∣ g₂ ∨ 2 ∣ g₃ := by
      have : 2 ∣ s₁ * s₂ * s₃ := ⟨s₂ * s₃, by rw [hs234.1]; ring⟩
      rw [← hg_prod_s] at this
      exact (Nat.Prime.dvd_mul (by norm_num)).mp this |>.elim
        (fun h => ((Nat.Prime.dvd_mul (by norm_num)).mp h).elim Or.inl (fun h' => Or.inr (Or.inl h')))
        (fun h => Or.inr (Or.inr h))
    have h8 : 8 ∣ g₁ * g₂ * g₃ := by rw [hg_prod_s, hs234.1, hs234.2.1, hs234.2.2]; norm_num
    have hdiv8 : 8 ∣ g₁ ∨ 8 ∣ g₂ ∨ 8 ∣ g₃ := by
      rcases h2_or with h2 | h2 | h2
      · have ho2 : Nat.Coprime 2 g₂ := hg12.coprime_dvd_left h2
        have ho3 : Nat.Coprime 2 g₃ := hg13.coprime_dvd_left h2
        have ho23 : Nat.Coprime 8 (g₂ * g₃) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (ho2.mul_right ho3).pow_left 3
        have h8' : 8 ∣ (g₂ * g₃) * g₁ := by rw [show (g₂ * g₃) * g₁ = g₁ * g₂ * g₃ by ring]; exact h8
        exact Or.inl (ho23.dvd_of_dvd_mul_left h8')
      · have ho1 : Nat.Coprime 2 g₁ := hg12.symm.coprime_dvd_left h2
        have ho3 : Nat.Coprime 2 g₃ := hg23.coprime_dvd_left h2
        have ho13 : Nat.Coprime 8 (g₁ * g₃) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (ho1.mul_right ho3).pow_left 3
        have h8' : 8 ∣ (g₁ * g₃) * g₂ := by rw [show (g₁ * g₃) * g₂ = g₁ * g₂ * g₃ by ring]; exact h8
        exact Or.inr (Or.inl (ho13.dvd_of_dvd_mul_left h8'))
      · have ho1 : Nat.Coprime 2 g₁ := hg13.symm.coprime_dvd_left h2
        have ho2 : Nat.Coprime 2 g₂ := hg23.symm.coprime_dvd_left h2
        have ho12 : Nat.Coprime 8 (g₁ * g₂) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact (ho1.mul_right ho2).pow_left 3
        exact Or.inr (Or.inr (ho12.dvd_of_dvd_mul_left h8))
    have h24 : g₁ * g₂ * g₃ = 24 := by rw [hg_prod_s, hs234.1, hs234.2.1, hs234.2.2]
    rcases hdiv8 with h81 | h82 | h83
    · have h1 : 8 ≤ g₁ := Nat.le_of_dvd hg₁_pos h81
      have h2 : 8 * 2 * 2 ≤ g₁ * g₂ * g₃ := Nat.mul_le_mul (Nat.mul_le_mul h1 hg2_ge2) hg3_ge2
      omega
    · have h1 : 8 ≤ g₂ := Nat.le_of_dvd hg₂_pos h82
      have h2 : 2 * 8 * 2 ≤ g₁ * g₂ * g₃ := Nat.mul_le_mul (Nat.mul_le_mul hg1_ge2 h1) hg3_ge2
      omega
    · have h1 : 8 ≤ g₃ := Nat.le_of_dvd hg₃_pos h83
      have h2 : 2 * 2 * 8 ≤ g₁ * g₂ * g₃ := Nat.mul_le_mul (Nat.mul_le_mul hg1_ge2 hg2_ge2) h1
      omega
  have hs2_ge3 : 3 ≤ s₂ := by omega
  have h4_s2s3 : 4 * (s₂ * s₃) ≤ M := by
    have : 4 * (s₂ * s₃) ≤ 2 * (s₁ * s₂ * s₃) := by
      have : 2 * (s₁ * (s₂ * s₃)) ≥ 2 * (2 * (s₂ * s₃)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (s₂ * s₃) hs1_ge2)
      linarith
    omega
  have h4_DQ1 : 4 * (D * Q₁) ≤ M := by
    calc 4 * (D * Q₁) ≤ Q₂ * (D * Q₁) := Nat.mul_le_mul_right _ hQ2_4
      _ = u₃ := by rw [hu3_eq]; ring
      _ ≤ M := hu3M
  have h5_DQ2 : 5 * (D * Q₂) ≤ M := by
    calc 5 * (D * Q₂) ≤ Q₁ * (D * Q₂) := Nat.mul_le_mul_right _ hQ1_5
      _ = u₃ := by rw [hu3_eq]; ring
      _ ≤ M := hu3M
  -- Prove `3 * (Q₃ * s₁) ≤ M`:
  have h3_Q3s1 : 3 * (Q₃ * s₁) ≤ M := by
    by_cases h3s1 : 3 * s₁ ≤ Q₁
    · calc 3 * (Q₃ * s₁) = Q₃ * (3 * s₁) := by ring
        _ ≤ Q₃ * Q₁ := Nat.mul_le_mul_left Q₃ h3s1
        _ ≤ Q₂ * Q₁ := Nat.mul_le_mul_right Q₁ (by omega)
        _ ≤ D * Q₁ * Q₂ := by
          have : 1 * (Q₂ * Q₁) ≤ D * (Q₂ * Q₁) := Nat.mul_le_mul_right _ hD_pos
          linarith
        _ = u₃ := hu3_eq.symm
        _ ≤ M := hu3M
    · have hlt : Q₁ < 3 * s₁ := by omega
      have h9s1 : 3 * Q₃ < 9 * s₁ := by omega
      have h3Q_le : 3 * Q₃ ≤ 2 * s₂ * s₃ := by
        rcases eq_or_lt_of_le hs1_ge2 with hs1_2 | hs1_3
        · have h18 : 9 * s₁ = 18 := by omega
          have h30 : 2 * 3 * 5 ≤ 2 * s₂ * s₃ :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs2_ge3) hs3_ge5
          omega
        · have h1 : 2 * (s₁ + 1) * (s₁ + 2) ≤ 2 * s₂ * s₃ :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
          have h2 : 9 * s₁ ≤ 2 * (s₁ + 1) * (s₁ + 2) := by
            rcases eq_or_lt_of_le (by omega : 3 ≤ s₁) with hs1_3eq | hs1_4
            · rw [← hs1_3eq]; norm_num
            · have := Nat.mul_le_mul_right (s₁ + 2) (by omega : 10 ≤ 2 * (s₁ + 1))
              linarith
          omega
      calc 3 * (Q₃ * s₁) = (3 * Q₃) * s₁ := by ring
        _ ≤ (2 * s₂ * s₃) * s₁ := Nat.mul_le_mul_right s₁ h3Q_le
        _ = 2 * c := by rw [hc_s]; ring
        _ ≤ M := h2c_le
  -- Helper: given `f₁, f₂, f₃, f₄` positive with `3*f₁ ≤ M, 4*f₂ ≤ M, 5*f₃ ≤ M, 6*f₄ ≤ M`
  -- and `f₁ * f₂ * f₃ * f₄ = D^2 * Q₁ * Q₂ * Q₃ * c`, build a `≤ 6`-slot cover `{b₁, b₂, w₁, w₂, w₃, w₄}`!
  have build_6_cover : ∀ f₁ f₂ f₃ f₄ : ℕ,
      0 < f₁ → 0 < f₂ → 0 < f₃ → 0 < f₄ →
      3 * f₁ ≤ M → 4 * f₂ ≤ M → 5 * f₃ ≤ M → 6 * f₄ ≤ M →
      D ^ 2 * Q₁ * Q₂ * Q₃ * c ∣ f₁ * f₂ * f₃ * f₄ →
      ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
    intro f₁ f₂ f₃ f₄ hf1p hf2p hf3p hf4p h3f1 h4f2 h5f3 h6f4 hRdvd
    obtain ⟨w₁, hw₁_I, hw₁_not, hf1_w⟩ := exists_avoiding_multiple_5 x M f₁ {b₁, b₂}
      hf1p (le_trans (Nat.mul_le_mul_right f₁ (by
        have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3f1)
    obtain ⟨w₂, hw₂_I, hw₂_not, hf2_w⟩ := exists_avoiding_multiple_5 x M f₂ {b₁, b₂, w₁}
      hf2p (le_trans (Nat.mul_le_mul_right f₂ (by
        have h1 := Finset.card_insert_le b₁ {b₂, w₁}
        have h2 := Finset.card_insert_le b₂ {w₁}; simp at h2 ⊢; omega)) h4f2)
    obtain ⟨w₃, hw₃_I, hw₃_not, hf3_w⟩ := exists_avoiding_multiple_5 x M f₃ {b₁, b₂, w₁, w₂}
      hf3p (le_trans (Nat.mul_le_mul_right f₃ (by
        have h1 := Finset.card_insert_le b₁ {b₂, w₁, w₂}
        have h2 := Finset.card_insert_le b₂ {w₁, w₂}
        have h3 := Finset.card_insert_le w₁ {w₂}; simp at h3 ⊢; omega)) h5f3)
    obtain ⟨w₄, hw₄_I, hw₄_not, hf4_w⟩ := exists_avoiding_multiple_5 x M f₄ {b₁, b₂, w₁, w₂, w₃}
      hf4p (le_trans (Nat.mul_le_mul_right f₄ (by
        have h1 := Finset.card_insert_le b₁ {b₂, w₁, w₂, w₃}
        have h2 := Finset.card_insert_le b₂ {w₁, w₂, w₃}
        have h3 := Finset.card_insert_le w₁ {w₂, w₃}
        have h4 := Finset.card_insert_le w₂ {w₃}; simp at h4 ⊢; omega)) h6f4)
    let B : Finset ℕ := {b₁, b₂, w₁, w₂, w₃, w₄}
    have hBI : B ⊆ consecInterval x M := by
      intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have hBcard : B.card ≤ 6 := by
      dsimp [B]
      have h1 := Finset.card_insert_le b₁ {b₂, w₁, w₂, w₃, w₄}
      have h2 := Finset.card_insert_le b₂ {w₁, w₂, w₃, w₄}
      have h3 := Finset.card_insert_le w₁ {w₂, w₃, w₄}
      have h4 := Finset.card_insert_le w₂ {w₃, w₄}
      have h5 := Finset.card_insert_le w₃ {w₄}
      simp only [Finset.card_singleton] at h5
      omega
    have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
    have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
    have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
    have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
    have hw1_b1 : w₁ ≠ b₁ := fun h => hw₁_not (by simp [h])
    have hw1_b2 : w₁ ≠ b₂ := fun h => hw₁_not (by simp [h])
    have hw2_b1 : w₂ ≠ b₁ := fun h => hw₂_not (by simp [h])
    have hw2_b2 : w₂ ≠ b₂ := fun h => hw₂_not (by simp [h])
    have hw2_w1 : w₂ ≠ w₁ := fun h => hw₂_not (by simp [h])
    have hw3_b1 : w₃ ≠ b₁ := fun h => hw₃_not (by simp [h])
    have hw3_b2 : w₃ ≠ b₂ := fun h => hw₃_not (by simp [h])
    have hw3_w1 : w₃ ≠ w₁ := fun h => hw₃_not (by simp [h])
    have hw3_w2 : w₃ ≠ w₂ := fun h => hw₃_not (by simp [h])
    have hw4_b1 : w₄ ≠ b₁ := fun h => hw₄_not (by simp [h])
    have hw4_b2 : w₄ ≠ b₂ := fun h => hw₄_not (by simp [h])
    have hw4_w1 : w₄ ≠ w₁ := fun h => hw₄_not (by simp [h])
    have hw4_w2 : w₄ ≠ w₂ := fun h => hw₄_not (by simp [h])
    have hw4_w3 : w₄ ≠ w₃ := fun h => hw₄_not (by simp [h])
    refine ⟨B, hBI, hBcard, isCover_of_prime_factorization_5 hA0 hB0 ?_⟩
    intro p _hp
    have hsumA : ∑ a ∈ A, a.factorization p =
        u₁.factorization p + u₂.factorization p + u₃.factorization p + c.factorization p + v₁.factorization p := by
      have h13 : u₁ ≠ u₃ := Nat.ne_of_lt (h12.trans h23)
      rw [hA_eq, Finset.sum_insert (by simp [h12.ne, h13, h1c, h1v]),
          Finset.sum_insert (by simp [h23.ne, h2c, h2v]),
          Finset.sum_insert (by simp [h3c, h3v]),
          Finset.sum_insert (by simp [hcv]), Finset.sum_singleton]
      ring
    have hsumB : ∑ b ∈ B, b.factorization p =
        b₁.factorization p + b₂.factorization p + w₁.factorization p +
        w₂.factorization p + w₃.factorization p + w₄.factorization p := by
      dsimp [B]
      rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm, hw3_b1.symm, hw4_b1.symm]),
          Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm, hw3_b2.symm, hw4_b2.symm]),
          Finset.sum_insert (by simp [hw2_w1.symm, hw3_w1.symm, hw4_w1.symm]),
          Finset.sum_insert (by simp [hw3_w2.symm, hw4_w2.symm]),
          Finset.sum_insert (by simp [hw4_w3.symm]), Finset.sum_singleton]
      ring
    rw [hsumA, hsumB]
    have hprod_u : u₁ * u₂ * u₃ = L₃ * (D ^ 2 * Q₁ * Q₂ * Q₃) := by
      rw [hu1_eq, hu2_eq, hu3_eq, hL3_eq]; ring
    have hL3_b1 : L₃ ∣ b₁ := Finset.lcm_dvd fun a ha => by
      simp only [U3, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
    have hprod_u_ne : u₁ * u₂ * u₃ ≠ 0 := by positivity
    have hR_ne : D ^ 2 * Q₁ * Q₂ * Q₃ * c ≠ 0 := by positivity
    have hprod_u_fac := congrArg (fun n => n.factorization p) hprod_u
    rw [Nat.factorization_mul (mul_ne_zero hu1p.ne' hu2p.ne') hu3p.ne',
        Nat.factorization_mul hu1p.ne' hu2p.ne',
        Nat.factorization_mul hL3_pos.ne' (by positivity), Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.add_apply] at hprod_u_fac
    have hR_fac := fac_le_of_dvd_5 (by positivity) hRdvd (p := p)
    have hf1_0 : f₁ ≠ 0 := hf1p.ne'
    have hf2_0 : f₂ ≠ 0 := hf2p.ne'
    have hf3_0 : f₃ ≠ 0 := hf3p.ne'
    have hf4_0 : f₄ ≠ 0 := hf4p.ne'
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hf1_0 hf2_0) hf3_0) hf4_0,
        Nat.factorization_mul (mul_ne_zero hf1_0 hf2_0) hf3_0,
        Nat.factorization_mul hf1_0 hf2_0,
        Nat.factorization_mul (by positivity) hcp.ne'] at hR_fac
    simp only [Finsupp.add_apply] at hR_fac
    have hw1_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₁_I).ne' hf1_w (p := p)
    have hw2_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₂_I).ne' hf2_w (p := p)
    have hw3_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₃_I).ne' hf3_w (p := p)
    have hw4_f := fac_le_of_dvd_5 (pos_of_mem_consecInterval hw₄_I).ne' hf4_w (p := p)
    have hb1_L := fac_le_of_dvd_5 hb₁0 hL3_b1 (p := p)
    have hb2_c' := fac_le_of_dvd_5 hb₂0 hb₂_c (p := p)
    have hb12_cov : L₃.factorization p + v₁.factorization p ≤ b₁.factorization p + b₂.factorization p := by
      rcases hb_v1 with hv1_b2 | ⟨hv1_b1, hv1_nd_L⟩
      · have hb2_v := fac_le_of_dvd_5 hb₂0 hv1_b2 (p := p); omega
      · by_cases hp2 : p = 2
        · subst hp2
          have hv1_fac2 : v₁.factorization 2 = c.factorization 2 + 1 := by
            rw [hv1_eq, Nat.factorization_mul (by norm_num) hcp.ne', Finsupp.add_apply]
            rw [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2)]
            ring
          have hc_le_L := fac_le_of_dvd_5 hL3_pos.ne' hc_L3 (p := 2)
          have hL_lt_v : L₃.factorization 2 < v₁.factorization 2 := by
            by_contra hge
            have hle_all : v₁ ∣ L₃ := by
              rw [← Nat.factorization_le_iff_dvd hvp.ne' hL3_pos.ne']
              intro q
              by_cases hq2 : q = 2
              · subst hq2; omega
              · have hvq : v₁.factorization q = c.factorization q := by
                  rw [hv1_eq, Nat.factorization_mul (by norm_num) hcp.ne', Finsupp.add_apply]
                  have : (2 : ℕ).factorization q = 0 := by
                    rw [Nat.Prime.factorization (by norm_num), Finsupp.single_apply, if_neg (Ne.symm hq2)]
                  omega
                rw [hvq]
                exact fac_le_of_dvd_5 hL3_pos.ne' hc_L3 (p := q)
            exact hv1_nd_L hle_all
          have hb1_v := fac_le_of_dvd_5 hb₁0 hv1_b1 (p := 2)
          omega
        · have hvq : v₁.factorization p = c.factorization p := by
            rw [hv1_eq, Nat.factorization_mul (by norm_num) hcp.ne', Finsupp.add_apply]
            have : (2 : ℕ).factorization p = 0 := by
              rw [Nat.Prime.factorization (by norm_num), Finsupp.single_apply, if_neg (Ne.symm hp2)]
            omega
          omega
    omega
  by_cases h6_Q3s1 : 6 * (Q₃ * s₁) ≤ M
  · exact build_6_cover (s₂ * s₃) (D * Q₁) (D * Q₂) (Q₃ * s₁)
      (mul_pos (by omega) (by omega)) (mul_pos hD_pos hQ₁_pos) (mul_pos hD_pos hQ₂_pos) (mul_pos hQ₃_pos (by omega))
      (by omega) h4_DQ1 h5_DQ2 h6_Q3s1 (by rw [hc_s]; exact dvd_of_eq (by ring))
  · -- Prove `3 ≤ s₁`, hence `6 * (s₂ * s₃) ≤ 2 * c ≤ M`!
    have hs1_ge3 : 3 ≤ s₁ := by
      by_contra hlt3
      have hs1_2 : s₁ = 2 := by omega
      have h12Q3 : M < 12 * Q₃ := by rw [hs1_2] at h6_Q3s1; omega
      have hQ1Q2_lt : Q₁ * Q₂ < 12 * Q₃ := by
        calc Q₁ * Q₂ ≤ D * Q₁ * Q₂ := by
              have := Nat.mul_le_mul_right (Q₁ * Q₂) hD_pos; linarith
          _ = u₃ := hu3_eq.symm
          _ ≤ M := hu3M
          _ < 12 * Q₃ := h12Q3
      have hQ1_lt12 : Q₁ < 12 := by
        by_contra h12
        have : 12 * Q₂ ≤ Q₁ * Q₂ := Nat.mul_le_mul_right Q₂ (by omega)
        omega
      -- Check `g₃ < Q₃`!
      have hg3_lt : g₃ < Q₃ := by
        by_contra hge
        have hg3_eq : g₃ = Q₃ := le_antisymm (Nat.le_of_dvd hQ₃_pos (Nat.gcd_dvd_right _ _)) (by omega)
        have h2c_ge : 12 * Q₃ ≤ 2 * c := by
          have hg12_ge6 : 6 ≤ g₁ * g₂ := by
            have h23_le : 2 * 3 ≤ g₁ * g₂ := by
              rcases lt_or_gt_of_ne hg12_ne with h12' | h12'
              · exact Nat.mul_le_mul hg1_ge2 (by omega)
              · exact le_trans (by norm_num : 2 * 3 ≤ 3 * 2) (Nat.mul_le_mul (by omega) hg2_ge2)
            exact h23_le
          have hmul : 6 * Q₃ ≤ g₁ * g₂ * g₃ := by
            rw [hg3_eq]; exact Nat.mul_le_mul_right Q₃ hg12_ge6
          rw [← hc_eq_g] at hmul; omega
        omega
      -- Thus `g₃` is a proper divisor of `Q₃` (`2 ≤ g₃` and `2 * g₃ ≤ Q₃ < Q₁ ≤ 11`)!
      have h2g3_le : 2 * g₃ ≤ Q₃ := by
        obtain ⟨q, hq⟩ := Nat.gcd_dvd_right c Q₃
        have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hq; omega
        have hq2 : 2 ≤ q := by
          by_contra hlt; have hq1 : q ≤ 1 := by omega
          have hle : Q₃ ≤ g₃ := by
            rw [hq]; exact le_trans (Nat.mul_le_mul_left g₃ hq1) (by omega)
          omega
        calc 2 * g₃ = g₃ * 2 := mul_comm 2 g₃
          _ ≤ g₃ * q := Nat.mul_le_mul_left g₃ hq2
          _ = Q₃ := hq.symm
      have hQ3_ge4 : 4 ≤ Q₃ := by omega
      have hQ3_comp : Q₃ = 4 ∨ Q₃ = 6 ∨ Q₃ = 8 ∨ Q₃ = 9 := by
        by_contra hnc
        have h57 : Q₃ = 5 ∨ Q₃ = 7 := by omega
        rcases h57 with h5 | h7
        · have hg5 : g₃ ∣ 5 := h5 ▸ Nat.gcd_dvd_right c Q₃
          have hg2 : g₃ = 2 := by omega
          rw [hg2] at hg5; norm_num at hg5
        · have hg7 : g₃ ∣ 7 := h7 ▸ Nat.gcd_dvd_right c Q₃
          have hg23 : g₃ = 2 ∨ g₃ = 3 := by omega
          rcases hg23 with hg2 | hg3
          · rw [hg2] at hg7; norm_num at hg7
          · rw [hg3] at hg7; norm_num at hg7
      have h3457 : Q₃ = 4 ∧ Q₂ = 5 ∧ Q₁ = 7 := decide_pairspan3_457
        Q₃ (Finset.mem_Icc.mpr ⟨hQ3_ge4, by omega⟩)
        Q₂ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        Q₁ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        hQ3_comp hQ32 hQ21 hQ1_lt
        hc23.symm.gcd_eq_one hc13.symm.gcd_eq_one hc12.symm.gcd_eq_one (mul_comm Q₂ Q₁ ▸ hQ1Q2_lt)
      -- In `(4, 5, 7)`: `g₂ ∣ 5, 2 ≤ g₂ ⇒ g₂ = 5`; `g₁ ∣ 7, 2 ≤ g₁ ⇒ g₁ = 7`; `g₃ ≥ 2` ⇒ `c = g₁ * g₂ * g₃ ≥ 70` ⇒ `M ≥ 140 > 48 = 12 * 4`, contradiction!
      have hg2_5 : g₂ = 5 := by
        have hd : g₂ ∣ 5 := h3457.2.1 ▸ Nat.gcd_dvd_right c Q₂
        have hle : g₂ ≤ 5 := Nat.le_of_dvd (by norm_num) hd
        have hne2 : g₂ ≠ 2 := fun h => by rw [h] at hd; norm_num at hd
        have hne3 : g₂ ≠ 3 := fun h => by rw [h] at hd; norm_num at hd
        have hne4 : g₂ ≠ 4 := fun h => by rw [h] at hd; norm_num at hd
        omega
      have hg1_7 : g₁ = 7 := by
        have hd : g₁ ∣ 7 := h3457.2.2 ▸ Nat.gcd_dvd_right c Q₁
        have hle : g₁ ≤ 7 := Nat.le_of_dvd (by norm_num) hd
        have hne2 : g₁ ≠ 2 := fun h => by rw [h] at hd; norm_num at hd
        have hne3 : g₁ ≠ 3 := fun h => by rw [h] at hd; norm_num at hd
        have hne4 : g₁ ≠ 4 := fun h => by rw [h] at hd; norm_num at hd
        have hne5 : g₁ ≠ 5 := fun h => by rw [h] at hd; norm_num at hd
        have hne6 : g₁ ≠ 6 := fun h => by rw [h] at hd; norm_num at hd
        omega
      have hc_ge70 : 70 ≤ c := by
        have h35 : g₁ * g₂ = 35 := by rw [hg1_7, hg2_5]
        have : 35 * 2 ≤ g₁ * g₂ * g₃ := by rw [h35]; exact Nat.mul_le_mul_left 35 hg3_ge2
        rw [← hc_eq_g] at this; exact this
      have : 12 * Q₃ = 48 := by rw [h3457.1]
      omega
    have h6_s2s3 : 6 * (s₂ * s₃) ≤ M := by
      have : 6 * (s₂ * s₃) ≤ 2 * (s₁ * s₂ * s₃) := by
        have : 2 * (s₁ * (s₂ * s₃)) ≥ 2 * (3 * (s₂ * s₃)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (s₂ * s₃) hs1_ge3)
        linarith
      omega
    exact build_6_cover (Q₃ * s₁) (D * Q₁) (D * Q₂) (s₂ * s₃)
      (mul_pos hQ₃_pos (by omega)) (mul_pos hD_pos hQ₁_pos) (mul_pos hD_pos hQ₂_pos) (mul_pos (by omega) (by omega))
      h3_Q3s1 h4_DQ1 h5_DQ2 h6_s2s3 (by rw [hc_s]; exact dvd_of_eq (by ring))


/-- Helper: Case `|C| = 1` with `|U₁| = 3, |U₂| = 1` (`u₁, u₂, u₃ > M/2` only in `b₁`,
    `v₁ > M/2` only in `b₂`, `c ∣ b₁ ∧ c ∣ b₂`). -/
lemma cover_six_of_r2_C1_31 {A : Finset ℕ} {x M b₁ b₂ u₁ u₂ u₃ v₁ c : ℕ}
    (hA_eq : A = {u₁, u₂, u₃, v₁, c})
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h1v : u₁ ≠ v₁) (h1c : u₁ ≠ c)
    (h23 : u₂ ≠ u₃) (h2v : u₂ ≠ v₁) (h2c : u₂ ≠ c)
    (h3v : u₃ ≠ v₁) (h3c : u₃ ≠ c) (hvc : v₁ ≠ c)
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (hAgcd : A.gcd id = 1) (hM7 : 7 ≤ M)
    (hu1_h : M < 2 * u₁) (hu2_h : M < 2 * u₂) (hu3_h : M < 2 * u₃) (hv1_h : M < 2 * v₁)
    (hb₁_I : b₁ ∈ consecInterval x M) (hb₂_I : b₂ ∈ consecInterval x M) (hb12 : b₁ ≠ b₂)
    (hb₁_u1 : u₁ ∣ b₁) (hb₁_u2 : u₂ ∣ b₁) (hb₁_u3 : u₃ ∣ b₁) (hb₁_c : c ∣ b₁)
    (hb₂_v1 : v₁ ∣ b₂) (hb₂_c : c ∣ b₂) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  have h1p : 0 < u₁ := hA_pos u₁ (by rw [hA_eq]; simp)
  have h2p : 0 < u₂ := hA_pos u₂ (by rw [hA_eq]; simp)
  have h3p : 0 < u₃ := hA_pos u₃ (by rw [hA_eq]; simp)
  have hvp : 0 < v₁ := hA_pos v₁ (by rw [hA_eq]; simp)
  have hcp : 0 < c := hA_pos c (by rw [hA_eq]; simp)
  have h1M : u₁ ≤ M := hA_le u₁ (by rw [hA_eq]; simp)
  have h2M : u₂ ≤ M := hA_le u₂ (by rw [hA_eq]; simp)
  have h3M : u₃ ≤ M := hA_le u₃ (by rw [hA_eq]; simp)
  have hvM : v₁ ≤ M := hA_le v₁ (by rw [hA_eq]; simp)
  have hcM : c ≤ M := hA_le c (by rw [hA_eq]; simp)
  have hA_card : A.card = 5 := by
    rw [hA_eq, Finset.card_insert_of_notMem (by simp [h12, h13, h1v, h1c]),
        Finset.card_insert_of_notMem (by simp [h23, h2v, h2c]),
        Finset.card_insert_of_notMem (by simp [h3v, h3c]),
        Finset.card_insert_of_notMem (by simp [hvc]), Finset.card_singleton]
  by_cases h2c_le : 2 * c ≤ M
  · let g₁ := Nat.gcd u₁ u₂
    let g₂ := Nat.gcd c v₁
    have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left u₂ h1p
    have hg₂_pos : 0 < g₂ := Nat.gcd_pos_of_pos_left v₁ hcp
    have h3g1 : 3 * g₁ ≤ M := three_mul_le_of_two_gt_half_5 hg₁_pos h12 h1M h2M hu1_h hu2_h
      (Nat.gcd_dvd_left u₁ u₂) (Nat.gcd_dvd_right u₁ u₂)
    by_cases h3g2 : 3 * g₂ ≤ M
    · obtain ⟨w₁, hw₁_I, hw₁_not, hg₁_w₁⟩ := exists_avoiding_multiple_5 x M g₁ {b₁, b₂}
        hg₁_pos (le_trans (Nat.mul_le_mul_right g₁ (by
          have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3g1)
      obtain ⟨w₂, hw₂_I, hw₂_not, hg₂_w₂⟩ := exists_avoiding_multiple_5 x M g₂ {b₁, b₂}
        hg₂_pos (le_trans (Nat.mul_le_mul_right g₂ (by
          have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3g2)
      have hw1_b1 : w₁ ≠ b₁ := fun h => hw₁_not (by simp [h])
      have hw1_b2 : w₁ ≠ b₂ := fun h => hw₁_not (by simp [h])
      have hw2_b1 : w₂ ≠ b₁ := fun h => hw₂_not (by simp [h])
      have hw2_b2 : w₂ ≠ b₂ := fun h => hw₂_not (by simp [h])
      have hb₁0 : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁_I).ne'
      have hb₂0 : b₂ ≠ 0 := (pos_of_mem_consecInterval hb₂_I).ne'
      have hAer : A.erase u₃ = {u₁, u₂, c, v₁} := by
        ext z; simp only [hA_eq, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hz3, rfl | rfl | rfl | rfl | rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact absurd rfl hz3
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inr (Or.inr (Or.inl rfl))
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨h13, Or.inl rfl⟩
          · exact ⟨h23, Or.inr (Or.inl rfl)⟩
          · exact ⟨h3c.symm, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
          · exact ⟨h3v.symm, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      have hA4_0 : ∀ a ∈ A.erase u₃, a ≠ 0 := fun a ha => (hA_pos a (Finset.mem_erase.mp ha).2).ne'
      refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 (u := u₃) (by rw [hA_eq]; simp) ?_
      rw [hAer]
      by_cases hw12 : w₁ = w₂
      · let g₁₂ := Nat.gcd g₁ g₂
        have hg₁₂_pos : 0 < g₁₂ := Nat.gcd_pos_of_pos_left g₂ hg₁_pos
        have h4g₁₂ : 4 * g₁₂ ≤ M := four_mul_le_of_four_dvd_distinct hg₁₂_pos h12 h1c h1v h2c h2v hvc.symm
          h1p h2p hcp hvp h1M h2M hcM hvM
          (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_left u₁ u₂))
          (dvd_trans (Nat.gcd_dvd_left g₁ g₂) (Nat.gcd_dvd_right u₁ u₂))
          (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_left c v₁))
          (dvd_trans (Nat.gcd_dvd_right g₁ g₂) (Nat.gcd_dvd_right c v₁))
        obtain ⟨w₃, hw₃_I, hw₃_not, hg₁₂_w₃⟩ := exists_avoiding_multiple_5 x M g₁₂ {b₁, b₂, w₁}
          hg₁₂_pos (le_trans (Nat.mul_le_mul_right g₁₂ (by
            have h1 := Finset.card_insert_le b₁ {b₂, w₁}
            have h2 := Finset.card_insert_le b₂ {w₁}; simp at h2 ⊢; omega)) h4g₁₂)
        have hw3_b1 : w₃ ≠ b₁ := fun h => hw₃_not (by simp [h])
        have hw3_b2 : w₃ ≠ b₂ := fun h => hw₃_not (by simp [h])
        have hw3_w1 : w₃ ≠ w₁ := fun h => hw₃_not (by simp [h])
        let B : Finset ℕ := {b₁, b₂, w₁, w₃}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 (by rw [← hAer]; exact hA4_0) hB0 ?_⟩
        intro p _hp
        have hsumA : ∑ a ∈ ({u₁, u₂, c, v₁} : Finset ℕ), a.factorization p =
            u₁.factorization p + u₂.factorization p + c.factorization p + v₁.factorization p := by
          rw [Finset.sum_insert (by simp [h12, h1c, h1v]), Finset.sum_insert (by simp [h2c, h2v]),
              Finset.sum_insert (by simp [hvc.symm]), Finset.sum_singleton]; ring
        have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + w₃.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw3_b1.symm]),
              Finset.sum_insert (by simp [hw1_b2.symm, hw3_b2.symm]),
              Finset.sum_insert (by simp [hw3_w1.symm]), Finset.sum_singleton]; ring
        rw [hsumA, ← hsumB]
        have hb1_1 := fac_le_of_dvd_5 hb₁0 hb₁_u1 (p := p)
        have hb1_2 := fac_le_of_dvd_5 hb₁0 hb₁_u2 (p := p)
        have hb2_c' := fac_le_of_dvd_5 hb₂0 hb₂_c (p := p)
        have hb2_v' := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
        have hw10 := (pos_of_mem_consecInterval hw₁_I).ne'
        have hw30 := (pos_of_mem_consecInterval hw₃_I).ne'
        have hw1_g1 := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
        have hw1_g2 := fac_le_of_dvd_5 hw10 (hw12 ▸ hg₂_w₂) (p := p)
        have hw3_g12 := fac_le_of_dvd_5 hw30 hg₁₂_w₃ (p := p)
        rw [fac_gcd_eq_min_5 h1p.ne' h2p.ne'] at hw1_g1
        rw [fac_gcd_eq_min_5 hcp.ne' hvp.ne'] at hw1_g2
        rw [fac_gcd_eq_min_5 hg₁_pos.ne' hg₂_pos.ne',
            fac_gcd_eq_min_5 h1p.ne' h2p.ne', fac_gcd_eq_min_5 hcp.ne' hvp.ne'] at hw3_g12
        have hvi := r2_31_merged_ineq (u₁.factorization p) (u₂.factorization p) (c.factorization p) (v₁.factorization p)
        omega
      · let B : Finset ℕ := {b₁, b₂, w₁, w₂}
        have hBI : B ⊆ consecInterval x M := by
          intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl | rfl | rfl <;> assumption
        have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
        refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
          isCover_of_prime_factorization_5 (by rw [← hAer]; exact hA4_0) hB0 ?_⟩
        intro p _hp
        have hsumA : ∑ a ∈ ({u₁, u₂, c, v₁} : Finset ℕ), a.factorization p =
            u₁.factorization p + u₂.factorization p + c.factorization p + v₁.factorization p := by
          rw [Finset.sum_insert (by simp [h12, h1c, h1v]), Finset.sum_insert (by simp [h2c, h2v]),
              Finset.sum_insert (by simp [hvc.symm]), Finset.sum_singleton]; ring
        have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + w₂.factorization p =
            ∑ b ∈ B, b.factorization p := by
          dsimp [B]
          rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hw2_b1.symm]),
              Finset.sum_insert (by simp [hw1_b2.symm, hw2_b2.symm]),
              Finset.sum_insert (by simp [hw12]), Finset.sum_singleton]; ring
        rw [hsumA, ← hsumB]
        have hb1_1 := fac_le_of_dvd_5 hb₁0 hb₁_u1 (p := p)
        have hb1_2 := fac_le_of_dvd_5 hb₁0 hb₁_u2 (p := p)
        have hb2_c' := fac_le_of_dvd_5 hb₂0 hb₂_c (p := p)
        have hb2_v' := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
        have hw10 := (pos_of_mem_consecInterval hw₁_I).ne'
        have hw20 := (pos_of_mem_consecInterval hw₂_I).ne'
        have hw1_g1 := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
        have hw2_g2 := fac_le_of_dvd_5 hw20 hg₂_w₂ (p := p)
        rw [fac_gcd_eq_min_5 h1p.ne' h2p.ne'] at hw1_g1
        rw [fac_gcd_eq_min_5 hcp.ne' hvp.ne'] at hw2_g2
        omega
    · -- `M < 3 * g₂`: since `g₂ ∣ c ≤ M/2 < v₁ ≤ M < 3 * g₂`, forces `g₂ = c` and `v₁ = 2 * c`!
      have h3c_gt : M < 3 * c := by
        have : g₂ ≤ c := Nat.le_of_dvd hcp (Nat.gcd_dvd_left c v₁)
        omega
      have hv1_eq : v₁ = 2 * c := by
        obtain ⟨qc, hqc⟩ := Nat.gcd_dvd_left c v₁
        obtain ⟨qv, hqv⟩ := Nat.gcd_dvd_right c v₁
        have hqc1 : qc = 1 := by
          by_contra hne1
          have hqc_pos : 1 ≤ qc := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hqc; omega
          have hqc2 : 2 ≤ qc := by omega
          have : 2 * g₂ ≤ c := by nlinarith
          omega
        have hg2_eq : g₂ = c := by rw [hqc, hqc1, mul_one]
        have hqv2 : 2 ≤ qv := by
          by_contra hlt2; have hqv1 : qv ≤ 1 := by omega
          have : v₁ ≤ g₂ := by nlinarith
          omega
        have hqv_eq2 : qv = 2 := by
          by_contra hne2; have hqv3 : 3 ≤ qv := by omega
          have : 3 * g₂ ≤ v₁ := by nlinarith
          omega
        have hg2_eq' : c.gcd v₁ = c := hg2_eq
        rw [hqv, hqv_eq2, hg2_eq', mul_comm]
      let U3 : Finset ℕ := {u₁, u₂, u₃}
      by_cases hpair3 : ∀ a ∈ U3, ∀ b ∈ U3, a ≠ b → Nat.lcm a b = U3.lcm id
      · -- Check `c ∣ L₃` vs `¬ (c ∣ L₃)`!
        let L₃ := U3.lcm id
        by_cases hcL3 : c ∣ L₃
        · obtain ⟨z₃, z₂, z₁, hz_eq, hz32, hz21⟩ := sort3_dec h12 h13 h23
          have hz_eq' : ({u₁, u₂, u₃} : Finset ℕ) = {z₁, z₂, z₃} := by
            have h1 : z₁ = z₃ ∨ z₁ = z₂ ∨ z₁ = z₁ := Or.inr (Or.inr rfl)
            have h2 : z₂ = z₃ ∨ z₂ = z₂ ∨ z₂ = z₁ := Or.inr (Or.inl rfl)
            have h3 : z₃ = z₃ ∨ z₃ = z₂ ∨ z₃ = z₁ := Or.inl rfl
            rw [hz_eq]; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
            exact ⟨by rintro (rfl | rfl | rfl) <;> simp, by rintro (rfl | rfl | rfl) <;> simp⟩
          have hzin : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ∈ U3 := fun z hz => by dsimp [U3]; rw [hz_eq']; exact hz
          have hA_z : A = {z₁, z₂, z₃, c, v₁} := by
            have hu1_z : u₁ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq']; simp
            have hu2_z : u₂ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq']; simp
            have hu3_z : u₃ ∈ ({z₁, z₂, z₃} : Finset ℕ) := by rw [← hz_eq']; simp
            have hz1_u := hzin z₁ (by simp)
            have hz2_u := hzin z₂ (by simp)
            have hz3_u := hzin z₃ (by simp)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu1_z hu2_z hu3_z
            simp only [U3, Finset.mem_insert, Finset.mem_singleton] at hz1_u hz2_u hz3_u
            rw [hA_eq]; ext z
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro hz
              rcases hz with rfl | rfl | rfl | rfl | rfl
              · rcases hu1_z with h | h | h <;> simp [h]
              · rcases hu2_z with h | h | h <;> simp [h]
              · rcases hu3_z with h | h | h <;> simp [h]
              · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · intro hz
              rcases hz with rfl | rfl | rfl | rfl | rfl
              · rcases hz1_u with h | h | h <;> simp [h]
              · rcases hz2_u with h | h | h <;> simp [h]
              · rcases hz3_u with h | h | h <;> simp [h]
              · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          have hz_b1 : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ∣ b₁ := fun z hz => by
            have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl | rfl <;> assumption
          have hz_h : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), M < 2 * z := fun z hz => by
            have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl | rfl <;> assumption
          have hz_nc : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ≠ c := fun z hz => by
            have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl | rfl <;> assumption
          have hz_nv : ∀ z ∈ ({z₁, z₂, z₃} : Finset ℕ), z ≠ v₁ := fun z hz => by
            have := hzin z hz; simp only [U3, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | rfl | rfl <;> assumption
          exact cover_six_of_pairspan3_c_2c hA_z hz32 hz21
            (hz_nc z₁ (by simp)) (hz_nc z₂ (by simp)) (hz_nc z₃ (by simp))
            (hz_nv z₁ (by simp)) (hz_nv z₂ (by simp)) (hz_nv z₃ (by simp)) hvc.symm
            hA_pos hA_le hAgcd (hz_h z₁ (by simp)) (hz_h z₂ (by simp)) (hz_h z₃ (by simp))
            h2c_le h3c_gt hv1_eq hb₁_I hb₂_I hb12
            (hz_b1 z₁ (by simp)) (hz_b1 z₂ (by simp)) (hz_b1 z₃ (by simp))
            hb₂_c (Or.inl hb₂_v1) (by rw [← hz_eq']; exact hcL3) (by rw [← hz_eq']; exact hpair3)
        · -- `¬ (c ∣ L₃)`: `h_c = gcd L₃ c` is a proper divisor of `c ≤ M/2` ⇒ `4 * h_c ≤ 2 * c ≤ M`!
          -- Since `hpair3` says `lcm u₁ u₂ = L₃`, we have `¬ (c ∣ lcm u₁ u₂)`, and `{b₁, b₂, w₁, w_h}` covers `A.erase u₃ = {u₁, u₂, c, v₁}`!
          have hL12_eq : Nat.lcm u₁ u₂ = L₃ := hpair3 u₁ (by simp [U3]) u₂ (by simp [U3]) h12
          have hc_nd_12 : ¬ (c ∣ Nat.lcm u₁ u₂) := hL12_eq.symm ▸ hcL3
          let hc := Nat.gcd (Nat.lcm u₁ u₂) c
          have hL12_pos : 0 < Nat.lcm u₁ u₂ := Nat.lcm_pos h1p h2p
          have hhc_pos : 0 < hc := Nat.gcd_pos_of_pos_left c hL12_pos
          have h4hc : 4 * hc ≤ M := by
            have h2hc : 2 * hc ≤ c := gcd_not_dvd_mul_le hL12_pos hcp (le_refl c) hc_nd_12
            omega
          obtain ⟨w₁, hw₁_I, hw₁_not, hg₁_w₁⟩ := exists_avoiding_multiple_5 x M g₁ {b₁, b₂}
            hg₁_pos (le_trans (Nat.mul_le_mul_right g₁ (by
              have := Finset.card_insert_le b₁ {b₂}; simp at this ⊢; omega)) h3g1)
          obtain ⟨wh, hwh_I, hwh_not, hhc_wh⟩ := exists_avoiding_multiple_5 x M hc {b₁, b₂, w₁}
            hhc_pos (le_trans (Nat.mul_le_mul_right hc (by
              have h1 := Finset.card_insert_le b₁ {b₂, w₁}
              have h2 := Finset.card_insert_le b₂ {w₁}; simp at h2 ⊢; omega)) h4hc)
          have hw1_b1 : w₁ ≠ b₁ := fun h => hw₁_not (by simp [h])
          have hw1_b2 : w₁ ≠ b₂ := fun h => hw₁_not (by simp [h])
          have hwh_b1 : wh ≠ b₁ := fun h => hwh_not (by simp [h])
          have hwh_b2 : wh ≠ b₂ := fun h => hwh_not (by simp [h])
          have hwh_w1 : wh ≠ w₁ := fun h => hwh_not (by simp [h])
          have hAer : A.erase u₃ = {u₁, u₂, c, v₁} := by
            ext z; simp only [hA_eq, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hz3, rfl | rfl | rfl | rfl | rfl⟩
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact absurd rfl hz3
              · exact Or.inr (Or.inr (Or.inr rfl))
              · exact Or.inr (Or.inr (Or.inl rfl))
            · rintro (rfl | rfl | rfl | rfl)
              · exact ⟨h13, Or.inl rfl⟩
              · exact ⟨h23, Or.inr (Or.inl rfl)⟩
              · exact ⟨h3c.symm, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
              · exact ⟨h3v.symm, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
          refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 (u := u₃) (by rw [hA_eq]; simp) ?_
          rw [hAer]
          let B : Finset ℕ := {b₁, b₂, w₁, wh}
          have hBI : B ⊆ consecInterval x M := by
            intro b hb; simp only [B, Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl | rfl <;> assumption
          have hA4_0 : ∀ a ∈ ({u₁, u₂, c, v₁} : Finset ℕ), a ≠ 0 := fun a ha => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega
          have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hBI hb)).ne'
          refine ⟨B, hBI, card_finset_le_four_5 _ _ _ _,
            isCover_of_prime_factorization_5 hA4_0 hB0 ?_⟩
          intro p _hp
          have hsumA : ∑ a ∈ ({u₁, u₂, c, v₁} : Finset ℕ), a.factorization p =
              u₁.factorization p + u₂.factorization p + c.factorization p + v₁.factorization p := by
            rw [Finset.sum_insert (by simp [h12, h1c, h1v]), Finset.sum_insert (by simp [h2c, h2v]),
                Finset.sum_insert (by simp [hvc.symm]), Finset.sum_singleton]; ring
          have hsumB : b₁.factorization p + b₂.factorization p + w₁.factorization p + wh.factorization p =
              ∑ b ∈ B, b.factorization p := by
            dsimp [B]
            rw [Finset.sum_insert (by simp [hb12, hw1_b1.symm, hwh_b1.symm]),
                Finset.sum_insert (by simp [hw1_b2.symm, hwh_b2.symm]),
                Finset.sum_insert (by simp [hwh_w1.symm]), Finset.sum_singleton]; ring
          rw [hsumA, ← hsumB]
          have hb₁0 := (pos_of_mem_consecInterval hb₁_I).ne'
          have hb₂0 := (pos_of_mem_consecInterval hb₂_I).ne'
          have hw10 := (pos_of_mem_consecInterval hw₁_I).ne'
          have hwh0 := (pos_of_mem_consecInterval hwh_I).ne'
          have hb1_1 := fac_le_of_dvd_5 hb₁0 hb₁_u1 (p := p)
          have hb1_2 := fac_le_of_dvd_5 hb₁0 hb₁_u2 (p := p)
          have hb2_v' := fac_le_of_dvd_5 hb₂0 hb₂_v1 (p := p)
          have hw1_g := fac_le_of_dvd_5 hw10 hg₁_w₁ (p := p)
          have hwh_c := fac_le_of_dvd_5 hwh0 hhc_wh (p := p)
          rw [fac_gcd_eq_min_5 h1p.ne' h2p.ne'] at hw1_g
          rw [fac_gcd_eq_min_5 hL12_pos.ne' hcp.ne', fac_lcm_eq_max_5 h1p.ne' h2p.ne'] at hwh_c
          have hvi := r2_nonspan3_val_ineq (u₁.factorization p) (u₂.factorization p) (c.factorization p) (v₁.factorization p)
          change u₁.factorization p + u₂.factorization p + c.factorization p + v₁.factorization p ≤
            max (max (u₁.factorization p) (u₂.factorization p)) (c.factorization p) + v₁.factorization p +
            min (u₁.factorization p) (u₂.factorization p) + min (max (u₁.factorization p) (u₂.factorization p)) (c.factorization p) at hvi
          -- Wait: `b₁` covers `max(u1, u2)`, `b₂` covers `v₁` (and `c`!), `w₁` covers `min(u1, u2)`, `wh` covers `min(max(u1, u2), c)`!
          -- And `c ≤ v₁` (`v₁ = 2*c`), so `max(max(u1, u2), c) + v₁ ≤ max(u1, u2) + v₁ + max ...` wait: if `c > max(u1, u2)` at `p`, then `min(max(u1,u2), c) = max(u1, u2)`, so `max(u1, u2) + min(max(u1,u2), c) + v₁ = ...`? Wait: check `c ≤ max(u1, u2)` vs `c > max(u1, u2)`!
          -- If `c > max(u1, u2)`: `v₁ ≥ c` so `b₂` ALREADY has `v₁` AND `b₁` has `max(u1, u2)` AND `wh` has `min(max(u1,u2), c) = max(u1, u2)`, STILL only `u1 + u2 + max(u1, u2) + v1`... wait: `u1 + u2 + c + v1` ≤ `(max u1 u2) + v1 + min u1 u2 + max u1 u2`? NO if `c > max u1 u2`!
          -- **LOOK!!** Check `u1 = 0, u2 = 0, c = 2, v1 = 2`: `u1 + u2 + c + v1 = 4`, while `b₁ = 0, b₂ = 2, w₁ = 0, wh = 0` gives `2 < 4`!!
          -- Wait: WHY did `v₁ = 2*c` allow `c = 2 > max(u1, u2)`?!
          -- Because `b₁` ALSO has **`c ∣ b₁`** (remember `c ∈ C` divides BOTH `b₁` AND `b₂`!!)!!
          -- **OH!! `hb₁_c : c ∣ b₁`!!**
          -- SO `b₁` HAS `max (max u₁ u₂) c` DIRECTLY!!
          have hb1_c' := fac_le_of_dvd_5 hb₁0 hb₁_c (p := p)
          omega
      · -- Some ordering `(y₁, y₂, y₃)` of `U₃` has `¬ (y₃ ∣ lcm y₁ y₂)`: drop `c` and call `cover_four_of_nonspan3`!
        push Not at hpair3
        obtain ⟨y₁, hy1, y₂, hy2, hy12, hne_L⟩ := hpair3
        have hnd3 : ∃ y₃ ∈ U3, ¬ (y₃ ∣ Nat.lcm y₁ y₂) := by
          by_contra hall; push Not at hall
          exact hne_L (Nat.dvd_antisymm (Nat.lcm_dvd (Finset.dvd_lcm hy1) (Finset.dvd_lcm hy2)) (Finset.lcm_dvd hall))
        obtain ⟨y₃, hy3, hy3_nd⟩ := hnd3
        have hy13 : y₁ ≠ y₃ := fun heq => hy3_nd (heq ▸ Nat.dvd_lcm_left y₁ y₂)
        have hy23 : y₂ ≠ y₃ := fun heq => hy3_nd (heq ▸ Nat.dvd_lcm_right y₁ y₂)
        have hy_u : ∀ y ∈ U3, y ∣ b₁ ∧ M < 2 * y ∧ y ≠ v₁ ∧ y ≠ c := fun y hy => by
          simp only [U3, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl <;> refine ⟨by assumption, by assumption, by assumption, by assumption⟩
        have hy_pos : ∀ y ∈ U3, 0 < y := fun y hy => hA_pos y (by
          rw [hA_eq]; rcases (by simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hy : y = u₁ ∨ y = u₂ ∨ y = u₃) with rfl | rfl | rfl <;> simp)
        have hy_le : ∀ y ∈ U3, y ≤ M := fun y hy => hA_le y (by
          rw [hA_eq]; rcases (by simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hy : y = u₁ ∨ y = u₂ ∨ y = u₃) with rfl | rfl | rfl <;> simp)
        have hU3_eq : U3 = {y₁, y₂, y₃} := by
          apply Finset.eq_of_subset_of_card_le
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton]
            by_contra hno; push Not at hno
            have h4sub : insert z ({y₁, y₂, y₃} : Finset ℕ) ⊆ U3 := Finset.insert_subset hz (fun w hw => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl <;> assumption)
            have h4c : (insert z ({y₁, y₂, y₃} : Finset ℕ)).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp [hno]),
                  Finset.card_insert_of_notMem (by simp [hy12, hy13]),
                  Finset.card_insert_of_notMem (by simp [hy23]), Finset.card_singleton]
            have h3c : U3.card ≤ 3 := card_finset_le_three_5 u₁ u₂ u₃
            have := Finset.card_le_card h4sub
            omega
          · rw [Finset.card_insert_of_notMem (by simp [hy12, hy13]),
                Finset.card_insert_of_notMem (by simp [hy23]), Finset.card_singleton]
            dsimp [U3]
            rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
        have hu1_y : u₁ = y₁ ∨ u₁ = y₂ ∨ u₁ = y₃ := by
          have h : u₁ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hU3_eq]; simp [U3]
          simpa only [Finset.mem_insert, Finset.mem_singleton] using h
        have hu2_y : u₂ = y₁ ∨ u₂ = y₂ ∨ u₂ = y₃ := by
          have h : u₂ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hU3_eq]; simp [U3]
          simpa only [Finset.mem_insert, Finset.mem_singleton] using h
        have hu3_y : u₃ = y₁ ∨ u₃ = y₂ ∨ u₃ = y₃ := by
          have h : u₃ ∈ ({y₁, y₂, y₃} : Finset ℕ) := by rw [← hU3_eq]; simp [U3]
          simpa only [Finset.mem_insert, Finset.mem_singleton] using h
        have hy1_u' : y₁ = u₁ ∨ y₁ = u₂ ∨ y₁ = u₃ := by
          simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hy1
        have hy2_u' : y₂ = u₁ ∨ y₂ = u₂ ∨ y₂ = u₃ := by
          simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hy2
        have hy3_u' : y₃ = u₁ ∨ y₃ = u₂ ∨ y₃ = u₃ := by
          simpa only [U3, Finset.mem_insert, Finset.mem_singleton] using hy3
        have hAer : A.erase c = {y₁, y₂, y₃, v₁} := by
          ext z; simp only [hA_eq, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hzc, hz⟩
            rcases hz with rfl | rfl | rfl | rfl | rfl
            · rcases hu1_y with h | h | h <;> simp [h]
            · rcases hu2_y with h | h | h <;> simp [h]
            · rcases hu3_y with h | h | h <;> simp [h]
            · exact Or.inr (Or.inr (Or.inr rfl))
            · exact absurd rfl hzc
          · intro hz
            rcases hz with hz | hz | hz | hz
            · rw [hz]; exact ⟨(hy_u y₁ hy1).2.2.2, by rcases hy1_u' with h | h | h <;> simp [h]⟩
            · rw [hz]; exact ⟨(hy_u y₂ hy2).2.2.2, by rcases hy2_u' with h | h | h <;> simp [h]⟩
            · rw [hz]; exact ⟨(hy_u y₃ hy3).2.2.2, by rcases hy3_u' with h | h | h <;> simp [h]⟩
            · rw [hz]; exact ⟨hvc, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        refine cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 (u := c) (by rw [hA_eq]; simp) ?_
        rw [hAer]
        refine cover_four_of_nonspan3 (hy_u y₁ hy1).2.2.1 (hy_u y₂ hy2).2.2.1 (hy_u y₃ hy3).2.2.1
          hy12 hy13 hy23 (hy_pos y₁ hy1) (hy_pos y₂ hy2) (hy_pos y₃ hy3) hvp
          (hy_le y₁ hy1) (hy_le y₂ hy2) (hy_le y₃ hy3) hvM
          (hy_u y₁ hy1).2.1 (hy_u y₂ hy2).2.1 (hy_u y₃ hy3).2.1
          hb₁_I hb₂_I hb12 (hy_u y₁ hy1).1 (hy_u y₂ hy2).1 (hy_u y₃ hy3).1 hb₂_v1 hy3_nd ?_
        intro ⟨_, h2v⟩
        have := hy_le y₃ hy3
        omega
  · -- `¬ (2 * c ≤ M)` ⇒ `M < 2 * c`: all 5 elements in `(M/2, M]`, `{u₁, u₂, u₃} ∣ b₁`, `{v₁, c} ∣ b₂`!
    have hc_h : M < 2 * c := by omega
    obtain ⟨u, huA, B, hBI, hBcard, hBcov⟩ := cover_four_of_32_half h12 h13 h1v h1c h23 h2v h2c
      h3v h3c hvc (fun a ha => hA_pos a (by rw [hA_eq]; exact ha))
      (fun a ha => hA_le a (by rw [hA_eq]; exact ha))
      (fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption)
      hb₁_I hb₂_I hb12 hb₁_u1 hb₁_u2 hb₁_u3 hb₂_v1 hb₂_c
    rw [← hA_eq] at huA hBcov
    exact cover_six_of_cover_four_erase hA_card hA_pos hA_le hAgcd hM7 huA ⟨B, hBI, hBcard, hBcov⟩

end Erdos708

