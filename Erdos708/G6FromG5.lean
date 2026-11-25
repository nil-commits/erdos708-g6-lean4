import Erdos708.G6R4

/-!
# PPL 176 (Erdős Problem #708) — Unconditional Conditional Reduction `g(5) ≤ 6 → g(6) ≤ 8`

This module proves:
1. **Generalized Layer-Cake Deficit Bounds (`layer_cake_deficit_le_of_pow_subset`)**:
   Under `A.card = 6` and `A.gcd id = 1`, if every multiple of `p ^ t` (`1 ≤ t`) in
   `consecInterval x M` belongs to `B₀`, then the `p`-adic deficit satisfies
   `(∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ (5 - M / p ^ t) * (t - 1)`.
   Immediate corollaries:
   - `t = 1`: deficit `= 0` (so any prime dividing `R` leaves at least one multiple outside `B₀`),
   - `M / p ^ t ≥ 5`: deficit `= 0`!
2. **Unconditional `≤ 2`-Slot Closure for `R ∣ M` (`exists_two_slots_for_R_dvd_M`)**:
   For `A.card = 6`, `A.gcd id = 1`, `9 ≤ M`, `B₀ ⊆ consecInterval x M` with `B₀.card ≤ 6`,
   and residual `R ∣ M` accounting for all prime-valuation deficits, there exists
   `B₁ ⊆ consecInterval x M` disjoint from `B₀` with `B₁.card ≤ 2` absorbing `R`.
3. **Master Reduction (`erdos708_upper_six_of_upper_five`)**:
   `SatisfiesBound 5 6 → SatisfiesBound 6 8`, proved via strong induction on `M`,
   `erdos708_gcd_reduction` (reducing `A.gcd id > 1`), `A.erase M` (feeding `hg5`),
   and `exists_two_slots_for_R_dvd_M`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Generalized Layer-Cake Deficit Bounds & Interval Helpers -/

private lemma consecInterval_eq_erdos708Interval (x M : ℕ) :
    consecInterval x M = Erdos708Interval x M := rfl

private lemma sup_id_eq_max' {A : Finset ℕ} (hA : A.Nonempty) :
    A.sup id = A.max' hA := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact Finset.le_max' A a ha
  · exact Finset.le_sup (f := id) (Finset.max'_mem A hA)

private lemma card_multiples_Icc_le_from5 (x M d : ℕ) (hM : 1 ≤ M) (_hd : 0 < d) :
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
      have hsub_eq : b₁ - b₀ = b₂ - b₀ := by
        rw [← hmul1, ← hmul2, heq]
      omega
    simpa [Finset.card_range] using Finset.card_le_card_of_injOn g hmaps hinj
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS, Finset.card_empty]
    exact Nat.zero_le _

private lemma card_multiples_M_le_one (x M : ℕ) (hM : 1 ≤ M) :
    ((consecInterval x M).filter (fun b => M ∣ b)).card ≤ 1 := by
  have h1 := card_multiples_Icc_le_from5 x M M hM (by omega)
  have h0 : (M - 1) / M = 0 := Nat.div_eq_of_lt (by omega)
  omega

private lemma sum_factorization_eq_sum_card_Icc {A : Finset ℕ} {M p : ℕ}
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

private lemma sum_card_Icc_le_sum_factorization {S : Finset ℕ} {x M K p : ℕ}
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

private lemma exists_not_dvd_of_gcd_one {A : Finset ℕ} (hAgcd : A.gcd id = 1)
    {p : ℕ} (hp : p.Prime) :
    ∃ a₀ ∈ A, ¬ (p ∣ a₀) := by
  by_contra hall
  push Not at hall
  have hpgcd : p ∣ A.gcd id := Finset.dvd_gcd (fun a ha => hall a ha)
  rw [hAgcd] at hpgcd
  exact hp.not_dvd_one hpgcd

private lemma card_filter_le_five_and_div {A : Finset ℕ} {M p j : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hp : p.Prime) (hj : 1 ≤ j) :
    (A.filter (fun a => p ^ j ∣ a)).card ≤ 5 ∧
      (A.filter (fun a => p ^ j ∣ a)).card ≤ M / p ^ j := by
  obtain ⟨a₀, ha₀A, ha₀_ndvd⟩ := exists_not_dvd_of_gcd_one hAgcd hp
  have hnot_pj : ¬ (p ^ j ∣ a₀) := by
    intro h
    exact ha₀_ndvd (dvd_trans (dvd_pow_self p (by omega)) h)
  have hsub5 : A.filter (fun a => p ^ j ∣ a) ⊆ A.erase a₀ := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_erase.mpr ⟨fun heq => hnot_pj (heq ▸ ha.2), ha.1⟩
  have hcard5 : (A.filter (fun a => p ^ j ∣ a)).card ≤ 5 := by
    have h1 := Finset.card_le_card hsub5
    rw [Finset.card_erase_of_mem ha₀A, hA_card] at h1
    exact h1
  have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
  have hsubI : A.filter (fun a => p ^ j ∣ a) ⊆ (Finset.Icc 1 M).filter (fun a => p ^ j ∣ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_Icc.mpr ⟨hA_pos a ha.1, hA_le a ha.1⟩, ha.2⟩
  have hcardDiv : (A.filter (fun a => p ^ j ∣ a)).card ≤ M / p ^ j :=
    le_trans (Finset.card_le_card hsubI) (card_multiples_Icc_one_le M (p ^ j) hpj_pos)
  exact ⟨hcard5, hcardDiv⟩

/-- **Generalized Layer-Cake Deficit Bound**:
    under `A.card = 6` and `A.gcd id = 1`, if `(consecInterval x M).filter (p ^ t ∣ ·) ⊆ B₀`
    (`1 ≤ t`), then `(∑ A, v_p) - (∑ B₀, v_p) ≤ (5 - M / p ^ t) * (t - 1)`. -/
private lemma layer_cake_deficit_le_of_pow_subset {A B₀ : Finset ℕ} {x M p t : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (_ht : 1 ≤ t) (hsub : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀) :
    (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ (5 - M / p ^ t) * (t - 1) := by
  have hA_sum := sum_factorization_eq_sum_card_Icc hA_pos hA_le hp
  have hB₀_sum := sum_card_Icc_le_sum_factorization (K := M) hB₀_I hp
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
        (B₀.filter (fun b => p ^ j ∣ b)).card + (5 - M / p ^ t) := by
    intro j hj
    have hj_mem := (Finset.mem_filter.mp hj).1
    have hj_lt : j < t := (Finset.mem_filter.mp hj).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
    have hA5 := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd hp hj1).1
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
    have hAdiv := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd hp hj1).2
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
      (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (5 - M / p ^ t) * (t - 1) := by
    calc
      ∑ j ∈ J_lo, (A.filter (fun a => p ^ j ∣ a)).card
          ≤ ∑ j ∈ J_lo, ((B₀.filter (fun b => p ^ j ∣ b)).card + (5 - M / p ^ t)) :=
            Finset.sum_le_sum hlo_term
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) +
          ∑ _j ∈ J_lo, (5 - M / p ^ t) := Finset.sum_add_distrib
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + J_lo.card * (5 - M / p ^ t) := by
          simp
      _ ≤ (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (t - 1) * (5 - M / p ^ t) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hJlo_card) _
      _ = (∑ j ∈ J_lo, (B₀.filter (fun b => p ^ j ∣ b)).card) + (5 - M / p ^ t) * (t - 1) := by
          ring
  have hhi_sum : ∑ j ∈ J_hi, (A.filter (fun a => p ^ j ∣ a)).card ≤
      ∑ j ∈ J_hi, (B₀.filter (fun b => p ^ j ∣ b)).card := Finset.sum_le_sum hhi_term
  omega

private lemma exists_prime_multiple_avoiding_of_deficit_pos {A B₀ : Finset ℕ} {x M p : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
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
  have h0 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I hp (le_refl 1) hsub
  omega

private lemma exists_pow_multiple_avoiding_of_deficit_ge {A B₀ : Finset ℕ} {x M p t e : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (ht : 1 ≤ t) (hc5 : 5 ≤ M / p ^ t)
    (hdef : 1 ≤ (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) + (e - e)) :
    ∃ b ∈ consecInterval x M, b ∉ B₀ ∧ p ^ t ∣ b := by
  by_contra hall
  push Not at hall
  have hsub : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀ := by
    intro b hb
    rw [Finset.mem_filter] at hb
    by_contra hbB₀
    exact hall b hb.1 hbB₀ hb.2
  have h0 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I hp ht hsub
  have hzero : (5 - M / p ^ t) * (t - 1) = 0 := by
    have : 5 - M / p ^ t = 0 := by omega
    rw [this, zero_mul]
  omega

/-! ## Part 2: 1-Slot and 2-Slot Realization Helpers -/

private lemma two_slots_of_one_dvd {B₀ : Finset ℕ} {x M R w : ℕ}
    (hw_I : w ∈ consecInterval x M) (hw_notB₀ : w ∉ B₀) (hRw : R ∣ w) (hR0 : R ≠ 0) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  refine ⟨{w}, Finset.singleton_subset_iff.mpr hw_I, Finset.disjoint_singleton_right.mpr hw_notB₀,
    by simp, ?_⟩
  intro p _hp
  rw [Finset.sum_singleton]
  exact (Nat.factorization_le_iff_dvd hR0 (pos_of_mem_consecInterval hw_I).ne').mpr hRw p

private lemma two_slots_of_two_dvd {B₀ : Finset ℕ} {x M R w₁ w₂ : ℕ}
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

private lemma two_slots_of_coprime_dvd {B₀ : Finset ℕ} {x M R d₁ d₂ w₁ w₂ : ℕ}
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
    exact two_slots_of_one_dvd hw₁_I hw₁_notB₀ hRw₁ hR0
  · have hRw : R ∣ w₁ * w₂ := by rw [hR_eq]; exact mul_dvd_mul hd₁_w₁ hd₂_w₂
    exact two_slots_of_two_dvd hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ heq hRw hR0

/-! ## Part 3: Concrete Small-Case Residual Closures (`M ∈ {30, 60, 12}`) -/

private lemma exists_two_slots_M30_R30 {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 6)
    (hM_eq : M = 30) (hR_eq : R = 30)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  subst hM_eq
  let I := consecInterval x 30
  let I₆ := I.filter (fun b => 6 ∣ b)
  let I₁₀ := I.filter (fun b => 10 ∣ b)
  let I₁₅ := I.filter (fun b => 15 ∣ b)
  let I₃₀ := I.filter (fun b => 30 ∣ b)
  have hI₆_5 : 5 ≤ I₆.card := by
    have h := card_multiples_Icc_ge x 30 6 (by norm_num)
    norm_num at h; exact h
  have hI₁₀_3 : 3 ≤ I₁₀.card := by
    have h := card_multiples_Icc_ge x 30 10 (by norm_num)
    norm_num at h; exact h
  have hI₁₅_2 : 2 ≤ I₁₅.card := by
    have h := card_multiples_Icc_ge x 30 15 (by norm_num)
    norm_num at h; exact h
  have hI₃₀_1 : I₃₀.card ≤ 1 := card_multiples_M_le_one x 30 (by norm_num)
  have h6_10 : I₆ ∩ I₁₀ ⊆ I₃₀ := by
    intro b hb
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
    rw [Finset.mem_filter]
    have hlcm : Nat.lcm 6 10 ∣ b := Nat.lcm_dvd hb.1.2 hb.2.2
    have h30 : (30 : ℕ) = Nat.lcm 6 10 := by decide
    exact ⟨hb.1.1, h30 ▸ hlcm⟩
  have hU1_card : 7 ≤ (I₆ ∪ I₁₀).card := by
    have h1 := Finset.card_union_add_card_inter I₆ I₁₀
    have h2 : (I₆ ∩ I₁₀).card ≤ 1 := le_trans (Finset.card_le_card h6_10) hI₃₀_1
    omega
  have hU1_15 : (I₆ ∪ I₁₀) ∩ I₁₅ ⊆ I₃₀ := by
    intro b hb
    rcases Finset.mem_inter.mp hb with ⟨hbU, hb15⟩
    rcases Finset.mem_filter.mp hb15 with ⟨hbI, h15⟩
    refine Finset.mem_filter.mpr ⟨hbI, ?_⟩
    rcases Finset.mem_union.mp hbU with hb6 | hb10
    · have h1 := Nat.lcm_dvd (Finset.mem_filter.mp hb6).2 h15
      have h30 : (30 : ℕ) = Nat.lcm 6 15 := by decide
      exact h30 ▸ h1
    · have h1 := Nat.lcm_dvd (Finset.mem_filter.mp hb10).2 h15
      have h30 : (30 : ℕ) = Nat.lcm 10 15 := by decide
      exact h30 ▸ h1
  have hU_card : 8 ≤ ((I₆ ∪ I₁₀) ∪ I₁₅).card := by
    have h1 := Finset.card_union_add_card_inter (I₆ ∪ I₁₀) I₁₅
    have h2 : ((I₆ ∪ I₁₀) ∩ I₁₅).card ≤ 1 := le_trans (Finset.card_le_card hU1_15) hI₃₀_1
    omega
  have hnot_sub : ¬ ((I₆ ∪ I₁₀) ∪ I₁₅ ⊆ B₀) := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨w₁, hw₁_U, hw₁_notB₀⟩ := Finset.not_subset.mp hnot_sub
  have hw₁_I : w₁ ∈ I := by
    rcases Finset.mem_union.mp hw₁_U with hw12 | hw15
    · rcases Finset.mem_union.mp hw12 with hw6 | hw10
      · exact (Finset.mem_filter.mp hw6).1
      · exact (Finset.mem_filter.mp hw10).1
    · exact (Finset.mem_filter.mp hw15).1
  have hR_def : ∀ p : ℕ, p.Prime → p ∣ 30 →
      ∃ w₂ ∈ I, w₂ ∉ B₀ ∧ p ∣ w₂ := by
    intro p hp hp30
    have he1 : 1 ≤ R.factorization p :=
      (hp.pow_dvd_iff_le_factorization (by omega : R ≠ 0)).mp (by rw [pow_one, hR_eq]; exact hp30)
    exact exists_prime_multiple_avoiding_of_deficit_pos hA_card hA_pos hA_le hAgcd hB₀_I hp
      (by rw [← hR_fac p hp]; exact he1)
  rcases Finset.mem_union.mp hw₁_U with hw12 | hw15
  · rcases Finset.mem_union.mp hw12 with hw6 | hw10
    · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h5_w₂⟩ := hR_def 5 (by norm_num) (by norm_num)
      exact two_slots_of_coprime_dvd (R := R) (d₁ := 6) (d₂ := 5)
        (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
        hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw6).2 h5_w₂
    · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h3_w₂⟩ := hR_def 3 (by norm_num) (by norm_num)
      exact two_slots_of_coprime_dvd (R := R) (d₁ := 10) (d₂ := 3)
        (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
        hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw10).2 h3_w₂
  · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h2_w₂⟩ := hR_def 2 (by norm_num) (by norm_num)
    exact two_slots_of_coprime_dvd (R := R) (d₁ := 15) (d₂ := 2)
      (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
      hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw15).2 h2_w₂

private lemma exists_two_slots_M60_R60 {B₀ : Finset ℕ} {x M R : ℕ}
    (hB₀_card : B₀.card ≤ 6) (hM_eq : M = 60) (hR_eq : R = 60) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  subst hM_eq
  let I := consecInterval x 60
  let I₁₂ := I.filter (fun b => 12 ∣ b)
  let I₂₀ := I.filter (fun b => 20 ∣ b)
  let I₁₅ := I.filter (fun b => 15 ∣ b)
  let I₆₀ := I.filter (fun b => 60 ∣ b)
  have hI₁₂_5 : 5 ≤ I₁₂.card := by
    have h := card_multiples_Icc_ge x 60 12 (by norm_num)
    norm_num at h; exact h
  have hI₂₀_3 : 3 ≤ I₂₀.card := by
    have h := card_multiples_Icc_ge x 60 20 (by norm_num)
    norm_num at h; exact h
  have hI₁₅_4 : 4 ≤ I₁₅.card := by
    have h := card_multiples_Icc_ge x 60 15 (by norm_num)
    norm_num at h; exact h
  have hI₆₀_1 : I₆₀.card ≤ 1 := card_multiples_M_le_one x 60 (by norm_num)
  have h12_20 : I₁₂ ∩ I₂₀ ⊆ I₆₀ := by
    intro b hb
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
    rw [Finset.mem_filter]
    have hlcm : Nat.lcm 12 20 ∣ b := Nat.lcm_dvd hb.1.2 hb.2.2
    have h60 : (60 : ℕ) = Nat.lcm 12 20 := by decide
    exact ⟨hb.1.1, h60 ▸ hlcm⟩
  have hU1_card : 7 ≤ (I₁₂ ∪ I₂₀).card := by
    have h1 := Finset.card_union_add_card_inter I₁₂ I₂₀
    have h2 : (I₁₂ ∩ I₂₀).card ≤ 1 := le_trans (Finset.card_le_card h12_20) hI₆₀_1
    omega
  have hU1_15 : (I₁₂ ∪ I₂₀) ∩ I₁₅ ⊆ I₆₀ := by
    intro b hb
    rcases Finset.mem_inter.mp hb with ⟨hbU, hb15⟩
    rcases Finset.mem_filter.mp hb15 with ⟨hbI, h15⟩
    refine Finset.mem_filter.mpr ⟨hbI, ?_⟩
    rcases Finset.mem_union.mp hbU with hb12 | hb20
    · have h1 := Nat.lcm_dvd (Finset.mem_filter.mp hb12).2 h15
      have h60 : (60 : ℕ) = Nat.lcm 12 15 := by decide
      exact h60 ▸ h1
    · have h1 := Nat.lcm_dvd (Finset.mem_filter.mp hb20).2 h15
      have h60 : (60 : ℕ) = Nat.lcm 20 15 := by decide
      exact h60 ▸ h1
  have hU_card : 10 ≤ ((I₁₂ ∪ I₂₀) ∪ I₁₅).card := by
    have h1 := Finset.card_union_add_card_inter (I₁₂ ∪ I₂₀) I₁₅
    have h2 : ((I₁₂ ∪ I₂₀) ∩ I₁₅).card ≤ 1 := le_trans (Finset.card_le_card hU1_15) hI₆₀_1
    omega
  have hnot_sub : ¬ ((I₁₂ ∪ I₂₀) ∪ I₁₅ ⊆ B₀) := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨w₁, hw₁_U, hw₁_notB₀⟩ := Finset.not_subset.mp hnot_sub
  have hw₁_I : w₁ ∈ I := by
    rcases Finset.mem_union.mp hw₁_U with hw12 | hw15
    · rcases Finset.mem_union.mp hw12 with hw12' | hw20
      · exact (Finset.mem_filter.mp hw12').1
      · exact (Finset.mem_filter.mp hw20).1
    · exact (Finset.mem_filter.mp hw15).1
  rcases Finset.mem_union.mp hw₁_U with hw12 | hw15
  · rcases Finset.mem_union.mp hw12 with hw12' | hw20
    · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h5_w₂⟩ :=
        exists_avoiding_multiple_in_consecInterval x 60 5 B₀ (by norm_num) (by omega)
      exact two_slots_of_coprime_dvd (R := R) (d₁ := 12) (d₂ := 5)
        (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
        hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw12').2 h5_w₂
    · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h3_w₂⟩ :=
        exists_avoiding_multiple_in_consecInterval x 60 3 B₀ (by norm_num) (by omega)
      exact two_slots_of_coprime_dvd (R := R) (d₁ := 20) (d₂ := 3)
        (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
        hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw20).2 h3_w₂
  · obtain ⟨w₂, hw₂_I, hw₂_notB₀, h4_w₂⟩ :=
      exists_avoiding_multiple_in_consecInterval x 60 4 B₀ (by norm_num) (by omega)
    exact two_slots_of_coprime_dvd (R := R) (d₁ := 15) (d₂ := 4)
      (by rw [hR_eq]) (by norm_num) (by norm_num) (by norm_num)
      hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ (Finset.mem_filter.mp hw15).2 h4_w₂

private lemma exists_two_slots_M12_R4_or_R12 {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hB₀_I : B₀ ⊆ consecInterval x M)
    (hM_eq : M = 12) (hR_pos : 0 < R) (hR12 : R ∣ 12) (h4R : 4 ∣ R)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  subst hM_eq
  let I := consecInterval x 12
  by_cases hsub4 : I.filter (fun b => 4 ∣ b) ⊆ B₀
  · -- All multiples of `4` (hence `8`) in `I` lie in `B₀`.
    have hB₀_4 : 3 ≤ (B₀.filter (fun b => 2 ^ 2 ∣ b)).card := by
      have h1 : I.filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 2 ∣ b) := by
        intro b hb
        rw [Finset.mem_filter] at hb ⊢
        exact ⟨hsub4 (Finset.mem_filter.mpr ⟨hb.1, by norm_num at hb ⊢; exact hb.2⟩), hb.2⟩
      have h2 := card_multiples_Icc_ge x 12 4 (by norm_num)
      norm_num at h2
      exact le_trans h2 (Finset.card_le_card h1)
    have hB₀_8 : 1 ≤ (B₀.filter (fun b => 2 ^ 3 ∣ b)).card := by
      have h1 : I.filter (fun b => 2 ^ 3 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 3 ∣ b) := by
        intro b hb
        rw [Finset.mem_filter] at hb ⊢
        have h4b : 4 ∣ b := dvd_trans (by norm_num) hb.2
        exact ⟨hsub4 (Finset.mem_filter.mpr ⟨hb.1, h4b⟩), hb.2⟩
      have h2 := card_multiples_Icc_ge x 12 8 (by norm_num)
      rw [show (12 / 8 : ℕ) = 1 by norm_num] at h2
      exact le_trans h2 (Finset.card_le_card h1)
    have hB₀_2_ge4 : (B₀.filter (fun b => 2 ^ 1 ∣ b)).card ≤ 3 := by
      by_contra hgt
      have h4_le : 4 ≤ (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by omega
      have hB₀_sum_ge8 : 8 ≤ ∑ b ∈ B₀, b.factorization 2 := by
        have h1 := sum_card_Icc_le_sum_factorization (K := 3) hB₀_I (by norm_num : Nat.Prime 2)
        have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
        rw [hIcc3, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h1
        omega
      have hA_sum_le9 : ∑ a ∈ A, a.factorization 2 ≤ 9 := by
        have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 2)
        have hc1 : (A.filter (fun a => 2 ^ 1 ∣ a)).card ≤ 5 :=
          (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 1) (by norm_num) (by omega)).1
        have hc2 : (A.filter (fun a => 2 ^ 2 ∣ a)).card ≤ 3 := by
          have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 2) (by norm_num) (by omega)).2
          rw [show (12 / 2 ^ 2 : ℕ) = 3 by norm_num] at h; exact h
        have hc3 : (A.filter (fun a => 2 ^ 3 ∣ a)).card ≤ 1 := by
          have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 3) (by norm_num) (by omega)).2
          rw [show (12 / 2 ^ 3 : ℕ) = 1 by norm_num] at h; exact h
        have hcz : ∀ j ∈ Finset.Icc 4 12, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := j) (by norm_num) (by omega)).2
          have hpow : 16 ≤ 2 ^ j :=
            le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hj.1)
          have hdiv0 : 12 / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
          omega
        have hIcc12 : Finset.Icc 1 12 = insert 1 (insert 2 (insert 3 (Finset.Icc 4 12))) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc12, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide)] at h1
        have hsum0 : ∑ j ∈ Finset.Icc 4 12, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 :=
          Finset.sum_eq_zero hcz
        omega
      have hdef2 : 2 ≤ R.factorization 2 :=
        ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hR_pos.ne').mp h4R
      have hfac2 := hR_fac 2 (by norm_num)
      omega
    have hB₀_2_eq_4 : B₀.filter (fun b => 2 ∣ b) = B₀.filter (fun b => 4 ∣ b) := by
      have h2eq : B₀.filter (fun b => 2 ∣ b) = B₀.filter (fun b => 2 ^ 1 ∣ b) := by
        ext b; simp only [pow_one]
      have h4eq : B₀.filter (fun b => 4 ∣ b) = B₀.filter (fun b => 2 ^ 2 ∣ b) := by
        ext b; simp only [show (4 : ℕ) = 2 ^ 2 by norm_num]
      have hsub24 : B₀.filter (fun b => 4 ∣ b) ⊆ B₀.filter (fun b => 2 ∣ b) := by
        intro b hb
        rw [Finset.mem_filter] at hb ⊢
        exact ⟨hb.1, dvd_trans (by norm_num) hb.2⟩
      have hle1 := Finset.card_le_card hsub24
      rw [h2eq, h4eq] at hle1
      have hcard : (B₀.filter (fun b => 2 ^ 2 ∣ b)).card = (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by
        omega
      apply Finset.eq_of_subset_of_card_le
      · rw [← h4eq, ← h2eq] at hcard
        exact (Finset.eq_of_subset_of_card_le hsub24 (le_of_eq hcard.symm)).symm.subset
      · rw [h2eq, h4eq]; omega
    have hI2_card : 6 ≤ (I.filter (fun b => 2 ∣ b)).card := by
      have h := card_multiples_Icc_ge x 12 2 (by norm_num)
      rw [show (12 / 2 : ℕ) = 6 by norm_num] at h; exact h
    have hJ2_card : 3 ≤ ((I \ B₀).filter (fun b => 2 ∣ b)).card := by
      have hsub : I.filter (fun b => 2 ∣ b) ⊆
          (I \ B₀).filter (fun b => 2 ∣ b) ∪ B₀.filter (fun b => 2 ∣ b) := by
        intro b hb
        rw [Finset.mem_filter] at hb
        by_cases hbB₀ : b ∈ B₀
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbB₀, hb.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩, hb.2⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((I \ B₀).filter (fun b => 2 ∣ b)) (B₀.filter (fun b => 2 ∣ b))
      have h2eq : B₀.filter (fun b => 2 ∣ b) = B₀.filter (fun b => 2 ^ 1 ∣ b) := by
        ext b; simp only [pow_one]
      rw [h2eq] at h1 h2
      omega
    by_cases h3R : 3 ∣ R
    · have hR_eq12 : R = 12 := by
        have h12_dvd_R : 12 ∣ R := (by norm_num : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4R h3R
        exact Nat.dvd_antisymm hR12 h12_dvd_R
      have hI6_2 : 2 ≤ (I.filter (fun b => 6 ∣ b)).card := by
        have h := card_multiples_Icc_ge x 12 6 (by norm_num)
        norm_num at h; exact h
      have hI12_1 : (I.filter (fun b => 12 ∣ b)).card ≤ 1 := card_multiples_M_le_one x 12 (by norm_num)
      have hnot_sub12 : ¬ (I.filter (fun b => 6 ∣ b) ⊆ I.filter (fun b => 12 ∣ b)) := by
        intro hsub
        have := Finset.card_le_card hsub
        omega
      obtain ⟨w₁, hw₁_6, hw₁_n12⟩ := Finset.not_subset.mp hnot_sub12
      rw [Finset.mem_filter] at hw₁_6
      have hw₁_I : w₁ ∈ I := hw₁_6.1
      have hw₁_dvd6 : 6 ∣ w₁ := hw₁_6.2
      have hw₁_not12 : ¬ (12 ∣ w₁) := fun h => hw₁_n12 (Finset.mem_filter.mpr ⟨hw₁_I, h⟩)
      have hw₁_not4 : ¬ (4 ∣ w₁) := by
        intro h4
        have h3 : 3 ∣ w₁ := dvd_trans (by norm_num) hw₁_dvd6
        exact hw₁_not12 ((by norm_num : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4 h3)
      have hw₁_notB₀ : w₁ ∉ B₀ := by
        intro hb
        have h2w₁ : 2 ∣ w₁ := dvd_trans (by norm_num) hw₁_dvd6
        have hmem : w₁ ∈ B₀.filter (fun b => 2 ∣ b) := Finset.mem_filter.mpr ⟨hb, h2w₁⟩
        rw [hB₀_2_eq_4, Finset.mem_filter] at hmem
        exact hw₁_not4 hmem.2
      have hJ2_erase : 2 ≤ (((I \ B₀).filter (fun b => 2 ∣ b)).erase w₁).card := by
        have hmem : w₁ ∈ (I \ B₀).filter (fun b => 2 ∣ b) :=
          Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hw₁_I, hw₁_notB₀⟩, dvd_trans (by norm_num) hw₁_dvd6⟩
        rw [Finset.card_erase_of_mem hmem]
        omega
      have hne_j : (((I \ B₀).filter (fun b => 2 ∣ b)).erase w₁).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨w₂, hw₂_er⟩ := hne_j
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_sdiff] at hw₂_er
      rcases hw₂_er with ⟨hw₂_ne, ⟨hw₂_I, hw₂_notB₀⟩, h2_w₂⟩
      have hRw : R ∣ w₁ * w₂ := by rw [hR_eq12]; exact mul_dvd_mul hw₁_dvd6 h2_w₂
      exact two_slots_of_two_dvd hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne.symm hRw hR_pos.ne'
    · have hR_eq4 : R = 4 := by
        obtain ⟨k, hk⟩ := h4R
        have hk3 : k ∣ 3 := by
          obtain ⟨q, hq⟩ := hR12
          have h12 : 12 = 4 * 3 := by norm_num
          rw [h12, hk, mul_assoc] at hq
          exact ⟨q, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) hq⟩
        have hk_le3 : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
        have hk_pos : 0 < k :=
          Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hR_pos.ne' hk
        have hnk3 : k ≠ 3 := fun h => h3R (by rw [hk, h]; norm_num)
        have hnk2 : k ≠ 2 := by
          intro h; rw [h] at hk3; norm_num at hk3
        have hk1 : k = 1 := by omega
        rw [hk, hk1, mul_one]
      have hJ2_gt1 : 1 < ((I \ B₀).filter (fun b => 2 ∣ b)).card := by omega
      obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hJ2_gt1
      rw [Finset.mem_filter, Finset.mem_sdiff] at hw₁ hw₂
      have hRw : R ∣ w₁ * w₂ := by rw [hR_eq4]; exact mul_dvd_mul hw₁.2 hw₂.2
      exact two_slots_of_two_dvd hw₁.1.1 hw₂.1.1 hw₁.1.2 hw₂.1.2 hne hRw hR_pos.ne'
  · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub4
    rw [Finset.mem_filter] at hw₁_flt
    by_cases h3R : 3 ∣ R
    · have hR_eq12 : R = 12 := Nat.dvd_antisymm hR12
        ((by norm_num : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4R h3R)
      have he3 : 1 ≤ R.factorization 3 :=
        ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hR_pos.ne').mp
          (by simpa only [pow_one] using h3R)
      obtain ⟨w₂, hw₂_I, hw₂_notB₀, h3_w₂⟩ := exists_prime_multiple_avoiding_of_deficit_pos
        hA_card hA_pos hA_le hAgcd hB₀_I (p := 3) (by norm_num) (by rw [← hR_fac 3 (by norm_num)]; exact he3)
      exact two_slots_of_coprime_dvd (R := R) (d₁ := 4) (d₂ := 3)
        hR_eq12 (by norm_num) (by norm_num) (by norm_num)
        hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₁_flt.2 h3_w₂
    · have hR_eq4 : R = 4 := by
        obtain ⟨k, hk⟩ := h4R
        have hk3 : k ∣ 3 := by
          obtain ⟨q, hq⟩ := hR12
          have h12 : 12 = 4 * 3 := by norm_num
          rw [h12, hk, mul_assoc] at hq
          exact ⟨q, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) hq⟩
        have hk_le3 : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
        have hk_pos : 0 < k :=
          Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hR_pos.ne' hk
        have hnk3 : k ≠ 3 := fun h => h3R (by rw [hk, h]; norm_num)
        have hnk2 : k ≠ 2 := fun h => by rw [h] at hk3; norm_num at hk3
        have hk1 : k = 1 := by omega
        rw [hk, hk1, mul_one]
      exact two_slots_of_one_dvd hw₁_flt.1 hw₁_notB₀ (hR_eq4 ▸ hw₁_flt.2) hR_pos.ne'

/-! ## Part 4: Master `R ∣ M` Two-Slot Residual Theorem (`exists_two_slots_for_R_dvd_M`) -/

private lemma exists_two_slots_M_eq_c_mul_pow {A B₀ : Finset ℕ} {x M R p t c : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM9 : 9 ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 6)
    (hR_pos : 0 < R) (hRM : R ∣ M) (hpt_R : p ^ t ∣ R) (ht_exact : R.factorization p = t)
    (hR_fac : ∀ q : ℕ, q.Prime →
      R.factorization q = (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q))
    (hp : p.Prime) (ht1 : 1 ≤ t) (hM_eq : M = c * p ^ t) (hc1 : 1 ≤ c) (hc6 : c ≤ 6)
    (hsub_q : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ q : ℕ, q.Prime → R.factorization q ≤ ∑ b ∈ B₁, b.factorization q := by
  have hdef_le := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I hp ht1 hsub_q
  have hc_div : M / p ^ t = c := by
    rw [hM_eq, Nat.mul_div_cancel c (pow_pos hp.pos t)]
  have ht_fac : t ≤ R.factorization p := (hp.pow_dvd_iff_le_factorization hR_pos.ne').mp hpt_R
  have hR_fac_p := hR_fac p hp
  rw [hc_div] at hdef_le
  have ht_ineq : t ≤ (5 - c) * (t - 1) := by omega
  have ht2 : 2 ≤ t := by
    by_contra hlt
    have ht_eq1 : t = 1 := by omega
    rw [ht_eq1] at ht_ineq
    simp at ht_ineq
  have hc3 : c ≤ 3 := by
    by_contra hgt
    have hc4 : 4 ≤ c := by omega
    have h5c : 5 - c ≤ 1 := by omega
    have : (5 - c) * (t - 1) ≤ 1 * (t - 1) := Nat.mul_le_mul_right (t - 1) h5c
    omega
  -- Helper: picking two distinct multiples of `d` in `I \ B₀` when `8 * d ≤ M`.
  have two_distinct_mults : ∀ (d : ℕ), 0 < d → 8 * d ≤ M → R ∣ d * d →
      ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
        ∀ q : ℕ, q.Prime → R.factorization q ≤ ∑ b ∈ B₁, b.factorization q := by
    intro d hd_pos h8d hRd2
    have hbd1 : (B₀.card + 1) * d ≤ M :=
      le_trans (Nat.mul_le_mul_right d (by omega : B₀.card + 1 ≤ 8)) h8d
    obtain ⟨w₁, hw₁_I, hw₁_notB₀, hdw₁⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d B₀ hd_pos hbd1
    have hcard_ins : (insert w₁ B₀).card + 1 ≤ 8 := by
      have h1 := Finset.card_insert_le w₁ B₀; omega
    obtain ⟨w₂, hw₂_I, hw₂_notIns, hdw₂⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d (insert w₁ B₀) hd_pos
        (le_trans (Nat.mul_le_mul_right d hcard_ins) h8d)
    have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
    have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
    exact two_slots_of_two_dvd hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
      (dvd_trans hRd2 (mul_dvd_mul hdw₁ hdw₂)) hR_pos.ne'
  -- Helper: picking `d₁ ∣ w₁` avoiding `B₀` (`7 * d₁ ≤ M`) and `d₂ ∣ w₂` avoiding `insert w₁ B₀` (`8 * d₂ ≤ M`).
  have two_split_mults : ∀ (d₁ d₂ : ℕ), 0 < d₁ → 0 < d₂ → 7 * d₁ ≤ M → 8 * d₂ ≤ M → R ∣ d₁ * d₂ →
      ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
        ∀ q : ℕ, q.Prime → R.factorization q ≤ ∑ b ∈ B₁, b.factorization q := by
    intro d₁ d₂ hd₁_pos hd₂_pos h7d₁ h8d₂ hRd12
    have hbd1 : (B₀.card + 1) * d₁ ≤ M :=
      le_trans (Nat.mul_le_mul_right d₁ (by omega : B₀.card + 1 ≤ 7)) h7d₁
    obtain ⟨w₁, hw₁_I, hw₁_notB₀, hd₁_w₁⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d₁ B₀ hd₁_pos hbd1
    have hcard_ins : (insert w₁ B₀).card + 1 ≤ 8 := by
      have h1 := Finset.card_insert_le w₁ B₀; omega
    obtain ⟨w₂, hw₂_I, hw₂_notIns, hd₂_w₂⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d₂ (insert w₁ B₀) hd₂_pos
        (le_trans (Nat.mul_le_mul_right d₂ hcard_ins) h8d₂)
    have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
    have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
    exact two_slots_of_two_dvd hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
      (dvd_trans hRd12 (mul_dvd_mul hd₁_w₁ hd₂_w₂)) hR_pos.ne'
  by_cases hc1_eq : c = 1
  · -- Subcase `c = 1`: `M = p ^ t`, `R ∣ M` so `R ∣ p ^ t`, hence `R = p ^ t`.
    have hM_pt : M = p ^ t := by rw [hM_eq, hc1_eq, one_mul]
    have hR_pt : R = p ^ t := Nat.dvd_antisymm (hM_pt ▸ hRM) hpt_R
    by_cases ht2_eq : t = 2
    · -- `t = 2`, `M = p ^ 2 ≥ 9`, so `p ≥ 3`.
      have hM_p2 : M = p ^ 2 := by rw [hM_pt, ht2_eq]
      let J := (consecInterval x M \ B₀).filter (fun b => p ∣ b)
      rcases le_or_gt 2 J.card with hJ2 | hJ1
      · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hJ2
        rw [Finset.mem_filter, Finset.mem_sdiff] at hw₁ hw₂
        have hRw : R ∣ w₁ * w₂ := by rw [hR_pt, ht2_eq, pow_two]; exact mul_dvd_mul hw₁.2 hw₂.2
        exact two_slots_of_two_dvd hw₁.1.1 hw₂.1.1 hw₁.1.2 hw₂.1.2 hne hRw hR_pos.ne'
      · -- `J.card ≤ 1` (`B₁ = J`, `card ≤ 1`), and `B₀ ∪ J` contains ALL multiples of `p` in `I`!
        -- Actually if `J.card = 0`, `t = 0` via `t = 1` layer cake; if `J.card = 1`, `B₀ ∪ J` has all multiples
        -- of `p` in `I`, Wait: `I.filter (p^2 ∣ ·) ⊆ B₀ ⊆ B₀ ∪ J`, and `I.filter (p ∣ ·) ⊆ B₀ ∪ J`,
        -- so `∑_A v_p ≤ ∑_{B₀ ∪ J} v_p = ∑_{B₀} v_p + ∑_J v_p`!
        have hJ_subI : J ⊆ consecInterval x M :=
          Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset
        have hJ_disj : Disjoint B₀ J :=
          Finset.disjoint_left.mpr fun _ hb hj => (Finset.mem_sdiff.mp (Finset.filter_subset _ _ hj)).2 hb
        have hsub_BJ : (consecInterval x M).filter (fun b => p ∣ b) ⊆ B₀ ∪ J := by
          intro b hb
          rw [Finset.mem_filter] at hb
          by_cases hbB₀ : b ∈ B₀
          · exact Finset.mem_union_left _ hbB₀
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩, hb.2⟩)
        have hBJ_I : B₀ ∪ J ⊆ consecInterval x M := Finset.union_subset hB₀_I hJ_subI
        have hdef_BJ := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hBJ_I hp
          (le_refl 1) (by simpa only [pow_one] using hsub_BJ)
        rw [Finset.sum_union hJ_disj] at hdef_BJ
        refine ⟨J, hJ_subI, hJ_disj, by omega, ?_⟩
        intro q hq
        by_cases hqp : q = p
        · subst hqp
          have h1 : R.factorization q = (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q) :=
            hR_fac q hq
          omega
        · have hnd : ¬ (q ∣ R) := by
            rw [hR_pt]
            intro hd
            exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd))
          rw [Nat.factorization_eq_zero_of_not_dvd hnd]
          exact Nat.zero_le _
    · -- `t ≥ 3`, `M = p ^ t`
      have ht3 : 3 ≤ t := by omega
      by_cases hp2 : p = 2
      · -- `p = 2, M = 2 ^ t ≥ 9`, so `t ≥ 4`.
        have ht4 : 4 ≤ t := by
          by_contra hlt4
          have ht3_eq : t = 3 := by omega
          rw [hM_pt, hp2, ht3_eq] at hM9
          norm_num at hM9
        rcases le_or_gt 6 t with ht6 | ht_lt6
        · -- `t ≥ 6`: `2 * (t - 3) ≥ t`, `M / 2^(t - 3) = 8`.
          have h8d : 8 * 2 ^ (t - 3) ≤ M := by
            rw [hM_pt, hp2]
            refine le_of_eq ?_
            calc 8 * 2 ^ (t - 3) = 2 ^ 3 * 2 ^ (t - 3) := by norm_num
              _ = 2 ^ (3 + (t - 3)) := (pow_add 2 3 (t - 3)).symm
              _ = 2 ^ t := by congr 1; omega
          have hRd2 : R ∣ 2 ^ (t - 3) * 2 ^ (t - 3) := by
            rw [hR_pt, hp2, ← pow_add]
            exact Nat.pow_dvd_pow 2 (by omega)
          exact two_distinct_mults (2 ^ (t - 3)) (pow_pos (by norm_num) _) h8d hRd2
        · have ht_cases : t = 4 ∨ t = 5 := by omega
          rcases ht_cases with ht4_eq | ht5_eq
          · -- `t = 4, M = 16, R = 16`.
            have hM16 : M = 16 := by rw [hM_pt, hp2, ht4_eq]; norm_num
            have hR16 : R = 16 := by rw [hR_pt, hp2, ht4_eq]; norm_num
            by_cases hsub8 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀
            · let J4 := (consecInterval x M \ B₀).filter (fun b => 4 ∣ b)
              rcases le_or_gt 2 J4.card with hJ4_2 | hJ4_1
              · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := Finset.one_lt_card.mp hJ4_2
                rw [Finset.mem_filter, Finset.mem_sdiff] at hw₁ hw₂
                have hRw : R ∣ w₁ * w₂ := by rw [hR16]; exact mul_dvd_mul hw₁.2 hw₂.2
                exact two_slots_of_two_dvd hw₁.1.1 hw₂.1.1 hw₁.1.2 hw₂.1.2 hne hRw hR_pos.ne'
              · have hI4_4 : 4 ≤ ((consecInterval x M).filter (fun b => 4 ∣ b)).card := by
                  have h := card_multiples_Icc_ge x M 4 (by norm_num)
                  rw [show M / 4 = 4 by rw [hM16]] at h; exact h
                have hB₀_4 : 3 ≤ (B₀.filter (fun b => 2 ^ 2 ∣ b)).card := by
                  have hsub_union : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆
                      B₀.filter (fun b => 4 ∣ b) ∪ J4 := by
                    intro b hb
                    rw [Finset.mem_filter] at hb
                    by_cases hbB₀ : b ∈ B₀
                    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbB₀, hb.2⟩)
                    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩, hb.2⟩)
                  have hle1 := Finset.card_le_card hsub_union
                  have hle2 := Finset.card_union_le (B₀.filter (fun b => 4 ∣ b)) J4
                  have heq4 : B₀.filter (fun b => 4 ∣ b) = B₀.filter (fun b => 2 ^ 2 ∣ b) := by
                    ext b; simp [show (4 : ℕ) = 2 ^ 2 by norm_num]
                  rw [heq4] at hle1 hle2
                  omega
                have hB₀_2 : 3 ≤ (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by
                  have hsub24 : B₀.filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 1 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hb.1, dvd_trans (by norm_num) hb.2⟩
                  exact le_trans hB₀_4 (Finset.card_le_card hsub24)
                have hB₀_8 : 2 ≤ (B₀.filter (fun b => 2 ^ 3 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 3 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hsub8 (Finset.mem_filter.mpr hb), by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 8 (by norm_num)
                  rw [show M / 8 = 2 by rw [hM16]] at h2
                  exact le_trans h2 (Finset.card_le_card h1)
                have hB₀_16 : 1 ≤ (B₀.filter (fun b => 2 ^ 4 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 16 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 4 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hsub8 (Finset.mem_filter.mpr ⟨hb.1, dvd_trans (by norm_num) hb.2⟩),
                      by simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 16 (by norm_num)
                  rw [show M / 16 = 1 by rw [hM16]] at h2
                  exact le_trans h2 (Finset.card_le_card h1)
                have hB₀_sum9 : 9 ≤ ∑ b ∈ B₀, b.factorization 2 := by
                  have h1 := sum_card_Icc_le_sum_factorization (K := 4) hB₀_I (by norm_num : Nat.Prime 2)
                  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
                  rw [hIcc4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                      Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                  omega
                have hA_sum12 : ∑ a ∈ A, a.factorization 2 ≤ 12 := by
                  have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 2)
                  have hc1 : (A.filter (fun a => 2 ^ 1 ∣ a)).card ≤ 5 :=
                    (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 1) (by norm_num) (by omega)).1
                  have hc2 : (A.filter (fun a => 2 ^ 2 ∣ a)).card ≤ 4 := by
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 2) (by norm_num) (by omega)).2
                    rw [show M / 2 ^ 2 = 4 by rw [hM16]; norm_num] at h; exact h
                  have hc3 : (A.filter (fun a => 2 ^ 3 ∣ a)).card ≤ 2 := by
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 3) (by norm_num) (by omega)).2
                    rw [show M / 2 ^ 3 = 2 by rw [hM16]; norm_num] at h; exact h
                  have hc4 : (A.filter (fun a => 2 ^ 4 ∣ a)).card ≤ 1 := by
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 4) (by norm_num) (by omega)).2
                    rw [show M / 2 ^ 4 = 1 by rw [hM16]; norm_num] at h; exact h
                  have hcz : ∀ j ∈ Finset.Icc 5 16, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 := by
                    intro j hj; rw [Finset.mem_Icc] at hj
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := j) (by norm_num) (by omega)).2
                    have hpow : 32 ≤ 2 ^ j :=
                      le_trans (by norm_num : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) hj.1)
                    have hdiv0 : M / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                    omega
                  have hIcc16 : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (insert 4 (Finset.Icc 5 16)))) := by
                    rw [hM16]; ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                  rw [hIcc16, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                      Finset.sum_insert (by decide), Finset.sum_insert (by decide)] at h1
                  have hsum0 : ∑ j ∈ Finset.Icc 5 16, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 :=
                    Finset.sum_eq_zero hcz
                  omega
                have hfac2 := hR_fac 2 (by norm_num)
                have ht_fac2 : R.factorization 2 = 4 := by
                  rw [hR16, show (16 : ℕ) = 2 ^ 4 by norm_num,
                      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
                omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub8
              rw [Finset.mem_filter] at hw₁_flt
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h2_w₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M 2 (insert w₁ B₀) (by norm_num)
                  (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM16]; omega)
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              have hRw : R ∣ w₁ * w₂ := by rw [hR16]; exact mul_dvd_mul hw₁_flt.2 h2_w₂
              exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'
          · -- `t = 5, M = 32, R = 32`.
            have hM32 : M = 32 := by rw [hM_pt, hp2, ht5_eq]; norm_num
            have hR32 : R = 32 := by rw [hR_pt, hp2, ht5_eq]; norm_num
            by_cases hsub8 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀
            · have h8_pow : (8 : ℕ) = 2 ^ 3 := by norm_num
              have hsub8' : (consecInterval x M).filter (fun b => 2 ^ 3 ∣ b) ⊆ B₀ := by
                simpa [h8_pow] using hsub8
              have hdef8 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I
                (by norm_num : Nat.Prime 2) (by norm_num : 1 ≤ 3) hsub8'
              have hdiv8 : M / 2 ^ 3 = 4 := by rw [hM32]; norm_num
              rw [hdiv8] at hdef8
              have hfac2 := hR_fac 2 (by norm_num)
              have ht_fac2 : R.factorization 2 = 5 := by
                rw [hR32, show (32 : ℕ) = 2 ^ 5 by norm_num,
                    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
              omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub8
              rw [Finset.mem_filter] at hw₁_flt
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h4_w₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M 4 (insert w₁ B₀) (by norm_num)
                  (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM32]; omega)
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              have hRw : R ∣ w₁ * w₂ := by rw [hR32]; exact mul_dvd_mul hw₁_flt.2 h4_w₂
              exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'
      · -- `p ≥ 3, t ≥ 3, M = p ^ t, R = p ^ t`
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        by_cases ht3_eq : t = 3
        · by_cases hsub_p2 : (consecInterval x M).filter (fun b => p ^ 2 ∣ b) ⊆ B₀
          · have hdef_p2 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I hp
              (by norm_num : 1 ≤ 2) hsub_p2
            have hdiv_p2 : M / p ^ 2 = p := by
              rw [hM_pt, ht3_eq, pow_succ p 2, Nat.mul_div_right p (pow_pos hp.pos 2)]
            rw [hdiv_p2] at hdef_p2
            have ht_fac_p : R.factorization p = 3 := by
              rw [hR_pt, ht3_eq, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
            have hfac_p := hR_fac p hp
            omega
          · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub_p2
            rw [Finset.mem_filter] at hw₁_flt
            have hp2_ge9 : 9 ≤ p ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hp3 2)
            have h8p : 8 * p ≤ M := by
              rw [hM_pt, ht3_eq, pow_succ p 2]
              exact Nat.mul_le_mul_right p (by omega)
            have hbd2 : ((insert w₁ B₀).card + 1) * p ≤ M :=
              le_trans (Nat.mul_le_mul_right p (by have h1 := Finset.card_insert_le w₁ B₀; omega)) h8p
            obtain ⟨w₂, hw₂_I, hw₂_notIns, hp_w₂⟩ :=
              exists_avoiding_multiple_in_consecInterval x M p (insert w₁ B₀) hp.pos hbd2
            have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
            have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
            have hRw : R ∣ w₁ * w₂ := by
              rw [hR_pt, ht3_eq, show p ^ 3 = p ^ 2 * p by ring]
              exact mul_dvd_mul hw₁_flt.2 hp_w₂
            exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'
        · -- `t ≥ 4`: `M / p^(t - 2) = p^2 ≥ 9 ≥ 8`, `2 * (t - 2) ≥ t`.
          have ht4 : 4 ≤ t := by omega
          have hp2_ge9 : 9 ≤ p ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hp3 2)
          have h8d : 8 * p ^ (t - 2) ≤ M := by
            rw [hM_pt]
            have hpow : p ^ t = p ^ 2 * p ^ (t - 2) := by
              rw [← pow_add]; congr 1; omega
            rw [hpow]
            exact Nat.mul_le_mul_right _ (by omega)
          have hRd2 : R ∣ p ^ (t - 2) * p ^ (t - 2) := by
            rw [hR_pt, ← pow_add]
            exact Nat.pow_dvd_pow p (by omega)
          exact two_distinct_mults (p ^ (t - 2)) (pow_pos hp.pos _) h8d hRd2
  · -- Subcase `c ∈ {2, 3}`, `M = c * p ^ t`, `R ∣ c * p ^ t`, `t ≥ 2`.
    have hc23 : c = 2 ∨ c = 3 := by omega
    have hRM_cpt : R ∣ c * p ^ t := by rwa [← hM_eq]
    by_cases hp7 : 7 ≤ p
    · -- `p ≥ 7`, `t ≥ 2`: `d₁ = c * p^(t - 1)` (`M / d₁ = p ≥ 7`), `d₂ = p^(t - 1)` (`M / d₂ = c * p ≥ 14 ≥ 8`),
      -- and `2 * (t - 1) ≥ t`, so `M = c * p ^ t ∣ d₁ * d₂`!
      have h7d₁ : 7 * (c * p ^ (t - 1)) ≤ M := by
        rw [hM_eq]
        have hpow : p ^ t = p * p ^ (t - 1) := by
          calc p ^ t = p ^ (1 + (t - 1)) := by congr 1; omega
            _ = p ^ 1 * p ^ (t - 1) := pow_add p 1 (t - 1)
            _ = p * p ^ (t - 1) := by rw [pow_one]
        rw [hpow]
        calc 7 * (c * p ^ (t - 1)) = c * (7 * p ^ (t - 1)) := by ring
          _ ≤ c * (p * p ^ (t - 1)) := Nat.mul_le_mul_left c (Nat.mul_le_mul_right _ hp7)
      have h8d₂ : 8 * p ^ (t - 1) ≤ M := by
        rw [hM_eq]
        have hpow : p ^ t = p * p ^ (t - 1) := by
          calc p ^ t = p ^ (1 + (t - 1)) := by congr 1; omega
            _ = p ^ 1 * p ^ (t - 1) := pow_add p 1 (t - 1)
            _ = p * p ^ (t - 1) := by rw [pow_one]
        rw [hpow]
        have h8_cp : 8 ≤ c * p := by
          have : 2 * 7 ≤ c * p := Nat.mul_le_mul (by omega) hp7
          omega
        calc 8 * p ^ (t - 1) ≤ (c * p) * p ^ (t - 1) := Nat.mul_le_mul_right _ h8_cp
          _ = c * (p * p ^ (t - 1)) := by ring
      have hRd12 : R ∣ (c * p ^ (t - 1)) * p ^ (t - 1) := by
        apply dvd_trans hRM_cpt
        have hpow : p ^ t ∣ p ^ (t - 1) * p ^ (t - 1) := by
          rw [← pow_add]; exact Nat.pow_dvd_pow p (by omega)
        calc c * p ^ t ∣ c * (p ^ (t - 1) * p ^ (t - 1)) := mul_dvd_mul_left c hpow
          _ = (c * p ^ (t - 1)) * p ^ (t - 1) := by ring
      exact two_split_mults (c * p ^ (t - 1)) (p ^ (t - 1))
        (mul_pos (by omega) (pow_pos hp.pos _)) (pow_pos hp.pos _) h7d₁ h8d₂ hRd12
    · -- `p ∈ {2, 3, 5}`!
      have hp_lt7 : p < 7 := by omega
      have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 := by
        have hp2 := hp.two_le
        have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
        have h6 : p ≠ 6 := fun h => by rw [h] at hp; norm_num at hp
        omega
      rcases hp_cases with rfl | rfl | rfl
      · -- `p = 2`: either `c = 2` (`M = 2^(t+1), R | 2^(t+1)`) or `c = 3` (`M = 3 * 2^t`).
        rcases hc23 with hc2 | hc3
        · have hM_2t1 : M = 2 ^ (t + 1) := by rw [hM_eq, hc2, pow_succ']
          have hR_2t : R = 2 ^ t := by
            obtain ⟨k, hk⟩ := hpt_R
            have hk_dvd : k ∣ 2 := by
              have hM_div := hRM_cpt
              rw [hc2, hk] at hM_div
              obtain ⟨q, hq⟩ := hM_div
              have hpow_pos : 0 < 2 ^ t := pow_pos (by norm_num) t
              exact ⟨q, Nat.eq_of_mul_eq_mul_left hpow_pos (by linarith)⟩
            have hk_not2 : ¬ (2 ∣ k) := by
              intro h2k
              have h2t1 : 2 ^ (t + 1) ∣ R := by
                rw [hk, pow_succ]; exact mul_dvd_mul_left (2 ^ t) h2k
              have ht1_le : t + 1 ≤ R.factorization 2 :=
                ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hR_pos.ne').mp h2t1
              omega
            have hk_pos : 0 < k :=
              Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hR_pos.ne' hk
            have hk_le2 : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk_dvd
            have hk1 : k = 1 := by omega
            rw [hk, hk1, mul_one]
          have ht3 : 3 ≤ t := by
            by_contra hlt3
            have ht2_eq : t = 2 := by omega
            rw [hM_2t1, ht2_eq] at hM9
            norm_num at hM9
          rcases le_or_gt 4 t with ht4 | ht3_eq
          · have h8d : 8 * 2 ^ (t - 2) ≤ M := by
              rw [hM_2t1]
              refine le_of_eq ?_
              calc 8 * 2 ^ (t - 2) = 2 ^ 3 * 2 ^ (t - 2) := by norm_num
                _ = 2 ^ (t + 1) := by rw [← pow_add]; congr 1; omega
            have hRd2 : R ∣ 2 ^ (t - 2) * 2 ^ (t - 2) := by
              rw [hR_2t, ← pow_add]; exact Nat.pow_dvd_pow 2 (by omega)
            exact two_distinct_mults (2 ^ (t - 2)) (pow_pos (by norm_num) _) h8d hRd2
          · have ht3_eq' : t = 3 := by omega
            have hM16 : M = 16 := by rw [hM_2t1, ht3_eq']; norm_num
            have hR8 : R = 8 := by rw [hR_2t, ht3_eq']; norm_num
            by_cases hsub4 : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆ B₀
            · have hsub4' : (consecInterval x M).filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀ := by
                simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hsub4
              have hdef4 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I
                (by norm_num : Nat.Prime 2) (by norm_num : 1 ≤ 2) hsub4'
              have hdiv4 : M / 2 ^ 2 = 4 := by rw [hM16]; norm_num
              rw [hdiv4] at hdef4
              omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub4
              rw [Finset.mem_filter] at hw₁_flt
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h2_w₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M 2 (insert w₁ B₀) (by norm_num)
                  (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM16]; omega)
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              have hRw : R ∣ w₁ * w₂ := by rw [hR8]; exact mul_dvd_mul hw₁_flt.2 h2_w₂
              exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'
        · -- `p = 2, c = 3, M = 3 * 2^t, R ∣ 3 * 2^t, t ≥ 2`
          rcases le_or_gt 6 t with ht6 | ht_lt6
          · have h7d₁ : 7 * (3 * 2 ^ (t - 3)) ≤ M := by
              rw [hM_eq, hc3]
              have hpow : 2 ^ t = 8 * 2 ^ (t - 3) := by
                calc 2 ^ t = 2 ^ 3 * 2 ^ (t - 3) := by rw [← pow_add]; congr 1; omega
                  _ = 8 * 2 ^ (t - 3) := by norm_num
              rw [hpow]; ring_nf; omega
            have h8d₂ : 8 * 2 ^ (t - 3) ≤ M := by
              rw [hM_eq, hc3]
              have hpow : 2 ^ t = 8 * 2 ^ (t - 3) := by
                calc 2 ^ t = 2 ^ 3 * 2 ^ (t - 3) := by rw [← pow_add]; congr 1; omega
                  _ = 8 * 2 ^ (t - 3) := by norm_num
              rw [hpow]; ring_nf; omega
            have hRd12 : R ∣ (3 * 2 ^ (t - 3)) * 2 ^ (t - 3) := by
              apply dvd_trans hRM_cpt
              rw [hc3]
              have hpow : 2 ^ t ∣ 2 ^ (t - 3) * 2 ^ (t - 3) := by
                rw [← pow_add]; exact Nat.pow_dvd_pow 2 (by omega)
              calc 3 * 2 ^ t ∣ 3 * (2 ^ (t - 3) * 2 ^ (t - 3)) := mul_dvd_mul_left 3 hpow
                _ = (3 * 2 ^ (t - 3)) * 2 ^ (t - 3) := by ring
            exact two_split_mults (3 * 2 ^ (t - 3)) (2 ^ (t - 3))
              (mul_pos (by norm_num) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
              h7d₁ h8d₂ hRd12
          · have ht_cases : t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
            rcases ht_cases with rfl | rfl | rfl | rfl
            · have hM12 : M = 12 := by rw [hM_eq, hc3]; norm_num
              have hR12 : R ∣ 12 := by rw [← hM12]; exact hRM
              have h4R : 4 ∣ R := by norm_num at hpt_R; exact hpt_R
              exact exists_two_slots_M12_R4_or_R12 hA_card hA_pos hA_le hAgcd hB₀_I
                hM12 hR_pos hR12 h4R hR_fac
            · have hM24 : M = 24 := by rw [hM_eq, hc3]; norm_num
              have hR24 : R ∣ 24 := by rw [← hM24]; exact hRM
              by_cases hsub4 : (consecInterval x M).filter (fun b => 4 ∣ b) ⊆ B₀
              · have hsub4' : (consecInterval x M).filter (fun b => 2 ^ 2 ∣ b) ⊆ B₀ := by
                  simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hsub4
                have hdef4 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I
                  (by norm_num : Nat.Prime 2) (by norm_num : 1 ≤ 2) hsub4'
                have hdiv4 : M / 2 ^ 2 = 6 := by rw [hM24]; norm_num
                rw [hdiv4] at hdef4
                omega
              · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub4
                rw [Finset.mem_filter] at hw₁_flt
                by_cases hsub6 : (consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀
                · have hI24_1 : ((consecInterval x M).filter (fun b => 24 ∣ b)).card ≤ 1 := by
                    rw [hM24]; exact card_multiples_M_le_one x 24 (by norm_num)
                  have hB₀_6 : 4 ≤ (B₀.filter (fun b => 6 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀.filter (fun b => 6 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hsub6 (Finset.mem_filter.mpr hb), hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 6 (by norm_num)
                    rw [show M / 6 = 4 by rw [hM24]] at h2
                    exact le_trans h2 (Finset.card_le_card h1)
                  have hB₀_8 : 3 ≤ (B₀.filter (fun b => 2 ^ 3 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 3 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩),
                        by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 8 (by norm_num)
                    rw [show M / 8 = 3 by rw [hM24]] at h2
                    exact le_trans h2 (Finset.card_le_card h1)
                  have h6_8_24 : B₀.filter (fun b => 6 ∣ b) ∩ B₀.filter (fun b => 2 ^ 3 ∣ b) ⊆
                      (consecInterval x M).filter (fun b => 24 ∣ b) := by
                    intro b hb
                    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
                    rw [Finset.mem_filter]
                    have hlcm : Nat.lcm 6 8 ∣ b := Nat.lcm_dvd hb.1.2 (by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2.2)
                    have h24eq : (24 : ℕ) = Nat.lcm 6 8 := by decide
                    exact ⟨hB₀_I hb.1.1, h24eq ▸ hlcm⟩
                  have hB₀_2 : 6 ≤ (B₀.filter (fun b => 2 ^ 1 ∣ b)).card := by
                    have hsub_u : B₀.filter (fun b => 6 ∣ b) ∪ B₀.filter (fun b => 2 ^ 3 ∣ b) ⊆
                        B₀.filter (fun b => 2 ^ 1 ∣ b) := by
                      intro b hb; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hb
                      rw [Finset.mem_filter]
                      rcases hb with hb6 | hb8
                      · exact ⟨hb6.1, dvd_trans (by norm_num) hb6.2⟩
                      · exact ⟨hb8.1, dvd_trans (by norm_num) hb8.2⟩
                    have h1 := Finset.card_union_add_card_inter
                      (B₀.filter (fun b => 6 ∣ b)) (B₀.filter (fun b => 2 ^ 3 ∣ b))
                    have h2 : (B₀.filter (fun b => 6 ∣ b) ∩ B₀.filter (fun b => 2 ^ 3 ∣ b)).card ≤ 1 :=
                      le_trans (Finset.card_le_card h6_8_24) hI24_1
                    exact le_trans (by omega) (Finset.card_le_card hsub_u)
                  have hB₀_12 : 2 ≤ (B₀.filter (fun b => 12 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 12 ∣ b) ⊆ B₀.filter (fun b => 12 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub6 (Finset.mem_filter.mpr ⟨hb.1, dvd_trans (by norm_num) hb.2⟩), hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 12 (by norm_num)
                    rw [show M / 12 = 2 by rw [hM24]] at h2
                    exact le_trans h2 (Finset.card_le_card h1)
                  have h12_8_24 : B₀.filter (fun b => 12 ∣ b) ∩ B₀.filter (fun b => 2 ^ 3 ∣ b) ⊆
                      (consecInterval x M).filter (fun b => 24 ∣ b) := by
                    intro b hb
                    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
                    rw [Finset.mem_filter]
                    have hlcm : Nat.lcm 12 8 ∣ b := Nat.lcm_dvd hb.1.2 (by simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hb.2.2)
                    have h24eq : (24 : ℕ) = Nat.lcm 12 8 := by decide
                    exact ⟨hB₀_I hb.1.1, h24eq ▸ hlcm⟩
                  have hB₀_4 : 4 ≤ (B₀.filter (fun b => 2 ^ 2 ∣ b)).card := by
                    have hsub_u : B₀.filter (fun b => 12 ∣ b) ∪ B₀.filter (fun b => 2 ^ 3 ∣ b) ⊆
                        B₀.filter (fun b => 2 ^ 2 ∣ b) := by
                      intro b hb; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hb
                      rw [Finset.mem_filter]
                      rcases hb with hb12 | hb8
                      · exact ⟨hb12.1, dvd_trans (by norm_num) hb12.2⟩
                      · exact ⟨hb8.1, dvd_trans (by norm_num) hb8.2⟩
                    have h1 := Finset.card_union_add_card_inter
                      (B₀.filter (fun b => 12 ∣ b)) (B₀.filter (fun b => 2 ^ 3 ∣ b))
                    have h2 : (B₀.filter (fun b => 12 ∣ b) ∩ B₀.filter (fun b => 2 ^ 3 ∣ b)).card ≤ 1 :=
                      le_trans (Finset.card_le_card h12_8_24) hI24_1
                    exact le_trans (by omega) (Finset.card_le_card hsub_u)
                  have hB₀_16 : 1 ≤ (B₀.filter (fun b => 2 ^ 4 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 16 ∣ b) ⊆ B₀.filter (fun b => 2 ^ 4 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, dvd_trans (by norm_num) hb.2⟩),
                        by simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 16 (by norm_num)
                    rw [show M / 16 = 1 by rw [hM24]] at h2
                    exact le_trans h2 (Finset.card_le_card h1)
                  have hB₀_sum14 : 14 ≤ ∑ b ∈ B₀, b.factorization 2 := by
                    have h1 := sum_card_Icc_le_sum_factorization (K := 4) hB₀_I (by norm_num : Nat.Prime 2)
                    have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
                    rw [hIcc4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                        Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                    omega
                  have hA_sum14 : ∑ a ∈ A, a.factorization 2 ≤ 14 := by
                    have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 2)
                    have hc1' : (A.filter (fun a => 2 ^ 1 ∣ a)).card ≤ 5 :=
                      (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 1) (by norm_num) (by omega)).1
                    have hc2' : (A.filter (fun a => 2 ^ 2 ∣ a)).card ≤ 5 :=
                      (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 2) (by norm_num) (by omega)).1
                    have hc3' : (A.filter (fun a => 2 ^ 3 ∣ a)).card ≤ 3 := by
                      have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 3) (by norm_num) (by omega)).2
                      rw [show M / 2 ^ 3 = 3 by rw [hM24]; norm_num] at h; exact h
                    have hc4' : (A.filter (fun a => 2 ^ 4 ∣ a)).card ≤ 1 := by
                      have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := 4) (by norm_num) (by omega)).2
                      rw [show M / 2 ^ 4 = 1 by rw [hM24]; norm_num] at h; exact h
                    have hcz : ∀ j ∈ Finset.Icc 5 24, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 := by
                      intro j hj; rw [Finset.mem_Icc] at hj
                      have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 2) (j := j) (by norm_num) (by omega)).2
                      have hpow : 32 ≤ 2 ^ j :=
                        le_trans (by norm_num : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) hj.1)
                      have hdiv0 : M / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                      omega
                    have hIcc24 : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (insert 4 (Finset.Icc 5 24)))) := by
                      rw [hM24]; ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                    rw [hIcc24, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                        Finset.sum_insert (by decide), Finset.sum_insert (by decide)] at h1
                    have hsum0 : ∑ j ∈ Finset.Icc 5 24, (A.filter (fun a => 2 ^ j ∣ a)).card = 0 :=
                      Finset.sum_eq_zero hcz
                    omega
                  omega
                · obtain ⟨w₂, hw₂_flt, hw₂_notB₀⟩ := Finset.not_subset.mp hsub6
                  rw [Finset.mem_filter] at hw₂_flt
                  by_cases h12 : w₁ = w₂
                  · have h12_w₁' : 12 ∣ w₁ :=
                      Nat.lcm_dvd hw₁_flt.2 (h12 ▸ hw₂_flt.2) |> fun h =>
                        (show (12 : ℕ) = Nat.lcm 4 6 by decide) ▸ h
                    obtain ⟨w₃, hw₃_I, hw₃_notIns, h2_w₃⟩ :=
                      exists_avoiding_multiple_in_consecInterval x M 2 (insert w₁ B₀) (by norm_num)
                        (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM24]; omega)
                    have hw₃_ne : w₁ ≠ w₃ := fun h => hw₃_notIns (by simp [h])
                    have hw₃_notB₀ : w₃ ∉ B₀ := fun h => hw₃_notIns (Finset.mem_insert_of_mem h)
                    exact two_slots_of_two_dvd hw₁_flt.1 hw₃_I hw₁_notB₀ hw₃_notB₀ hw₃_ne
                      (dvd_trans hR24 (mul_dvd_mul h12_w₁' h2_w₃)) hR_pos.ne'
                  · exact two_slots_of_two_dvd hw₁_flt.1 hw₂_flt.1 hw₁_notB₀ hw₂_notB₀ h12
                      (dvd_trans hR24 (mul_dvd_mul hw₁_flt.2 hw₂_flt.2)) hR_pos.ne'
            · have hM48 : M = 48 := by rw [hM_eq, hc3]; norm_num
              have hR48 : R ∣ 48 := by rw [← hM48]; exact hRM
              by_cases hsub8 : (consecInterval x M).filter (fun b => 8 ∣ b) ⊆ B₀
              · have hsub8' : (consecInterval x M).filter (fun b => 2 ^ 3 ∣ b) ⊆ B₀ := by
                  simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using hsub8
                have hdef8 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I
                  (by norm_num : Nat.Prime 2) (by norm_num : 1 ≤ 3) hsub8'
                have hdiv8 : M / 2 ^ 3 = 6 := by rw [hM48]; norm_num
                rw [hdiv8] at hdef8
                omega
              · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub8
                rw [Finset.mem_filter] at hw₁_flt
                obtain ⟨w₂, hw₂_I, hw₂_notIns, h6_w₂⟩ :=
                  exists_avoiding_multiple_in_consecInterval x M 6 (insert w₁ B₀) (by norm_num)
                    (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM48]; omega)
                have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
                have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
                exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                  (dvd_trans hR48 (mul_dvd_mul hw₁_flt.2 h6_w₂)) hR_pos.ne'
            · have hM96 : M = 96 := by rw [hM_eq, hc3]; norm_num
              exact two_split_mults 12 8 (by norm_num) (by norm_num)
                (by rw [hM96]; norm_num) (by rw [hM96]; norm_num)
                (by rw [show (12 * 8 : ℕ) = 96 by norm_num, ← hM96]; exact hRM)
      · -- `p = 3`: `c = 2` (`M = 2 * 3^t`) OR `c = 3` (`M = 3^(t+1), R = 3^t`).
        rcases hc23 with hc2 | hc3
        · rcases le_or_gt 4 t with ht4 | ht_lt4
          · have h7d₁ : 7 * (2 * 3 ^ (t - 2)) ≤ M := by
              rw [hM_eq, hc2]
              have hpow : 3 ^ t = 9 * 3 ^ (t - 2) := by
                calc 3 ^ t = 3 ^ 2 * 3 ^ (t - 2) := by rw [← pow_add]; congr 1; omega
                  _ = 9 * 3 ^ (t - 2) := by norm_num
              rw [hpow]; ring_nf; omega
            have h8d₂ : 8 * 3 ^ (t - 2) ≤ M := by
              rw [hM_eq, hc2]
              have hpow : 3 ^ t = 9 * 3 ^ (t - 2) := by
                calc 3 ^ t = 3 ^ 2 * 3 ^ (t - 2) := by rw [← pow_add]; congr 1; omega
                  _ = 9 * 3 ^ (t - 2) := by norm_num
              rw [hpow]; ring_nf; omega
            have hRd12 : R ∣ (2 * 3 ^ (t - 2)) * 3 ^ (t - 2) := by
              apply dvd_trans hRM_cpt
              rw [hc2]
              have hpow : 3 ^ t ∣ 3 ^ (t - 2) * 3 ^ (t - 2) := by
                rw [← pow_add]; exact Nat.pow_dvd_pow 3 (by omega)
              calc 2 * 3 ^ t ∣ 2 * (3 ^ (t - 2) * 3 ^ (t - 2)) := mul_dvd_mul_left 2 hpow
                _ = (2 * 3 ^ (t - 2)) * 3 ^ (t - 2) := by ring
            exact two_split_mults (2 * 3 ^ (t - 2)) (3 ^ (t - 2))
              (mul_pos (by norm_num) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
              h7d₁ h8d₂ hRd12
          · have ht_cases : t = 2 ∨ t = 3 := by omega
            rcases ht_cases with rfl | rfl
            · have hM18 : M = 18 := by rw [hM_eq, hc2]; norm_num
              have hR18 : R ∣ 18 := by rw [← hM18]; exact hRM
              by_cases hsub6 : (consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀
              · have hB₀_6 : 3 ≤ (B₀.filter (fun b => 6 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀.filter (fun b => 6 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hsub6 (Finset.mem_filter.mpr hb), hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 6 (by norm_num)
                  rw [show M / 6 = 3 by rw [hM18]] at h2
                  exact le_trans h2 (Finset.card_le_card h1)
                have hB₀_9 : 2 ≤ (B₀.filter (fun b => 3 ^ 2 ∣ b)).card := by
                  have h1 : (consecInterval x M).filter (fun b => 9 ∣ b) ⊆ B₀.filter (fun b => 3 ^ 2 ∣ b) := by
                    intro b hb; rw [Finset.mem_filter] at hb ⊢
                    exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩),
                      by simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using hb.2⟩
                  have h2 := card_multiples_Icc_ge x M 9 (by norm_num)
                  rw [show M / 9 = 2 by rw [hM18]] at h2
                  exact le_trans h2 (Finset.card_le_card h1)
                have hI18_1 : ((consecInterval x M).filter (fun b => 18 ∣ b)).card ≤ 1 := by
                  rw [hM18]; exact card_multiples_M_le_one x 18 (by norm_num)
                have h6_9_18 : B₀.filter (fun b => 6 ∣ b) ∩ B₀.filter (fun b => 3 ^ 2 ∣ b) ⊆
                    (consecInterval x M).filter (fun b => 18 ∣ b) := by
                  intro b hb
                  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
                  rw [Finset.mem_filter]
                  have hlcm : Nat.lcm 6 9 ∣ b := Nat.lcm_dvd hb.1.2 (by simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using hb.2.2)
                  have h18eq : (18 : ℕ) = Nat.lcm 6 9 := by decide
                  exact ⟨hB₀_I hb.1.1, h18eq ▸ hlcm⟩
                have hB₀_3 : 4 ≤ (B₀.filter (fun b => 3 ^ 1 ∣ b)).card := by
                  have hsub_u : B₀.filter (fun b => 6 ∣ b) ∪ B₀.filter (fun b => 3 ^ 2 ∣ b) ⊆
                      B₀.filter (fun b => 3 ^ 1 ∣ b) := by
                    intro b hb; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hb
                    rw [Finset.mem_filter]
                    rcases hb with hb6 | hb9
                    · exact ⟨hb6.1, dvd_trans (by norm_num) hb6.2⟩
                    · exact ⟨hb9.1, dvd_trans (by norm_num) hb9.2⟩
                  have h1 := Finset.card_union_add_card_inter
                    (B₀.filter (fun b => 6 ∣ b)) (B₀.filter (fun b => 3 ^ 2 ∣ b))
                  have h2 : (B₀.filter (fun b => 6 ∣ b) ∩ B₀.filter (fun b => 3 ^ 2 ∣ b)).card ≤ 1 :=
                    le_trans (Finset.card_le_card h6_9_18) hI18_1
                  exact le_trans (by omega) (Finset.card_le_card hsub_u)
                have hB₀_sum6 : 6 ≤ ∑ b ∈ B₀, b.factorization 3 := by
                  have h1 := sum_card_Icc_le_sum_factorization (K := 2) hB₀_I (by norm_num : Nat.Prime 3)
                  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
                  rw [hIcc2, Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                  omega
                have hA_sum7 : ∑ a ∈ A, a.factorization 3 ≤ 7 := by
                  have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 3)
                  have hc1' : (A.filter (fun a => 3 ^ 1 ∣ a)).card ≤ 5 :=
                    (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := 1) (by norm_num) (by omega)).1
                  have hc2' : (A.filter (fun a => 3 ^ 2 ∣ a)).card ≤ 2 := by
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := 2) (by norm_num) (by omega)).2
                    rw [show M / 3 ^ 2 = 2 by rw [hM18]; norm_num] at h; exact h
                  have hcz : ∀ j ∈ Finset.Icc 3 18, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 := by
                    intro j hj; rw [Finset.mem_Icc] at hj
                    have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := j) (by norm_num) (by omega)).2
                    have hpow : 27 ≤ 3 ^ j :=
                      le_trans (by norm_num : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_right (by norm_num) hj.1)
                    have hdiv0 : M / 3 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                    omega
                  have hIcc18 : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 18)) := by
                    rw [hM18]; ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                  rw [hIcc18, Finset.sum_insert (by decide), Finset.sum_insert (by decide)] at h1
                  have hsum0 : ∑ j ∈ Finset.Icc 3 18, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 :=
                    Finset.sum_eq_zero hcz
                  omega
                omega
              · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub6
                rw [Finset.mem_filter] at hw₁_flt
                by_cases hsub3 : (consecInterval x M).filter (fun b => 3 ∣ b) ⊆ insert w₁ B₀
                · have hI3_6 : 6 ≤ ((consecInterval x M).filter (fun b => 3 ∣ b)).card := by
                    have h := card_multiples_Icc_ge x M 3 (by norm_num)
                    rw [show M / 3 = 6 by rw [hM18]] at h; exact h
                  have hB₀_3 : 5 ≤ (B₀.filter (fun b => 3 ^ 1 ∣ b)).card := by
                    have hsub_u : (consecInterval x M).filter (fun b => 3 ∣ b) ⊆
                        {w₁} ∪ B₀.filter (fun b => 3 ^ 1 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb
                      have hmem := hsub3 (Finset.mem_filter.mpr hb)
                      rcases Finset.mem_insert.mp hmem with rfl | hbB₀
                      · exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
                      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbB₀, by simpa using hb.2⟩)
                    have hle1 := Finset.card_le_card hsub_u
                    have hle2 := Finset.card_union_le {w₁} (B₀.filter (fun b => 3 ^ 1 ∣ b))
                    simp only [Finset.card_singleton] at hle2
                    omega
                  have hB₀_9 : 2 ≤ (B₀.filter (fun b => 3 ^ 2 ∣ b)).card := by
                    have h1 : (consecInterval x M).filter (fun b => 9 ∣ b) ⊆ B₀.filter (fun b => 3 ^ 2 ∣ b) := by
                      intro b hb; rw [Finset.mem_filter] at hb ⊢
                      exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩),
                        by simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using hb.2⟩
                    have h2 := card_multiples_Icc_ge x M 9 (by norm_num)
                    rw [show M / 9 = 2 by rw [hM18]] at h2
                    exact le_trans h2 (Finset.card_le_card h1)
                  have hB₀_sum7 : 7 ≤ ∑ b ∈ B₀, b.factorization 3 := by
                    have h1 := sum_card_Icc_le_sum_factorization (K := 2) hB₀_I (by norm_num : Nat.Prime 3)
                    have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
                    rw [hIcc2, Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                    omega
                  have hA_sum7 : ∑ a ∈ A, a.factorization 3 ≤ 7 := by
                    have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 3)
                    have hc1' : (A.filter (fun a => 3 ^ 1 ∣ a)).card ≤ 5 :=
                      (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := 1) (by norm_num) (by omega)).1
                    have hc2' : (A.filter (fun a => 3 ^ 2 ∣ a)).card ≤ 2 := by
                      have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := 2) (by norm_num) (by omega)).2
                      rw [show M / 3 ^ 2 = 2 by rw [hM18]; norm_num] at h; exact h
                    have hcz : ∀ j ∈ Finset.Icc 3 18, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 := by
                      intro j hj; rw [Finset.mem_Icc] at hj
                      have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 3) (j := j) (by norm_num) (by omega)).2
                      have hpow : 27 ≤ 3 ^ j :=
                        le_trans (by norm_num : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_right (by norm_num) hj.1)
                      have hdiv0 : M / 3 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                      omega
                    have hIcc18 : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 18)) := by
                      rw [hM18]; ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                    rw [hIcc18, Finset.sum_insert (by decide), Finset.sum_insert (by decide)] at h1
                    have hsum0 : ∑ j ∈ Finset.Icc 3 18, (A.filter (fun a => 3 ^ j ∣ a)).card = 0 :=
                      Finset.sum_eq_zero hcz
                    omega
                  omega
                · obtain ⟨w₂, hw₂_flt, hw₂_notIns⟩ := Finset.not_subset.mp hsub3
                  rw [Finset.mem_filter] at hw₂_flt
                  have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
                  have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
                  exact two_slots_of_two_dvd hw₁_flt.1 hw₂_flt.1 hw₁_notB₀ hw₂_notB₀ hw₂_ne
                    (dvd_trans hR18 (mul_dvd_mul hw₁_flt.2 hw₂_flt.2)) hR_pos.ne'
            · have hM54 : M = 54 := by rw [hM_eq, hc2]; norm_num
              have hR54 : R ∣ 54 := by rw [← hM54]; exact hRM
              by_cases hsub9 : (consecInterval x M).filter (fun b => 9 ∣ b) ⊆ B₀
              · have hsub9' : (consecInterval x M).filter (fun b => 3 ^ 2 ∣ b) ⊆ B₀ := by
                  simpa [show (9 : ℕ) = 3 ^ 2 by norm_num] using hsub9
                have hdef9 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I
                  (by norm_num : Nat.Prime 3) (by norm_num : 1 ≤ 2) hsub9'
                have hdiv9 : M / 3 ^ 2 = 6 := by rw [hM54]; norm_num
                rw [hdiv9] at hdef9
                omega
              · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub9
                rw [Finset.mem_filter] at hw₁_flt
                obtain ⟨w₂, hw₂_I, hw₂_notIns, h6_w₂⟩ :=
                  exists_avoiding_multiple_in_consecInterval x M 6 (insert w₁ B₀) (by norm_num)
                    (by have h1 := Finset.card_insert_le w₁ B₀; rw [hM54]; omega)
                have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
                have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
                exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne
                  (dvd_trans hR54 (mul_dvd_mul hw₁_flt.2 h6_w₂)) hR_pos.ne'
        · have hM_3t1 : M = 3 ^ (t + 1) := by rw [hM_eq, hc3, pow_succ']
          have hR_3t : R = 3 ^ t := by
            obtain ⟨k, hk⟩ := hpt_R
            have hk_dvd : k ∣ 3 := by
              have hM_div := hRM_cpt
              rw [hc3, hk] at hM_div
              obtain ⟨q, hq⟩ := hM_div
              have hpow_pos : 0 < 3 ^ t := pow_pos (by norm_num) t
              exact ⟨q, Nat.eq_of_mul_eq_mul_left hpow_pos (by linarith)⟩
            have hk_not3 : ¬ (3 ∣ k) := by
              intro h3k
              have h3t1 : 3 ^ (t + 1) ∣ R := by
                rw [hk, pow_succ]; exact mul_dvd_mul_left (3 ^ t) h3k
              have ht1_le : t + 1 ≤ R.factorization 3 :=
                ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hR_pos.ne').mp h3t1
              omega
            have hk_pos : 0 < k :=
              Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; exact hR_pos.ne' hk
            have hk_le3 : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk_dvd
            have hk_ne2 : k ≠ 2 := fun h => by rw [h] at hk_dvd; norm_num at hk_dvd
            have hk1 : k = 1 := by omega
            rw [hk, hk1, mul_one]
          have h8d : 8 * 3 ^ (t - 1) ≤ M := by
            rw [hM_3t1]
            have hpow : 3 ^ (t + 1) = 9 * 3 ^ (t - 1) := by
              calc 3 ^ (t + 1) = 3 ^ 2 * 3 ^ (t - 1) := by rw [← pow_add]; congr 1; omega
                _ = 9 * 3 ^ (t - 1) := by norm_num
            rw [hpow]
            exact Nat.mul_le_mul_right _ (by norm_num)
          have hRd2 : R ∣ 3 ^ (t - 1) * 3 ^ (t - 1) := by
            rw [hR_3t, ← pow_add]; exact Nat.pow_dvd_pow 3 (by omega)
          exact two_distinct_mults (3 ^ (t - 1)) (pow_pos (by norm_num) _) h8d hRd2
      · -- `p = 5`, `c ∈ {2, 3}`, `M = c * 5^t`, `R ∣ c * 5^t`, `t ≥ 2`
        rcases le_or_gt 4 t with ht4 | ht_lt4
        · have h7d₁ : 7 * (c * 5 ^ (t - 2)) ≤ M := by
            rw [hM_eq]
            have hpow : 5 ^ t = 25 * 5 ^ (t - 2) := by
              calc 5 ^ t = 5 ^ 2 * 5 ^ (t - 2) := by rw [← pow_add]; congr 1; omega
                _ = 25 * 5 ^ (t - 2) := by norm_num
            rw [hpow]
            calc 7 * (c * 5 ^ (t - 2)) = c * (7 * 5 ^ (t - 2)) := by ring
              _ ≤ c * (25 * 5 ^ (t - 2)) := Nat.mul_le_mul_left c (Nat.mul_le_mul_right _ (by norm_num))
          have h8d₂ : 8 * 5 ^ (t - 2) ≤ M := by
            rw [hM_eq]
            have hpow : 5 ^ t = 25 * 5 ^ (t - 2) := by
              calc 5 ^ t = 5 ^ 2 * 5 ^ (t - 2) := by rw [← pow_add]; congr 1; omega
                _ = 25 * 5 ^ (t - 2) := by norm_num
            rw [hpow]
            have h8c : 8 ≤ c * 25 := by omega
            calc 8 * 5 ^ (t - 2) ≤ (c * 25) * 5 ^ (t - 2) := Nat.mul_le_mul_right _ h8c
              _ = c * (25 * 5 ^ (t - 2)) := by ring
          have hRd12 : R ∣ (c * 5 ^ (t - 2)) * 5 ^ (t - 2) := by
            apply dvd_trans hRM_cpt
            have hpow : 5 ^ t ∣ 5 ^ (t - 2) * 5 ^ (t - 2) := by
              rw [← pow_add]; exact Nat.pow_dvd_pow 5 (by omega)
            calc c * 5 ^ t ∣ c * (5 ^ (t - 2) * 5 ^ (t - 2)) := mul_dvd_mul_left c hpow
              _ = (c * 5 ^ (t - 2)) * 5 ^ (t - 2) := by ring
          exact two_split_mults (c * 5 ^ (t - 2)) (5 ^ (t - 2))
            (mul_pos (by omega) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
            h7d₁ h8d₂ hRd12
        · have ht_cases : t = 2 ∨ t = 3 := by omega
          rcases ht_cases with rfl | rfl
          · have hM25c : M = c * 25 := by rw [hM_eq]; norm_num
            have hR25c : R ∣ c * 25 := by rw [← hM25c]; exact hRM
            by_cases hsub5c : (consecInterval x M).filter (fun b => c * 5 ∣ b) ⊆ B₀
            · have hB₀_5c : 5 ≤ (B₀.filter (fun b => c * 5 ∣ b)).card := by
                have h1 : (consecInterval x M).filter (fun b => c * 5 ∣ b) ⊆ B₀.filter (fun b => c * 5 ∣ b) := by
                  intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hsub5c (Finset.mem_filter.mpr hb), hb.2⟩
                have h2 := card_multiples_Icc_ge x M (c * 5) (by omega)
                have hdiv : M / (c * 5) = 5 := by
                  rw [hM25c, show c * 25 = 5 * (c * 5) by ring, Nat.mul_div_left 5 (by omega)]
                rw [hdiv] at h2
                exact le_trans h2 (Finset.card_le_card h1)
              have hB₀_25 : c ≤ (B₀.filter (fun b => 5 ^ 2 ∣ b)).card := by
                have h1 : (consecInterval x M).filter (fun b => 25 ∣ b) ⊆ B₀.filter (fun b => 5 ^ 2 ∣ b) := by
                  intro b hb; rw [Finset.mem_filter] at hb ⊢
                  exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩),
                    by simpa [show (25 : ℕ) = 5 ^ 2 by norm_num] using hb.2⟩
                have h2 := card_multiples_Icc_ge x M 25 (by norm_num)
                have hdiv : M / 25 = c := by rw [hM25c, Nat.mul_div_cancel c (by norm_num)]
                rw [hdiv] at h2
                exact le_trans h2 (Finset.card_le_card h1)
              have hIM_1 : ((consecInterval x M).filter (fun b => M ∣ b)).card ≤ 1 :=
                card_multiples_M_le_one x M (by omega)
              have h5c_25_M : B₀.filter (fun b => c * 5 ∣ b) ∩ B₀.filter (fun b => 5 ^ 2 ∣ b) ⊆
                  (consecInterval x M).filter (fun b => M ∣ b) := by
                intro b hb
                rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
                rw [Finset.mem_filter]
                have hc5_dvd : c * 5 ∣ b := hb.1.2
                have h25_dvd : 25 ∣ b := by simpa [show (25 : ℕ) = 5 ^ 2 by norm_num] using hb.2.2
                have hlcm_dvd : Nat.lcm (c * 5) 25 ∣ b := Nat.lcm_dvd hc5_dvd h25_dvd
                have hM_lcm : M = Nat.lcm (c * 5) 25 := by
                  rw [hM25c]
                  rcases hc23 with h2 | h3 <;> [rw [h2]; rw [h3]] <;> decide
                exact ⟨hB₀_I hb.1.1, hM_lcm ▸ hlcm_dvd⟩
              have hB₀_5 : 4 + c ≤ (B₀.filter (fun b => 5 ^ 1 ∣ b)).card := by
                have hsub_u : B₀.filter (fun b => c * 5 ∣ b) ∪ B₀.filter (fun b => 5 ^ 2 ∣ b) ⊆
                    B₀.filter (fun b => 5 ^ 1 ∣ b) := by
                  intro b hb; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hb
                  rw [Finset.mem_filter]
                  rcases hb with hba | hbb
                  · exact ⟨hba.1, dvd_trans (dvd_mul_left 5 c) hba.2⟩
                  · exact ⟨hbb.1, dvd_trans (by norm_num) hbb.2⟩
                have h1 := Finset.card_union_add_card_inter
                  (B₀.filter (fun b => c * 5 ∣ b)) (B₀.filter (fun b => 5 ^ 2 ∣ b))
                have h2 : (B₀.filter (fun b => c * 5 ∣ b) ∩ B₀.filter (fun b => 5 ^ 2 ∣ b)).card ≤ 1 :=
                  le_trans (Finset.card_le_card h5c_25_M) hIM_1
                exact le_trans (by omega) (Finset.card_le_card hsub_u)
              have hB₀_sum : 4 + 2 * c ≤ ∑ b ∈ B₀, b.factorization 5 := by
                have h1 := sum_card_Icc_le_sum_factorization (K := 2) hB₀_I (by norm_num : Nat.Prime 5)
                have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
                rw [hIcc2, Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                omega
              have hA_sum : ∑ a ∈ A, a.factorization 5 ≤ 5 + c := by
                have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 5)
                have hc1' : (A.filter (fun a => 5 ^ 1 ∣ a)).card ≤ 5 :=
                  (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := 1) (by norm_num) (by omega)).1
                have hc2' : (A.filter (fun a => 5 ^ 2 ∣ a)).card ≤ c := by
                  have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := 2) (by norm_num) (by omega)).2
                  have hdiv : M / 5 ^ 2 = c := by rw [hM25c]; norm_num
                  omega
                have hcz : ∀ j ∈ Finset.Icc 3 M, (A.filter (fun a => 5 ^ j ∣ a)).card = 0 := by
                  intro j hj; rw [Finset.mem_Icc] at hj
                  have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := j) (by norm_num) (by omega)).2
                  have hpow : 125 ≤ 5 ^ j :=
                    le_trans (by norm_num : 125 ≤ 5 ^ 3) (Nat.pow_le_pow_right (by norm_num) hj.1)
                  have hM_lt125 : M < 125 := by omega
                  have hdiv0 : M / 5 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                  omega
                have hIccM : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
                  ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                rw [hIccM, Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at h1
                have hsum0 : ∑ j ∈ Finset.Icc 3 M, (A.filter (fun a => 5 ^ j ∣ a)).card = 0 :=
                  Finset.sum_eq_zero hcz
                omega
              omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub5c
              rw [Finset.mem_filter] at hw₁_flt
              have h85 : 8 * 5 ≤ M := by rw [hM25c]; omega
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h5_w₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M 5 (insert w₁ B₀) (by norm_num)
                  (by have h1 := Finset.card_insert_le w₁ B₀; omega)
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              have hRw : R ∣ w₁ * w₂ := by
                apply dvd_trans hR25c
                calc c * 25 = (c * 5) * 5 := by ring
                  _ ∣ w₁ * w₂ := mul_dvd_mul hw₁_flt.2 h5_w₂
              exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'
          · have hM125c : M = c * 125 := by rw [hM_eq]; norm_num
            have hR125c : R ∣ c * 125 := by rw [← hM125c]; exact hRM
            by_cases hsub25c : (consecInterval x M).filter (fun b => c * 25 ∣ b) ⊆ B₀
            · have hB₀_25 : 5 ≤ (B₀.filter (fun b => 5 ^ 2 ∣ b)).card := by
                have h1 : (consecInterval x M).filter (fun b => c * 25 ∣ b) ⊆ B₀.filter (fun b => 5 ^ 2 ∣ b) := by
                  intro b hb; rw [Finset.mem_filter] at hb ⊢
                  exact ⟨hsub25c (Finset.mem_filter.mpr hb), dvd_trans (dvd_mul_left 25 c) hb.2⟩
                have h2 := card_multiples_Icc_ge x M (c * 25) (by omega)
                have hdiv : M / (c * 25) = 5 := by
                  rw [hM125c, show c * 125 = 5 * (c * 25) by ring, Nat.mul_div_left 5 (by omega)]
                rw [hdiv] at h2
                exact le_trans h2 (Finset.card_le_card h1)
              have hB₀_5 : 5 ≤ (B₀.filter (fun b => 5 ^ 1 ∣ b)).card := by
                have hsub12 : B₀.filter (fun b => 5 ^ 2 ∣ b) ⊆ B₀.filter (fun b => 5 ^ 1 ∣ b) := by
                  intro b hb; rw [Finset.mem_filter] at hb ⊢; exact ⟨hb.1, dvd_trans (by norm_num) hb.2⟩
                exact le_trans hB₀_25 (Finset.card_le_card hsub12)
              have hB₀_125 : c ≤ (B₀.filter (fun b => 5 ^ 3 ∣ b)).card := by
                have h1 : (consecInterval x M).filter (fun b => 125 ∣ b) ⊆ B₀.filter (fun b => 5 ^ 3 ∣ b) := by
                  intro b hb; rw [Finset.mem_filter] at hb ⊢
                  exact ⟨hsub_q (Finset.mem_filter.mpr ⟨hb.1, by simpa using hb.2⟩),
                    by simpa [show (125 : ℕ) = 5 ^ 3 by norm_num] using hb.2⟩
                have h2 := card_multiples_Icc_ge x M 125 (by norm_num)
                have hdiv : M / 125 = c := by rw [hM125c, Nat.mul_div_cancel c (by norm_num)]
                rw [hdiv] at h2
                exact le_trans h2 (Finset.card_le_card h1)
              have hB₀_sum : 10 + c ≤ ∑ b ∈ B₀, b.factorization 5 := by
                have h1 := sum_card_Icc_le_sum_factorization (K := 3) hB₀_I (by norm_num : Nat.Prime 5)
                have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
                rw [hIcc3, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h1
                omega
              have hA_sum : ∑ a ∈ A, a.factorization 5 ≤ 10 + c := by
                have h1 := sum_factorization_eq_sum_card_Icc hA_pos hA_le (by norm_num : Nat.Prime 5)
                have hc1' : (A.filter (fun a => 5 ^ 1 ∣ a)).card ≤ 5 :=
                  (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := 1) (by norm_num) (by omega)).1
                have hc2' : (A.filter (fun a => 5 ^ 2 ∣ a)).card ≤ 5 :=
                  (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := 2) (by norm_num) (by omega)).1
                have hc3' : (A.filter (fun a => 5 ^ 3 ∣ a)).card ≤ c := by
                  have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := 3) (by norm_num) (by omega)).2
                  have hdiv : M / 5 ^ 3 = c := by rw [hM125c]; norm_num
                  omega
                have hcz : ∀ j ∈ Finset.Icc 4 M, (A.filter (fun a => 5 ^ j ∣ a)).card = 0 := by
                  intro j hj; rw [Finset.mem_Icc] at hj
                  have h := (card_filter_le_five_and_div hA_card hA_pos hA_le hAgcd (p := 5) (j := j) (by norm_num) (by omega)).2
                  have hpow : 625 ≤ 5 ^ j :=
                    le_trans (by norm_num : 625 ≤ 5 ^ 4) (Nat.pow_le_pow_right (by norm_num) hj.1)
                  have hM_lt625 : M < 625 := by omega
                  have hdiv0 : M / 5 ^ j = 0 := Nat.div_eq_of_lt (by omega)
                  omega
                have hIccM : Finset.Icc 1 M = insert 1 (insert 2 (insert 3 (Finset.Icc 4 M))) := by
                  ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                rw [hIccM, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
                    Finset.sum_insert (by simp)] at h1
                have hsum0 : ∑ j ∈ Finset.Icc 4 M, (A.filter (fun a => 5 ^ j ∣ a)).card = 0 :=
                  Finset.sum_eq_zero hcz
                omega
              omega
            · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub25c
              rw [Finset.mem_filter] at hw₁_flt
              have h85 : 8 * 5 ≤ M := by rw [hM125c]; omega
              obtain ⟨w₂, hw₂_I, hw₂_notIns, h5_w₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M 5 (insert w₁ B₀) (by norm_num)
                  (by have h1 := Finset.card_insert_le w₁ B₀; omega)
              have hw₂_ne : w₁ ≠ w₂ := fun h => hw₂_notIns (by simp [h])
              have hw₂_notB₀ : w₂ ∉ B₀ := fun h => hw₂_notIns (Finset.mem_insert_of_mem h)
              have hRw : R ∣ w₁ * w₂ := by
                apply dvd_trans hR125c
                calc c * 125 = (c * 25) * 5 := by ring
                  _ ∣ w₁ * w₂ := mul_dvd_mul hw₁_flt.2 h5_w₂
              exact two_slots_of_two_dvd hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₂_ne hRw hR_pos.ne'

private lemma prod_prime_ge_30_of_card_ge_3 {S : Finset ℕ} (hS : 3 ≤ S.card)
    (hprime : ∀ p ∈ S, p.Prime) :
    30 ≤ ∏ p ∈ S, p := by
  have hS0 : S.Nonempty := Finset.card_pos.mp (by omega)
  let p₀ := S.min' hS0
  have hp₀_mem : p₀ ∈ S := Finset.min'_mem S hS0
  let S₁ := S.erase p₀
  have hS₁_card : 2 ≤ S₁.card := by rw [Finset.card_erase_of_mem hp₀_mem]; omega
  have hS₁_ne : S₁.Nonempty := Finset.card_pos.mp (by omega)
  let p₁ := S₁.min' hS₁_ne
  have hp₁_S₁ : p₁ ∈ S₁ := Finset.min'_mem S₁ hS₁_ne
  have hp₁_ne : p₁ ≠ p₀ := (Finset.mem_erase.mp hp₁_S₁).1
  have hp₁_mem : p₁ ∈ S := (Finset.mem_erase.mp hp₁_S₁).2
  have hp₀_lt_p₁ : p₀ < p₁ := lt_of_le_of_ne (Finset.min'_le S p₁ hp₁_mem) hp₁_ne.symm
  let S₂ := S₁.erase p₁
  have hS₂_card : 1 ≤ S₂.card := by rw [Finset.card_erase_of_mem hp₁_S₁]; omega
  have hS₂_ne : S₂.Nonempty := Finset.card_pos.mp hS₂_card
  let p₂ := S₂.min' hS₂_ne
  have hp₂_S₂ : p₂ ∈ S₂ := Finset.min'_mem S₂ hS₂_ne
  have hp₂_ne1 : p₂ ≠ p₁ := (Finset.mem_erase.mp hp₂_S₂).1
  have hp₂_S₁ : p₂ ∈ S₁ := (Finset.mem_erase.mp hp₂_S₂).2
  have hp₂_mem : p₂ ∈ S := (Finset.mem_erase.mp hp₂_S₁).2
  have hp₁_lt_p₂ : p₁ < p₂ := lt_of_le_of_ne (Finset.min'_le S₁ p₂ hp₂_S₁) hp₂_ne1.symm
  have hp₀ := hprime p₀ hp₀_mem
  have hp₁ := hprime p₁ hp₁_mem
  have hp₂ := hprime p₂ hp₂_mem
  have hp0_2 : 2 ≤ p₀ := hp₀.two_le
  have hp1_3 : 3 ≤ p₁ := by omega
  have hp2_ne4 : p₂ ≠ 4 := fun h => by rw [h] at hp₂; norm_num at hp₂
  have hp2_5 : 5 ≤ p₂ := by omega
  have hsub : {p₀, p₁, p₂} ⊆ S := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact hp₀_mem
    · rcases Finset.mem_insert.mp hq' with rfl | hq''
      · exact hp₁_mem
      · rw [Finset.mem_singleton.mp hq'']; exact hp₂_mem
  have hdvd : (∏ q ∈ ({p₀, p₁, p₂} : Finset ℕ), q) ∣ ∏ p ∈ S, p :=
    Finset.prod_dvd_prod_of_subset _ S id hsub
  have hprod_eq : ∏ q ∈ ({p₀, p₁, p₂} : Finset ℕ), q = p₀ * p₁ * p₂ := by
    rw [Finset.prod_insert (by simp [hp₀_lt_p₁.ne, (lt_trans hp₀_lt_p₁ hp₁_lt_p₂).ne]),
        Finset.prod_insert (by simp [hp₁_lt_p₂.ne]), Finset.prod_singleton]
    ring
  have hprod_pos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hle_prod : p₀ * p₁ * p₂ ≤ ∏ p ∈ S, p :=
    Nat.le_of_dvd hprod_pos (hprod_eq ▸ hdvd)
  have h30 : 30 ≤ p₀ * p₁ * p₂ := Nat.mul_le_mul (Nat.mul_le_mul hp0_2 hp1_3) hp2_5
  omega

/-- **Master `R ∣ M` Two-Slot Residual Theorem**:
    Given `A.card = 6`, `A.gcd id = 1`, `9 ≤ M`, `B₀ ⊆ consecInterval x M` (`B₀.card ≤ 6`),
    and positive residual `R ∣ M` matching all prime-valuation deficits, there exists
    `B₁ ⊆ consecInterval x M` disjoint from `B₀` with `B₁.card ≤ 2` absorbing `R`. -/
private theorem exists_two_slots_for_R_dvd_M {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hAgcd : A.gcd id = 1) (hM9 : 9 ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 6)
    (hR_pos : 0 < R) (hRM : R ∣ M)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  by_cases hR0_pf : R.primeFactors.card = 0
  · refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp, ?_⟩
    intro p hp
    have hmem : p ∉ R.primeFactors := by rw [Finset.card_eq_zero.mp hR0_pf]; simp
    have hnd : ¬ (p ∣ R) := fun h => hmem ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr ⟨hp, h⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
  let L₇ := M / 7
  let P_big := R.primeFactors.filter (fun p => L₇ < p ^ (R.factorization p))
  let P_small := R.primeFactors.filter (fun p => ¬ (L₇ < p ^ (R.factorization p)))
  have hR_self : R = ∏ p ∈ R.primeFactors, p ^ (R.factorization p) := by
    have h := (Nat.prod_factorization_pow_eq_self hR_pos.ne').symm
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hR_split : R = (∏ p ∈ P_big, p ^ (R.factorization p)) *
      (∏ p ∈ P_small, p ^ (R.factorization p)) := by
    calc R = ∏ p ∈ R.primeFactors, p ^ (R.factorization p) := hR_self
      _ = (∏ p ∈ P_big, p ^ (R.factorization p)) * (∏ p ∈ P_small, p ^ (R.factorization p)) :=
          (Finset.prod_filter_mul_prod_filter_not R.primeFactors
            (fun p => L₇ < p ^ (R.factorization p)) (fun p => p ^ (R.factorization p))).symm
  have hPsmall_pos : 1 ≤ ∏ p ∈ P_small, p ^ (R.factorization p) :=
    Finset.one_le_prod' (fun q hq =>
      Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos)
  have hPbig_le_R : ∏ p ∈ P_big, p ^ (R.factorization p) ≤ R := by
    conv_rhs => rw [hR_split]
    exact Nat.le_mul_of_pos_right _ hPsmall_pos
  have hR_le_M : R ≤ M := Nat.le_of_dvd (by omega) hRM
  have hM_lt : M < 7 * (L₇ + 1) := by
    have hdm := Nat.div_add_mod M 7
    have hml := Nat.mod_lt M (by norm_num : 0 < 7)
    dsimp [L₇]
    omega
  have hPbig_lt3 : P_big.card < 3 := by
    by_contra hge3
    push Not at hge3
    have hpow : (L₇ + 1) ^ 3 ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
      have h1 : (L₇ + 1) ^ P_big.card ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
        calc (L₇ + 1) ^ P_big.card = ∏ _p ∈ P_big, (L₇ + 1) := by simp
          _ ≤ ∏ p ∈ P_big, p ^ (R.factorization p) :=
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (Finset.mem_filter.mp hp).2)
      exact le_trans (Nat.pow_le_pow_right (by omega) hge3) h1
    have hpow_leM : (L₇ + 1) ^ 3 ≤ M := le_trans hpow (le_trans hPbig_le_R hR_le_M)
    by_cases hM19 : 19 ≤ M
    · have hcub : M ^ 3 < 343 * (L₇ + 1) ^ 3 := by
        have h1 : M ^ 3 < (7 * (L₇ + 1)) ^ 3 := Nat.pow_lt_pow_left hM_lt (by omega)
        have h2 : (7 * (L₇ + 1)) ^ 3 = 343 * (L₇ + 1) ^ 3 := by ring
        omega
      have hM3 : 343 * (L₇ + 1) ^ 3 ≤ 343 * M := Nat.mul_le_mul_left 343 hpow_leM
      have h343 : 343 * M < M ^ 2 * M := by
        have h19 : 361 ≤ M ^ 2 := by
          have : 19 ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hM19 2
          norm_num at this; exact this
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      have hM3' : M ^ 2 * M = M ^ 3 := by ring
      omega
    · have hM18 : M ≤ 18 := by omega
      have h30 : 30 ≤ ∏ p ∈ P_big, p :=
        prod_prime_ge_30_of_card_ge_3 hge3
          (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      have hprod_le : ∏ p ∈ P_big, p ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
        apply Finset.prod_le_prod'
        intro p hp
        have hmem := (Finset.mem_filter.mp hp).1
        have h1 := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hmem
        have he1 : 1 ≤ R.factorization p :=
          (h1.1.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h1.2)
        exact Nat.le_self_pow (by omega) p
      omega
  have hPbig_cases : P_big.card = 0 ∨ P_big.card = 1 ∨ P_big.card = 2 := by omega
  rcases hPbig_cases with hbig0 | hbig1 | hbig2
  · -- **Case 0 (`P_big.card = 0`)**: bin pack `P_small` into `L₇`.
    have hPbig_emp : P_big = ∅ := Finset.card_eq_zero.mp hbig0
    have hsmall_bnd : ∀ p ∈ R.primeFactors, p ^ (R.factorization p) ≤ L₇ := by
      intro p hp
      by_contra hlt
      have hp_big : p ∈ P_big := Finset.mem_filter.mpr ⟨hp, by omega⟩
      rw [hPbig_emp] at hp_big
      simp at hp_big
    let xs : List ℕ := R.primeFactors.toList.map (fun p => p ^ (R.factorization p))
    have hxs_bnd : ∀ u ∈ xs, 1 ≤ u ∧ u ≤ L₇ := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      rw [Finset.mem_toList] at hp
      exact ⟨Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos, hsmall_bnd p hp⟩
    have hxs_cop : xs.Pairwise Nat.Coprime := by
      have aux : ∀ (l : List ℕ), l.Nodup → (∀ p ∈ l, p.Prime) →
          (l.map (fun p => p ^ (R.factorization p))).Pairwise Nat.Coprime := by
        intro l hnod hpr
        induction l with
        | nil => simp
        | cons p ps ih =>
          rw [List.nodup_cons] at hnod
          rw [List.map_cons, List.pairwise_cons]
          refine ⟨?_, ih hnod.2 (fun q hq => hpr q (List.mem_cons_of_mem p hq))⟩
          intro u hu
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
          have hp_pr := hpr p List.mem_cons_self
          have hq_pr := hpr q (List.mem_cons_of_mem p hq)
          have hne : p ≠ q := fun h => hnod.1 (h ▸ hq)
          exact ((Nat.coprime_primes hp_pr hq_pr).mpr hne).pow _ _
      exact aux R.primeFactors.toList (Finset.nodup_toList R.primeFactors)
        (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp))
    have hxs_prod : xs.prod = R := by
      dsimp [xs]
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
      exact hR_self.symm
    obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw, hbs_cop⟩ :=
      list_bin_pack_coprime L₇ xs.length xs rfl hxs_bnd hxs_cop
    rw [hxs_prod] at hbs_prod
    have hcover_of_bins_le2 : ∀ (bs' : List ℕ), bs'.length ≤ 2 →
        (∀ u ∈ bs', 1 ≤ u ∧ u ≤ L₇) → bs'.prod = R → bs'.Pairwise Nat.Coprime →
        ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
          ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
      intro bs' hlen' hbnd' hprod' hcop'
      match bs' with
      | [] =>
        simp only [List.prod_nil] at hprod'
        rw [← hprod', Nat.primeFactors_one, Finset.card_empty] at hR0_pf
        exact absurd rfl hR0_pf
      | [D₁] =>
        simp only [List.prod_cons, List.prod_nil, mul_one] at hprod'
        have hD₁ := hbnd' D₁ List.mem_cons_self
        have h7D₁ : (B₀.card + 1) * D₁ ≤ M := by
          have h1 : (B₀.card + 1) * D₁ ≤ 7 * L₇ := Nat.mul_le_mul (by omega) hD₁.2
          exact le_trans h1 (Nat.mul_div_le M 7)
        obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
          exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁.1 h7D₁
        exact two_slots_of_one_dvd hb₁_I hb₁_notB₀ (hprod' ▸ hD₁_b₁) hR_pos.ne'
      | [D₁, D₂] =>
        have hD₁ := hbnd' D₁ List.mem_cons_self
        have hD₂ := hbnd' D₂ (List.mem_cons_of_mem D₁ List.mem_cons_self)
        have h7L : 7 * L₇ ≤ M := Nat.mul_div_le M 7
        have h7D₁ : (B₀.card + 1) * D₁ ≤ M := le_trans (Nat.mul_le_mul (by omega) hD₁.2) h7L
        have h7D₂ : (B₀.card + 1) * D₂ ≤ M := le_trans (Nat.mul_le_mul (by omega) hD₂.2) h7L
        obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
          exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁.1 h7D₁
        obtain ⟨b₂, hb₂_I, hb₂_notB₀, hD₂_b₂⟩ :=
          exists_avoiding_multiple_in_consecInterval x M D₂ B₀ hD₂.1 h7D₂
        rw [List.pairwise_cons] at hcop'
        have hcop12 : Nat.Coprime D₁ D₂ := hcop'.1 D₂ List.mem_cons_self
        have hR_eq12 : R = D₁ * D₂ := by rw [← hprod']; simp [List.prod_cons]
        exact two_slots_of_coprime_dvd hR_eq12 hcop12 hD₁.1 hD₂.1 hb₁_I hb₂_I hb₁_notB₀ hb₂_notB₀
          hD₁_b₁ hD₂_b₂
      | _ :: _ :: _ :: _ => simp at hlen'
    rcases le_or_gt bs.length 2 with hlen2 | hlen3
    · exact hcover_of_bins_le2 bs hlen2 hbs_bnd hbs_prod hbs_cop
    · have hbs_ge2 : ∀ u ∈ bs, 2 ≤ u := by
        intro u hu
        have hu1 := (hbs_bnd u hu).1
        by_contra hlt2
        have hu_eq1 : u = 1 := by omega
        obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hu
        have hv_ex : ∃ v ∈ l₁ ++ l₂, True := by
          cases l₁ with
          | nil =>
            cases l₂ with
            | nil => simp at hlen3
            | cons v vs => exact ⟨v, by simp, trivial⟩
          | cons v vs => exact ⟨v, by simp, trivial⟩
        obtain ⟨v, hv_mem, _⟩ := hv_ex
        have hv_bnd : v ≤ L₇ := by
          have : v ∈ l₁ ++ u :: l₂ := by
            rcases List.mem_append.mp hv_mem with hv1 | hv2
            · exact List.mem_append_left _ hv1
            · exact List.mem_append_right _ (List.mem_cons_of_mem u hv2)
          exact (hbs_bnd v this).2
        rw [List.pairwise_append] at hbs_pw
        rcases List.mem_append.mp hv_mem with hv1 | hv2
        · have hgt : L₇ < v * u := hbs_pw.2.2 v hv1 u List.mem_cons_self
          rw [hu_eq1, mul_one] at hgt; omega
        · have hpw2 := hbs_pw.2.1; rw [List.pairwise_cons] at hpw2
          have hgt : L₇ < u * v := hpw2.1 v hv2
          rw [hu_eq1, one_mul] at hgt; omega
      match bs with
      | [] | [_] | [_, _] => simp at hlen3
      | u₀ :: u₁ :: u₂ :: rest =>
        have hpos_rest : 1 ≤ rest.prod := List.one_le_prod (fun x hx => (hbs_bnd x (by simp [hx])).1)
        have hpw0 := hbs_pw; rw [List.pairwise_cons] at hpw0
        have hpw1 := hpw0.2; rw [List.pairwise_cons] at hpw1
        have hgt01 : L₇ + 1 ≤ u₀ * u₁ := hpw0.1 u₁ (by simp)
        have hgt02 : L₇ + 1 ≤ u₀ * u₂ := hpw0.1 u₂ (by simp)
        have hgt12 : L₇ + 1 ≤ u₁ * u₂ := hpw1.1 u₂ (by simp)
        have hprod_eq : u₀ * u₁ * u₂ * rest.prod = R := by
          rw [← hbs_prod]; simp only [List.prod_cons]; ring
        have hu₂_lt7 : u₂ ≤ 6 := by
          have h1 : (L₇ + 1) * u₂ ≤ u₀ * u₁ * u₂ * rest.prod := by
            calc (L₇ + 1) * u₂ ≤ (u₀ * u₁) * u₂ := Nat.mul_le_mul_right u₂ hgt01
              _ = u₀ * u₁ * u₂ * 1 := by ring
              _ ≤ u₀ * u₁ * u₂ * rest.prod := Nat.mul_le_mul_left _ hpos_rest
          have h2 : (L₇ + 1) * u₂ < (L₇ + 1) * 7 := by rw [hprod_eq] at h1; omega
          have h3 := Nat.lt_of_mul_lt_mul_left h2
          omega
        have hu₁_lt7 : u₁ ≤ 6 := by
          have h1 : (L₇ + 1) * u₁ ≤ u₀ * u₁ * u₂ * rest.prod := by
            calc (L₇ + 1) * u₁ ≤ (u₀ * u₂) * u₁ := Nat.mul_le_mul_right u₁ hgt02
              _ = u₀ * u₁ * u₂ * 1 := by ring
              _ ≤ u₀ * u₁ * u₂ * rest.prod := Nat.mul_le_mul_left _ hpos_rest
          have h2 : (L₇ + 1) * u₁ < (L₇ + 1) * 7 := by rw [hprod_eq] at h1; omega
          have h3 := Nat.lt_of_mul_lt_mul_left h2
          omega
        have hu₀_lt7 : u₀ ≤ 6 := by
          have h1 : (L₇ + 1) * u₀ ≤ u₀ * u₁ * u₂ * rest.prod := by
            calc (L₇ + 1) * u₀ ≤ (u₁ * u₂) * u₀ := Nat.mul_le_mul_right u₀ hgt12
              _ = u₀ * u₁ * u₂ * 1 := by ring
              _ ≤ u₀ * u₁ * u₂ * rest.prod := Nat.mul_le_mul_left _ hpos_rest
          have h2 : (L₇ + 1) * u₀ < (L₇ + 1) * 7 := by rw [hprod_eq] at h1; omega
          have h3 := Nat.lt_of_mul_lt_mul_left h2
          omega
        have hrest_nil : rest = [] := by
          cases rest with
          | nil => rfl
          | cons u₃ ts =>
            have hu₀_2 : 2 ≤ u₀ := hbs_ge2 u₀ (by simp)
            have hu₁_2 : 2 ≤ u₁ := hbs_ge2 u₁ (by simp)
            have hu₂_2 : 2 ≤ u₂ := hbs_ge2 u₂ (by simp)
            have hu₃_2 : 2 ≤ u₃ := hbs_ge2 u₃ (by simp)
            have hu₃_lt7 : u₃ ≤ 6 := by
              have hts : 1 ≤ ts.prod := List.one_le_prod (fun x hx => (hbs_bnd x (by simp [hx])).1)
              have h1 : (L₇ + 1) * u₃ ≤ u₀ * u₁ * u₂ * (u₃ * ts.prod) := by
                calc (L₇ + 1) * u₃ ≤ (u₀ * u₁) * u₃ := Nat.mul_le_mul_right u₃ hgt01
                  _ ≤ (u₀ * u₁ * u₂) * u₃ := Nat.mul_le_mul_right u₃ (Nat.le_mul_of_pos_right _ (by omega))
                  _ = u₀ * u₁ * u₂ * (u₃ * 1) := by ring
                  _ ≤ u₀ * u₁ * u₂ * (u₃ * ts.prod) :=
                      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left u₃ hts)
              have h2 : (L₇ + 1) * u₃ < (L₇ + 1) * 7 := by
                have heq : (u₃ :: ts).prod = u₃ * ts.prod := List.prod_cons
                rw [← heq, hprod_eq] at h1; omega
              have h3 := Nat.lt_of_mul_lt_mul_left h2
              omega
            have hcop0 := hbs_cop; rw [List.pairwise_cons] at hcop0
            have hcop1 := hcop0.2; rw [List.pairwise_cons] at hcop1
            have hcop2 := hcop1.2; rw [List.pairwise_cons] at hcop2
            have hc01 := hcop0.1 u₁ (by simp)
            have hc02 := hcop0.1 u₂ (by simp)
            have hc03 := hcop0.1 u₃ (by simp)
            have hc12 := hcop1.1 u₂ (by simp)
            have hc13 := hcop1.1 u₃ (by simp)
            have hc23 := hcop2.1 u₃ (by simp)
            have hq_mem : ∀ x : ℕ, 2 ≤ x → x ≤ 6 → x.minFac ∈ ({2, 3, 5} : Finset ℕ) := by
              intro x hx2 hx6
              have hxp := Nat.minFac_prime (by omega : x ≠ 1)
              have hx_le := Nat.minFac_le (by omega : 0 < x)
              have hx_4 : x.minFac ≠ 4 := fun h => by rw [h] at hxp; norm_num at hxp
              have hx_6 : x.minFac ≠ 6 := fun h => by rw [h] at hxp; norm_num at hxp
              have hx2' := hxp.two_le
              simp only [Finset.mem_insert, Finset.mem_singleton]
              omega
            have hq0_m := hq_mem u₀ hu₀_2 hu₀_lt7
            have hq1_m := hq_mem u₁ hu₁_2 hu₁_lt7
            have hq2_m := hq_mem u₂ hu₂_2 hu₂_lt7
            have hq3_m := hq_mem u₃ hu₃_2 hu₃_lt7
            have hne_of_cop : ∀ a b : ℕ, a ≠ 1 → Nat.Coprime a b → a.minFac ≠ b.minFac := by
              intro a b ha1 hcop heq
              have h1 : a.minFac ∣ Nat.gcd a b := Nat.dvd_gcd (Nat.minFac_dvd a) (heq ▸ Nat.minFac_dvd b)
              rw [hcop.gcd_eq_one] at h1
              exact (Nat.minFac_prime ha1).not_dvd_one h1
            have h01' := hne_of_cop u₀ u₁ (by omega) hc01
            have h02' := hne_of_cop u₀ u₂ (by omega) hc02
            have h03' := hne_of_cop u₀ u₃ (by omega) hc03
            have h12' := hne_of_cop u₁ u₂ (by omega) hc12
            have h13' := hne_of_cop u₁ u₃ (by omega) hc13
            have h23' := hne_of_cop u₂ u₃ (by omega) hc23
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq0_m hq1_m hq2_m hq3_m
            omega
        subst hrest_nil
        simp only [List.prod_nil, mul_one] at hprod_eq
        have hu₀_2 : 2 ≤ u₀ := hbs_ge2 u₀ (by simp)
        have hu₁_2 : 2 ≤ u₁ := hbs_ge2 u₁ (by simp)
        have hu₂_2 : 2 ≤ u₂ := hbs_ge2 u₂ (by simp)
        have hcop0 := hbs_cop; rw [List.pairwise_cons] at hcop0
        have hcop1 := hcop0.2; rw [List.pairwise_cons] at hcop1
        have hc01 := hcop0.1 u₁ (by simp)
        have hc02 := hcop0.1 u₂ (by simp)
        have hc12 := hcop1.1 u₂ (by simp)
        have hn6 : ∀ a ∈ Finset.Icc 2 6, ∀ b ∈ Finset.Icc 2 6, ∀ c ∈ Finset.Icc 2 6,
            Nat.gcd a b = 1 → Nat.gcd a c = 1 → Nat.gcd b c = 1 →
            (a * b * c = 30 ∧ (a * b = 6 ∨ a * c = 6 ∨ b * c = 6)) ∨
            (a * b * c = 60 ∧ (a * b = 12 ∨ a * c = 12 ∨ b * c = 12)) := by decide
        rcases hn6 u₀ (Finset.mem_Icc.mpr ⟨hu₀_2, hu₀_lt7⟩)
            u₁ (Finset.mem_Icc.mpr ⟨hu₁_2, hu₁_lt7⟩)
            u₂ (Finset.mem_Icc.mpr ⟨hu₂_2, hu₂_lt7⟩)
            hc01.gcd_eq_one hc02.gcd_eq_one hc12.gcd_eq_one with
          ⟨hR30, hpair6⟩ | ⟨hR60, hpair12⟩
        · rw [hprod_eq] at hR30
          have hL7_le5 : L₇ ≤ 5 := by omega
          have hM_le41 : M ≤ 41 := by dsimp [L₇] at hL7_le5; omega
          have hM30 : M = 30 := by
            obtain ⟨k, hk⟩ := hRM; rw [hR30] at hk
            have hk1 : k = 1 := by
              by_contra hne1
              have hk0 : k = 0 ∨ 2 ≤ k := by omega
              rcases hk0 with rfl | hk2 <;> omega
            rw [hk, hk1, mul_one]
          exact exists_two_slots_M30_R30 hA_card hA_pos hA_le hAgcd hB₀_I hB₀_card hM30 hR30 hR_fac
        · rw [hprod_eq] at hR60
          have hL7_le11 : L₇ ≤ 11 := by omega
          have hM_le83 : M ≤ 83 := by dsimp [L₇] at hL7_le11; omega
          have hM60 : M = 60 := by
            obtain ⟨k, hk⟩ := hRM; rw [hR60] at hk
            have hk1 : k = 1 := by
              by_contra hne1
              have hk0 : k = 0 ∨ 2 ≤ k := by omega
              rcases hk0 with rfl | hk2 <;> omega
            rw [hk, hk1, mul_one]
          exact exists_two_slots_M60_R60 hB₀_card hM60 hR60
  · -- **Case 1 (`P_big.card = 1`)**: `P_big = {p}`, `q = p ^ t > L₇`, `R = q * R_small`, `M = c * q`.
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hbig1
    have hp_big : p ∈ P_big := by rw [hp_eq]; exact Finset.mem_singleton_self p
    have hp_mem : p ∈ R.primeFactors := (Finset.mem_filter.mp hp_big).1
    have hp_gt : L₇ < p ^ (R.factorization p) := (Finset.mem_filter.mp hp_big).2
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    let t := R.factorization p
    let q := p ^ t
    let R_small := ∏ r ∈ P_small, r ^ (R.factorization r)
    have ht1 : 1 ≤ t := by
      have hpd : p ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp_mem).2
      exact (hp_prime.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hpd)
    have hq_pos : 0 < q := pow_pos hp_prime.pos t
    have hR_small_pos : 0 < R_small := hPsmall_pos
    have hR_eq : R = q * R_small := by
      calc R = (∏ r ∈ P_big, r ^ (R.factorization r)) * R_small := hR_split
        _ = q * R_small := by rw [hp_eq, Finset.prod_singleton]
    have hq_R : q ∣ R := ⟨R_small, hR_eq⟩
    have hq_M : q ∣ M := dvd_trans hq_R hRM
    obtain ⟨c, hc_eq⟩ := hq_M
    have hM_eq : M = c * q := by rw [hc_eq, mul_comm]
    have hc1 : 1 ≤ c :=
      Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hM_eq; exact (by omega : M ≠ 0) hM_eq
    have hc6 : c ≤ 6 := by
      have hlt : c * q < 7 * q := by
        calc c * q = M := hM_eq.symm
          _ < 7 * (L₇ + 1) := hM_lt
          _ ≤ 7 * q := Nat.mul_le_mul_left 7 hp_gt
      exact Nat.lt_of_mul_lt_mul_right hlt |> fun h => by omega
    have hcop_q_Rsm : Nat.Coprime q R_small := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hr_mem := (Finset.mem_filter.mp hr).1
      have hr_pr := Nat.prime_of_mem_primeFactors hr_mem
      have hr_ne : p ≠ r := by
        intro heq
        have hlt_gt := (Finset.mem_filter.mp hr).2
        rw [← heq] at hlt_gt
        exact hlt_gt hp_gt
      exact ((Nat.coprime_primes hp_prime hr_pr).mpr hr_ne).pow _ _
    have hRsm_dvd_c : R_small ∣ c := by
      obtain ⟨k, hk⟩ := hRM
      rw [hR_eq, hc_eq] at hk
      have h1 : q * c = q * (R_small * k) := by rw [hk]; ring
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hq_pos h1⟩
    by_cases hsub_q : (consecInterval x M).filter (fun b => q ∣ b) ⊆ B₀
    · exact exists_two_slots_M_eq_c_mul_pow hA_card hA_pos hA_le hAgcd hM9 hB₀_I hB₀_card
        hR_pos hRM hq_R rfl hR_fac hp_prime ht1 hM_eq hc1 hc6 hsub_q
    · obtain ⟨w₁, hw₁_flt, hw₁_notB₀⟩ := Finset.not_subset.mp hsub_q
      rw [Finset.mem_filter] at hw₁_flt
      by_cases hRsm1 : R_small = 1
      · have hRq : R = q := by rw [hR_eq, hRsm1, mul_one]
        exact two_slots_of_one_dvd hw₁_flt.1 hw₁_notB₀ (hRq ▸ hw₁_flt.2) hR_pos.ne'
      · have hRsm_ge2 : 2 ≤ R_small := by omega
        by_cases h7Rsm : 7 * R_small ≤ M
        · obtain ⟨w₂, hw₂_I, hw₂_notB₀, hRsm_w₂⟩ :=
            exists_avoiding_multiple_in_consecInterval x M R_small B₀ hR_small_pos
              (le_trans (Nat.mul_le_mul_right _ (by omega : B₀.card + 1 ≤ 7)) h7Rsm)
          exact two_slots_of_coprime_dvd hR_eq hcop_q_Rsm hq_pos hR_small_pos
            hw₁_flt.1 hw₂_I hw₁_notB₀ hw₂_notB₀ hw₁_flt.2 hRsm_w₂
        · have hRsm_le6 : R_small ≤ 6 := le_trans (Nat.le_of_dvd (by omega) hRsm_dvd_c) hc6
          have hPsm_le : ∀ r ∈ P_small, r ^ (R.factorization r) ≤ L₇ := fun r hr =>
            Nat.le_of_not_lt (Finset.mem_filter.mp hr).2
          have hL7_lt_Rsm : L₇ < R_small := by
            have h7L : 7 * L₇ ≤ M := Nat.mul_div_le M 7
            omega
          have hRsm_eq6 : R_small = 6 := by
            have hnot_pp : ¬ (∃ r e : ℕ, r.Prime ∧ R_small = r ^ e ∧ R_small.factorization r = e) := by
              rintro ⟨r, e, hr_pr, hr_pow, _⟩
              have he1 : 1 ≤ e :=
                Nat.pos_of_ne_zero fun h => by rw [h, pow_zero] at hr_pow; omega
              have hr_dvd_R : r ∣ R := by
                rw [hR_eq, hr_pow]
                exact dvd_mul_of_dvd_right (dvd_pow_self r (by omega)) q
              have hr_mem : r ∈ R.primeFactors := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr ⟨hr_pr, hr_dvd_R⟩
              have hr_ne_p : r ≠ p := by
                intro heq
                have hd : p ∣ Nat.gcd q R_small :=
                  Nat.dvd_gcd (dvd_pow_self p (by omega)) (heq ▸ (by rw [hr_pow]; exact dvd_pow_self r (by omega)))
                rw [hcop_q_Rsm.gcd_eq_one] at hd
                exact hp_prime.not_dvd_one hd
              have hr_sm : r ∈ P_small := Finset.mem_filter.mpr ⟨hr_mem, fun hbig => by
                have hr_big : r ∈ P_big := Finset.mem_filter.mpr ⟨hr_mem, hbig⟩
                have hr_eq_p : r = p := Finset.mem_singleton.mp (hp_eq ▸ hr_big)
                exact hr_ne_p hr_eq_p⟩
              have hfac_eq : R.factorization r = R_small.factorization r := by
                rw [hR_eq, Nat.factorization_mul hq_pos.ne' hR_small_pos.ne', Finsupp.add_apply]
                have hq0 : q.factorization r = 0 := by
                  rw [Nat.Prime.factorization_pow hp_prime, Finsupp.single_apply, if_neg hr_ne_p.symm]
                omega
              have hpow_le := hPsm_le r hr_sm
              rw [hfac_eq, hr_pow, Nat.Prime.factorization_pow hr_pr, Finsupp.single_eq_same, ← hr_pow] at hpow_le
              omega
            have hRsm_cases : R_small = 2 ∨ R_small = 3 ∨ R_small = 4 ∨ R_small = 5 ∨ R_small = 6 := by omega
            rcases hRsm_cases with hR | hR | hR | hR | hR
            · exact absurd ⟨2, 1, by norm_num, by rw [hR, pow_one], by
                have hf : (2 ^ 1 : ℕ).factorization 2 = 1 := by
                  rw [Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
                rw [hR]; simpa using hf⟩ hnot_pp
            · exact absurd ⟨3, 1, by norm_num, by rw [hR, pow_one], by
                have hf : (3 ^ 1 : ℕ).factorization 3 = 1 := by
                  rw [Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
                rw [hR]; simpa using hf⟩ hnot_pp
            · exact absurd ⟨2, 2, by norm_num, by rw [hR]; norm_num, by
                have hf : (2 ^ 2 : ℕ).factorization 2 = 2 := by
                  rw [Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
                rw [hR]; simpa using hf⟩ hnot_pp
            · exact absurd ⟨5, 1, by norm_num, by rw [hR, pow_one], by
                have hf : (5 ^ 1 : ℕ).factorization 5 = 1 := by
                  rw [Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same]
                rw [hR]; simpa using hf⟩ hnot_pp
            · exact hR
          have hc_eq6 : c = 6 := by
            have := Nat.le_of_dvd (by omega) hRsm_dvd_c
            omega
          have h3_sm : 3 ∈ P_small := by
            have h3R : 3 ∣ R := by rw [hR_eq, hRsm_eq6]; exact dvd_mul_of_dvd_right (by norm_num) q
            have h3_mem : 3 ∈ R.primeFactors := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr ⟨by norm_num, h3R⟩
            refine Finset.mem_filter.mpr ⟨h3_mem, fun hbig => ?_⟩
            have h3_big : 3 ∈ P_big := Finset.mem_filter.mpr ⟨h3_mem, hbig⟩
            have h3p : 3 = p := Finset.mem_singleton.mp (hp_eq ▸ h3_big)
            have h3_cop : 3 ∣ Nat.gcd q R_small :=
              Nat.dvd_gcd (h3p ▸ dvd_pow_self p (by omega)) (by rw [hRsm_eq6]; norm_num)
            rw [hcop_q_Rsm.gcd_eq_one] at h3_cop; omega
          have h3_le_L7 : 3 ≤ L₇ := by
            have hle := hPsm_le 3 h3_sm
            have hfac3 : 1 ≤ R.factorization 3 :=
              ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization hR_pos.ne').mp
                (by rw [hR_eq, hRsm_eq6]; norm_num; exact dvd_mul_of_dvd_right (by norm_num) q)
            have h3_pow : 3 ≤ 3 ^ (R.factorization 3) := Nat.le_self_pow (by omega) 3
            omega
          have hM_ge21 : 21 ≤ M := by
            have h7L : 7 * L₇ ≤ M := Nat.mul_div_le M 7
            omega
          have hq_cases : q = 4 ∨ q = 5 ∨ q = 6 := by
            have h1 : M < 42 := by omega
            have h2 : 21 ≤ 6 * q := by rw [← hc_eq6, ← hM_eq]; exact hM_ge21
            have h3 : 6 * q < 42 := by rw [← hc_eq6, ← hM_eq]; exact h1
            omega
          have hq5 : q = 5 := by
            rcases hq_cases with hq4 | hq5 | hq6
            · exfalso
              have h2q : 2 ∣ Nat.gcd q R_small :=
                Nat.dvd_gcd (by rw [hq4]; norm_num) (by rw [hRsm_eq6]; norm_num)
              rw [hcop_q_Rsm.gcd_eq_one] at h2q; omega
            · exact hq5
            · exfalso
              have h2q : 2 ∣ Nat.gcd q R_small :=
                Nat.dvd_gcd (by rw [hq6]; norm_num) (by rw [hRsm_eq6]; norm_num)
              rw [hcop_q_Rsm.gcd_eq_one] at h2q; omega
          have hM30 : M = 30 := by rw [hM_eq, hc_eq6, hq5]
          have hR30 : R = 30 := by rw [hR_eq, hRsm_eq6, hq5]
          exact exists_two_slots_M30_R30 hA_card hA_pos hA_le hAgcd hB₀_I hB₀_card hM30 hR30 hR_fac
  · -- **Case 2 (`P_big.card = 2`)**: `P_big = {p₁, p₂}`, exact 5 finite configurations!
    obtain ⟨p₁, p₂, hp12, hPbig_eq⟩ := Finset.card_eq_two.mp hbig2
    have hp₁_big : p₁ ∈ P_big := by rw [hPbig_eq]; exact Finset.mem_insert_self p₁ {p₂}
    have hp₂_big : p₂ ∈ P_big := by rw [hPbig_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p₂)
    have hp₁_mem : p₁ ∈ R.primeFactors := (Finset.mem_filter.mp hp₁_big).1
    have hp₂_mem : p₂ ∈ R.primeFactors := (Finset.mem_filter.mp hp₂_big).1
    have hp₁_pr : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_mem
    have hp₂_pr : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_mem
    let q₁ := p₁ ^ (R.factorization p₁)
    let q₂ := p₂ ^ (R.factorization p₂)
    have hq₁_gt : L₇ < q₁ := (Finset.mem_filter.mp hp₁_big).2
    have hq₂_gt : L₇ < q₂ := (Finset.mem_filter.mp hp₂_big).2
    have hq₁_pos : 0 < q₁ := pow_pos hp₁_pr.pos _
    have hq₂_pos : 0 < q₂ := pow_pos hp₂_pr.pos _
    have hcop_q12 : Nat.Coprime q₁ q₂ := ((Nat.coprime_primes hp₁_pr hp₂_pr).mpr hp12).pow _ _
    have hPbig_prod : ∏ p ∈ P_big, p ^ (R.factorization p) = q₁ * q₂ := by
      rw [hPbig_eq, Finset.prod_pair hp12]
    have hq12_dvd_R : q₁ * q₂ ∣ R := by
      rw [hR_split, hPbig_prod]; exact dvd_mul_right (q₁ * q₂) _
    have hq12_dvd_M : q₁ * q₂ ∣ M := dvd_trans hq12_dvd_R hRM
    obtain ⟨k, hk_eq⟩ := hq12_dvd_M
    have hk_pos : 1 ≤ k :=
      Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk_eq; omega
    have hk_q2_lt7 : k * q₂ < 7 := by
      have h1 : q₁ * (k * q₂) < q₁ * 7 := by
        calc q₁ * (k * q₂) = M := by rw [hk_eq]; ring
          _ < 7 * (L₇ + 1) := hM_lt
          _ ≤ 7 * q₁ := Nat.mul_le_mul_left 7 hq₁_gt
          _ = q₁ * 7 := mul_comm 7 q₁
      exact Nat.lt_of_mul_lt_mul_left h1
    have hk_q1_lt7 : k * q₁ < 7 := by
      have h1 : q₂ * (k * q₁) < q₂ * 7 := by
        calc q₂ * (k * q₁) = M := by rw [hk_eq]; ring
          _ < 7 * (L₇ + 1) := hM_lt
          _ ≤ 7 * q₂ := Nat.mul_le_mul_left 7 hq₂_gt
          _ = q₂ * 7 := mul_comm 7 q₂
      exact Nat.lt_of_mul_lt_mul_left h1
    have hq₁_ge2 : 2 ≤ q₁ := by
      have h1d : p₁ ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp₁_mem).2
      have he1 : 1 ≤ R.factorization p₁ :=
        (hp₁_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h1d)
      exact le_trans hp₁_pr.two_le (Nat.le_self_pow (by omega) p₁)
    have hq₂_ge2 : 2 ≤ q₂ := by
      have h2d : p₂ ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp₂_mem).2
      have he2 : 1 ≤ R.factorization p₂ :=
        (hp₂_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h2d)
      exact le_trans hp₂_pr.two_le (Nat.le_self_pow (by omega) p₂)
    have hq₁_le6 : q₁ ≤ 6 := by
      have h1 : 1 * q₁ ≤ k * q₁ := Nat.mul_le_mul_right q₁ hk_pos
      omega
    have hq₂_le6 : q₂ ≤ 6 := by
      have h1 : 1 * q₂ ≤ k * q₂ := Nat.mul_le_mul_right q₂ hk_pos
      omega
    have hq₁_ne6 : q₁ ≠ 6 := by
      intro h6
      have h2_q : 2 ∣ p₁ ^ (R.factorization p₁) := by dsimp only [q₁] at h6; rw [h6]; norm_num
      have h3_q : 3 ∣ p₁ ^ (R.factorization p₁) := by dsimp only [q₁] at h6; rw [h6]; norm_num
      have h2p : p₁ = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₁_pr).mp
        ((by norm_num : Nat.Prime 2).dvd_of_dvd_pow h2_q)).symm
      have h3p : p₁ = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₁_pr).mp
        ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow h3_q)).symm
      omega
    have hq₂_ne6 : q₂ ≠ 6 := by
      intro h6
      have h2_q : 2 ∣ p₂ ^ (R.factorization p₂) := by dsimp only [q₂] at h6; rw [h6]; norm_num
      have h3_q : 3 ∣ p₂ ^ (R.factorization p₂) := by dsimp only [q₂] at h6; rw [h6]; norm_num
      have h2p : p₂ = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₂_pr).mp
        ((by norm_num : Nat.Prime 2).dvd_of_dvd_pow h2_q)).symm
      have h3p : p₂ = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₂_pr).mp
        ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow h3_q)).symm
      omega
    have hq₁_le5 : q₁ ≤ 5 := by omega
    have hq₂_le5 : q₂ ≤ 5 := by omega
    have hk_le3 : k ≤ 3 := by
      have h1 : k * 2 ≤ k * q₁ := Nat.mul_le_mul_left k hq₁_ge2
      omega
    have hPsmall_eq1 : ∏ p ∈ P_small, p ^ (R.factorization p) = 1 := by
      by_contra hne1
      have hPsm_ge2 : 2 ≤ ∏ p ∈ P_small, p ^ (R.factorization p) := by omega
      have hPsm_dvd_k : (∏ p ∈ P_small, p ^ (R.factorization p)) ∣ k := by
        obtain ⟨m, hm⟩ := hRM
        rw [hR_split, hPbig_prod] at hm
        rw [hm] at hk_eq
        have hmul_pos : 0 < q₁ * q₂ := mul_pos hq₁_pos hq₂_pos
        have h1 : q₁ * q₂ * k = q₁ * q₂ * ((∏ p ∈ P_small, p ^ R.factorization p) * m) := by
          rw [← hk_eq]; ring
        exact ⟨m, Nat.eq_of_mul_eq_mul_left hmul_pos h1⟩
      have hk_ge2 : 2 ≤ k := le_trans hPsm_ge2 (Nat.le_of_dvd (by omega) hPsm_dvd_k)
      have hcop_Psm_q12 : Nat.Coprime (∏ p ∈ P_small, p ^ (R.factorization p)) (q₁ * q₂) := by
        apply Nat.Coprime.prod_left
        intro r hr
        have hr_mem := (Finset.mem_filter.mp hr).1
        have hr_pr := Nat.prime_of_mem_primeFactors hr_mem
        have hr_ne1 : r ≠ p₁ := fun heq => by
          have hlt := (Finset.mem_filter.mp hr).2
          rw [heq] at hlt; exact hlt hq₁_gt
        have hr_ne2 : r ≠ p₂ := fun heq => by
          have hlt := (Finset.mem_filter.mp hr).2
          rw [heq] at hlt; exact hlt hq₂_gt
        exact Nat.Coprime.mul_right
          (((Nat.coprime_primes hr_pr hp₁_pr).mpr hr_ne1).pow _ _)
          (((Nat.coprime_primes hr_pr hp₂_pr).mpr hr_ne2).pow _ _)
      have hPsm_le_k : ∏ p ∈ P_small, p ^ (R.factorization p) ≤ k := Nat.le_of_dvd (by omega) hPsm_dvd_k
      have h2_q1 : 2 * q₁ < 7 := by
        have : 2 * q₁ ≤ k * q₁ := Nat.mul_le_mul_right q₁ hk_ge2
        omega
      have h2_q2 : 2 * q₂ < 7 := by
        have : 2 * q₂ ≤ k * q₂ := Nat.mul_le_mul_right q₂ hk_ge2
        omega
      have hq₁_le3 : q₁ ≤ 3 := by omega
      have hq₂_le3 : q₂ ≤ 3 := by omega
      have hq12_23 : (q₁ = 2 ∧ q₂ = 3) ∨ (q₁ = 3 ∧ q₂ = 2) := by
        have hne : q₁ ≠ q₂ := fun heq => by
          have hd : q₁ ∣ Nat.gcd q₁ q₂ := Nat.dvd_gcd dvd_rfl (heq ▸ dvd_rfl)
          rw [hcop_q12.gcd_eq_one] at hd
          have hle := Nat.le_of_dvd (by norm_num) hd
          omega
        omega
      have hk_eq2_or3 : k = 2 ∨ k = 3 := by omega
      rcases hk_eq2_or3 with rfl | rfl
      · have hPsm2 : ∏ p ∈ P_small, p ^ (R.factorization p) = 2 := by omega
        rw [hPsm2] at hcop_Psm_q12
        rcases hq12_23 with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩ <;> rw [hq1, hq2] at hcop_Psm_q12 <;> norm_num at hcop_Psm_q12
      · have hPsm3 : ∏ p ∈ P_small, p ^ (R.factorization p) = 3 := by omega
        rw [hPsm3] at hcop_Psm_q12
        rcases hq12_23 with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩ <;> rw [hq1, hq2] at hcop_Psm_q12 <;> norm_num at hcop_Psm_q12
    have hR_q12 : R = q₁ * q₂ := by rw [hR_split, hPbig_prod, hPsmall_eq1, mul_one]
    have avoid_of_5_le_div : ∀ (p t q : ℕ), p.Prime → 1 ≤ t → q = p ^ t →
        5 * q ≤ M → 1 ≤ R.factorization p →
        ∃ w ∈ consecInterval x M, w ∉ B₀ ∧ q ∣ w := by
      intro p t q hp ht hq h5q hdef_p
      by_contra hall; push Not at hall
      have hsub : (consecInterval x M).filter (fun b => p ^ t ∣ b) ⊆ B₀ := by
        intro b hb; rw [Finset.mem_filter] at hb
        by_contra hbB₀; exact hall b hb.1 hbB₀ (hq ▸ hb.2)
      have h0 := layer_cake_deficit_le_of_pow_subset hA_card hA_pos hA_le hAgcd hB₀_I hp ht hsub
      have hc5 : 5 ≤ M / p ^ t := (Nat.le_div_iff_mul_le (pow_pos hp.pos t)).mpr (hq ▸ h5q)
      have hzero : 5 - M / p ^ t = 0 := by omega
      rw [hzero, zero_mul] at h0
      have hfac := hR_fac p hp
      omega
    have hcop_gcd := hcop_q12.gcd_eq_one
    have h9_mul : 9 ≤ q₁ * q₂ * k := by omega
    have h_enum : ∀ a ∈ Finset.Icc 2 5, ∀ b ∈ Finset.Icc 2 5, ∀ k₀ ∈ Finset.Icc 1 3,
        k₀ * a < 7 → k₀ * b < 7 → Nat.gcd a b = 1 → 9 ≤ a * b * k₀ →
        (a = 2 ∧ b = 3 ∧ k₀ = 2) ∨ (a = 3 ∧ b = 2 ∧ k₀ = 2) ∨
        (a = 2 ∧ b = 5 ∧ k₀ = 1) ∨ (a = 5 ∧ b = 2 ∧ k₀ = 1) ∨
        (a = 3 ∧ b = 4 ∧ k₀ = 1) ∨ (a = 4 ∧ b = 3 ∧ k₀ = 1) ∨
        (a = 3 ∧ b = 5 ∧ k₀ = 1) ∨ (a = 5 ∧ b = 3 ∧ k₀ = 1) ∨
        (a = 4 ∧ b = 5 ∧ k₀ = 1) ∨ (a = 5 ∧ b = 4 ∧ k₀ = 1) := by decide
    have close_two_primes : ∀ a b : ℕ, a.Prime → b.Prime → R = a * b → a ≠ b →
        ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
          ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
      intro a b ha hb hRab hne
      have haR : 1 ≤ R.factorization a :=
        (ha.pow_dvd_iff_le_factorization hR_pos.ne').mp (by rw [hRab, pow_one]; exact dvd_mul_right a b)
      have hbR : 1 ≤ R.factorization b :=
        (hb.pow_dvd_iff_le_factorization hR_pos.ne').mp (by rw [hRab, pow_one]; exact dvd_mul_left b a)
      obtain ⟨w₁, hw₁_I, hw₁_notB₀, ha_w₁⟩ := exists_prime_multiple_avoiding_of_deficit_pos
        hA_card hA_pos hA_le hAgcd hB₀_I ha (by rw [← hR_fac a ha]; exact haR)
      obtain ⟨w₂, hw₂_I, hw₂_notB₀, hb_w₂⟩ := exists_prime_multiple_avoiding_of_deficit_pos
        hA_card hA_pos hA_le hAgcd hB₀_I hb (by rw [← hR_fac b hb]; exact hbR)
      exact two_slots_of_coprime_dvd hRab ((Nat.coprime_primes ha hb).mpr hne)
        ha.pos hb.pos hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ ha_w₁ hb_w₂
    have close_12 : M = 12 → R = 12 →
        ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
          ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
      intro hM12 hR12
      exact exists_two_slots_M12_R4_or_R12 hA_card hA_pos hA_le hAgcd hB₀_I hM12 hR_pos
        (by rw [hR12]) (by rw [hR12]; norm_num) hR_fac
    have close_20 : M = 20 → R = 20 →
        ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
          ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
      intro hM20 hR20
      have h2R : 1 ≤ R.factorization 2 :=
        ((by norm_num : Nat.Prime 2).pow_dvd_iff_le_factorization hR_pos.ne').mp
          (by rw [hR20, pow_one]; norm_num)
      have h5R : 1 ≤ R.factorization 5 :=
        ((by norm_num : Nat.Prime 5).pow_dvd_iff_le_factorization hR_pos.ne').mp
          (by rw [hR20, pow_one]; norm_num)
      obtain ⟨w₁, hw₁_I, hw₁_notB₀, h4_w₁⟩ := avoid_of_5_le_div 2 2 4 (by norm_num) (by omega)
        (by norm_num) (hM20 ▸ by norm_num) h2R
      obtain ⟨w₂, hw₂_I, hw₂_notB₀, h5_w₂⟩ := exists_prime_multiple_avoiding_of_deficit_pos
        hA_card hA_pos hA_le hAgcd hB₀_I (p := 5) (by norm_num) (by rw [← hR_fac 5 (by norm_num)]; exact h5R)
      exact two_slots_of_coprime_dvd hR20 (by norm_num) (by norm_num) (by norm_num)
        hw₁_I hw₂_I hw₁_notB₀ hw₂_notB₀ h4_w₁ h5_w₂
    rcases h_enum q₁ (Finset.mem_Icc.mpr ⟨hq₁_ge2, hq₁_le5⟩)
        q₂ (Finset.mem_Icc.mpr ⟨hq₂_ge2, hq₂_le5⟩)
        k (Finset.mem_Icc.mpr ⟨hk_pos, hk_le3⟩)
        hk_q1_lt7 hk_q2_lt7 hcop_gcd h9_mul with
      ⟨hq1, hq2, hk0⟩ | ⟨hq1, hq2, hk0⟩ |
      ⟨hq1, hq2, hk0⟩ | ⟨hq1, hq2, hk0⟩ |
      ⟨hq1, hq2, hk0⟩ | ⟨hq1, hq2, hk0⟩ |
      ⟨hq1, hq2, hk0⟩ | ⟨hq1, hq2, hk0⟩ |
      ⟨hq1, hq2, hk0⟩ | ⟨hq1, hq2, hk0⟩
    · exact close_two_primes 2 3 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_two_primes 3 2 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_two_primes 2 5 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_two_primes 5 2 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_12 (by rw [hk_eq, hq1, hq2, hk0]) (by rw [hR_q12, hq1, hq2])
    · exact close_12 (by rw [hk_eq, hq1, hq2, hk0]) (by rw [hR_q12, hq1, hq2])
    · exact close_two_primes 3 5 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_two_primes 5 3 (by norm_num) (by norm_num) (by rw [hR_q12, hq1, hq2]) (by norm_num)
    · exact close_20 (by rw [hk_eq, hq1, hq2, hk0]) (by rw [hR_q12, hq1, hq2])
    · exact close_20 (by rw [hk_eq, hq1, hq2, hk0]) (by rw [hR_q12, hq1, hq2])

/-! ## Part 5: Master Conditional Reduction (`SatisfiesBound 5 6 → SatisfiesBound 6 8`) -/

/-- **Unconditional Reduction `g(5) ≤ 6 → g(6) ≤ 8`**:
    assuming `SatisfiesBound 5 6`, every 6-element valid set `A ⊆ [2, ∞)` has a cover `B`
    of size at most `8` in every consecutive interval `consecInterval x (max A)`. -/
theorem erdos708_upper_six_of_upper_five (hg5 : SatisfiesBound 5 6) : SatisfiesBound 6 8 := by
  suffices hmain : ∀ M : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty), IsValidSet A 6 →
      A.max' hA = M → ∀ x : ℕ, ∃ B ⊆ consecInterval x M, B.card ≤ 8 ∧ IsCover A B by
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
    have hsup_eq : A.sup id = M := by rw [sup_id_eq_max' hA, hM]
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
      have hC_card : C.card = 6 := by rw [Finset.card_image_of_injOn hinj_div, hA_card]
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
        have hC'_card : C'.card = 5 := by rw [Finset.card_erase_of_mem h1C, hC_card]
        have hC'_ne : C'.Nonempty := Finset.card_pos.mp (by omega)
        have hC'_valid : IsValidSet C' 5 := by
          refine ⟨hC'_card, ?_⟩
          intro c hc
          have hmem := Finset.mem_erase.mp hc
          have hc1 := hC_pos c hmem.2
          omega
        have hC'_max_le : C'.max' hC'_ne ≤ M / g := by
          apply Finset.max'_le
          intro c hc
          exact hC_le c (Finset.mem_erase.mp hc).2
        obtain ⟨B', hB'I, hB'card, hB'cov⟩ := hg5 C' hC'_ne hC'_valid (x / g)
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
        have hC_valid : IsValidSet C 6 := by
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
      by_cases hM8 : M ≤ 8
      · have hsup_le : A.sup id ≤ 8 := by omega
        obtain ⟨B, hBI, hBcard, hBcov⟩ := erdos708_upper_six_of_max_le_eight hA_pos hsup_le x
        rw [hsup_eq] at hBI
        exact ⟨B, hBI, hBcard, hBcov⟩
      · have hM9 : 9 ≤ M := by omega
        have hM_mem : M ∈ A := hM ▸ Finset.max'_mem A hA
        let A' := A.erase M
        have hA'_card : A'.card = 5 := by rw [Finset.card_erase_of_mem hM_mem, hA_card]
        have hA'_ne : A'.Nonempty := Finset.card_pos.mp (by omega)
        have hA'_valid : IsValidSet A' 5 :=
          ⟨hA'_card, fun a ha => hA_ge2 a (Finset.mem_erase.mp ha).2⟩
        have hA'_max_le : A'.max' hA'_ne ≤ M := by
          apply Finset.max'_le
          intro a ha
          exact hA_le a (Finset.mem_erase.mp ha).2
        obtain ⟨B₀, hB₀_I', hB₀_card, hB₀_cov⟩ := hg5 A' hA'_ne hA'_valid x
        have hB₀_I : B₀ ⊆ consecInterval x M := by
          intro b hb
          have hb' := hB₀_I' hb
          simp only [consecInterval, Finset.mem_Icc] at hb' ⊢
          exact ⟨hb'.1, by omega⟩
        have hA_eq : A = insert M A' := (Finset.insert_erase hM_mem).symm
        have hM_notA' : M ∉ A' := Finset.notMem_erase M A
        have hA'0 : ∀ a ∈ A', a ≠ 0 := fun a ha => (hA_pos a (Finset.mem_erase.mp ha).2).ne'
        have hB₀0 : ∀ b ∈ B₀, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hB₀_I hb)).ne'
        have hcov'_sum : ∀ p : ℕ, ∑ a ∈ A', a.factorization p ≤ ∑ b ∈ B₀, b.factorization p :=
          fun p => sum_factorization_le_of_isCover hA'0 hB₀0 hB₀_cov p
        have hdef_le_M : ∀ p : ℕ,
            (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ M.factorization p := by
          intro p
          have h1 : ∑ a ∈ A, a.factorization p =
              M.factorization p + ∑ a ∈ A', a.factorization p := by
            rw [hA_eq, Finset.sum_insert hM_notA']
          have h2 := hcov'_sum p
          omega
        let R : ℕ := ∏ p ∈ M.primeFactors,
          p ^ ((∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p))
        have hR_pos : 0 < R := Finset.prod_pos (fun p hp =>
          pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
        have hR_fac : ∀ p : ℕ, p.Prime →
            R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) := by
          intro p hp
          have hterm_ne : ∀ q ∈ M.primeFactors,
              q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q)) ≠ 0 :=
            fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
          rw [Nat.factorization_prod hterm_ne]
          simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
          have hterm : ∀ q ∈ M.primeFactors,
              (q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q))).factorization p =
                if q = p then (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q) else 0 := by
            intro q hq
            rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hq), Finsupp.single_apply]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
          split_ifs with hp_mem
          · rfl
          · have hfac0 : M.factorization p = 0 := by
              rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hp_mem
              exact hp_mem
            have hle := hdef_le_M p
            rw [hfac0] at hle
            omega
        have hRM : R ∣ M := by
          rw [← Nat.factorization_le_iff_dvd hR_pos.ne' (by omega)]
          intro p
          by_cases hp : p.Prime
          · rw [hR_fac p hp]; exact hdef_le_M p
          · rw [Nat.factorization_eq_zero_of_not_prime R hp]; exact Nat.zero_le _
        obtain ⟨B₁, hB₁_I, hdisj, hB₁_card, hB₁_val⟩ := exists_two_slots_for_R_dvd_M
          hA_card hA_pos hA_le hg_eq1 hM9 hB₀_I hB₀_card hR_pos hRM hR_fac
        refine ⟨B₀ ∪ B₁, Finset.union_subset hB₀_I hB₁_I, ?_, ?_⟩
        · have h1 := Finset.card_union_le B₀ B₁
          omega
        · apply isCover_union_of_disjoint_factorization
            (fun a ha => (hA_pos a ha).ne')
            hB₀0
            (fun b hb => (pos_of_mem_consecInterval (hB₁_I hb)).ne')
            hdisj
          intro p hp
          have h1 := hR_fac p hp
          have h2 := hB₁_val p hp
          omega

#print axioms erdos708_upper_six_of_upper_five

end Erdos708
