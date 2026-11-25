import Erdos708.Lower
import Erdos708.UpperCore

/-!
# PPL 176 (Erdős Problem #708) — Sharp `g(6) ≥ 8`, Exact `g(3) = 4`, and `g(6) ≤ 8` Foundations

## Main Results (complete proofs, zero custom axioms, `leanchecker: PASS`)
1. **`erdos708_lower_six_sharp`** (`g(6) ≥ 8`):
   Improves `erdos708_lower_six` (`g(6) ≥ 7`) from `Erdos708.Lower` to the sharp lower bound
   `¬ SatisfiesBound 6 7` via the explicit CRT witness
   `A₆ = {851, 943, 1073, 1147, 1189, 1271} = {23, 29, 31} × {37, 41}` (`M = 1271`), matching
   the computational Branch-and-Bound minimum (`|B| = 8`) in `erdos708_lower_results.json`.
2. **`erdos708_upper_three` & `erdos708_exact_three`** (`g(3) = 4`):
   Complete unconditional proof of `SatisfiesBound 3 4` (`g(3) ≤ 4`), combined with
   `erdos708_lower_three` (`g(3) ≥ 4`) to settle `g(3) = 4` cleanly without large case explosion.
3. **`g(6) ≤ 8` Foundation Lemmas**:
   - `erdos708_upper_six_of_omega_le_eight`: `∑ a ∈ A, a.primeFactors.card ≤ 8 → Erdos708Covers A m 8`
   - `erdos708_upper_six_of_max_le_eight`: `A.sup id ≤ 8 → Erdos708Covers A m 8`
   - `erdos708_upper_six_of_hall_six`: injective Hall map in `[x+1, x+M]` gives `B.card ≤ 6` cover.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Sharp Lower Bound `g(6) ≥ 8` -/

private lemma lower_six_A6_card :
    ({851, 943, 1073, 1147, 1189, 1271} : Finset ℕ).card = 6 := by decide

private lemma lower_six_A6_nonempty :
    ({851, 943, 1073, 1147, 1189, 1271} : Finset ℕ).Nonempty := by decide

private lemma lower_six_A6_max :
    ({851, 943, 1073, 1147, 1189, 1271} : Finset ℕ).max' lower_six_A6_nonempty = 1271 := by
  apply le_antisymm
  · apply Finset.max'_le
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · exact Finset.le_max' _ 1271 (by decide)

/-- Sharp lower bound for `n = 6`: `g(6) ≥ 8`, proved via CRT on
    `A₆ = {851, 943, 1073, 1147, 1189, 1271} = {23, 29, 31} × {37, 41}` (`M = 1271`). -/
theorem erdos708_lower_six_sharp : ¬ SatisfiesBound 6 7 := by
  intro hbound
  set A6 : Finset ℕ := {851, 943, 1073, 1147, 1189, 1271}
  set P6 : Finset ℕ := {23, 29, 31, 37, 41}
  have hvalid : IsValidSet A6 6 := by
    refine ⟨lower_six_A6_card, ?_⟩
    intro a ha
    simp only [A6, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hA0 : ∀ a ∈ A6, a ≠ 0 := fun a ha => by
    have := hvalid.2 a ha; omega
  let mfn : ℕ → ℕ := fun p => p ^ 2
  let ffn : ℕ → ℕ := fun p =>
    if p = 37 then 666 else if p = 41 then 820 else p
  have hm_pos : ∀ u ∈ P6, 0 < mfn u := fun u hu => by
    simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> norm_num [mfn]
  have hcop : ∀ u ∈ P6, ∀ v ∈ P6, u ≠ v → Nat.Coprime (mfn u) (mfn v) := by
    intro u hu v hv huv
    simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl huv | norm_num [mfn]
  obtain ⟨b₀, hb0_gt, hb0_mod⟩ := exists_crt_finset P6 mfn ffn hm_pos hcop 635
  have hb0_ne0 : b₀ ≠ 0 := by omega
  set x : ℕ := b₀ - 636
  have hmax : A6.max' lower_six_A6_nonempty = 1271 := lower_six_A6_max
  obtain ⟨B, hBI_raw, hBcard, hcov⟩ := hbound A6 lower_six_A6_nonempty hvalid x
  have hBI : B ⊆ consecInterval x 1271 := by
    rw [hmax] at hBI_raw; exact hBI_raw
  have hB0 : ∀ b ∈ B, b ≠ 0 := fun b hb =>
    (pos_of_mem_consecInterval (hBI hb)).ne'
  have hI_bounds : ∀ b ∈ consecInterval x 1271, b₀ - 635 ≤ b ∧ b ≤ b₀ + 635 := by
    intro b hb
    simp only [consecInterval, Finset.mem_Icc] at hb
    omega
  -- CRT congruences for each prime in P6
  have h23 : b₀ ≡ 23 [MOD 529] := by simpa [mfn, ffn] using hb0_mod 23 (by decide)
  have h29 : b₀ ≡ 29 [MOD 841] := by simpa [mfn, ffn] using hb0_mod 29 (by decide)
  have h31 : b₀ ≡ 31 [MOD 961] := by simpa [mfn, ffn] using hb0_mod 31 (by decide)
  have h37 : b₀ ≡ 666 [MOD 1369] := by simpa [mfn, ffn] using hb0_mod 37 (by decide)
  have h41 : b₀ ≡ 820 [MOD 1681] := by simpa [mfn, ffn] using hb0_mod 41 (by decide)
  -- Divisibility of `b₀` by each `p ∈ P6`
  have h23_b0 : 23 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := Nat.ModEq.of_dvd (by norm_num : 23 ∣ 529) h23
    simpa [Nat.ModEq] using this)
  have h29_b0 : 29 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := Nat.ModEq.of_dvd (by norm_num : 29 ∣ 841) h29
    simpa [Nat.ModEq] using this)
  have h31_b0 : 31 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := Nat.ModEq.of_dvd (by norm_num : 31 ∣ 961) h31
    simpa [Nat.ModEq] using this)
  have h37_b0 : 37 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := Nat.ModEq.of_dvd (by norm_num : 37 ∣ 1369) h37
    simpa [Nat.ModEq] using this)
  have h41_b0 : 41 ∣ b₀ := Nat.dvd_of_mod_eq_zero (by
    have := Nat.ModEq.of_dvd (by norm_num : 41 ∣ 1681) h41
    simpa [Nat.ModEq] using this)
  -- `p^2 ∤ b₀` for all `p ∈ P6`
  have not_dvd_of_mod_pos : ∀ {m r : ℕ}, 0 < r → r < m → b₀ ≡ r [MOD m] → ¬ (m ∣ b₀) := by
    intro m r hrpos hrm hmod hd
    have h0 : b₀ % m = 0 := Nat.mod_eq_zero_of_dvd hd
    have hmod' : b₀ % m = r % m := hmod
    rw [h0, Nat.mod_eq_of_lt hrm] at hmod'
    omega
  have h529_nb0 : ¬ (529 ∣ b₀) := not_dvd_of_mod_pos (by norm_num) (by norm_num) h23
  have h841_nb0 : ¬ (841 ∣ b₀) := not_dvd_of_mod_pos (by norm_num) (by norm_num) h29
  have h961_nb0 : ¬ (961 ∣ b₀) := not_dvd_of_mod_pos (by norm_num) (by norm_num) h31
  have h1369_nb0 : ¬ (1369 ∣ b₀) := not_dvd_of_mod_pos (by norm_num) (by norm_num) h37
  have h1681_nb0 : ¬ (1681 ∣ b₀) := not_dvd_of_mod_pos (by norm_num) (by norm_num) h41
  -- Exact valuation 1 of `b₀` at each `p ∈ P6`
  have hv_b0_eq1 : ∀ p ∈ P6, b₀.factorization p = 1 := by
    intro p hp
    have hp_prime : Nat.Prime p := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hp_dvd : p ∣ b₀ := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hp2_ndvd : ¬ (p ^ 2 ∣ b₀) := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · norm_num; exact h529_nb0
      · norm_num; exact h841_nb0
      · norm_num; exact h961_nb0
      · norm_num; exact h1369_nb0
      · norm_num; exact h1681_nb0
    have h1 : 1 ≤ b₀.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp_prime hb0_ne0).mp (by simpa using hp_dvd)
    have h2 : ¬ (2 ≤ b₀.factorization p) := fun hge =>
      hp2_ndvd ((Nat.Prime.pow_dvd_iff_le_factorization hp_prime hb0_ne0).mpr hge)
    omega
  -- On the entire interval `I`, `b.factorization 37 ≤ 1` and `b.factorization 41 ≤ 1`
  have hv37_le1 : ∀ b ∈ consecInterval x 1271, b.factorization 37 ≤ 1 := by
    intro b hb
    have ⟨hlo, hhi⟩ := hI_bounds b hb
    have hnd : ¬ (1369 ∣ b) := not_dvd_of_modEq_and_dist (by norm_num) h37 hlo hhi (le_of_lt hb0_gt)
      (by norm_num) (by norm_num)
    have h37sq : (37 ^ 2 : ℕ) = 1369 := by norm_num
    by_contra hgt
    have hge2 : 2 ≤ b.factorization 37 := Nat.lt_of_not_ge hgt
    exact hnd (h37sq ▸ (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num)
      (pos_of_mem_consecInterval hb).ne').mpr hge2)
  have hv41_le1 : ∀ b ∈ consecInterval x 1271, b.factorization 41 ≤ 1 := by
    intro b hb
    have ⟨hlo, hhi⟩ := hI_bounds b hb
    have hnd : ¬ (1681 ∣ b) := not_dvd_of_modEq_and_dist (by norm_num) h41 hlo hhi (le_of_lt hb0_gt)
      (by norm_num) (by norm_num)
    have h41sq : (41 ^ 2 : ℕ) = 1681 := by norm_num
    by_contra hgt
    have hge2 : 2 ≤ b.factorization 41 := Nat.lt_of_not_ge hgt
    exact hnd (h41sq ▸ (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num)
      (pos_of_mem_consecInterval hb).ne').mpr hge2)
  -- No element of `B \ {b₀}` is divisible by two distinct primes from `P6` (`23 * 29 = 667 > 635`)
  have hsep : ∀ b ∈ B.erase b₀, ∀ u ∈ P6, ∀ v ∈ P6, u ≠ v → u ∣ b → ¬ (v ∣ b) := by
    intro b hb u hu v hv huv hub hvb
    have hne : b ≠ b₀ := (Finset.mem_erase.mp hb).1
    have hbI : b ∈ consecInterval x 1271 := hBI (Finset.mem_erase.mp hb).2
    have ⟨hlo, hhi⟩ := hI_bounds b hbI
    have hu_b0 : u ∣ b₀ := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hv_b0 : v ∣ b₀ := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hcop_uv : Nat.Coprime u v := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl huv | norm_num
    have huv_ge : 667 ≤ u * v := by
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl huv | norm_num
    clear h23 h29 h31 h37 h41 h23_b0 h29_b0 h31_b0 h37_b0 h41_b0 h529_nb0 h841_nb0 h961_nb0 h1369_nb0 h1681_nb0 hb0_mod
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have huv_sub : u * v ∣ b₀ - b :=
        hcop_uv.mul_dvd_of_dvd_of_dvd (Nat.dvd_sub hu_b0 hub) (Nat.dvd_sub hv_b0 hvb)
      have hle := Nat.le_of_dvd (by omega) huv_sub
      omega
    · have huv_sub : u * v ∣ b - b₀ :=
        hcop_uv.mul_dvd_of_dvd_of_dvd (Nat.dvd_sub hub hu_b0) (Nat.dvd_sub hvb hv_b0)
      have hle := Nat.le_of_dvd (by omega) huv_sub
      omega
  clear h23 h29 h31 h37 h41 h23_b0 h29_b0 h31_b0 h37_b0 h41_b0 h529_nb0 h841_nb0 h961_nb0 h1369_nb0 h1681_nb0 hb0_mod
  -- Required valuations in `B`: `2` for `23, 29, 31` and `3` for `37, 41`
  have hprod_eq : ∏ a ∈ A6, a = 23 ^ 2 * 29 ^ 2 * 31 ^ 2 * 37 ^ 3 * 41 ^ 3 := by
    simp only [A6]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
  have hreq : ∀ p ∈ P6, (if p = 37 ∨ p = 41 then 3 else 2) ≤ ∑ b ∈ B, b.factorization p := by
    intro p hp
    have hle := sum_factorization_le_of_isCover hA0 hB0 hcov p
    have hfacA : ∑ a ∈ A6, a.factorization p = (if p = 37 ∨ p = 41 then 3 else 2) := by
      rw [← factorization_finset_prod _ hA0 p, hprod_eq,
          Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity),
          Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 23),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 29),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 31),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 37),
          Nat.Prime.factorization_pow (by norm_num : Nat.Prime 41)]
      simp only [P6, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp
    omega
  have hsum_card := sum_card_filter_le_of_no_two_primes P6 (B.erase b₀) hsep
  have hsum_expand :
      ∑ u ∈ P6, ((B.erase b₀).filter (fun b => u ∣ b)).card =
        ((B.erase b₀).filter (fun b => 23 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 29 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 31 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 37 ∣ b)).card +
        ((B.erase b₀).filter (fun b => 41 ∣ b)).card := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hsum_expand] at hsum_card
  have hpos_card_of_sum_pos : ∀ (S : Finset ℕ) (p : ℕ),
      1 ≤ ∑ b ∈ S, b.factorization p → 1 ≤ (S.filter (fun b => p ∣ b)).card := by
    intro S p hs
    rw [sum_factorization_eq_filter] at hs
    by_contra hlt
    have h0 : (S.filter (fun b => p ∣ b)).card = 0 := by omega
    rw [Finset.card_eq_zero.mp h0] at hs
    simp at hs
  by_cases hb0B : b₀ ∈ B
  · have hcard_er : (B.erase b₀).card + 1 = B.card := by
      rw [Finset.card_erase_of_mem hb0B]
      have := Finset.card_pos.mpr ⟨b₀, hb0B⟩
      omega
    have hsplit : ∀ p : ℕ, ∑ b ∈ B, b.factorization p =
        b₀.factorization p + ∑ b ∈ B.erase b₀, b.factorization p := fun p =>
      (Finset.add_sum_erase B (fun b => b.factorization p) hb0B).symm
    have hc23 : 1 ≤ ((B.erase b₀).filter (fun b => 23 ∣ b)).card := by
      apply hpos_card_of_sum_pos
      have hr := hreq 23 (by decide); norm_num at hr; have hv := hv_b0_eq1 23 (by decide); rw [hsplit 23] at hr; omega
    have hc29 : 1 ≤ ((B.erase b₀).filter (fun b => 29 ∣ b)).card := by
      apply hpos_card_of_sum_pos
      have hr := hreq 29 (by decide); norm_num at hr; have hv := hv_b0_eq1 29 (by decide); rw [hsplit 29] at hr; omega
    have hc31 : 1 ≤ ((B.erase b₀).filter (fun b => 31 ∣ b)).card := by
      apply hpos_card_of_sum_pos
      have hr := hreq 31 (by decide); norm_num at hr; have hv := hv_b0_eq1 31 (by decide); rw [hsplit 31] at hr; omega
    have hc37 : 2 ≤ ((B.erase b₀).filter (fun b => 37 ∣ b)).card := by
      have h1 : ∑ b ∈ B.erase b₀, b.factorization 37 ≤
          ((B.erase b₀).filter (fun b => 37 ∣ b)).card := by
        rw [sum_factorization_eq_filter]
        calc ∑ b ∈ (B.erase b₀).filter (fun b => 37 ∣ b), b.factorization 37
            ≤ ∑ _b ∈ (B.erase b₀).filter (fun b => 37 ∣ b), 1 := by
              apply Finset.sum_le_sum
              intro b hb
              exact hv37_le1 b (hBI (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2)
          _ = ((B.erase b₀).filter (fun b => 37 ∣ b)).card := by simp
      have hr := hreq 37 (by decide); norm_num at hr; have hv := hv_b0_eq1 37 (by decide); rw [hsplit 37] at hr; omega
    have hc41 : 2 ≤ ((B.erase b₀).filter (fun b => 41 ∣ b)).card := by
      have h1 : ∑ b ∈ B.erase b₀, b.factorization 41 ≤
          ((B.erase b₀).filter (fun b => 41 ∣ b)).card := by
        rw [sum_factorization_eq_filter]
        calc ∑ b ∈ (B.erase b₀).filter (fun b => 41 ∣ b), b.factorization 41
            ≤ ∑ _b ∈ (B.erase b₀).filter (fun b => 41 ∣ b), 1 := by
              apply Finset.sum_le_sum
              intro b hb
              exact hv41_le1 b (hBI (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).2)
          _ = ((B.erase b₀).filter (fun b => 41 ∣ b)).card := by simp
      have hr := hreq 41 (by decide); norm_num at hr; have hv := hv_b0_eq1 41 (by decide); rw [hsplit 41] at hr; omega
    omega
  · have h_er : B.erase b₀ = B := Finset.erase_eq_of_notMem hb0B
    rw [h_er] at hsum_card
    have hc23 : 1 ≤ (B.filter (fun b => 23 ∣ b)).card :=
      hpos_card_of_sum_pos B 23 (by have hr := hreq 23 (by decide); norm_num at hr; omega)
    have hc29 : 1 ≤ (B.filter (fun b => 29 ∣ b)).card :=
      hpos_card_of_sum_pos B 29 (by have hr := hreq 29 (by decide); norm_num at hr; omega)
    have hc31 : 1 ≤ (B.filter (fun b => 31 ∣ b)).card :=
      hpos_card_of_sum_pos B 31 (by have hr := hreq 31 (by decide); norm_num at hr; omega)
    have hc37 : 3 ≤ (B.filter (fun b => 37 ∣ b)).card := by
      have h1 : ∑ b ∈ B, b.factorization 37 ≤ (B.filter (fun b => 37 ∣ b)).card := by
        rw [sum_factorization_eq_filter]
        calc ∑ b ∈ B.filter (fun b => 37 ∣ b), b.factorization 37
            ≤ ∑ _b ∈ B.filter (fun b => 37 ∣ b), 1 := by
              apply Finset.sum_le_sum
              intro b hb
              exact hv37_le1 b (hBI (Finset.mem_filter.mp hb).1)
          _ = (B.filter (fun b => 37 ∣ b)).card := by simp
      have hr := hreq 37 (by decide); norm_num at hr; omega
    have hc41 : 3 ≤ (B.filter (fun b => 41 ∣ b)).card := by
      have h1 : ∑ b ∈ B, b.factorization 41 ≤ (B.filter (fun b => 41 ∣ b)).card := by
        rw [sum_factorization_eq_filter]
        calc ∑ b ∈ B.filter (fun b => 41 ∣ b), b.factorization 41
            ≤ ∑ _b ∈ B.filter (fun b => 41 ∣ b), 1 := by
              apply Finset.sum_le_sum
              intro b hb
              exact hv41_le1 b (hBI (Finset.mem_filter.mp hb).1)
          _ = (B.filter (fun b => 41 ∣ b)).card := by simp
      have hr := hreq 41 (by decide); norm_num at hr; omega
    omega

/-! ## Part 2: Exact Small Value `g(3) = 4` (`erdos708_upper_three` & `erdos708_exact_three`) -/

private lemma two_mul_gcd_le_of_lt_g6 {a₁ a₂ : ℕ} (ha₁ : 2 ≤ a₁) (hlt : a₁ < a₂) :
    2 * Nat.gcd a₁ a₂ ≤ a₂ := by
  set g := Nat.gcd a₁ a₂
  have hg2 : g ∣ a₂ := Nat.gcd_dvd_right a₁ a₂
  obtain ⟨k, hk⟩ := hg2
  have hg_le1 : g ≤ a₁ := Nat.gcd_le_left a₂ (by omega)
  have hk_ne0 : k ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hk; omega
  have hk_ne1 : k ≠ 1 := by
    intro h1; rw [h1, mul_one] at hk; omega
  have hk_ge2 : 2 ≤ k := by omega
  nlinarith

private lemma three_mul_le_of_three_distinct_dvd {d a₁ a₂ a₃ : ℕ}
    (ha₁ : 0 < a₁) (h12 : a₁ < a₂) (h23 : a₂ < a₃)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) :
    3 * d ≤ a₃ := by
  obtain ⟨q₁, rfl⟩ := hd1
  obtain ⟨q₂, rfl⟩ := hd2
  obtain ⟨q₃, rfl⟩ := hd3
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp at ha₁
    · exact hpos
  have hq1 : 1 ≤ q₁ := by nlinarith
  have hq12 : q₁ < q₂ := by nlinarith
  have hq23 : q₂ < q₃ := by nlinarith
  have hq3 : 3 ≤ q₃ := by omega
  nlinarith

private lemma three_mul_le_of_ne {d u v a₃ : ℕ}
    (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (hu3 : u < a₃) (hv3 : v < a₃)
    (hdu : d ∣ u) (hdv : d ∣ v) (hd3 : d ∣ a₃) :
    3 * d ≤ a₃ := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact three_mul_le_of_three_distinct_dvd hu hlt hv3 hdu hdv hd3
  · exact three_mul_le_of_three_distinct_dvd hv hgt hu3 hdv hdu hd3

private lemma exists_avoiding_multiple (x M d : ℕ) (S : Finset ℕ)
    (hd : 0 < d) (hbound : (S.card + 1) * d ≤ M) :
    ∃ b ∈ consecInterval x M, b ∉ S ∧ d ∣ b := by
  have hle_div : S.card + 1 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr hbound
  have hcard_flt := card_multiples_Icc_ge x M d hd
  change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at hcard_flt
  have hnot_sub : ¬ ((consecInterval x M).filter (fun b => d ∣ b) ⊆ S) := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨b, hb_mem, hb_notS⟩ := Finset.not_subset.mp hnot_sub
  rw [Finset.mem_filter] at hb_mem
  exact ⟨b, hb_mem.1, hb_notS, hb_mem.2⟩

private lemma cover_triple_when_one_dvd_b3 {x a₃ u v b₃ : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u ≠ v) (hu3 : u < a₃) (hv3 : v < a₃)
    (hb₃_I : b₃ ∈ consecInterval x a₃) (ha₃_b3 : a₃ ∣ b₃)
    (hu_b3 : u ∣ b₃) (hv_nb3 : ¬ (v ∣ b₃)) :
    ∃ B ⊆ consecInterval x a₃, B.card ≤ 4 ∧ u * v * a₃ ∣ ∏ b ∈ B, b := by
  obtain ⟨bv, hbv_I, hv_bv⟩ := exists_multiple_in_consecInterval x v a₃ (by omega) (by omega)
  have hbv_nb3 : bv ≠ b₃ := fun h => hv_nb3 (h ▸ hv_bv)
  set g := Nat.gcd u a₃
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left a₃ (by omega)
  have h2g : 2 * g ≤ a₃ := two_mul_gcd_le_of_lt_g6 hu hu3
  obtain ⟨bu, hbu_I, hbu_ne, hg_bu⟩ :=
    exists_avoiding_multiple x a₃ g {b₃} hg_pos (by simpa using h2g)
  have hbu_nb3 : bu ≠ b₃ := by simpa using hbu_ne
  have hlcm_b3 : Nat.lcm u a₃ ∣ b₃ := Nat.lcm_dvd hu_b3 ha₃_b3
  by_cases hbuv : bu = bv
  · subst hbuv
    set d := Nat.gcd v g
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left g (by omega)
    have hdu : d ∣ u := dvd_trans (Nat.gcd_dvd_right v g) (Nat.gcd_dvd_left u a₃)
    have hdv : d ∣ v := Nat.gcd_dvd_left v g
    have hd3 : d ∣ a₃ := dvd_trans (Nat.gcd_dvd_right v g) (Nat.gcd_dvd_right u a₃)
    have hS2 : ({b₃, bu} : Finset ℕ).card + 1 ≤ 3 := by
      have hcard_S := Finset.card_insert_le b₃ {bu}
      simp only [Finset.card_singleton] at hcard_S
      omega
    obtain ⟨c, hc_I, hc_ne, hd_c⟩ := exists_avoiding_multiple x a₃ d {b₃, bu} hd_pos
      (le_trans (Nat.mul_le_mul_right d hS2) (three_mul_le_of_ne (by omega) (by omega) huv hu3 hv3 hdu hdv hd3))
    have hc_nb3 : c ≠ b₃ := fun h => hc_ne (by simp [h])
    have hc_nbu : c ≠ bu := fun h => hc_ne (by simp [h])
    refine ⟨{b₃, bu, c}, by simp [Finset.insert_subset_iff, hb₃_I, hbu_I, hc_I], ?_, ?_⟩
    · have h1 := Finset.card_insert_le b₃ {bu, c}
      have h2 := Finset.card_insert_le bu {c}
      simp at h1 h2; omega
    · have hprod : ∏ b ∈ ({b₃, bu, c} : Finset ℕ), b = b₃ * (bu * c) := by
        rw [Finset.prod_insert (by simp [hbu_nb3.symm, hc_nb3.symm]),
            Finset.prod_insert (by simp [hc_nbu.symm]), Finset.prod_singleton]
      rw [hprod]
      have hlcm_vg : Nat.lcm v g ∣ bu := Nat.lcm_dvd hv_bv hg_bu
      calc u * v * a₃
          = (u * a₃) * v := by ring
        _ = (Nat.lcm u a₃ * g) * v := by rw [Nat.lcm_mul_gcd u a₃]
        _ = Nat.lcm u a₃ * (v * g) := by ring
        _ = Nat.lcm u a₃ * (Nat.lcm v g * d) := by rw [Nat.lcm_mul_gcd v g]
        _ ∣ b₃ * (bu * c) := mul_dvd_mul hlcm_b3 (mul_dvd_mul hlcm_vg hd_c)
  · refine ⟨{b₃, bu, bv}, by simp [Finset.insert_subset_iff, hb₃_I, hbu_I, hbv_I], ?_, ?_⟩
    · have h1 := Finset.card_insert_le b₃ {bu, bv}
      have h2 := Finset.card_insert_le bu {bv}
      simp at h1 h2; omega
    · have hprod : ∏ b ∈ ({b₃, bu, bv} : Finset ℕ), b = b₃ * bu * bv := by
        rw [Finset.prod_insert (by simp [hbu_nb3.symm, hbv_nb3.symm]),
            Finset.prod_insert (by simp [hbuv]), Finset.prod_singleton]
        ring
      rw [hprod]
      calc u * v * a₃
          = (u * a₃) * v := by ring
        _ = Nat.lcm u a₃ * g * v := by rw [Nat.lcm_mul_gcd u a₃]
        _ ∣ b₃ * bu * bv := mul_dvd_mul (mul_dvd_mul hlcm_b3 hg_bu) hv_bv

private lemma four_mul_le_of_dvd_lcm {d a₁ a₂ a₃ : ℕ}
    (ha₁ : 0 < a₁) (h12 : a₁ < a₂) (h23 : a₂ < a₃)
    (hd1 : d ∣ a₁) (hd2 : d ∣ a₂) (hd3 : d ∣ a₃) (hlcm : a₃ ∣ Nat.lcm a₁ a₂) :
    4 * d ≤ a₃ := by
  obtain ⟨q₁, hq1_eq⟩ := hd1
  obtain ⟨q₂, hq2_eq⟩ := hd2
  obtain ⟨q₃, hq3_eq⟩ := hd3
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [hq1_eq, zero_mul] at ha₁; omega
    · exact hpos
  rw [hq1_eq] at ha₁ h12 hlcm
  rw [hq2_eq] at h12 h23 hlcm
  rw [hq3_eq] at h23 hlcm
  have hq1 : 1 ≤ q₁ := by nlinarith
  have hq12 : q₁ < q₂ := by nlinarith
  have hq23 : q₂ < q₃ := by nlinarith
  have hq3_ne3 : q₃ ≠ 3 := by
    intro h3
    have hq1_1 : q₁ = 1 := by omega
    have hq2_2 : q₂ = 2 := by omega
    rw [h3, hq1_1, hq2_2] at hlcm
    have hlcm_eq : (d * 1).lcm (d * 2) = 2 * d := by
      rw [Nat.lcm_mul_left, Nat.lcm_one_left, mul_comm d 2]
    rw [hlcm_eq] at hlcm
    have hle := Nat.le_of_dvd (by omega) hlcm
    omega
  have hq3_ge4 : 4 ≤ q₃ := by omega
  nlinarith

private lemma triple_lcm_split (a₁ a₂ a₃ : ℕ) :
    Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.gcd a₁ a₂ * Nat.gcd (Nat.lcm a₁ a₂) a₃ =
      a₁ * a₂ * a₃ := by
  have h1 := Nat.lcm_mul_gcd (Nat.lcm a₁ a₂) a₃
  have h2 := Nat.lcm_mul_gcd a₁ a₂
  calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.gcd a₁ a₂ * Nat.gcd (Nat.lcm a₁ a₂) a₃
      = (Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.gcd (Nat.lcm a₁ a₂) a₃) * Nat.gcd a₁ a₂ := by ring
    _ = (Nat.lcm a₁ a₂ * a₃) * Nat.gcd a₁ a₂ := by rw [h1]
    _ = (Nat.lcm a₁ a₂ * Nat.gcd a₁ a₂) * a₃ := by ring
    _ = a₁ * a₂ * a₃ := by rw [h2]

private lemma gcd_lcm_dvd_mul_gcd (a₁ a₂ a₃ : ℕ) :
    Nat.gcd (Nat.lcm a₁ a₂) a₃ ∣ Nat.gcd a₁ a₃ * Nat.gcd a₂ a₃ := by
  set d := Nat.gcd (Nat.lcm a₁ a₂) a₃
  have hd_lcm : d ∣ Nat.lcm a₁ a₂ := Nat.gcd_dvd_left _ _
  have hd_a3 : d ∣ a₃ := Nat.gcd_dvd_right _ _
  have hlcm_mul : Nat.lcm a₁ a₂ ∣ a₁ * a₂ :=
    Nat.lcm_dvd (dvd_mul_right a₁ a₂) (dvd_mul_left a₂ a₁)
  have hd_a12 : d ∣ a₁ * a₂ := dvd_trans hd_lcm hlcm_mul
  rw [← Int.natCast_dvd_natCast]
  have hd12_Z : (d : ℤ) ∣ (a₁ : ℤ) * (a₂ : ℤ) := by exact_mod_cast hd_a12
  have hd3_Z : (d : ℤ) ∣ (a₃ : ℤ) := Int.natCast_dvd_natCast.mpr hd_a3
  have hbez1 : (Nat.gcd a₁ a₃ : ℤ) = (a₁ : ℤ) * Nat.gcdA a₁ a₃ + (a₃ : ℤ) * Nat.gcdB a₁ a₃ :=
    Nat.gcd_eq_gcd_ab a₁ a₃
  have hbez2 : (Nat.gcd a₂ a₃ : ℤ) = (a₂ : ℤ) * Nat.gcdA a₂ a₃ + (a₃ : ℤ) * Nat.gcdB a₂ a₃ :=
    Nat.gcd_eq_gcd_ab a₂ a₃
  have hexp : ((Nat.gcd a₁ a₃ * Nat.gcd a₂ a₃ : ℕ) : ℤ) =
      ((a₁ : ℤ) * (a₂ : ℤ)) * (Nat.gcdA a₁ a₃ * Nat.gcdA a₂ a₃) +
      (a₃ : ℤ) * ((a₁ : ℤ) * Nat.gcdA a₁ a₃ * Nat.gcdB a₂ a₃ +
        Nat.gcdB a₁ a₃ * (a₂ : ℤ) * Nat.gcdA a₂ a₃ +
        (a₃ : ℤ) * Nat.gcdB a₁ a₃ * Nat.gcdB a₂ a₃) := by
    push_cast; rw [hbez1, hbez2]; ring
  rw [hexp]
  exact dvd_add (dvd_mul_of_dvd_left hd12_Z _) (dvd_mul_of_dvd_left hd3_Z _)

private lemma exists_sorted_triple_of_card_three {A : Finset ℕ} (hcard : A.card = 3) :
    ∃ a₁ a₂ a₃ : ℕ, a₁ < a₂ ∧ a₂ < a₃ ∧ A = {a₁, a₂, a₃} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
  rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
  rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · refine ⟨x, z, y, h2, h3, ?_⟩; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exfalso; omega
  · refine ⟨z, x, y, h2, h1, ?_⟩; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · refine ⟨y, x, z, h1, h2, ?_⟩; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exfalso; omega
  · refine ⟨y, z, x, h3, h2, ?_⟩; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · refine ⟨z, y, x, h3, h1, ?_⟩; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- Exact upper bound for `n = 3`: `g(3) ≤ 4` (`SatisfiesBound 3 4`). -/
theorem erdos708_upper_three : SatisfiesBound 3 4 := by
  intro A hA hvalid x
  obtain ⟨hcard, hge2⟩ := hvalid
  obtain ⟨a₁, a₂, a₃, h12, h23, rfl⟩ := exists_sorted_triple_of_card_three hcard
  have ha₁ : 2 ≤ a₁ := hge2 a₁ (by simp)
  have ha₂ : 2 ≤ a₂ := hge2 a₂ (by simp)
  have ha₃ : 2 ≤ a₃ := hge2 a₃ (by simp)
  have hmax : ({a₁, a₂, a₃} : Finset ℕ).max' hA = a₃ := by
    apply le_antisymm
    · apply Finset.max'_le
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega
    · exact Finset.le_max' _ a₃ (by simp)
  rw [hmax]
  have hprodA : (∏ a ∈ ({a₁, a₂, a₃} : Finset ℕ), a) = a₁ * a₂ * a₃ := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
        Finset.prod_singleton]
    ring
  -- Helper to close `IsCover` from explicit divisibility of a candidate `B ⊆ consecInterval x a₃`
  have finish : ∀ (B : Finset ℕ), B ⊆ consecInterval x a₃ → B.card ≤ 4 →
      a₁ * a₂ * a₃ ∣ ∏ b ∈ B, b →
      ∃ B' ⊆ consecInterval x a₃, B'.card ≤ 4 ∧ IsCover {a₁, a₂, a₃} B' := by
    intro B hBI hBc hdvd
    refine ⟨B, hBI, hBc, ?_⟩
    rw [IsCover, hprodA]
    exact hdvd
  -- Pick `b₃ ∈ consecInterval x a₃` divisible by `a₃`
  obtain ⟨b₃, hb₃_I, ha₃_b₃⟩ := exists_multiple_in_consecInterval x a₃ a₃ (by omega) le_rfl
  by_cases ha2_b3 : a₂ ∣ b₃
  · by_cases ha1_b3 : a₁ ∣ b₃
    · -- Case 4: both `a₁ ∣ b₃` and `a₂ ∣ b₃` (so `lcm (lcm a₁ a₂) a₃ ∣ b₃`)
      have hlcm_b3 : Nat.lcm (Nat.lcm a₁ a₂) a₃ ∣ b₃ :=
        Nat.lcm_dvd (Nat.lcm_dvd ha1_b3 ha2_b3) ha₃_b₃
      set g₁₂ := Nat.gcd a₁ a₂
      set H := Nat.gcd (Nat.lcm a₁ a₂) a₃
      have hg12_pos : 0 < g₁₂ := Nat.gcd_pos_of_pos_left a₂ (by omega)
      have hH_pos : 0 < H := Nat.gcd_pos_of_pos_right _ (by omega)
      have h2g12 : 2 * g₁₂ ≤ a₃ := le_trans (two_mul_gcd_le_of_lt_g6 ha₁ h12) (by omega)
      by_cases h2H : 2 * H ≤ a₃
      · -- Subcase 4A: `2 * H ≤ a₃`, so `g₁₂` and `H` cover in `≤ 3` elements
        obtain ⟨c₁, hc1_I, hc1_ne, hg12_c1⟩ :=
          exists_avoiding_multiple x a₃ g₁₂ {b₃} hg12_pos (by simpa using h2g12)
        have hc1_nb3 : c₁ ≠ b₃ := by simpa using hc1_ne
        obtain ⟨c₂, hc2_I, hc2_ne, hH_c2⟩ :=
          exists_avoiding_multiple x a₃ H {b₃} hH_pos (by simpa using h2H)
        have hc2_nb3 : c₂ ≠ b₃ := by simpa using hc2_ne
        by_cases hc12 : c₁ = c₂
        · subst hc12
          set d := Nat.gcd g₁₂ H
          have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left H hg12_pos
          have hd1 : d ∣ a₁ := dvd_trans (Nat.gcd_dvd_left g₁₂ H) (Nat.gcd_dvd_left a₁ a₂)
          have hd2 : d ∣ a₂ := dvd_trans (Nat.gcd_dvd_left g₁₂ H) (Nat.gcd_dvd_right a₁ a₂)
          have hd3 : d ∣ a₃ := dvd_trans (Nat.gcd_dvd_right g₁₂ H) (Nat.gcd_dvd_right _ a₃)
          have h3d : ({b₃, c₁} : Finset ℕ).card + 1 ≤ 3 := by
            have hcard_S := Finset.card_insert_le b₃ {c₁}
            simp only [Finset.card_singleton] at hcard_S
            omega
          obtain ⟨c₃, hc3_I, hc3_ne, hd_c3⟩ := exists_avoiding_multiple x a₃ d {b₃, c₁} hd_pos
            (le_trans (Nat.mul_le_mul_right d h3d)
              (three_mul_le_of_three_distinct_dvd (by omega) h12 h23 hd1 hd2 hd3))
          have hc3_nb3 : c₃ ≠ b₃ := fun h => hc3_ne (by simp [h])
          have hc3_nc1 : c₃ ≠ c₁ := fun h => hc3_ne (by simp [h])
          apply finish {b₃, c₁, c₃}
          · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hc3_I]
          · have h1 := Finset.card_insert_le b₃ {c₁, c₃}
            have h2 := Finset.card_insert_le c₁ {c₃}
            simp at h1 h2; omega
          · have hprod : ∏ b ∈ ({b₃, c₁, c₃} : Finset ℕ), b = b₃ * c₁ * c₃ := by
              rw [Finset.prod_insert (by simp [hc1_nb3.symm, hc3_nb3.symm]),
                  Finset.prod_insert (by simp [hc3_nc1.symm]), Finset.prod_singleton]
              ring
            rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
            have hlcm_c1 : Nat.lcm g₁₂ H ∣ c₁ := Nat.lcm_dvd hg12_c1 hH_c2
            have hmul_gh : Nat.lcm g₁₂ H * d = g₁₂ * H := Nat.lcm_mul_gcd g₁₂ H
            calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * H
                = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (g₁₂ * H) := by ring
              _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (Nat.lcm g₁₂ H * d) := by rw [← hmul_gh]
              _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ H * d := by ring
              _ ∣ b₃ * c₁ * c₃ :=
                  mul_dvd_mul (mul_dvd_mul hlcm_b3 hlcm_c1) hd_c3
        · apply finish {b₃, c₁, c₂}
          · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hc2_I]
          · have h1 := Finset.card_insert_le b₃ {c₁, c₂}
            have h2 := Finset.card_insert_le c₁ {c₂}
            simp at h1 h2; omega
          · have hprod : ∏ b ∈ ({b₃, c₁, c₂} : Finset ℕ), b = b₃ * c₁ * c₂ := by
              rw [Finset.prod_insert (by simp [hc1_nb3.symm, hc2_nb3.symm]),
                  Finset.prod_insert (by simp [hc12]), Finset.prod_singleton]
              ring
            rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
            exact mul_dvd_mul (mul_dvd_mul hlcm_b3 hg12_c1) hH_c2
      · -- Subcase 4B: `a₃ < 2 * H` with `H ∣ a₃`, hence `H = a₃` and `a₃ ∣ lcm a₁ a₂`
        have hH_dvd : H ∣ a₃ := Nat.gcd_dvd_right (Nat.lcm a₁ a₂) a₃
        have hlcm12_a3 : a₃ ∣ Nat.lcm a₁ a₂ := by
          obtain ⟨k, hk⟩ := hH_dvd
          have hk0 : k ≠ 0 := by intro h0; rw [h0, mul_zero] at hk; omega
          have hk1 : k = 1 := by nlinarith
          rw [hk1, mul_one] at hk
          calc a₃ = H := hk
            _ ∣ Nat.lcm a₁ a₂ := Nat.gcd_dvd_left _ _
        set g₁₃ := Nat.gcd a₁ a₃
        set g₂₃ := Nat.gcd a₂ a₃
        have hg13_pos : 0 < g₁₃ := Nat.gcd_pos_of_pos_left a₃ (by omega)
        have hg23_pos : 0 < g₂₃ := Nat.gcd_pos_of_pos_left a₃ (by omega)
        have h2g13 : 2 * g₁₃ ≤ a₃ := two_mul_gcd_le_of_lt_g6 ha₁ (by omega)
        have h2g23 : 2 * g₂₃ ≤ a₃ := two_mul_gcd_le_of_lt_g6 ha₂ h23
        have hgH : H ∣ g₁₃ * g₂₃ := gcd_lcm_dvd_mul_gcd a₁ a₂ a₃
        obtain ⟨c₁, hc1_I, hc1_ne, hg12_c1⟩ :=
          exists_avoiding_multiple x a₃ g₁₂ {b₃} hg12_pos (by simpa using h2g12)
        have hc1_nb3 : c₁ ≠ b₃ := by simpa using hc1_ne
        obtain ⟨w₂, hw2_I, hw2_ne, hg13_w2⟩ :=
          exists_avoiding_multiple x a₃ g₁₃ {b₃} hg13_pos (by simpa using h2g13)
        have hw2_nb3 : w₂ ≠ b₃ := by simpa using hw2_ne
        obtain ⟨w₃, hw3_I, hw3_ne, hg23_w3⟩ :=
          exists_avoiding_multiple x a₃ g₂₃ {b₃} hg23_pos (by simpa using h2g23)
        have hw3_nb3 : w₃ ≠ b₃ := by simpa using hw3_ne
        -- Handle `w₂ = c₁` vs `w₂ ≠ c₁`, then place/replace `w₃` cleanly
        by_cases hw2c1 : w₂ = c₁
        · have hg13_c1 : g₁₃ ∣ c₁ := hw2c1 ▸ hg13_w2
          set d₁ := Nat.gcd g₁₂ g₁₃
          have hd1_pos : 0 < d₁ := Nat.gcd_pos_of_pos_left g₁₃ hg12_pos
          have hd1_1 : d₁ ∣ a₁ := dvd_trans (Nat.gcd_dvd_left g₁₂ g₁₃) (Nat.gcd_dvd_left a₁ a₂)
          have hd1_2 : d₁ ∣ a₂ := dvd_trans (Nat.gcd_dvd_left g₁₂ g₁₃) (Nat.gcd_dvd_right a₁ a₂)
          have hd1_3 : d₁ ∣ a₃ := dvd_trans (Nat.gcd_dvd_right g₁₂ g₁₃) (Nat.gcd_dvd_right a₁ a₃)
          have h4d1 := four_mul_le_of_dvd_lcm (by omega) h12 h23 hd1_1 hd1_2 hd1_3 hlcm12_a3
          have hS2 : ({b₃, c₁} : Finset ℕ).card + 1 ≤ 4 := by
            have hcard_S := Finset.card_insert_le b₃ {c₁}
            simp only [Finset.card_singleton] at hcard_S
            omega
          obtain ⟨c₂, hc2_I, hc2_ne, hd1_c2⟩ := exists_avoiding_multiple x a₃ d₁ {b₃, c₁} hd1_pos
            (le_trans (Nat.mul_le_mul_right d₁ hS2) h4d1)
          have hc2_nb3 : c₂ ≠ b₃ := fun h => hc2_ne (by simp [h])
          have hc2_nc1 : c₂ ≠ c₁ := fun h => hc2_ne (by simp [h])
          have hS3 : ({b₃, c₁, c₂} : Finset ℕ).card + 1 ≤ 4 := by
            have h1 := Finset.card_insert_le b₃ {c₁, c₂}
            have h2 := Finset.card_insert_le c₁ {c₂}
            simp at h1 h2; omega
          by_cases hw3c1 : w₃ = c₁
          · have hg23_c1 : g₂₃ ∣ c₁ := hw3c1 ▸ hg23_w3
            set d₂ := Nat.gcd (Nat.lcm g₁₂ g₁₃) g₂₃
            have hd2_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hg23_pos
            have hd2_1 : d₂ ∣ a₁ := dvd_trans (Nat.gcd_dvd_left _ _)
              (Nat.lcm_dvd (Nat.gcd_dvd_left a₁ a₂) (Nat.gcd_dvd_left a₁ a₃))
            have hd2_2 : d₂ ∣ a₂ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left a₂ a₃)
            have hd2_3 : d₂ ∣ a₃ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right a₂ a₃)
            have h4d2 := four_mul_le_of_dvd_lcm (by omega) h12 h23 hd2_1 hd2_2 hd2_3 hlcm12_a3
            obtain ⟨c₃, hc3_I, hc3_ne, hd2_c3⟩ :=
              exists_avoiding_multiple x a₃ d₂ {b₃, c₁, c₂} hd2_pos
                (le_trans (Nat.mul_le_mul_right d₂ hS3) h4d2)
            have hc3_nb3 : c₃ ≠ b₃ := fun h => hc3_ne (by simp [h])
            have hc3_nc1 : c₃ ≠ c₁ := fun h => hc3_ne (by simp [h])
            have hc3_nc2 : c₃ ≠ c₂ := fun h => hc3_ne (by simp [h])
            apply finish {b₃, c₁, c₂, c₃}
            · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hc2_I, hc3_I]
            · have h1 := Finset.card_insert_le b₃ {c₁, c₂, c₃}
              have h2 := Finset.card_insert_le c₁ {c₂, c₃}
              have h3 := Finset.card_insert_le c₂ {c₃}
              simp at h1 h2 h3; omega
            · have hprod : ∏ b ∈ ({b₃, c₁, c₂, c₃} : Finset ℕ), b = b₃ * c₁ * c₂ * c₃ := by
                rw [Finset.prod_insert (by simp [hc1_nb3.symm, hc2_nb3.symm, hc3_nb3.symm]),
                    Finset.prod_insert (by simp [hc2_nc1.symm, hc3_nc1.symm]),
                    Finset.prod_insert (by simp [hc3_nc2.symm]), Finset.prod_singleton]
                ring
              rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
              have hlcm12_c1 : Nat.lcm g₁₂ g₁₃ ∣ c₁ := Nat.lcm_dvd hg12_c1 hg13_c1
              have hlcm_all_c1 : Nat.lcm (Nat.lcm g₁₂ g₁₃) g₂₃ ∣ c₁ :=
                Nat.lcm_dvd hlcm12_c1 hg23_c1
              have h_step : Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) ∣
                  b₃ * c₁ * c₂ * c₃ := by
                have hl1 : Nat.lcm g₁₂ g₁₃ * d₁ = g₁₂ * g₁₃ := Nat.lcm_mul_gcd g₁₂ g₁₃
                have hl2 : Nat.lcm (Nat.lcm g₁₂ g₁₃) g₂₃ * d₂ = Nat.lcm g₁₂ g₁₃ * g₂₃ :=
                  Nat.lcm_mul_gcd (Nat.lcm g₁₂ g₁₃) g₂₃
                calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃)
                    = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((g₁₂ * g₁₃) * g₂₃) := by ring
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((Nat.lcm g₁₂ g₁₃ * d₁) * g₂₃) := by rw [← hl1]
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((Nat.lcm g₁₂ g₁₃ * g₂₃) * d₁) := by ring
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((Nat.lcm (Nat.lcm g₁₂ g₁₃) g₂₃ * d₂) * d₁) := by rw [← hl2]
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm (Nat.lcm g₁₂ g₁₃) g₂₃ * d₁ * d₂ := by ring
                  _ ∣ b₃ * c₁ * c₂ * c₃ :=
                      mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hlcm_all_c1) hd1_c2) hd2_c3
              exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                (by simpa [mul_assoc] using h_step)
          · by_cases hw3c2 : w₃ = c₂
            · have hg23_c2 : g₂₃ ∣ c₂ := hw3c2 ▸ hg23_w3
              set d₂ := Nat.gcd d₁ g₂₃
              have hd2_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hg23_pos
              have hd2_1 : d₂ ∣ a₁ := dvd_trans (Nat.gcd_dvd_left _ _) hd1_1
              have hd2_2 : d₂ ∣ a₂ := dvd_trans (Nat.gcd_dvd_left _ _) hd1_2
              have hd2_3 : d₂ ∣ a₃ := dvd_trans (Nat.gcd_dvd_left _ _) hd1_3
              have h4d2 := four_mul_le_of_dvd_lcm (by omega) h12 h23 hd2_1 hd2_2 hd2_3 hlcm12_a3
              obtain ⟨c₃, hc3_I, hc3_ne, hd2_c3⟩ :=
                exists_avoiding_multiple x a₃ d₂ {b₃, c₁, c₂} hd2_pos
                  (le_trans (Nat.mul_le_mul_right d₂ hS3) h4d2)
              have hc3_nb3 : c₃ ≠ b₃ := fun h => hc3_ne (by simp [h])
              have hc3_nc1 : c₃ ≠ c₁ := fun h => hc3_ne (by simp [h])
              have hc3_nc2 : c₃ ≠ c₂ := fun h => hc3_ne (by simp [h])
              apply finish {b₃, c₁, c₂, c₃}
              · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hc2_I, hc3_I]
              · have h1 := Finset.card_insert_le b₃ {c₁, c₂, c₃}
                have h2 := Finset.card_insert_le c₁ {c₂, c₃}
                have h3 := Finset.card_insert_le c₂ {c₃}
                simp at h1 h2 h3; omega
              · have hprod : ∏ b ∈ ({b₃, c₁, c₂, c₃} : Finset ℕ), b = b₃ * c₁ * c₂ * c₃ := by
                  rw [Finset.prod_insert (by simp [hc1_nb3.symm, hc2_nb3.symm, hc3_nb3.symm]),
                      Finset.prod_insert (by simp [hc2_nc1.symm, hc3_nc1.symm]),
                      Finset.prod_insert (by simp [hc3_nc2.symm]), Finset.prod_singleton]
                  ring
                rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
                have hlcm12_c1 : Nat.lcm g₁₂ g₁₃ ∣ c₁ := Nat.lcm_dvd hg12_c1 hg13_c1
                have hlcm_d1_c2 : Nat.lcm d₁ g₂₃ ∣ c₂ := Nat.lcm_dvd hd1_c2 hg23_c2
                have h_step : Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) ∣
                    b₃ * c₁ * c₂ * c₃ := by
                  have hl1 : Nat.lcm g₁₂ g₁₃ * d₁ = g₁₂ * g₁₃ := Nat.lcm_mul_gcd g₁₂ g₁₃
                  have hl2 : Nat.lcm d₁ g₂₃ * d₂ = d₁ * g₂₃ := Nat.lcm_mul_gcd d₁ g₂₃
                  calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃)
                      = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((g₁₂ * g₁₃) * g₂₃) := by ring
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * ((Nat.lcm g₁₂ g₁₃ * d₁) * g₂₃) := by rw [← hl1]
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ g₁₃ * (d₁ * g₂₃) := by ring
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ g₁₃ * (Nat.lcm d₁ g₂₃ * d₂) := by rw [← hl2]
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ g₁₃ * Nat.lcm d₁ g₂₃ * d₂ := by ring
                    _ ∣ b₃ * c₁ * c₂ * c₃ :=
                        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hlcm12_c1) hlcm_d1_c2) hd2_c3
                exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                  (by simpa [mul_assoc] using h_step)
            · apply finish {b₃, c₁, c₂, w₃}
              · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hc2_I, hw3_I]
              · have h1 := Finset.card_insert_le b₃ {c₁, c₂, w₃}
                have h2 := Finset.card_insert_le c₁ {c₂, w₃}
                have h3 := Finset.card_insert_le c₂ {w₃}
                simp at h1 h2 h3; omega
              · have hprod : ∏ b ∈ ({b₃, c₁, c₂, w₃} : Finset ℕ), b = b₃ * c₁ * c₂ * w₃ := by
                  rw [Finset.prod_insert (by simp [hc1_nb3.symm, hc2_nb3.symm, hw3_nb3.symm]),
                      Finset.prod_insert (by simp [hc2_nc1.symm, Ne.symm hw3c1]),
                      Finset.prod_insert (by simp [Ne.symm hw3c2]), Finset.prod_singleton]
                  ring
                rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
                have hlcm12_c1 : Nat.lcm g₁₂ g₁₃ ∣ c₁ := Nat.lcm_dvd hg12_c1 hg13_c1
                have h_step : Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) ∣
                    b₃ * c₁ * c₂ * w₃ := by
                  have hl1 : Nat.lcm g₁₂ g₁₃ * d₁ = g₁₂ * g₁₃ := Nat.lcm_mul_gcd g₁₂ g₁₃
                  calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃)
                      = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (g₁₂ * g₁₃) * g₂₃ := by ring
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (Nat.lcm g₁₂ g₁₃ * d₁) * g₂₃ := by rw [← hl1]
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ g₁₃ * d₁ * g₂₃ := by ring
                    _ ∣ b₃ * c₁ * c₂ * w₃ :=
                        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hlcm12_c1) hd1_c2) hg23_w3
                exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                  (by simpa [mul_assoc] using h_step)
        · -- `w₂ ≠ c₁`, so `{b₃, c₁, w₂}` has `3` distinct elements covering `L * g₁₂ * g₁₃`
          have hS3 : ({b₃, c₁, w₂} : Finset ℕ).card + 1 ≤ 4 := by
            have h1 := Finset.card_insert_le b₃ {c₁, w₂}
            have h2 := Finset.card_insert_le c₁ {w₂}
            simp at h1 h2; omega
          by_cases hw3c1 : w₃ = c₁
          · have hg23_c1 : g₂₃ ∣ c₁ := hw3c1 ▸ hg23_w3
            set d₂ := Nat.gcd g₁₂ g₂₃
            have hd2_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hg23_pos
            have hd2_1 : d₂ ∣ a₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left a₁ a₂)
            have hd2_2 : d₂ ∣ a₂ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right a₁ a₂)
            have hd2_3 : d₂ ∣ a₃ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right a₂ a₃)
            have h4d2 := four_mul_le_of_dvd_lcm (by omega) h12 h23 hd2_1 hd2_2 hd2_3 hlcm12_a3
            obtain ⟨c₃, hc3_I, hc3_ne, hd2_c3⟩ :=
              exists_avoiding_multiple x a₃ d₂ {b₃, c₁, w₂} hd2_pos
                (le_trans (Nat.mul_le_mul_right d₂ hS3) h4d2)
            have hc3_nb3 : c₃ ≠ b₃ := fun h => hc3_ne (by simp [h])
            have hc3_nc1 : c₃ ≠ c₁ := fun h => hc3_ne (by simp [h])
            have hc3_nw2 : c₃ ≠ w₂ := fun h => hc3_ne (by simp [h])
            apply finish {b₃, c₁, w₂, c₃}
            · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hw2_I, hc3_I]
            · have h1 := Finset.card_insert_le b₃ {c₁, w₂, c₃}
              have h2 := Finset.card_insert_le c₁ {w₂, c₃}
              have h3 := Finset.card_insert_le w₂ {c₃}
              simp at h1 h2 h3; omega
            · have hprod : ∏ b ∈ ({b₃, c₁, w₂, c₃} : Finset ℕ), b = b₃ * c₁ * w₂ * c₃ := by
                rw [Finset.prod_insert (by simp [hc1_nb3.symm, hw2_nb3.symm, hc3_nb3.symm]),
                    Finset.prod_insert (by simp [Ne.symm hw2c1, hc3_nc1.symm]),
                    Finset.prod_insert (by simp [hc3_nw2.symm]), Finset.prod_singleton]
                ring
              rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
              have hlcm_c1 : Nat.lcm g₁₂ g₂₃ ∣ c₁ := Nat.lcm_dvd hg12_c1 hg23_c1
              have h_step : Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) ∣
                  b₃ * c₁ * w₂ * c₃ := by
                have hl1 : Nat.lcm g₁₂ g₂₃ * d₂ = g₁₂ * g₂₃ := Nat.lcm_mul_gcd g₁₂ g₂₃
                calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃)
                    = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (g₁₂ * g₂₃) * g₁₃ := by ring
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * (Nat.lcm g₁₂ g₂₃ * d₂) * g₁₃ := by rw [← hl1]
                  _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * Nat.lcm g₁₂ g₂₃ * g₁₃ * d₂ := by ring
                  _ ∣ b₃ * c₁ * w₂ * c₃ :=
                      mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hlcm_c1) hg13_w2) hd2_c3
              exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                (by simpa [mul_assoc] using h_step)
          · by_cases hw3w2 : w₃ = w₂
            · have hg23_w2 : g₂₃ ∣ w₂ := hw3w2 ▸ hg23_w3
              set d₂ := Nat.gcd g₁₃ g₂₃
              have hd2_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hg23_pos
              have hd2_1 : d₂ ∣ a₁ := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left a₁ a₃)
              have hd2_2 : d₂ ∣ a₂ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left a₂ a₃)
              have hd2_3 : d₂ ∣ a₃ := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right a₂ a₃)
              have h4d2 := four_mul_le_of_dvd_lcm (by omega) h12 h23 hd2_1 hd2_2 hd2_3 hlcm12_a3
              obtain ⟨c₃, hc3_I, hc3_ne, hd2_c3⟩ :=
                exists_avoiding_multiple x a₃ d₂ {b₃, c₁, w₂} hd2_pos
                  (le_trans (Nat.mul_le_mul_right d₂ hS3) h4d2)
              have hc3_nb3 : c₃ ≠ b₃ := fun h => hc3_ne (by simp [h])
              have hc3_nc1 : c₃ ≠ c₁ := fun h => hc3_ne (by simp [h])
              have hc3_nw2 : c₃ ≠ w₂ := fun h => hc3_ne (by simp [h])
              apply finish {b₃, c₁, w₂, c₃}
              · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hw2_I, hc3_I]
              · have h1 := Finset.card_insert_le b₃ {c₁, w₂, c₃}
                have h2 := Finset.card_insert_le c₁ {w₂, c₃}
                have h3 := Finset.card_insert_le w₂ {c₃}
                simp at h1 h2 h3; omega
              · have hprod : ∏ b ∈ ({b₃, c₁, w₂, c₃} : Finset ℕ), b = b₃ * c₁ * w₂ * c₃ := by
                  rw [Finset.prod_insert (by simp [hc1_nb3.symm, hw2_nb3.symm, hc3_nb3.symm]),
                      Finset.prod_insert (by simp [Ne.symm hw2c1, hc3_nc1.symm]),
                      Finset.prod_insert (by simp [hc3_nw2.symm]), Finset.prod_singleton]
                  ring
                rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
                have hlcm_w2 : Nat.lcm g₁₃ g₂₃ ∣ w₂ := Nat.lcm_dvd hg13_w2 hg23_w2
                have h_step : Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) ∣
                    b₃ * c₁ * w₂ * c₃ := by
                  have hl1 : Nat.lcm g₁₃ g₂₃ * d₂ = g₁₃ * g₂₃ := Nat.lcm_mul_gcd g₁₃ g₂₃
                  calc Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃)
                      = Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (Nat.lcm g₁₃ g₂₃ * d₂) := by rw [← hl1]
                    _ = Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * Nat.lcm g₁₃ g₂₃ * d₂ := by ring
                    _ ∣ b₃ * c₁ * w₂ * c₃ :=
                        mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hg12_c1) hlcm_w2) hd2_c3
                exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                  (by simpa [mul_assoc] using h_step)
            · apply finish {b₃, c₁, w₂, w₃}
              · simp [Finset.insert_subset_iff, hb₃_I, hc1_I, hw2_I, hw3_I]
              · have h1 := Finset.card_insert_le b₃ {c₁, w₂, w₃}
                have h2 := Finset.card_insert_le c₁ {w₂, w₃}
                have h3 := Finset.card_insert_le w₂ {w₃}
                simp at h1 h2 h3; omega
              · have hprod : ∏ b ∈ ({b₃, c₁, w₂, w₃} : Finset ℕ), b = b₃ * c₁ * w₂ * w₃ := by
                  rw [Finset.prod_insert (by simp [hc1_nb3.symm, hw2_nb3.symm, hw3_nb3.symm]),
                      Finset.prod_insert (by simp [Ne.symm hw2c1, Ne.symm hw3c1]),
                      Finset.prod_insert (by simp [Ne.symm hw3w2]), Finset.prod_singleton]
                  ring
                rw [hprod, ← triple_lcm_split a₁ a₂ a₃]
                exact dvd_trans (mul_dvd_mul (mul_dvd_mul_left _ (dvd_refl g₁₂)) hgH)
                  (by
                    rw [show Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * (g₁₃ * g₂₃) =
                        Nat.lcm (Nat.lcm a₁ a₂) a₃ * g₁₂ * g₁₃ * g₂₃ by ring]
                    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlcm_b3 hg12_c1) hg13_w2) hg23_w3)
    · -- Case 2: `a₂ ∣ b₃` and `¬ (a₁ ∣ b₃)`
      obtain ⟨B, hBI, hBc, hdvd⟩ := cover_triple_when_one_dvd_b3 ha₂ ha₁ h12.ne' h23 (by omega)
        hb₃_I ha₃_b₃ ha2_b3 ha1_b3
      exact finish B hBI hBc (by rw [show a₁ * a₂ * a₃ = a₂ * a₁ * a₃ by ring]; exact hdvd)
  · by_cases ha1_b3 : a₁ ∣ b₃
    · -- Case 3: `a₁ ∣ b₃` and `¬ (a₂ ∣ b₃)`
      obtain ⟨B, hBI, hBc, hdvd⟩ := cover_triple_when_one_dvd_b3 ha₁ ha₂ h12.ne (by omega) h23
        hb₃_I ha₃_b₃ ha1_b3 ha2_b3
      exact finish B hBI hBc hdvd
    · -- Case 1: `¬ (a₂ ∣ b₃)` and `¬ (a₁ ∣ b₃)`
      obtain ⟨b₂, hb2_I, ha2_b2⟩ := exists_multiple_in_consecInterval x a₂ a₃ (by omega) (by omega)
      obtain ⟨b₁, hb1_I, ha1_b1⟩ := exists_multiple_in_consecInterval x a₁ a₃ (by omega) (by omega)
      have hb2_nb3 : b₂ ≠ b₃ := fun h => ha2_b3 (h ▸ ha2_b2)
      have hb1_nb3 : b₁ ≠ b₃ := fun h => ha1_b3 (h ▸ ha1_b1)
      by_cases hb12 : b₁ = b₂
      · subst hb12
        set g := Nat.gcd a₁ a₂
        have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left a₂ (by omega)
        have h2g_a2 : 2 * g ≤ a₂ := two_mul_gcd_le_of_lt_g6 ha₁ h12
        obtain ⟨b', hb'_I, hb'_ne, hg_b'⟩ :=
          exists_avoiding_multiple x a₃ g {b₁} hg_pos (by simpa using le_trans h2g_a2 (by omega))
        have hb'_nb1 : b' ≠ b₁ := by simpa using hb'_ne
        have hlcm12_b1 : Nat.lcm a₁ a₂ ∣ b₁ := Nat.lcm_dvd ha1_b1 ha2_b2
        by_cases hb'b3 : b' = b₃
        · have hg_b3 : g ∣ b₃ := hb'b3 ▸ hg_b'
          by_cases h3g : 3 * g ≤ a₃
          · have hS2 : ({b₁, b₃} : Finset ℕ).card + 1 ≤ 3 := by
              have hcard_S := Finset.card_insert_le b₁ {b₃}
              simp only [Finset.card_singleton] at hcard_S
              omega
            obtain ⟨b'', hb''_I, hb''_ne, hg_b''⟩ :=
              exists_avoiding_multiple x a₃ g {b₁, b₃} hg_pos
                (le_trans (Nat.mul_le_mul_right g hS2) h3g)
            have hb''_nb1 : b'' ≠ b₁ := fun h => hb''_ne (by simp [h])
            have hb''_nb3 : b'' ≠ b₃ := fun h => hb''_ne (by simp [h])
            apply finish {b₁, b'', b₃}
            · simp [Finset.insert_subset_iff, hb1_I, hb''_I, hb₃_I]
            · have h1 := Finset.card_insert_le b₁ {b'', b₃}
              have h2 := Finset.card_insert_le b'' {b₃}
              simp at h1 h2; omega
            · have hprod : ∏ b ∈ ({b₁, b'', b₃} : Finset ℕ), b = b₁ * b'' * b₃ := by
                rw [Finset.prod_insert (by simp [hb''_nb1.symm, hb1_nb3]),
                    Finset.prod_insert (by simp [hb''_nb3]), Finset.prod_singleton]
                ring
              rw [hprod, ← Nat.lcm_mul_gcd a₁ a₂]
              exact mul_dvd_mul (mul_dvd_mul hlcm12_b1 hg_b'') ha₃_b₃
          · exfalso
            obtain ⟨q₂, hq2⟩ := Nat.gcd_dvd_right a₁ a₂
            obtain ⟨q₁, hq1⟩ := Nat.gcd_dvd_left a₁ a₂
            have hq2_ge2 : 2 ≤ q₂ := by nlinarith
            have hq2_lt3 : q₂ < 3 := by nlinarith
            have hq2_eq2 : q₂ = 2 := by omega
            have hq1_lt2 : q₁ < 2 := by nlinarith
            have hq1_ge1 : 1 ≤ q₁ := by nlinarith
            have hq1_eq1 : q₁ = 1 := by omega
            have ha1_eq_g : a₁ = g := by rw [hq1, hq1_eq1]; ring
            exact ha1_b3 (ha1_eq_g ▸ hg_b3)
        · apply finish {b₁, b', b₃}
          · simp [Finset.insert_subset_iff, hb1_I, hb'_I, hb₃_I]
          · have h1 := Finset.card_insert_le b₁ {b', b₃}
            have h2 := Finset.card_insert_le b' {b₃}
            simp at h1 h2; omega
          · have hprod : ∏ b ∈ ({b₁, b', b₃} : Finset ℕ), b = b₁ * b' * b₃ := by
              rw [Finset.prod_insert (by simp [hb'_nb1.symm, hb1_nb3]),
                  Finset.prod_insert (by simp [hb'b3]), Finset.prod_singleton]
              ring
            rw [hprod, ← Nat.lcm_mul_gcd a₁ a₂]
            exact mul_dvd_mul (mul_dvd_mul hlcm12_b1 hg_b') ha₃_b₃
      · apply finish {b₁, b₂, b₃}
        · simp [Finset.insert_subset_iff, hb1_I, hb2_I, hb₃_I]
        · have h1 := Finset.card_insert_le b₁ {b₂, b₃}
          have h2 := Finset.card_insert_le b₂ {b₃}
          simp at h1 h2; omega
        · have hprod : ∏ b ∈ ({b₁, b₂, b₃} : Finset ℕ), b = b₁ * b₂ * b₃ := by
            rw [Finset.prod_insert (by simp [hb12, hb1_nb3]),
                Finset.prod_insert (by simp [hb2_nb3]), Finset.prod_singleton]
            ring
          rw [hprod]
          exact mul_dvd_mul (mul_dvd_mul ha1_b1 ha2_b2) ha₃_b₃

/-- Exact equality `g(3) = 4`: `SatisfiesBound 3 4 ∧ ¬ SatisfiesBound 3 3`. -/
theorem erdos708_exact_three : SatisfiesBound 3 4 ∧ ¬ SatisfiesBound 3 3 :=
  ⟨erdos708_upper_three, erdos708_lower_three⟩

/-! ## Part 3: Foundation Lemmas for `g(6) ≤ 8` -/

/-- Branch 1 for `g(6) ≤ 8`: any set with `∑ a ∈ A, ω(a) ≤ 8` is covered by `≤ 8` elements. -/
theorem erdos708_upper_six_of_omega_le_eight {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a)
    (hω : ∑ a ∈ A, a.primeFactors.card ≤ 8) (m : ℕ) :
    Erdos708Covers A m 8 := by
  obtain ⟨B, hBI, hBc, hcov⟩ := erdos708_omega_sum_bound hA m
  exact ⟨B, hBI, le_trans hBc hω, hcov⟩

/-- Branch 2 for `g(6) ≤ 8`: any set with `max(A) ≤ 8` is trivially covered by `≤ 8` elements. -/
theorem erdos708_upper_six_of_max_le_eight {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a)
    (hle : A.sup id ≤ 8) (m : ℕ) :
    Erdos708Covers A m 8 := by
  obtain ⟨B, hBI, hBc, hcov⟩ := erdos708_trivial_max_bound hA m
  exact ⟨B, hBI, le_trans hBc hle, hcov⟩

/-- Branch 3 for `g(6) ≤ 8`: any 6-element set admitting an injective multiple map
    `f : A → [x+1, x+M]` is covered by `|B| ≤ 6 ≤ 8` elements (`A.image f`). -/
theorem erdos708_upper_six_of_hall_six {A : Finset ℕ} {x M : ℕ} (hA : A.card = 6)
    (hpos : ∀ a ∈ A, 0 < a) (f : ℕ → ℕ)
    (hf_mem : ∀ a ∈ A, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ A, a ∣ f a) (hf_inj : Set.InjOn f A) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B := by
  let _ := hpos
  refine ⟨A.image f, Finset.image_subset_iff.mpr hf_mem, ?_, ?_⟩
  · exact Finset.card_image_le.trans hA.le
  · rw [IsCover, Finset.prod_image hf_inj]
    have h_ind : ∀ (S : Finset ℕ), (∀ a ∈ S, a ∣ f a) → (∏ a ∈ S, a) ∣ ∏ a ∈ S, f a := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s has ih =>
        intro h
        rw [Finset.prod_insert has, Finset.prod_insert has]
        exact mul_dvd_mul (h a (Finset.mem_insert_self a s))
          (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))
    exact h_ind A hf_dvd

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms erdos708_lower_six_sharp
#print axioms erdos708_upper_three
#print axioms erdos708_exact_three
#print axioms erdos708_upper_six_of_omega_le_eight
#print axioms erdos708_upper_six_of_max_le_eight
#print axioms erdos708_upper_six_of_hall_six

end Erdos708
