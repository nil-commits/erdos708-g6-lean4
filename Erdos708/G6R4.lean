import Erdos708.CoprimePack

/-!
# PPL 176 (Erdős Problem #708) — GCD Reduction, Max Matching, and Unconditional `r = 4` Closure

This module proves:
1. **`erdos708_gcd_reduction`**: Unconditional GCD reduction reducing any `A` with common divisor `g`
   to `A.image (· / g)`.
2. **`exists_max_matching_in_consecInterval`**: Existence of a maximum-cardinality matching
   `S ⊆ A` (`1 ≤ S.card ≤ A.card`) into `consecInterval x M`, with the maximality property that
   every unmatched `u ∈ A \ S` has all of its multiples in `consecInterval x M` inside `S.image f`.
3. **`exists_six_cover_with_gcd_deficit`**: Two-Chain Defect-2 Theorem for `A.card = 6, S.card = 4`:
   yields `B₀ ⊆ consecInterval x M` with `B₀.card ≤ 6` and residual `R ∣ Nat.gcd u₁ u₂` (`2 * R ≤ M`)
   absorbing all prime-valuation deficits.
4. **`erdos708_upper_six_of_matching_four`**: Complete unconditional closure of the `r = 4` branch
   (`B.card ≤ 8`) for ALL `M` and ALL `x`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-! ## Part 1: Unconditional GCD Reduction -/

/-- Unconditional GCD reduction: if `g > 0` divides every element of `A` (`A.Nonempty`, `0 < a`)
    and `C := A.image (· / g)` admits a cover `B' ⊆ consecInterval (x / g) (M / g)` of size `≤ k`
    (with `A.card ≤ k`), then `A` admits a cover `B ⊆ consecInterval x M` of size `≤ k`. -/
theorem erdos708_gcd_reduction {A : Finset ℕ} {x M g k : ℕ}
    (hA_ne : A.Nonempty) (hA_pos : ∀ a ∈ A, 0 < a) (hM_eq : M = A.sup id)
    (hg_pos : 0 < g) (hg_dvd : ∀ a ∈ A, g ∣ a) (hA_le_k : A.card ≤ k)
    (hcov : ∃ B' ⊆ consecInterval (x / g) (M / g), B'.card ≤ k ∧ IsCover (A.image (· / g)) B') :
    ∃ B ⊆ consecInterval x M, B.card ≤ k ∧ IsCover A B := by
  let _ := hA_ne
  let C : Finset ℕ := A.image (· / g)
  have hinj_div : Set.InjOn (· / g) A := by
    intro a ha b hb hab
    dsimp only at hab
    calc a = g * (a / g) := (Nat.mul_div_cancel' (hg_dvd a ha)).symm
      _ = g * (b / g) := by rw [hab]
      _ = b := Nat.mul_div_cancel' (hg_dvd b hb)
  have hC_card : C.card = A.card := Finset.card_image_of_injOn hinj_div
  have hC_sub : C ⊆ Finset.Icc 1 (M / g) := by
    intro c hc
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_Icc]
    have ha_pos := hA_pos a haA
    have hg_le_a : g ≤ a := Nat.le_of_dvd ha_pos (hg_dvd a haA)
    have haM : a ≤ M := by rw [hM_eq]; exact Finset.le_sup (f := id) haA
    exact ⟨(Nat.le_div_iff_mul_le hg_pos).mpr (by simpa using hg_le_a), Nat.div_le_div_right haM⟩
  have hA_le_Mg : A.card ≤ M / g := by
    calc A.card = C.card := hC_card.symm
      _ ≤ (Finset.Icc 1 (M / g)).card := Finset.card_le_card hC_sub
      _ = M / g := by simp [Nat.card_Icc]
  let I' := consecInterval (x / g) (M / g)
  have hI'_card : I'.card = M / g := card_consecInterval (x / g) (M / g)
  obtain ⟨B', hB'I, hB'card, hB'cov⟩ := hcov
  have hpad : ∃ B'' ⊆ I', A.card ≤ B''.card ∧ B''.card ≤ k ∧ IsCover C B'' := by
    by_cases hlt : B'.card < A.card
    · have hle_diff : A.card - B'.card ≤ (I' \ B').card := by
        rw [Finset.card_sdiff_of_subset hB'I, hI'_card]
        omega
      obtain ⟨P, hPI, hPcard⟩ := Finset.exists_subset_card_eq hle_diff
      have hP_sub : P ⊆ I' := Finset.Subset.trans hPI Finset.sdiff_subset
      have hdisj : Disjoint B' P :=
        Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp (hPI hy)).2 hx
      refine ⟨B' ∪ P, Finset.union_subset hB'I hP_sub, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hPcard]; omega
      · rw [Finset.card_union_of_disjoint hdisj, hPcard]; omega
      · rw [IsCover] at hB'cov ⊢
        rw [Finset.prod_union hdisj]
        exact dvd_mul_of_dvd_left hB'cov _
    · exact ⟨B', hB'I, by omega, hB'card, hB'cov⟩
  obtain ⟨B'', hB''I, hAB'', hB''k, hB''cov⟩ := hpad
  let B : Finset ℕ := B''.image (g * ·)
  have hinj_mul : Set.InjOn (g * ·) B'' := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hg_pos hab
  refine ⟨B, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb'I, rfl⟩ := Finset.mem_image.mp hb
    have hb'_mem := hB''I hb'I
    simp only [I', consecInterval, Finset.mem_Icc] at hb'_mem ⊢
    have hdiv_x : x < g * (x / g) + g := by
      have h1 := Nat.div_add_mod x g
      have h2 := Nat.mod_lt x hg_pos
      omega
    have hle_x : g * (x / g) ≤ x := Nat.mul_div_le x g
    have hle_M : g * (M / g) ≤ M := Nat.mul_div_le M g
    constructor
    · have h1 : g * (x / g + 1) ≤ g * b' := Nat.mul_le_mul_left g hb'_mem.1
      rw [mul_add, mul_one] at h1
      omega
    · have h1 : g * b' ≤ g * (x / g + M / g) := Nat.mul_le_mul_left g hb'_mem.2
      rw [mul_add] at h1
      omega
  · rw [Finset.card_image_of_injOn hinj_mul]
    exact hB''k
  · rw [IsCover] at hB''cov ⊢
    have hprodA : ∏ a ∈ A, a = g ^ A.card * ∏ c ∈ C, c := by
      have h1 : ∏ c ∈ C, c = ∏ a ∈ A, (a / g) := Finset.prod_image hinj_div
      rw [h1]
      calc ∏ a ∈ A, a = ∏ a ∈ A, (g * (a / g)) := by
            apply Finset.prod_congr rfl
            intro a ha
            exact (Nat.mul_div_cancel' (hg_dvd a ha)).symm
        _ = (∏ _a ∈ A, g) * ∏ a ∈ A, (a / g) := Finset.prod_mul_distrib
        _ = g ^ A.card * ∏ a ∈ A, (a / g) := by simp
    have hprodB : ∏ b ∈ B, b = g ^ B''.card * ∏ b' ∈ B'', b' := by
      rw [Finset.prod_image hinj_mul, Finset.prod_mul_distrib]
      simp
    rw [hprodA, hprodB]
    exact mul_dvd_mul (Nat.pow_dvd_pow g hAB'') hB''cov

/-! ## Part 2: Maximum Matching Existence & Maximality -/

/-- Existence of a matching of size `r` from `A` into `consecInterval x M` via divisibility. -/
def HasMatching (A : Finset ℕ) (x M r : ℕ) : Prop :=
  ∃ S ⊆ A, S.card = r ∧ ∃ f : ℕ → ℕ,
    (∀ a ∈ S, f a ∈ consecInterval x M) ∧ (∀ a ∈ S, a ∣ f a) ∧ Set.InjOn f S

/-- Every nonempty `A ⊆ [1, M]` admits a maximum-cardinality matching `S ⊆ A` (`1 ≤ S.card`)
    into `consecInterval x M`, such that every unmatched `u ∈ A \ S` has all of its multiples
    in `consecInterval x M` contained in `S.image f`. -/
theorem exists_max_matching_in_consecInterval {A : Finset ℕ} {x M : ℕ}
    (hA_ne : A.Nonempty) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) :
    ∃ (S : Finset ℕ) (f : ℕ → ℕ),
      S ⊆ A ∧ 1 ≤ S.card ∧ S.card ≤ A.card ∧
      (∀ a ∈ S, f a ∈ consecInterval x M) ∧ (∀ a ∈ S, a ∣ f a) ∧ Set.InjOn f S ∧
      (∀ u ∈ A \ S, ∀ b ∈ consecInterval x M, u ∣ b → b ∈ S.image f) := by
  classical
  let R : Finset ℕ := (Finset.range (A.card + 1)).filter (HasMatching A x M)
  have h1_mem : 1 ∈ R := by
    rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨a₀, ha₀⟩ := hA_ne
    have hcard_pos : 1 ≤ A.card := Finset.card_pos.mpr ⟨a₀, ha₀⟩
    refine ⟨by omega, ?_⟩
    obtain ⟨b₀, hb₀I, ha₀b₀⟩ := exists_multiple_in_consecInterval x a₀ M (hA_pos a₀ ha₀) (hA_le a₀ ha₀)
    refine ⟨{a₀}, Finset.singleton_subset_iff.mpr ha₀, Finset.card_singleton a₀, fun _ => b₀, ?_⟩
    refine ⟨fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hb₀I, ?_, ?_⟩
    · intro a ha; rw [Finset.mem_singleton.mp ha]; exact ha₀b₀
    · intro a ha b hb _
      rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
  obtain ⟨r, hrR, hr_max⟩ := Finset.exists_max_image R id ⟨1, h1_mem⟩
  have h1_le_r : 1 ≤ r := hr_max 1 h1_mem
  rw [Finset.mem_filter, Finset.mem_range] at hrR
  obtain ⟨hr_lt, S, hSA, hS_card, f, hf_mem, hf_dvd, hf_inj⟩ := hrR
  refine ⟨S, f, hSA, by omega, Finset.card_le_card hSA, hf_mem, hf_dvd, hf_inj, ?_⟩
  intro u hu b hbI hub
  by_contra hb_not_img
  rw [Finset.mem_sdiff] at hu
  rcases hu with ⟨huA, huS⟩
  let f' : ℕ → ℕ := fun a => if a = u then b else f a
  have hmatch_succ : HasMatching A x M (r + 1) := by
    refine ⟨insert u S, Finset.insert_subset_iff.mpr ⟨huA, hSA⟩, ?_, f', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem huS, hS_card]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hbI]
      · have hne : a ≠ u := fun h => huS (h ▸ haS)
        simp [f', hne, hf_mem a haS]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haS
      · simp [f', hub]
      · have hne : a ≠ u := fun h => huS (h ▸ haS)
        simp [f', hne, hf_dvd a haS]
    · intro a₁ ha₁ a₂ ha₂ heq
      rcases Finset.mem_insert.mp ha₁ with ha₁_eq | ha₁S <;>
      rcases Finset.mem_insert.mp ha₂ with ha₂_eq | ha₂S
      · exact ha₁_eq.trans ha₂_eq.symm
      · have hne : a₂ ≠ u := fun h => huS (h ▸ ha₂S)
        simp only [f', ha₁_eq, ite_true, if_neg hne] at heq
        exact False.elim (hb_not_img (Finset.mem_image.mpr ⟨a₂, ha₂S, heq.symm⟩))
      · have hne : a₁ ≠ u := fun h => huS (h ▸ ha₁S)
        simp only [f', ha₂_eq, ite_true, if_neg hne] at heq
        exact False.elim (hb_not_img (Finset.mem_image.mpr ⟨a₁, ha₁S, heq⟩))
      · have h1 : a₁ ≠ u := fun h => huS (h ▸ ha₁S)
        have h2 : a₂ ≠ u := fun h => huS (h ▸ ha₂S)
        simp only [f', if_neg h1, if_neg h2] at heq
        exact hf_inj ha₁S ha₂S heq
  have hr1_le_card : r + 1 ≤ A.card := by
    have h1 := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨huA, hSA⟩)
    rw [Finset.card_insert_of_notMem huS, hS_card] at h1
    exact h1
  have hr1_mem : r + 1 ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmatch_succ⟩
  have hle : r + 1 ≤ r := hr_max (r + 1) hr1_mem
  omega

/-! ## Part 3: Two-Chain Defect-2 Theorem -/

/-- Two-Chain Defect-2 Theorem (`A.card = 6, S.card = 4`):
    running two independent defect-1 chains from `S` produces `B₀ ⊆ consecInterval x M`
    (`B₀.card ≤ 6`) and a positive residual divisor `R ∣ Nat.gcd u₁ u₂` (`2 * R ≤ M`)
    accounting for every prime valuation deficit `(∑ A, v_p) - (∑ B₀, v_p)`. -/
theorem exists_six_cover_with_gcd_deficit {A S : Finset ℕ} {x M : ℕ} {f : ℕ → ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hSA : S ⊆ A) (hS_card : S.card = 4)
    (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ (B₀ : Finset ℕ) (R : ℕ),
      B₀ ⊆ consecInterval x M ∧ B₀.card ≤ 6 ∧ 0 < R ∧ 2 * R ≤ M ∧
      (∀ p : ℕ, p.Prime →
        R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) ∧
      (∀ p : ℕ, p.Prime →
        ∑ a ∈ A, a.factorization p ≤ (∑ b ∈ B₀, b.factorization p) + R.factorization p) := by
  have hcard_sum : (A \ S).card + S.card = A.card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left, Finset.sdiff_union_of_subset hSA]
  have hsdiff_two : (A \ S).card = 2 := by omega
  obtain ⟨u₁, u₂, hu12, hdiff_eq⟩ := Finset.card_eq_two.mp hsdiff_two
  have hu₁_sdiff : u₁ ∈ A \ S := by rw [hdiff_eq]; exact Finset.mem_insert_self u₁ {u₂}
  have hu₂_sdiff : u₂ ∈ A \ S := by rw [hdiff_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u₂)
  obtain ⟨hu₁A, hu₁S⟩ := Finset.mem_sdiff.mp hu₁_sdiff
  obtain ⟨hu₂A, hu₂S⟩ := Finset.mem_sdiff.mp hu₂_sdiff
  have hS_pos : ∀ a ∈ S, 0 < a := fun a ha => hA_pos a (hSA ha)
  have hS_le : ∀ a ∈ S, a ≤ M := fun a ha => hA_le a (hSA ha)
  obtain ⟨w₁, hw₁_mem, _, hcov₁⟩ := exists_witness_add_one_of_matching
    hS_pos hS_le (hA_pos u₁ hu₁A) (hA_le u₁ hu₁A) hu₁S hf_mem hf_dvd hf_inj
  obtain ⟨w₂, hw₂_mem, _, hcov₂⟩ := exists_witness_add_one_of_matching
    hS_pos hS_le (hA_pos u₂ hu₂A) (hA_le u₂ hu₂A) hu₂S hf_mem hf_dvd hf_inj
  let B₀ : Finset ℕ := insert w₁ (insert w₂ (S.image f))
  have hB₀_I : B₀ ⊆ consecInterval x M := by
    refine Finset.insert_subset_iff.mpr ⟨hw₁_mem, Finset.insert_subset_iff.mpr ⟨hw₂_mem, ?_⟩⟩
    exact Finset.image_subset_iff.mpr hf_mem
  have hB₀_card : B₀.card ≤ 6 := by
    have h1 := Finset.card_insert_le w₁ (insert w₂ (S.image f))
    have h2 := Finset.card_insert_le w₂ (S.image f)
    have h3 : (S.image f).card ≤ S.card := Finset.card_image_le
    dsimp only [B₀]
    omega
  have hA_eq : A = insert u₁ (insert u₂ S) := by
    rw [← Finset.sdiff_union_of_subset hSA, hdiff_eq, Finset.insert_union, Finset.singleton_union]
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hB₀0 : ∀ b ∈ B₀, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hB₀_I hb)).ne'
  have hu₁_not : u₁ ∉ insert u₂ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hu12, hu₁S⟩
  have hsum_A : ∀ p : ℕ, ∑ a ∈ A, a.factorization p =
      u₁.factorization p + (u₂.factorization p + ∑ a ∈ S, a.factorization p) := by
    intro p
    rw [hA_eq, Finset.sum_insert hu₁_not, Finset.sum_insert hu₂S]
  have hle_gcd : ∀ p : ℕ, p.Prime →
      (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤
        (Nat.gcd u₁ u₂).factorization p := by
    intro p _hp
    have hu₁S_pos : ∀ a ∈ insert u₁ S, a ≠ 0 := by
      intro a ha
      rcases Finset.mem_insert.mp ha with ha_eq | haS
      · rw [ha_eq]; exact (hA_pos u₁ hu₁A).ne'
      · exact (hS_pos a haS).ne'
    have hu₂S_pos : ∀ a ∈ insert u₂ S, a ≠ 0 := by
      intro a ha
      rcases Finset.mem_insert.mp ha with ha_eq | haS
      · rw [ha_eq]; exact (hA_pos u₂ hu₂A).ne'
      · exact (hS_pos a haS).ne'
    have hB₁_pos : ∀ b ∈ insert w₁ (S.image f), b ≠ 0 := by
      intro b hb
      rcases Finset.mem_insert.mp hb with hb_eq | hbS
      · rw [hb_eq]; exact (pos_of_mem_consecInterval hw₁_mem).ne'
      · obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hbS
        exact (pos_of_mem_consecInterval (hf_mem a haS)).ne'
    have hB₂_pos : ∀ b ∈ insert w₂ (S.image f), b ≠ 0 := by
      intro b hb
      rcases Finset.mem_insert.mp hb with hb_eq | hbS
      · rw [hb_eq]; exact (pos_of_mem_consecInterval hw₂_mem).ne'
      · obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hbS
        exact (pos_of_mem_consecInterval (hf_mem a haS)).ne'
    have hsum1 : u₁.factorization p + ∑ a ∈ S, a.factorization p ≤ ∑ b ∈ B₀, b.factorization p := by
      have h1 := sum_factorization_le_of_isCover hu₁S_pos hB₁_pos hcov₁ p
      rw [Finset.sum_insert hu₁S] at h1
      have hsub1 : insert w₁ (S.image f) ⊆ B₀ := by
        intro b hb
        rcases Finset.mem_insert.mp hb with hb_eq | hbS
        · rw [hb_eq]; exact Finset.mem_insert_self w₁ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hbS)
      exact le_trans h1 (Finset.sum_le_sum_of_subset hsub1)
    have hsum2 : u₂.factorization p + ∑ a ∈ S, a.factorization p ≤ ∑ b ∈ B₀, b.factorization p := by
      have h2 := sum_factorization_le_of_isCover hu₂S_pos hB₂_pos hcov₂ p
      rw [Finset.sum_insert hu₂S] at h2
      have hsub2 : insert w₂ (S.image f) ⊆ B₀ := by
        intro b hb
        exact Finset.mem_insert_of_mem hb
      exact le_trans h2 (Finset.sum_le_sum_of_subset hsub2)
    have hsumA_eq := hsum_A p
    have hdef1 : (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ u₂.factorization p := by
      omega
    have hdef2 : (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ u₁.factorization p := by
      omega
    rw [Nat.factorization_gcd (hA_pos u₁ hu₁A).ne' (hA_pos u₂ hu₂A).ne', Finsupp.inf_apply]
    exact le_min hdef2 hdef1
  let g : ℕ := Nat.gcd u₁ u₂
  let R : ℕ := ∏ p ∈ g.primeFactors,
    p ^ ((∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p))
  have hR_pos : 0 < R := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) := by
    intro p hp
    have hterm_ne : ∀ q ∈ g.primeFactors,
        q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q)) ≠ 0 := by
      intro q hq
      exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero
    rw [Nat.factorization_prod hterm_ne]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ q ∈ g.primeFactors,
        (q ^ ((∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q))).factorization p =
          if q = p then (∑ a ∈ A, a.factorization q) - (∑ b ∈ B₀, b.factorization q) else 0 := by
      intro q hq
      rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hq), Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hp_mem
    · rfl
    · have hg_ne : g ≠ 0 := (Nat.gcd_pos_of_pos_left u₂ (hA_pos u₁ hu₁A)).ne'
      have hfac0 : g.factorization p = 0 := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hp_mem
        exact hp_mem
      have hle := hle_gcd p hp
      rw [hfac0] at hle
      omega
  have hR_dvd_g : R ∣ g := by
    have hg_ne : g ≠ 0 := (Nat.gcd_pos_of_pos_left u₂ (hA_pos u₁ hu₁A)).ne'
    rw [← Nat.factorization_le_iff_dvd hR_pos.ne' hg_ne]
    intro p
    by_cases hp : p.Prime
    · rw [hR_fac p hp]
      exact hle_gcd p hp
    · rw [Nat.factorization_eq_zero_of_not_prime R hp]
      exact Nat.zero_le _
  have h2R : 2 * R ≤ M := by
    have hT : ∀ a ∈ ({u₁, u₂} : Finset ℕ), 0 < a ∧ a ≤ M ∧ R ∣ a := by
      intro a ha
      rcases Finset.mem_insert.mp ha with ha_eq | ha'
      · rw [ha_eq]; exact ⟨hA_pos u₁ hu₁A, hA_le u₁ hu₁A, dvd_trans hR_dvd_g (Nat.gcd_dvd_left u₁ u₂)⟩
      · rw [Finset.mem_singleton.mp ha']
        exact ⟨hA_pos u₂ hu₂A, hA_le u₂ hu₂A, dvd_trans hR_dvd_g (Nat.gcd_dvd_right u₁ u₂)⟩
    have hcard_pair : ({u₁, u₂} : Finset ℕ).card = 2 := Finset.card_pair hu12
    have hmul := card_mul_le_of_forall_dvd hR_pos hT
    rwa [hcard_pair] at hmul
  refine ⟨B₀, R, hB₀_I, hB₀_card, hR_pos, h2R, hR_fac, ?_⟩
  intro p hp
  have h1 := hR_fac p hp
  omega

/-! ## Part 4: Unconditional `≤ 2`-Slot Residual Closure for `R` (`2 * R ≤ M`, `B₀.card ≤ 6`) -/

private lemma sum_factorization_le_consecInterval {A : Finset ℕ} {x M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M) (_hp : p.Prime) :
    ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ consecInterval x M, b.factorization p := by
  have hsub : A ⊆ Finset.Icc 1 M := fun a ha => Finset.mem_Icc.mpr ⟨hA_pos a ha, hA_le a ha⟩
  have hdvd : (∏ a ∈ A, a) ∣ ∏ b ∈ consecInterval x M, b :=
    dvd_trans (prod_subset_Icc_dvd_factorial hsub) (factorial_dvd_prod_Icc x M)
  have hA0 : ∀ a ∈ A, a ≠ 0 := fun a ha => (hA_pos a ha).ne'
  have hI0 : ∀ b ∈ consecInterval x M, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval hb).ne'
  exact sum_factorization_le_of_isCover hA0 hI0 hdvd p

private lemma deficit_le_sum_sdiff {A B₀ : Finset ℕ} {x M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime) :
    (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤
      ∑ b ∈ consecInterval x M \ B₀, b.factorization p := by
  have htot := sum_factorization_le_consecInterval (x := x) hA_pos hA_le hp
  have hsplit : ∑ b ∈ consecInterval x M, b.factorization p =
      (∑ b ∈ B₀, b.factorization p) + ∑ b ∈ consecInterval x M \ B₀, b.factorization p := by
    have hunion : B₀ ∪ (consecInterval x M \ B₀) = consecInterval x M :=
      Finset.union_sdiff_of_subset hB₀_I
    have hdisj : Disjoint B₀ (consecInterval x M \ B₀) :=
      Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
    conv_lhs => rw [← hunion]
    exact Finset.sum_union hdisj
  omega

private lemma exists_prime_multiple_of_deficit_pos {A B₀ : Finset ℕ} {x M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (hdef : 1 ≤ (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ b ∈ consecInterval x M, b ∉ B₀ ∧ p ∣ b := by
  have hsum := le_trans hdef (deficit_le_sum_sdiff hA_pos hA_le hB₀_I hp)
  rw [sum_factorization_eq_filter] at hsum
  have hne : ((consecInterval x M \ B₀).filter (fun b => p ∣ b)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum
    omega
  obtain ⟨b, hb⟩ := hne
  rw [Finset.mem_filter, Finset.mem_sdiff] at hb
  exact ⟨b, hb.1.1, hb.1.2, hb.2⟩

/-- Layer-cake deficit bound: if every multiple of `p^2` in `consecInterval x M` lies in `B₀`,
    then `(∑ A, v_p) - (∑ B₀, v_p) ≤ A.card - ((consecInterval x M).filter (p^2 ∣ ·)).card`. -/
private lemma layer_cake_deficit_le_of_sq_subset {A B₀ : Finset ℕ} {x M p : ℕ}
    (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (_hB₀_I : B₀ ⊆ consecInterval x M) (hp : p.Prime)
    (hsub_hi : (consecInterval x M).filter (fun b => p ^ 2 ∣ b) ⊆ B₀) :
    (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤
      A.card - ((consecInterval x M).filter (fun b => p ^ 2 ∣ b)).card := by
  let I_hi := (consecInterval x M).filter (fun b => p ^ 2 ∣ b)
  change (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) ≤ A.card - I_hi.card
  have hIhi_sum_le : ∑ b ∈ I_hi, b.factorization p ≤ ∑ b ∈ B₀, b.factorization p :=
    Finset.sum_le_sum_of_subset hsub_hi
  have hIhi_ge2 : ∀ b ∈ I_hi, 2 ≤ b.factorization p := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hb0 : b ≠ 0 := (pos_of_mem_consecInterval hb.1).ne'
    exact (hp.pow_dvd_iff_le_factorization hb0).mp hb.2
  have h2Ihi_le : 2 * I_hi.card ≤ ∑ b ∈ I_hi, b.factorization p := by
    calc 2 * I_hi.card = ∑ _b ∈ I_hi, 2 := by simp [mul_comm]
      _ ≤ ∑ b ∈ I_hi, b.factorization p := Finset.sum_le_sum hIhi_ge2
  by_cases hM2 : M < p ^ 2
  · have hA_le1 : ∀ a ∈ A, a.factorization p ≤ 1 := by
      intro a ha
      by_contra hgt
      have hge2 : 2 ≤ a.factorization p := by omega
      have hpa := (hp.pow_dvd_iff_le_factorization (hA_pos a ha).ne').mpr hge2
      have hle_a := Nat.le_of_dvd (hA_pos a ha) hpa
      have haM := hA_le a ha
      omega
    have hsumA_le : ∑ a ∈ A, a.factorization p ≤ A.card := by
      calc ∑ a ∈ A, a.factorization p ≤ ∑ _a ∈ A, 1 := Finset.sum_le_sum hA_le1
        _ = A.card := by simp
    omega
  · push Not at hM2
    have h2_le_M : 2 ≤ M := by
      have hp2 : 4 ≤ p ^ 2 := by
        have := hp.two_le
        nlinarith
      omega
    let A_hi := A.filter (fun a => p ^ 2 ∣ a)
    let A_lo := A.filter (fun a => ¬ (p ^ 2 ∣ a))
    have hA_card_split : A_hi.card + A_lo.card = A.card := by
      have h1 := Finset.sum_filter_add_sum_filter_not A (fun a => p ^ 2 ∣ a) (fun _ => (1 : ℕ))
      simpa using h1
    have hA_sum_split : ∑ a ∈ A, a.factorization p =
        (∑ a ∈ A_hi, a.factorization p) + ∑ a ∈ A_lo, a.factorization p :=
      (Finset.sum_filter_add_sum_filter_not A (fun a => p ^ 2 ∣ a) (fun a => a.factorization p)).symm
    have hAlo_le : ∑ a ∈ A_lo, a.factorization p ≤ A_lo.card := by
      calc ∑ a ∈ A_lo, a.factorization p ≤ ∑ _a ∈ A_lo, 1 := by
            apply Finset.sum_le_sum
            intro a ha
            rw [Finset.mem_filter] at ha
            by_contra hgt
            have hge2 : 2 ≤ a.factorization p := by omega
            exact ha.2 ((hp.pow_dvd_iff_le_factorization (hA_pos a ha.1).ne').mpr hge2)
        _ = A_lo.card := by simp
    have hAhi_ge2 : ∀ a ∈ A_hi, 2 ≤ a.factorization p := by
      intro a ha
      rw [Finset.mem_filter] at ha
      exact (hp.pow_dvd_iff_le_factorization (hA_pos a ha.1).ne').mp ha.2
    have hIcc_split : Finset.Icc 1 M = insert 1 (insert 2 (Finset.Icc 3 M)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h1_not_Icc3 : (1 : ℕ) ∉ Finset.Icc 3 M := by simp
    have h2_not_Icc3 : (2 : ℕ) ∉ Finset.Icc 3 M := by simp
    have h1_not_ins : (1 : ℕ) ∉ insert 2 (Finset.Icc 3 M) := by simp
    have hAhi_tail : ∀ a ∈ A_hi, a.factorization p =
        2 + ∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ a then 1 else 0 := by
      intro a ha
      have ha_mem := (Finset.mem_filter.mp ha).1
      have ha_dvd2 := (Finset.mem_filter.mp ha).2
      have ha_dvd1 : p ^ 1 ∣ a := dvd_trans (by simp) ha_dvd2
      rw [factorization_eq_sum_dvd hp (hA_pos a ha_mem) (hA_le a ha_mem), hIcc_split,
          Finset.sum_insert h1_not_ins, Finset.sum_insert h2_not_Icc3]
      simp only [ha_dvd1, ha_dvd2, ↓reduceIte]
      omega
    have hIhi_tail : ∀ b ∈ I_hi,
        2 + ∑ j ∈ Finset.Icc 3 M, (if p ^ j ∣ b then 1 else 0) ≤ b.factorization p := by
      intro b hb
      have hb_mem := (Finset.mem_filter.mp hb).1
      have hb_dvd2 := (Finset.mem_filter.mp hb).2
      have hb_dvd1 : p ^ 1 ∣ b := dvd_trans (by simp) hb_dvd2
      have h1 := sum_dvd_le_factorization (M := M) hp (pos_of_mem_consecInterval hb_mem)
      rw [hIcc_split, Finset.sum_insert h1_not_ins, Finset.sum_insert h2_not_Icc3] at h1
      simp only [hb_dvd1, hb_dvd2, ↓reduceIte] at h1
      omega
    have htail_le : ∑ a ∈ A_hi, (∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ a then 1 else 0) ≤
        ∑ b ∈ I_hi, (∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ b then 1 else 0) := by
      rw [Finset.sum_comm, Finset.sum_comm (s := I_hi)]
      apply Finset.sum_le_sum
      intro j hj
      have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [Finset.sum_boole, Nat.cast_id, Finset.sum_boole, Nat.cast_id]
      have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
      have hA_sub : A_hi.filter (fun a => p ^ j ∣ a) ⊆ (Finset.Icc 1 M).filter (fun a => p ^ j ∣ a) := by
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_Icc.mpr ⟨hA_pos a (Finset.mem_filter.mp ha.1).1,
          hA_le a (Finset.mem_filter.mp ha.1).1⟩, ha.2⟩
      have hI_eq : I_hi.filter (fun b => p ^ j ∣ b) = (consecInterval x M).filter (fun b => p ^ j ∣ b) := by
        ext b
        simp only [I_hi, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hbI, _⟩, hbj⟩; exact ⟨hbI, hbj⟩
        · rintro ⟨hbI, hbj⟩
          have hp2j : p ^ 2 ∣ p ^ j := Nat.pow_dvd_pow p (by omega)
          exact ⟨⟨hbI, dvd_trans hp2j hbj⟩, hbj⟩
      rw [hI_eq]
      exact le_trans (le_trans (Finset.card_le_card hA_sub) (card_multiples_Icc_one_le M (p ^ j) hpj_pos))
        (card_multiples_Icc_ge x M (p ^ j) hpj_pos)
    have hAhi_sum : ∑ a ∈ A_hi, a.factorization p =
        2 * A_hi.card + ∑ a ∈ A_hi, (∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ a then 1 else 0) := by
      rw [Finset.sum_congr rfl hAhi_tail, Finset.sum_add_distrib]
      simp [mul_comm]
    have hIhi_sum : 2 * I_hi.card + ∑ b ∈ I_hi, (∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ b then 1 else 0) ≤
        ∑ b ∈ I_hi, b.factorization p := by
      have h1 : ∑ b ∈ I_hi, (2 + ∑ j ∈ Finset.Icc 3 M, if p ^ j ∣ b then 1 else 0) ≤
          ∑ b ∈ I_hi, b.factorization p := Finset.sum_le_sum hIhi_tail
      rw [Finset.sum_add_distrib] at h1
      simpa [mul_comm] using h1
    have hAhi_le_Ihi : A_hi.card ≤ I_hi.card := by
      have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
      have hA_sub : A_hi ⊆ (Finset.Icc 1 M).filter (fun a => p ^ 2 ∣ a) := by
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_Icc.mpr ⟨hA_pos a ha.1, hA_le a ha.1⟩, ha.2⟩
      exact le_trans (le_trans (Finset.card_le_card hA_sub) (card_multiples_Icc_one_le M (p ^ 2) hp2_pos))
        (card_multiples_Icc_ge x M (p ^ 2) hp2_pos)
    omega

/-- Upper bound on the number of multiples of `d > 0` in `consecInterval x M` (`1 ≤ M`). -/
private lemma card_multiples_Icc_le (x M d : ℕ) (hM : 1 ≤ M) (_hd : 0 < d) :
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

/-- Any single prime power `p^e` (`e = R.factorization p ≥ 1`, `2 * p^e ≤ M`) is covered by
    at most `2` elements of `consecInterval x M \ B₀` when `B₀.card ≤ 6` and `A.card = 6`. -/
private lemma exists_two_slots_for_prime_pow {A B₀ : Finset ℕ} {x M p e : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 6)
    (hp : p.Prime) (he1 : 1 ≤ e) (h2pe : 2 * p ^ e ≤ M)
    (he_eq : e = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ T ⊆ consecInterval x M, Disjoint B₀ T ∧ T.card ≤ 2 ∧ e ≤ ∑ b ∈ T, b.factorization p := by
  have hdef_sum := le_trans (le_of_eq he_eq) (deficit_le_sum_sdiff hA_pos hA_le hB₀_I hp)
  rcases Nat.lt_or_ge e 4 with he4 | he4
  · have he_cases : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases he_cases with rfl | rfl | rfl
    · obtain ⟨b, hbI, hbB₀, hpb⟩ :=
        exists_prime_multiple_of_deficit_pos hA_pos hA_le hB₀_I hp (by omega)
      refine ⟨{b}, Finset.singleton_subset_iff.mpr hbI, Finset.disjoint_singleton_right.mpr hbB₀,
        by simp, ?_⟩
      simpa using (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hbI).ne').mp (by simpa using hpb)
    · by_cases hsq : ∃ b ∈ consecInterval x M \ B₀, p ^ 2 ∣ b
      · obtain ⟨b, hb, hp2b⟩ := hsq
        rw [Finset.mem_sdiff] at hb
        refine ⟨{b}, Finset.singleton_subset_iff.mpr hb.1, Finset.disjoint_singleton_right.mpr hb.2,
          by simp, ?_⟩
        simpa using (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb.1).ne').mp hp2b
      · push Not at hsq
        let J := (consecInterval x M \ B₀).filter (fun b => p ∣ b)
        have hJ_le1 : ∀ b ∈ J, b.factorization p ≤ 1 := by
          intro b hb
          have hb_sdiff := (Finset.mem_filter.mp hb).1
          have hb_I := (Finset.mem_sdiff.mp hb_sdiff).1
          by_contra hgt
          have hge2 : 2 ≤ b.factorization p := by omega
          exact hsq b hb_sdiff ((hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb_I).ne').mpr hge2)
        have hJ_sum : 2 ≤ ∑ b ∈ J, b.factorization p := by
          rwa [sum_factorization_eq_filter] at hdef_sum
        have hJ_card : 2 ≤ J.card := by
          have hle : ∑ b ∈ J, b.factorization p ≤ J.card := by
            calc ∑ b ∈ J, b.factorization p ≤ ∑ _b ∈ J, 1 := Finset.sum_le_sum hJ_le1
              _ = J.card := by simp
          omega
        obtain ⟨T, hTJ, hTcard⟩ := Finset.exists_subset_card_eq hJ_card
        refine ⟨T, Finset.Subset.trans hTJ (Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset),
          ?_, le_of_eq hTcard, ?_⟩
        · exact Finset.disjoint_left.mpr fun _ hx hy =>
            (Finset.mem_sdiff.mp (Finset.filter_subset _ _ (hTJ hy))).2 hx
        · calc 2 = T.card := hTcard.symm
            _ = ∑ _b ∈ T, 1 := by simp
            _ ≤ ∑ b ∈ T, b.factorization p := by
              apply Finset.sum_le_sum
              intro b hb
              have hbf := Finset.mem_filter.mp (hTJ hb)
              have hbI := (Finset.mem_sdiff.mp hbf.1).1
              exact (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hbI).ne').mp (by simpa using hbf.2)
    · by_cases hsq : ∃ b₁ ∈ consecInterval x M \ B₀, p ^ 2 ∣ b₁
      · obtain ⟨b₁, hb₁, hp2b₁⟩ := hsq
        rw [Finset.mem_sdiff] at hb₁
        have hb₁_pos : b₁ ≠ 0 := (pos_of_mem_consecInterval hb₁.1).ne'
        by_cases hcb : p ^ 3 ∣ b₁
        · refine ⟨{b₁}, Finset.singleton_subset_iff.mpr hb₁.1, Finset.disjoint_singleton_right.mpr hb₁.2,
            by simp, ?_⟩
          simpa using (hp.pow_dvd_iff_le_factorization hb₁_pos).mp hcb
        · have hv1_eq : b₁.factorization p = 2 := by
            have hge2 : 2 ≤ b₁.factorization p := (hp.pow_dvd_iff_le_factorization hb₁_pos).mp hp2b₁
            have hlt3 : b₁.factorization p < 3 := by
              by_contra hge3
              exact hcb ((hp.pow_dvd_iff_le_factorization hb₁_pos).mpr (by omega))
            omega
          have hb₁_sdiff : b₁ ∈ consecInterval x M \ B₀ := Finset.mem_sdiff.mpr hb₁
          have hrem_sum : 1 ≤ ∑ b ∈ (consecInterval x M \ B₀).erase b₁, b.factorization p := by
            rw [← Finset.add_sum_erase (consecInterval x M \ B₀) (fun b => b.factorization p) hb₁_sdiff,
                hv1_eq] at hdef_sum
            omega
          rw [sum_factorization_eq_filter] at hrem_sum
          have hne2 : (((consecInterval x M \ B₀).erase b₁).filter (fun b => p ∣ b)).Nonempty := by
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            rw [hemp, Finset.sum_empty] at hrem_sum
            omega
          obtain ⟨b₂, hb₂⟩ := hne2
          rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_sdiff] at hb₂
          rcases hb₂ with ⟨⟨hb₂_ne, hb₂_I, hb₂_notB₀⟩, hpb₂⟩
          have hv2_ge1 : 1 ≤ b₂.factorization p :=
            (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₂_I).ne').mp (by simpa using hpb₂)
          refine ⟨{b₁, b₂}, Finset.insert_subset hb₁.1 (Finset.singleton_subset_iff.mpr hb₂_I), ?_,
            Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
          · rw [Finset.disjoint_insert_right]
            exact ⟨hb₁.2, Finset.disjoint_singleton_right.mpr hb₂_notB₀⟩
          · rw [Finset.sum_pair hb₂_ne.symm, hv1_eq]
            omega
      · push Not at hsq
        have hsub_hi : (consecInterval x M).filter (fun b => p ^ 2 ∣ b) ⊆ B₀ := by
          intro b hb
          rw [Finset.mem_filter] at hb
          by_contra hbB₀
          exact hsq b (Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩) hb.2
        have hdef_le := layer_cake_deficit_le_of_sq_subset hA_pos hA_le hB₀_I hp hsub_hi
        have hp2 : 2 ≤ p := hp.two_le
        have h4pe : 4 * p ^ 2 ≤ M := by
          have hpow3 : p ^ 3 = p * p ^ 2 := by ring
          nlinarith
        have hcard_hi : 4 ≤ ((consecInterval x M).filter (fun b => p ^ 2 ∣ b)).card := by
          have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
          have h4_div : 4 ≤ M / p ^ 2 := (Nat.le_div_iff_mul_le hp2_pos).mpr h4pe
          exact le_trans h4_div (card_multiples_Icc_ge x M (p ^ 2) hp2_pos)
        omega
  · -- `e ≥ 4`: pick two distinct multiples of `p ^ ((e + 1) / 2)` avoiding `B₀`!
    let e₁ := (e + 1) / 2
    let e₂ := e / 2
    have he12 : e₁ + e₂ = e := by omega
    have he₂_ge2 : 2 ≤ e₂ := by omega
    have he₁_ge2 : 2 ≤ e₁ := by omega
    have hpe₂_ge4 : 4 ≤ p ^ e₂ := by
      have hp2 : 2 ≤ p := hp.two_le
      have h1 : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
      have h2 : p ^ 2 ≤ p ^ e₂ := Nat.pow_le_pow_right hp.pos he₂_ge2
      omega
    have h8pe₁ : 8 * p ^ e₁ ≤ M := by
      have hpow : p ^ e = p ^ e₁ * p ^ e₂ := by rw [← pow_add, he12]
      nlinarith
    have hpe₁_pos : 0 < p ^ e₁ := pow_pos hp.pos e₁
    obtain ⟨b₁, hb₁_I, hb₁_notB₀, hdvd₁⟩ := exists_avoiding_multiple_in_consecInterval x M (p ^ e₁) B₀
      hpe₁_pos (by nlinarith)
    have hcard_ins : (insert b₁ B₀).card + 1 ≤ 8 := by
      have h1 := Finset.card_insert_le b₁ B₀
      omega
    obtain ⟨b₂, hb₂_I, hb₂_notIns, hdvd₂⟩ := exists_avoiding_multiple_in_consecInterval x M (p ^ e₁)
      (insert b₁ B₀) hpe₁_pos (le_trans (Nat.mul_le_mul_right _ hcard_ins) h8pe₁)
    have hb₂_ne : b₂ ≠ b₁ := fun h => hb₂_notIns (by simp [h])
    have hb₂_notB₀ : b₂ ∉ B₀ := fun h => hb₂_notIns (Finset.mem_insert_of_mem h)
    refine ⟨{b₁, b₂}, Finset.insert_subset hb₁_I (Finset.singleton_subset_iff.mpr hb₂_I), ?_,
      Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
    · rw [Finset.disjoint_insert_right]
      exact ⟨hb₁_notB₀, Finset.disjoint_singleton_right.mpr hb₂_notB₀⟩
    · have hv1 : e₁ ≤ b₁.factorization p :=
        (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_I).ne').mp hdvd₁
      have hv2 : e₁ ≤ b₂.factorization p :=
        (hp.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₂_I).ne').mp hdvd₂
      rw [Finset.sum_pair hb₂_ne.symm]
      omega

private lemma prod_ge_30_of_card_prime_ge_3 {S : Finset ℕ} (hS : 3 ≤ S.card)
    (hprime : ∀ p ∈ S, p.Prime) :
    ∃ p₀ p₁ p₂ : ℕ, p₀ ∈ S ∧ p₁ ∈ S ∧ p₂ ∈ S ∧ p₀ < p₁ ∧ p₁ < p₂ ∧
      p₀.Prime ∧ p₁.Prime ∧ p₂.Prime ∧ p₀ * p₁ * p₂ ∣ ∏ p ∈ S, p := by
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
  have hp₂_ne0 : p₂ ≠ p₀ := (Finset.mem_erase.mp hp₂_S₁).1
  have hp₂_mem : p₂ ∈ S := (Finset.mem_erase.mp hp₂_S₁).2
  have hp₁_lt_p₂ : p₁ < p₂ := lt_of_le_of_ne (Finset.min'_le S₁ p₂ hp₂_S₁) hp₂_ne1.symm
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
  rw [hprod_eq] at hdvd
  exact ⟨p₀, p₁, p₂, hp₀_mem, hp₁_mem, hp₂_mem, hp₀_lt_p₁, hp₁_lt_p₂,
    hprime p₀ hp₀_mem, hprime p₁ hp₁_mem, hprime p₂ hp₂_mem, hdvd⟩

private lemma exists_two_slots_for_R {A B₀ : Finset ℕ} {x M R : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hB₀_I : B₀ ⊆ consecInterval x M) (hB₀_card : B₀.card ≤ 6)
    (hR_pos : 0 < R) (h2R : 2 * R ≤ M)
    (hR_fac : ∀ p : ℕ, p.Prime →
      R.factorization p = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p)) :
    ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
      ∀ p : ℕ, p.Prime → R.factorization p ≤ ∑ b ∈ B₁, b.factorization p := by
  by_cases hR1 : R.primeFactors.card = 0
  · refine ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp, ?_⟩
    intro p hp
    have hmem : p ∉ R.primeFactors := by rw [Finset.card_eq_zero.mp hR1]; simp
    rw [Nat.mem_primeFactors_of_ne_zero hR_pos.ne'] at hmem
    have hnd : ¬ (p ∣ R) := fun h => hmem ⟨hp, h⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    exact Nat.zero_le _
  by_cases hR_one : R.primeFactors.card = 1
  · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hR_one
    have hp_mem : p ∈ R.primeFactors := by rw [hp_eq]; exact Finset.mem_singleton_self p
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have he_pos : 1 ≤ R.factorization p := by
      have hp_dvd_R : p ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp_mem).2
      exact (hp_prime.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hp_dvd_R)
    have hR_pow : R = p ^ (R.factorization p) := by
      have h1 := (Nat.prod_factorization_pow_eq_self hR_pos.ne').symm
      rw [Finsupp.prod, Nat.support_factorization, hp_eq, Finset.prod_singleton] at h1
      exact h1
    have h2pe : 2 * p ^ (R.factorization p) ≤ M := by rwa [← hR_pow]
    obtain ⟨T, hTI, hdisj, hTcard, hTval⟩ := exists_two_slots_for_prime_pow
      hA_card hA_pos hA_le hB₀_I hB₀_card hp_prime he_pos h2pe (hR_fac p hp_prime)
    refine ⟨T, hTI, hdisj, hTcard, ?_⟩
    intro q hq
    by_cases hqp : q = p
    · subst hqp; exact hTval
    · have hq_not_mem : q ∉ R.primeFactors := by rw [hp_eq]; exact Finset.notMem_singleton.mpr hqp
      have hnd : ¬ (q ∣ R) := fun hd => hq_not_mem ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr ⟨hq, hd⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd]
      exact Nat.zero_le _
  -- Now `2 ≤ R.primeFactors.card`
  have hR_ge2 : 2 ≤ R.primeFactors.card := by omega
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
  have hPsmall_pos : 1 ≤ ∏ p ∈ P_small, p ^ (R.factorization p) := by
    apply Finset.one_le_prod'
    intro q hq
    exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos
  have hPbig_le_R : ∏ p ∈ P_big, p ^ (R.factorization p) ≤ R := by
    conv_rhs => rw [hR_split]
    exact Nat.le_mul_of_pos_right _ hPsmall_pos
  have hM_lt : M < 7 * (L₇ + 1) := by
    have hdm := Nat.div_add_mod M 7
    have hml := Nat.mod_lt M (by norm_num : 0 < 7)
    dsimp [L₇]
    nlinarith
  by_cases hbig2 : 2 ≤ P_big.card
  · -- Case `2 ≤ P_big.card`: forces `M ≤ 20, R ≤ 10`, hence `R = 6` or `R = 10` (both squarefree 2-prime!).
    have hpow_big : (L₇ + 1) ^ 2 ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
      have h1 : (L₇ + 1) ^ P_big.card ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
        calc (L₇ + 1) ^ P_big.card = ∏ _p ∈ P_big, (L₇ + 1) := by simp
          _ ≤ ∏ p ∈ P_big, p ^ (R.factorization p) := by
            apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            intro p hp; exact (Finset.mem_filter.mp hp).2
      exact le_trans (Nat.pow_le_pow_right (by omega) hbig2) h1
    have hL7_sq : 2 * (L₇ + 1) ^ 2 < 7 * (L₇ + 1) := by nlinarith
    have hL7_le2 : L₇ ≤ 2 := by nlinarith
    have hR_le10 : R ≤ 10 := by omega
    have hR_pf_lt3 : R.primeFactors.card < 3 := by
      by_contra h3
      push Not at h3
      obtain ⟨p₀, p₁, p₂, _, _, _, h01, h12, hp₀, hp₁, hp₂, hdvd⟩ :=
        prod_ge_30_of_card_prime_ge_3 h3 (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have hp0_ge2 : 2 ≤ p₀ := hp₀.two_le
      have hp1_ge3 : 3 ≤ p₁ := by omega
      have hne4 : p₂ ≠ 4 := fun h => by rw [h] at hp₂; norm_num at hp₂
      have hp2_ge5 : 5 ≤ p₂ := by omega
      have h30_le : 30 ≤ p₀ * p₁ * p₂ :=
        Nat.mul_le_mul (Nat.mul_le_mul hp0_ge2 hp1_ge3) hp2_ge5
      have hle_R : p₀ * p₁ * p₂ ≤ R := by
        have hdvdR : p₀ * p₁ * p₂ ∣ ∏ p ∈ R.primeFactors, p := hdvd
        have hprod_dvd : (∏ p ∈ R.primeFactors, p) ∣ R := by
          calc ∏ p ∈ R.primeFactors, p
              ∣ ∏ p ∈ R.primeFactors, p ^ (R.factorization p) := by
                apply Finset.prod_dvd_prod_of_dvd
                intro p hp
                have h1 := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp
                have he1 : 1 ≤ R.factorization p :=
                  (h1.1.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h1.2)
                exact dvd_pow_self p (by omega)
            _ = R := hR_self.symm
        exact Nat.le_of_dvd hR_pos (dvd_trans hdvdR hprod_dvd)
      omega
    have hR_pf_eq2 : R.primeFactors.card = 2 := by omega
    obtain ⟨p₀, p₁, hp₀₁, hpf_eq⟩ := Finset.card_eq_two.mp hR_pf_eq2
    have hp₀_mem : p₀ ∈ R.primeFactors := by rw [hpf_eq]; exact Finset.mem_insert_self p₀ {p₁}
    have hp₁_mem : p₁ ∈ R.primeFactors := by rw [hpf_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p₁)
    have hp₀ : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀_mem
    have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_mem
    have he₀_pos : 1 ≤ R.factorization p₀ := by
      have h0d : p₀ ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp₀_mem).2
      exact (hp₀.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h0d)
    have he₁_pos : 1 ≤ R.factorization p₁ := by
      have h1d : p₁ ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp₁_mem).2
      exact (hp₁.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h1d)
    have hR_eq_p : R = p₀ ^ (R.factorization p₀) * p₁ ^ (R.factorization p₁) := by
      have h1 := hR_self
      rw [hpf_eq, Finset.prod_pair hp₀₁] at h1
      exact h1
    have hp_ge3 : 3 ≤ p₀ ∨ 3 ≤ p₁ := by
      have h0 := hp₀.two_le
      have h1 := hp₁.two_le
      omega
    have he₀_eq1 : R.factorization p₀ = 1 := by
      by_contra hne
      have hge2 : 2 ≤ R.factorization p₀ := by omega
      have hp₀2 : p₀ ^ 2 ≤ p₀ ^ (R.factorization p₀) := Nat.pow_le_pow_right hp₀.pos hge2
      have hp₁1 : p₁ ≤ p₁ ^ (R.factorization p₁) := Nat.le_self_pow (by omega) p₁
      have h0 := hp₀.two_le
      have h1 := hp₁.two_le
      have h12 : 12 ≤ p₀ ^ 2 * p₁ := by
        rcases hp_ge3 with hp03 | hp13 <;> nlinarith
      have hle_R : p₀ ^ 2 * p₁ ≤ R := by
        rw [hR_eq_p]; exact Nat.mul_le_mul hp₀2 hp₁1
      omega
    have he₁_eq1 : R.factorization p₁ = 1 := by
      by_contra hne
      have hge2 : 2 ≤ R.factorization p₁ := by omega
      have hp₁2 : p₁ ^ 2 ≤ p₁ ^ (R.factorization p₁) := Nat.pow_le_pow_right hp₁.pos hge2
      have hp₀1' : p₀ ≤ p₀ ^ (R.factorization p₀) := Nat.le_self_pow (by omega) p₀
      have h0 := hp₀.two_le
      have h1 := hp₁.two_le
      have h12 : 12 ≤ p₀ * p₁ ^ 2 := by
        rcases hp_ge3 with hp03 | hp13 <;> nlinarith
      have hle_R : p₀ * p₁ ^ 2 ≤ R := by
        rw [hR_eq_p]; exact Nat.mul_le_mul hp₀1' hp₁2
      omega
    obtain ⟨b₀, hb₀_I, hb₀_notB₀, hp₀_b₀⟩ :=
      exists_prime_multiple_of_deficit_pos hA_pos hA_le hB₀_I hp₀ (by rw [← hR_fac p₀ hp₀]; omega)
    obtain ⟨b₁, hb₁_I, hb₁_notB₀, hp₁_b₁⟩ :=
      exists_prime_multiple_of_deficit_pos hA_pos hA_le hB₀_I hp₁ (by rw [← hR_fac p₁ hp₁]; omega)
    refine ⟨{b₀, b₁}, Finset.insert_subset hb₀_I (Finset.singleton_subset_iff.mpr hb₁_I), ?_,
      Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
    · rw [Finset.disjoint_insert_right]
      exact ⟨hb₀_notB₀, Finset.disjoint_singleton_right.mpr hb₁_notB₀⟩
    · intro q hq
      by_cases hqp₀ : q = p₀
      · subst hqp₀
        rw [he₀_eq1]
        have hv : 1 ≤ b₀.factorization q :=
          (hp₀.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₀_I).ne').mp
            (by simpa only [pow_one] using hp₀_b₀)
        exact le_trans hv (Finset.single_le_sum (f := fun b => b.factorization q)
          (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self b₀ {b₁}))
      · by_cases hqp₁ : q = p₁
        · subst hqp₁
          rw [he₁_eq1]
          have hv : 1 ≤ b₁.factorization q :=
            (hp₁.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_I).ne').mp
              (by simpa only [pow_one] using hp₁_b₁)
          exact le_trans hv (Finset.single_le_sum (f := fun b => b.factorization q)
            (fun _ _ => Nat.zero_le _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self b₁)))
        · rw [hR_eq_p, Nat.factorization_mul (pow_ne_zero _ hp₀.ne_zero) (pow_ne_zero _ hp₁.ne_zero),
              Finsupp.add_apply, Nat.Prime.factorization_pow hp₀, Nat.Prime.factorization_pow hp₁,
              Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm hqp₀), if_neg (Ne.symm hqp₁)]
          exact Nat.zero_le _
  · -- Case `P_big.card < 2`: either `P_big.card = 0` or `P_big.card = 1`.
    push Not at hbig2
    have hP_card_sum : P_big.card + P_small.card = R.primeFactors.card := by
      have h1 := Finset.sum_filter_add_sum_filter_not R.primeFactors
        (fun p => L₇ < p ^ (R.factorization p)) (fun _ => (1 : ℕ))
      simpa only [Finset.sum_const, smul_eq_mul, mul_one] using h1
    by_cases hbig0 : P_big.card = 0
    · -- Subcase `P_big.card = 0`: every prime power is `≤ L₇`.
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
          rw [← hprod', Nat.primeFactors_one, Finset.card_empty] at hR_ge2
          omega
        | [D₁] =>
          simp only [List.prod_cons, List.prod_nil, mul_one] at hprod'
          have hD₁ := hbnd' D₁ List.mem_cons_self
          have h7D₁ : (B₀.card + 1) * D₁ ≤ M := by
            have h1 : (B₀.card + 1) * D₁ ≤ 7 * L₇ := Nat.mul_le_mul (by omega) hD₁.2
            exact le_trans h1 (Nat.mul_div_le M 7)
          obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
            exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁.1 h7D₁
          refine ⟨{b₁}, Finset.singleton_subset_iff.mpr hb₁_I,
            Finset.disjoint_singleton_right.mpr hb₁_notB₀, by simp, ?_⟩
          intro p _hp
          rw [Finset.sum_singleton, ← hprod']
          exact (Nat.factorization_le_iff_dvd (by omega : D₁ ≠ 0)
            (pos_of_mem_consecInterval hb₁_I).ne').mpr hD₁_b₁ p
        | [D₁, D₂] =>
          have hD₁ := hbnd' D₁ List.mem_cons_self
          have hD₂ := hbnd' D₂ (List.mem_cons_of_mem D₁ List.mem_cons_self)
          have h7L : 7 * L₇ ≤ M := Nat.mul_div_le M 7
          have h7D₁ : (B₀.card + 1) * D₁ ≤ M :=
            le_trans (Nat.mul_le_mul (by omega) hD₁.2) h7L
          have h7D₂ : (B₀.card + 1) * D₂ ≤ M :=
            le_trans (Nat.mul_le_mul (by omega) hD₂.2) h7L
          obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
            exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁.1 h7D₁
          obtain ⟨b₂, hb₂_I, hb₂_notB₀, hD₂_b₂⟩ :=
            exists_avoiding_multiple_in_consecInterval x M D₂ B₀ hD₂.1 h7D₂
          refine ⟨{b₁, b₂}, Finset.insert_subset hb₁_I (Finset.singleton_subset_iff.mpr hb₂_I), ?_,
            Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
          · rw [Finset.disjoint_insert_right]
            exact ⟨hb₁_notB₀, Finset.disjoint_singleton_right.mpr hb₂_notB₀⟩
          · intro p hp
            by_cases hRp : 0 < R.factorization p
            · rw [← hprod'] at hRp
              obtain ⟨D, hD_mem, hD_eq⟩ := exists_factor_dvd_of_pairwise_coprime hp [D₁, D₂]
                (fun u hu => (hbnd' u hu).1) hcop' hRp
              have hRp_eq : R.factorization p = D.factorization p := by rw [← hprod', hD_eq]
              rw [hRp_eq]
              rcases List.mem_cons.mp hD_mem with hD1_eq | hD_mem2
              · subst hD1_eq
                have hle_b₁ : D.factorization p ≤ b₁.factorization p :=
                  (Nat.factorization_le_iff_dvd (by omega : D ≠ 0)
                    (pos_of_mem_consecInterval hb₁_I).ne').mpr hD₁_b₁ p
                have hb₁_le_sum : b₁.factorization p ≤ ∑ b ∈ ({b₁, b₂} : Finset ℕ), b.factorization p :=
                  Finset.single_le_sum (f := fun b => b.factorization p) (fun _ _ => Nat.zero_le _)
                    (Finset.mem_insert_self b₁ {b₂})
                exact le_trans hle_b₁ hb₁_le_sum
              · have hD2_eq : D = D₂ := by simpa using hD_mem2
                subst hD2_eq
                have hle_b₂ : D.factorization p ≤ b₂.factorization p :=
                  (Nat.factorization_le_iff_dvd (by omega : D ≠ 0)
                    (pos_of_mem_consecInterval hb₂_I).ne').mpr hD₂_b₂ p
                have hb₂_le_sum : b₂.factorization p ≤ ∑ b ∈ ({b₁, b₂} : Finset ℕ), b.factorization p :=
                  Finset.single_le_sum (f := fun b => b.factorization p) (fun _ _ => Nat.zero_le _)
                    (Finset.mem_insert_of_mem (Finset.mem_singleton_self b₂))
                exact le_trans hle_b₂ hb₂_le_sum
            · have h0 : R.factorization p = 0 := by omega
              rw [h0]; exact Nat.zero_le _
        | _ :: _ :: _ :: _ => simp at hlen'
      rcases le_or_gt bs.length 2 with hlen2 | hlen3
      · exact hcover_of_bins_le2 bs hlen2 hbs_bnd hbs_prod hbs_cop
      · -- `3 ≤ bs.length`: forces `L₇ ≤ 11`, `M ≤ 83`, `R ≤ 41`, and `R = 30`.
        have hsq := pairwise_mul_gt_pow_le_sq L₇ bs.length bs rfl (by omega) hbs_pw
        rw [hbs_prod] at hsq
        have hpow3 : (L₇ + 1) ^ 3 ≤ R ^ 2 :=
          le_trans (Nat.pow_le_pow_right (by omega) hlen3) hsq
        have h4R2 : 4 * R ^ 2 < 49 * (L₇ + 1) ^ 2 := by
          have h1 : (2 * R) ^ 2 < (7 * (L₇ + 1)) ^ 2 :=
            Nat.pow_lt_pow_left (lt_of_le_of_lt h2R hM_lt) (by omega)
          have h2 : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
          have h3 : (7 * (L₇ + 1)) ^ 2 = 49 * (L₇ + 1) ^ 2 := by ring
          omega
        have hL7_cub : 4 * (L₇ + 1) ^ 3 < 49 * (L₇ + 1) ^ 2 :=
          lt_of_le_of_lt (Nat.mul_le_mul_left 4 hpow3) h4R2
        have hL7_le11 : L₇ ≤ 11 := by
          have hmul : (L₇ + 1) ^ 2 * (4 * (L₇ + 1)) < (L₇ + 1) ^ 2 * 49 := by
            have hpow : (L₇ + 1) ^ 3 = (L₇ + 1) ^ 2 * (L₇ + 1) := by ring
            have heq1 : (L₇ + 1) ^ 2 * (4 * (L₇ + 1)) = 4 * (L₇ + 1) ^ 3 := by rw [hpow]; ring
            have heq2 : (L₇ + 1) ^ 2 * 49 = 49 * (L₇ + 1) ^ 2 := by ring
            omega
          have hlt49 : 4 * (L₇ + 1) < 49 := Nat.lt_of_mul_lt_mul_left hmul
          omega
        have hR_le41 : R ≤ 41 := by omega
        -- Every bin `u ∈ bs` has `2 ≤ u` (otherwise `1 * v ≤ L₇` contradicts `hbs_pw`).
        have hbs_ge2 : ∀ u ∈ bs, 2 ≤ u := by
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
            rw [hu_eq1, mul_one] at hgt
            omega
          · have hpw2 := hbs_pw.2.1
            rw [List.pairwise_cons] at hpw2
            have hgt : L₇ < u * v := hpw2.1 v hv2
            rw [hu_eq1, one_mul] at hgt
            omega
        -- `3 ≤ bs.length` + pairwise coprime + `≥ 2` implies `3 ≤ R.primeFactors.card`.
        have hR_ge3 : 3 ≤ R.primeFactors.card := by
          match bs with
          | [] | [_] | [_, _] => simp at hlen3
          | u₀ :: u₁ :: u₂ :: rest =>
            have hu₀ := hbs_ge2 u₀ (by simp)
            have hu₁ := hbs_ge2 u₁ (by simp)
            have hu₂ := hbs_ge2 u₂ (by simp)
            let p₀ := u₀.minFac
            let p₁ := u₁.minFac
            let p₂ := u₂.minFac
            have hp₀ : p₀.Prime := Nat.minFac_prime (by omega)
            have hp₁ : p₁.Prime := Nat.minFac_prime (by omega)
            have hp₂ : p₂.Prime := Nat.minFac_prime (by omega)
            have hp₀_u₀ : p₀ ∣ u₀ := Nat.minFac_dvd u₀
            have hp₁_u₁ : p₁ ∣ u₁ := Nat.minFac_dvd u₁
            have hp₂_u₂ : p₂ ∣ u₂ := Nat.minFac_dvd u₂
            rw [List.pairwise_cons] at hbs_cop
            have hcop01 : Nat.Coprime u₀ u₁ := hbs_cop.1 u₁ (by simp)
            have hcop02 : Nat.Coprime u₀ u₂ := hbs_cop.1 u₂ (by simp)
            have hbs_cop2 := hbs_cop.2
            rw [List.pairwise_cons] at hbs_cop2
            have hcop12 : Nat.Coprime u₁ u₂ := hbs_cop2.1 u₂ (by simp)
            have hne01 : p₀ ≠ p₁ := by
              intro heq
              have hd : p₀ ∣ Nat.gcd u₀ u₁ := Nat.dvd_gcd hp₀_u₀ (heq ▸ hp₁_u₁)
              rw [hcop01.gcd_eq_one] at hd
              exact hp₀.not_dvd_one hd
            have hne02 : p₀ ≠ p₂ := by
              intro heq
              have hd : p₀ ∣ Nat.gcd u₀ u₂ := Nat.dvd_gcd hp₀_u₀ (heq ▸ hp₂_u₂)
              rw [hcop02.gcd_eq_one] at hd
              exact hp₀.not_dvd_one hd
            have hne12 : p₁ ≠ p₂ := by
              intro heq
              have hd : p₁ ∣ Nat.gcd u₁ u₂ := Nat.dvd_gcd hp₁_u₁ (heq ▸ hp₂_u₂)
              rw [hcop12.gcd_eq_one] at hd
              exact hp₁.not_dvd_one hd
            have hp₀_R : p₀ ∈ R.primeFactors := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr
              ⟨hp₀, dvd_trans hp₀_u₀ (by rw [← hbs_prod]; simp [List.prod_cons, dvd_mul_right])⟩
            have hp₁_R : p₁ ∈ R.primeFactors := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr
              ⟨hp₁, dvd_trans hp₁_u₁ (by
                rw [← hbs_prod]; simp only [List.prod_cons]
                exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)⟩
            have hp₂_R : p₂ ∈ R.primeFactors := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mpr
              ⟨hp₂, dvd_trans hp₂_u₂ (by
                rw [← hbs_prod]; simp only [List.prod_cons]
                exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _)⟩
            have hsub3 : {p₀, p₁, p₂} ⊆ R.primeFactors := by
              intro q hq
              rcases Finset.mem_insert.mp hq with rfl | hq'
              · exact hp₀_R
              · rcases Finset.mem_insert.mp hq' with rfl | hq''
                · exact hp₁_R
                · rw [Finset.mem_singleton.mp hq'']; exact hp₂_R
            have hcard3 : ({p₀, p₁, p₂} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]), Finset.card_pair hne12]
            exact hcard3 ▸ Finset.card_le_card hsub3
        obtain ⟨p₀, p₁, p₂, hp₀_mem, hp₁_mem, hp₂_mem, h01, h12, hp₀, hp₁, hp₂, hdvd⟩ :=
          prod_ge_30_of_card_prime_ge_3 hR_ge3 (fun p hp => Nat.prime_of_mem_primeFactors hp)
        have hprod_dvd : (∏ p ∈ R.primeFactors, p) ∣ R := by
          calc ∏ p ∈ R.primeFactors, p
              ∣ ∏ p ∈ R.primeFactors, p ^ (R.factorization p) := by
                apply Finset.prod_dvd_prod_of_dvd
                intro p hp
                have h1 := (Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp
                have he1 : 1 ≤ R.factorization p :=
                  (h1.1.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using h1.2)
                exact dvd_pow_self p (by omega)
            _ = R := hR_self.symm
        have hp012_dvd : p₀ * p₁ * p₂ ∣ R := dvd_trans hdvd hprod_dvd
        have hp012_le : p₀ * p₁ * p₂ ≤ 41 := le_trans (Nat.le_of_dvd hR_pos hp012_dvd) hR_le41
        have hp0_eq2 : p₀ = 2 := by
          have hp0_ge2 := hp₀.two_le
          by_contra hne2
          have hp0_ge3 : 3 ≤ p₀ := by omega
          have hp1_ge5 : 5 ≤ p₁ := by
            have hne4 : p₁ ≠ 4 := fun h => by rw [h] at hp₁; norm_num at hp₁
            omega
          have hp2_ge7 : 7 ≤ p₂ := by
            have hne6 : p₂ ≠ 6 := fun h => by rw [h] at hp₂; norm_num at hp₂
            omega
          have hge : 105 ≤ p₀ * p₁ * p₂ :=
            Nat.mul_le_mul (Nat.mul_le_mul hp0_ge3 hp1_ge5) hp2_ge7
          omega
        have hp1_eq3 : p₁ = 3 := by
          by_contra hne3
          have hp0_ge2 := hp₀.two_le
          have hp1_ge5 : 5 ≤ p₁ := by
            have hne4 : p₁ ≠ 4 := fun h => by rw [h] at hp₁; norm_num at hp₁
            omega
          have hp2_ge7 : 7 ≤ p₂ := by
            have hne6 : p₂ ≠ 6 := fun h => by rw [h] at hp₂; norm_num at hp₂
            omega
          have hge : 70 ≤ p₀ * p₁ * p₂ :=
            Nat.mul_le_mul (Nat.mul_le_mul hp0_ge2 hp1_ge5) hp2_ge7
          omega
        have hp2_eq5 : p₂ = 5 := by
          by_contra hne5
          have hp0_ge2 := hp₀.two_le
          have hp1_ge3 : 3 ≤ p₁ := by omega
          have hp2_ge4 : 4 ≤ p₂ := by omega
          have hne4 : p₂ ≠ 4 := fun h => by rw [h] at hp₂; norm_num at hp₂
          have hne6 : p₂ ≠ 6 := fun h => by rw [h] at hp₂; norm_num at hp₂
          have hp2_ge7 : 7 ≤ p₂ := by omega
          have hge : 42 ≤ p₀ * p₁ * p₂ :=
            Nat.mul_le_mul (Nat.mul_le_mul hp0_ge2 hp1_ge3) hp2_ge7
          omega
        rw [hp0_eq2, hp1_eq3, hp2_eq5] at hp012_dvd
        obtain ⟨k30, hk30⟩ := hp012_dvd
        have hk_pos : 1 ≤ k30 := by
          by_contra h0
          have hk0 : k30 = 0 := by omega
          rw [hk0, mul_zero] at hk30
          omega
        have hk_eq1 : k30 = 1 := by
          rw [hk30] at hR_le41
          omega
        have hR_eq30 : R = 30 := by rw [hk30, hk_eq1]
        have hM_ge60 : 60 ≤ M := by omega
        obtain ⟨b₁, hb₁_I, hb₁_notB₀, h6b₁⟩ :=
          exists_avoiding_multiple_in_consecInterval x M 6 B₀ (by norm_num) (by omega)
        obtain ⟨b₂, hb₂_I, hb₂_notB₀, h5b₂⟩ :=
          exists_avoiding_multiple_in_consecInterval x M 5 B₀ (by norm_num) (by omega)
        refine ⟨{b₁, b₂}, Finset.insert_subset hb₁_I (Finset.singleton_subset_iff.mpr hb₂_I), ?_,
          Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
        · rw [Finset.disjoint_insert_right]
          exact ⟨hb₁_notB₀, Finset.disjoint_singleton_right.mpr hb₂_notB₀⟩
        · intro p hp
          rw [hR_eq30]
          have h30_fac : (30 : ℕ) = 2 * 3 * 5 := by norm_num
          rw [h30_fac, Nat.factorization_mul (by norm_num) (by norm_num),
              Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply]
          have h2_b₁ : (2 : ℕ).factorization p ≤ b₁.factorization p :=
            (Nat.factorization_le_iff_dvd (by norm_num) (pos_of_mem_consecInterval hb₁_I).ne').mpr
              (dvd_trans (by norm_num) h6b₁) p
          have h3_b₁ : (3 : ℕ).factorization p ≤ b₁.factorization p :=
            (Nat.factorization_le_iff_dvd (by norm_num) (pos_of_mem_consecInterval hb₁_I).ne').mpr
              (dvd_trans (by norm_num) h6b₁) p
          have h5_b₂ : (5 : ℕ).factorization p ≤ b₂.factorization p :=
            (Nat.factorization_le_iff_dvd (by norm_num) (pos_of_mem_consecInterval hb₂_I).ne').mpr h5b₂ p
          have hb₁_sum : b₁.factorization p ≤ ∑ b ∈ ({b₁, b₂} : Finset ℕ), b.factorization p :=
            Finset.single_le_sum (f := fun b => b.factorization p) (fun _ _ => Nat.zero_le _)
              (Finset.mem_insert_self b₁ {b₂})
          have hb₂_sum : b₂.factorization p ≤ ∑ b ∈ ({b₁, b₂} : Finset ℕ), b.factorization p :=
            Finset.single_le_sum (f := fun b => b.factorization p) (fun _ _ => Nat.zero_le _)
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self b₂))
          by_cases hp2 : p = 2
          · subst hp2; norm_num at h2_b₁ ⊢; exact le_trans h2_b₁ hb₁_sum
          · by_cases hp3 : p = 3
            · subst hp3; norm_num at h3_b₁ ⊢; exact le_trans h3_b₁ hb₁_sum
            · by_cases hp5 : p = 5
              · subst hp5; norm_num at h5_b₂ ⊢; exact le_trans h5_b₂ hb₂_sum
              · have hf2 : (2 : ℕ).factorization p = 0 := by
                  rw [← pow_one 2, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_apply,
                      if_neg (Ne.symm hp2)]
                have hf3 : (3 : ℕ).factorization p = 0 := by
                  rw [← pow_one 3, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_apply,
                      if_neg (Ne.symm hp3)]
                have hf5 : (5 : ℕ).factorization p = 0 := by
                  rw [← pow_one 5, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_apply,
                      if_neg (Ne.symm hp5)]
                rw [hf2, hf3, hf5]
                exact Nat.zero_le _
    · -- Subcase `P_big.card = 1`: `R = p^e * Q` with `Q ∈ {2, 3}`.
      have hPbig_card : P_big.card = 1 := by omega
      obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hPbig_card
      have hp_big : p ∈ P_big := by rw [hp_eq]; exact Finset.mem_singleton_self p
      have hp_mem : p ∈ R.primeFactors := (Finset.mem_filter.mp hp_big).1
      have hp_gt : L₇ < p ^ (R.factorization p) := (Finset.mem_filter.mp hp_big).2
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      let e := R.factorization p
      let Q := ∏ q ∈ P_small, q ^ (R.factorization q)
      have he_pos : 1 ≤ e := by
        have hpd : p ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hp_mem).2
        exact (hp_prime.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hpd)
      have hR_pQ : R = p ^ e * Q := by
        calc R = (∏ q ∈ P_big, q ^ (R.factorization q)) * Q := hR_split
          _ = p ^ e * Q := by rw [hp_eq, Finset.prod_singleton]
      have hPsmall_ne : P_small.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨q₀, hq₀_small⟩ := hPsmall_ne
      have hQ_ge2 : 2 ≤ Q := by
        have hq₀_mem := (Finset.mem_filter.mp hq₀_small).1
        have hq₀_pr : q₀.Prime := Nat.prime_of_mem_primeFactors hq₀_mem
        have hq₀_d : q₀ ∣ R := ((Nat.mem_primeFactors_of_ne_zero hR_pos.ne').mp hq₀_mem).2
        have hq₀_e : 1 ≤ R.factorization q₀ :=
          (hq₀_pr.pow_dvd_iff_le_factorization hR_pos.ne').mp (by simpa only [pow_one] using hq₀_d)
        have hpow_ge2 : 2 ≤ q₀ ^ (R.factorization q₀) := by
          calc 2 ≤ q₀ := hq₀_pr.two_le
            _ = q₀ ^ 1 := (pow_one q₀).symm
            _ ≤ q₀ ^ (R.factorization q₀) := Nat.pow_le_pow_right hq₀_pr.pos hq₀_e
        have hdvd_Q : q₀ ^ (R.factorization q₀) ∣ Q := Finset.dvd_prod_of_mem _ hq₀_small
        have hQ_pos : 0 < Q := Finset.prod_pos (fun q hq =>
          pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _)
        exact le_trans hpow_ge2 (Nat.le_of_dvd hQ_pos hdvd_Q)
      have hQ_le3 : Q ≤ 3 := by
        have hpe_ge : L₇ + 1 ≤ p ^ e := hp_gt
        have hmul1 : 2 * (L₇ + 1) * Q ≤ 2 * p ^ e * Q :=
          Nat.mul_le_mul_right Q (Nat.mul_le_mul_left 2 hpe_ge)
        have hmul2 : 2 * p ^ e * Q = 2 * R := by rw [hR_pQ, mul_assoc]
        have hlt : 2 * (L₇ + 1) * Q < 7 * (L₇ + 1) :=
          lt_of_le_of_lt (le_trans hmul1 (by rw [hmul2]; exact h2R)) hM_lt
        have hcomm : (L₇ + 1) * (2 * Q) < (L₇ + 1) * 7 := by
          simpa only [mul_comm, mul_assoc, mul_left_comm] using hlt
        have h2Q_lt7 : 2 * Q < 7 := Nat.lt_of_mul_lt_mul_left hcomm
        omega
      have hQ_cases : Q = 2 ∨ Q = 3 := by omega
      have hQ_prime : Q.Prime := by
        rcases hQ_cases with h2 | h3 <;> [rw [h2]; rw [h3]] <;> norm_num
      have hQp_ne : p ≠ Q := by
        intro heq
        have hp_dvd_Q : p ∣ Q := heq ▸ dvd_refl p
        obtain ⟨q, hq_sm, hq_dvd⟩ :=
          (hp_prime.prime.dvd_finsetProd_iff (fun q => q ^ (R.factorization q))).mp hp_dvd_Q
        have hq_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq_sm).1
        have hqp_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_pr).mp
          (hp_prime.dvd_of_dvd_pow hq_dvd)
        have hp_sm : p ∈ P_small := hqp_eq ▸ hq_sm
        exact (Finset.mem_filter.mp hp_sm).2 hp_gt
      have hR_fac_other : ∀ q : ℕ, q.Prime → q ≠ p → q ≠ Q → R.factorization q = 0 := by
        intro q _hq hqp hqQ
        rw [hR_pQ, Nat.factorization_mul (pow_ne_zero _ hp_prime.ne_zero) hQ_prime.ne_zero,
            Finsupp.add_apply, Nat.Prime.factorization_pow hp_prime, Finsupp.single_apply,
            if_neg hqp.symm, ← pow_one Q, Nat.Prime.factorization_pow hQ_prime, Finsupp.single_apply,
            if_neg (Ne.symm hqQ)]
        rfl
      have hR_fac_Q : R.factorization Q = 1 := by
        rw [hR_pQ, Nat.factorization_mul (pow_ne_zero _ hp_prime.ne_zero) hQ_prime.ne_zero,
            Finsupp.add_apply, Nat.Prime.factorization_pow hp_prime, Finsupp.single_apply,
            if_neg hQp_ne, hQ_prime.factorization_self]
      have hcover_p_Q : ∀ b₁ b₂ : ℕ, b₁ ∈ consecInterval x M → b₂ ∈ consecInterval x M →
          b₁ ∉ B₀ → b₂ ∉ B₀ → e ≤ b₁.factorization p + b₂.factorization p →
          (b₁ = b₂ → e ≤ b₁.factorization p) → Q ∣ b₁ ∨ Q ∣ b₂ →
          ∃ B₁ ⊆ consecInterval x M, Disjoint B₀ B₁ ∧ B₁.card ≤ 2 ∧
            ∀ q : ℕ, q.Prime → R.factorization q ≤ ∑ b ∈ B₁, b.factorization q := by
        intro b₁ b₂ hb₁_I hb₂_I hb₁_notB₀ hb₂_notB₀ hp_cov hb_eq hQ_cov
        refine ⟨{b₁, b₂}, Finset.insert_subset hb₁_I (Finset.singleton_subset_iff.mpr hb₂_I), ?_,
          Finset.card_insert_le _ _ |>.trans (by simp), ?_⟩
        · rw [Finset.disjoint_insert_right]
          exact ⟨hb₁_notB₀, Finset.disjoint_singleton_right.mpr hb₂_notB₀⟩
        · intro q hq
          by_cases hqp : q = p
          · subst hqp
            by_cases h12 : b₁ = b₂
            · have hle_eq := hb_eq h12
              subst h12
              have heq_set : ({b₁, b₁} : Finset ℕ) = {b₁} := by simp
              rw [heq_set, Finset.sum_singleton]
              exact hle_eq
            · rw [Finset.sum_pair h12]; exact hp_cov
          · by_cases hqQ : q = Q
            · subst hqQ
              rw [hR_fac_Q]
              rcases hQ_cov with hQb₁ | hQb₂
              · have hv1 : 1 ≤ b₁.factorization Q :=
                  (hQ_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_I).ne').mp
                    (by simpa only [pow_one] using hQb₁)
                exact le_trans hv1 (Finset.single_le_sum (f := fun b => b.factorization Q)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self b₁ {b₂}))
              · have hv2 : 1 ≤ b₂.factorization Q :=
                  (hQ_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₂_I).ne').mp
                    (by simpa only [pow_one] using hQb₂)
                exact le_trans hv2 (Finset.single_le_sum (f := fun b => b.factorization Q)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self b₂)))
            · rw [hR_fac_other q hq hqp hqQ]; exact Nat.zero_le _
      obtain ⟨bQ, hbQ_I, hbQ_notB₀, hQ_dvd⟩ :=
        exists_prime_multiple_of_deficit_pos hA_pos hA_le hB₀_I hQ_prime (by rw [← hR_fac Q hQ_prime]; omega)
      by_cases he1_eq : e = 1
      · obtain ⟨bp, hbp_I, hbp_notB₀, hp_dvd⟩ :=
          exists_prime_multiple_of_deficit_pos hA_pos hA_le hB₀_I hp_prime (by rw [← hR_fac p hp_prime]; omega)
        have hv_bp : 1 ≤ bp.factorization p :=
          (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hbp_I).ne').mp
            (by simpa only [pow_one] using hp_dvd)
        have hvp : e ≤ bp.factorization p + bQ.factorization p := by omega
        exact hcover_p_Q bp bQ hbp_I hbQ_I hbp_notB₀ hbQ_notB₀ hvp (fun _ => by omega) (Or.inr hQ_dvd)
      · have he2 : 2 ≤ e := by omega
        by_cases hpe_ex : ∃ b₁ ∈ consecInterval x M \ B₀, p ^ e ∣ b₁
        · obtain ⟨b₁, hb₁_sdiff, hpe_b₁⟩ := hpe_ex
          rw [Finset.mem_sdiff] at hb₁_sdiff
          have hv_b1 : e ≤ b₁.factorization p :=
            (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_sdiff.1).ne').mp hpe_b₁
          have hvp : e ≤ b₁.factorization p + bQ.factorization p := by omega
          exact hcover_p_Q b₁ bQ hb₁_sdiff.1 hbQ_I hb₁_sdiff.2 hbQ_notB₀ hvp
            (fun _ => hv_b1) (Or.inr hQ_dvd)
        · push Not at hpe_ex
          by_cases he_odd : e % 2 = 1
          · -- Odd `e = 2*m + 1` (`m ≥ 1`): split `R = p^(m+1) * (p^m * Q)`.
            let m := e / 2
            have hm_ge1 : 1 ≤ m := by omega
            have he_eq : e = 2 * m + 1 := by omega
            let D₁ := p ^ (m + 1)
            let D₂ := p ^ m * Q
            have hD₁_pos : 0 < D₁ := pow_pos hp_prime.pos _
            have hD₂_pos : 0 < D₂ := mul_pos (pow_pos hp_prime.pos _) hQ_prime.pos
            have hM_ge48 : 48 ≤ M := by
              have he3 : 3 ≤ e := by omega
              by_cases hp_eq2 : p = 2
              · have hQ3 : Q = 3 := by
                  rcases hQ_cases with h2 | h3
                  · exact absurd (hp_eq2.trans h2.symm) hQp_ne
                  · exact h3
                have h8 : 8 ≤ p ^ e := by
                  rw [hp_eq2]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) he3)
                have hR24 : 24 ≤ R := by rw [hR_pQ, hQ3]; exact Nat.mul_le_mul_right 3 h8
                omega
              · have hp3 : 3 ≤ p := by have := hp_prime.two_le; omega
                have h27 : 27 ≤ p ^ e := by
                  have h1 : 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
                  have h2 : p ^ 3 ≤ p ^ e := Nat.pow_le_pow_right hp_prime.pos he3
                  exact le_trans (by norm_num) (le_trans h1 h2)
                have hR54 : 54 ≤ R := by rw [hR_pQ]; exact Nat.mul_le_mul h27 hQ_ge2
                omega
            have h8D₁ : 8 * D₁ ≤ M := by
              have hcub : (8 * D₁) ^ 3 ≤ M ^ 3 := by
                have h1 : (8 * D₁) ^ 3 = 512 * p ^ (3 * m + 3) := by
                  dsimp [D₁]; rw [mul_pow, ← pow_mul]; ring
                have hpow_le : p ^ (3 * m + 3) ≤ p ^ (4 * m + 2) :=
                  Nat.pow_le_pow_right hp_prime.pos (by omega)
                have hQ4 : 4 ≤ Q ^ 2 := by
                  rcases hQ_cases with h2 | h3 <;> [rw [h2]; rw [h3]] <;> norm_num
                have h2b : 512 * p ^ (3 * m + 3) ≤ 128 * R ^ 2 := by
                  have hR2_eq : R ^ 2 = p ^ (4 * m + 2) * Q ^ 2 := by
                    rw [hR_pQ, he_eq, mul_pow, ← pow_mul]; ring
                  rw [hR2_eq]
                  exact le_trans (Nat.mul_le_mul_left 512 hpow_le)
                    (calc 512 * p ^ (4 * m + 2) = 128 * (p ^ (4 * m + 2) * 4) := by ring
                      _ ≤ 128 * (p ^ (4 * m + 2) * Q ^ 2) :=
                          Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left _ hQ4))
                have h4R2 : 4 * R ^ 2 ≤ M ^ 2 := by
                  have hsq : (2 * R) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left h2R 2
                  linarith [show (2 * R) ^ 2 = 4 * R ^ 2 by ring]
                have hM2 : 128 * R ^ 2 ≤ 32 * M ^ 2 := by linarith
                have hM3 : 32 * M ^ 2 ≤ M ^ 3 := by
                  have h32M : 32 ≤ M := by omega
                  calc 32 * M ^ 2 = M ^ 2 * 32 := by ring
                    _ ≤ M ^ 2 * M := Nat.mul_le_mul_left _ h32M
                    _ = M ^ 3 := by ring
                omega
              by_contra hlt
              push Not at hlt
              exact absurd (Nat.pow_lt_pow_left hlt (by omega)) (not_lt_of_ge hcub)
            have h8D₂ : 8 * D₂ ≤ M := by
              have hsq : p * (8 * D₂) ^ 2 ≤ p * M ^ 2 := by
                have h1 : p * (8 * D₂) ^ 2 = 32 * Q * (2 * R) := by
                  dsimp [D₂]; rw [hR_pQ, he_eq]; ring
                have h2 : 32 * Q * (2 * R) ≤ 32 * Q * M := Nat.mul_le_mul_left _ h2R
                have h3 : 32 * Q ≤ p * M := by
                  have h32Q : 32 * Q ≤ 96 := by omega
                  have hpM : 96 ≤ p * M :=
                    calc 96 = 2 * 48 := by norm_num
                      _ ≤ p * M := Nat.mul_le_mul hp_prime.two_le hM_ge48
                  omega
                calc p * (8 * D₂) ^ 2 = 32 * Q * (2 * R) := h1
                  _ ≤ 32 * Q * M := h2
                  _ ≤ (p * M) * M := Nat.mul_le_mul_right M h3
                  _ = p * M ^ 2 := by ring
              have hsq2 : (8 * D₂) ^ 2 ≤ M ^ 2 := Nat.le_of_mul_le_mul_left hsq hp_prime.pos
              by_contra hlt
              push Not at hlt
              exact absurd (Nat.pow_lt_pow_left hlt (by omega)) (not_lt_of_ge hsq2)
            obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
              exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁_pos
                (le_trans (Nat.mul_le_mul_right D₁ (by omega : B₀.card + 1 ≤ 8)) h8D₁)
            have hcard_ins : (insert b₁ B₀).card + 1 ≤ 8 := by
              have h1 := Finset.card_insert_le b₁ B₀; omega
            obtain ⟨b₂, hb₂_I, hb₂_notIns, hD₂_b₂⟩ :=
              exists_avoiding_multiple_in_consecInterval x M D₂ (insert b₁ B₀) hD₂_pos
                (le_trans (Nat.mul_le_mul_right _ hcard_ins) h8D₂)
            have hb₂_notB₀ : b₂ ∉ B₀ := fun h => hb₂_notIns (Finset.mem_insert_of_mem h)
            have hv1 : m + 1 ≤ b₁.factorization p :=
              (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_I).ne').mp hD₁_b₁
            have hv2 : m ≤ b₂.factorization p :=
              (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₂_I).ne').mp
                (dvd_trans (dvd_mul_right (p ^ m) Q) hD₂_b₂)
            have hb₂_ne : b₁ ≠ b₂ := fun h => hb₂_notIns (by simp [h])
            exact hcover_p_Q b₁ b₂ hb₁_I hb₂_I hb₁_notB₀ hb₂_notB₀ (by omega)
              (fun h => absurd h hb₂_ne)
              (Or.inr (dvd_trans (dvd_mul_left Q (p ^ m)) hD₂_b₂))
          · -- Even `e = 2*m` (`m ≥ 1`).
            let m := e / 2
            have hm_ge1 : 1 ≤ m := by omega
            have he_eq : e = 2 * m := by omega
            by_cases hM96 : 96 ≤ M
            · let D₁ := p ^ m
              let D₂ := p ^ m * Q
              have hD₁_pos : 0 < D₁ := pow_pos hp_prime.pos _
              have hD₂_pos : 0 < D₂ := mul_pos hD₁_pos hQ_prime.pos
              have h8D₂ : 8 * D₂ ≤ M := by
                have hsq : (8 * D₂) ^ 2 ≤ M ^ 2 := by
                  have h1 : (8 * D₂) ^ 2 = 32 * Q * (2 * R) := by
                    dsimp [D₂]; rw [hR_pQ, he_eq]; ring
                  have h2 : 32 * Q * (2 * R) ≤ 96 * M :=
                    Nat.mul_le_mul (by omega : 32 * Q ≤ 96) h2R
                  have h3 : 96 * M ≤ M ^ 2 := by
                    calc 96 * M = M * 96 := by ring
                      _ ≤ M * M := Nat.mul_le_mul_left M hM96
                      _ = M ^ 2 := by ring
                  omega
                by_contra hlt
                push Not at hlt
                exact absurd (Nat.pow_lt_pow_left hlt (by omega)) (not_lt_of_ge hsq)
              have h8D₁ : 8 * D₁ ≤ M := by
                have hle : D₁ ≤ D₂ := Nat.le_mul_of_pos_right D₁ hQ_prime.pos
                exact le_trans (Nat.mul_le_mul_left 8 hle) h8D₂
              obtain ⟨b₁, hb₁_I, hb₁_notB₀, hD₁_b₁⟩ :=
                exists_avoiding_multiple_in_consecInterval x M D₁ B₀ hD₁_pos
                  (le_trans (Nat.mul_le_mul_right D₁ (by omega : B₀.card + 1 ≤ 8)) h8D₁)
              have hcard_ins : (insert b₁ B₀).card + 1 ≤ 8 := by
                have h1 := Finset.card_insert_le b₁ B₀; omega
              obtain ⟨b₂, hb₂_I, hb₂_notIns, hD₂_b₂⟩ :=
                exists_avoiding_multiple_in_consecInterval x M D₂ (insert b₁ B₀) hD₂_pos
                  (le_trans (Nat.mul_le_mul_right _ hcard_ins) h8D₂)
              have hb₂_notB₀ : b₂ ∉ B₀ := fun h => hb₂_notIns (Finset.mem_insert_of_mem h)
              have hv1 : m ≤ b₁.factorization p :=
                (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₁_I).ne').mp hD₁_b₁
              have hv2 : m ≤ b₂.factorization p :=
                (hp_prime.pow_dvd_iff_le_factorization (pos_of_mem_consecInterval hb₂_I).ne').mp
                  (dvd_trans (dvd_mul_right (p ^ m) Q) hD₂_b₂)
              have hb₂_ne : b₁ ≠ b₂ := fun h => hb₂_notIns (by simp [h])
              have hp_cov : e ≤ b₁.factorization p + b₂.factorization p := by
                rw [he_eq, two_mul]; exact Nat.add_le_add hv1 hv2
              exact hcover_p_Q b₁ b₂ hb₁_I hb₂_I hb₁_notB₀ hb₂_notB₀ hp_cov
                (fun h => absurd h hb₂_ne)
                (Or.inr (dvd_trans (dvd_mul_left Q (p ^ m)) hD₂_b₂))
            · -- Small `M < 96`: only `(p=2, m=1, Q=3)` or `(p=3, m=1, Q=2)` is possible!
              have hp2m_le : p ^ (2 * m) * Q ≤ 47 := by rw [← he_eq, ← hR_pQ]; omega
              have hm_eq1 : m = 1 := by
                by_contra hm2
                have hm_ge2 : 2 ≤ m := by omega
                by_cases hQ2 : Q = 2
                · have hp3 : 3 ≤ p := by
                    have := hp_prime.two_le
                    have : p ≠ 2 := fun h => hQp_ne (h.trans hQ2.symm)
                    omega
                  have h81 : 81 ≤ p ^ (2 * m) := by
                    have h1 : 3 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp3 4
                    have h2 : p ^ 4 ≤ p ^ (2 * m) := Nat.pow_le_pow_right hp_prime.pos (by omega)
                    exact le_trans (by norm_num) (le_trans h1 h2)
                  have h162 : 162 ≤ p ^ (2 * m) * Q := Nat.mul_le_mul h81 hQ_ge2
                  omega
                · have hQ3 : 3 ≤ Q := by omega
                  have hpow4 : 16 ≤ p ^ (2 * m) := by
                    have h1 : 2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp_prime.two_le 4
                    have h2 : p ^ 4 ≤ p ^ (2 * m) := Nat.pow_le_pow_right hp_prime.pos (by omega)
                    exact le_trans (by norm_num) (le_trans h1 h2)
                  have h48 : 48 ≤ p ^ (2 * m) * Q := Nat.mul_le_mul hpow4 hQ3
                  omega
              have hp_lt5 : p < 5 := by
                by_contra hp5
                have h25 : 25 ≤ p ^ (2 * m) := by
                  rw [hm_eq1, mul_one]
                  have h1 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega : 5 ≤ p) 2
                  exact le_trans (by norm_num) h1
                have h50 : 50 ≤ p ^ (2 * m) * Q := Nat.mul_le_mul h25 hQ_ge2
                omega
              have hpe_eq2 : e = 2 := by omega
              have hp_cases : (p = 2 ∧ Q = 3) ∨ (p = 3 ∧ Q = 2) := by
                rcases hQ_cases with h2 | h3
                · have hp3 : p = 3 := by
                    have := hp_prime.two_le
                    have hne4 : p ≠ 4 := fun h => by rw [h] at hp_prime; norm_num at hp_prime
                    omega
                  exact Or.inr ⟨hp3, h2⟩
                · have hp2 : p = 2 := by
                    have := hp_prime.two_le
                    have hne4 : p ≠ 4 := fun h => by rw [h] at hp_prime; norm_num at hp_prime
                    omega
                  exact Or.inl ⟨hp2, h3⟩
              have hsub_hi : (consecInterval x M).filter (fun b => p ^ 2 ∣ b) ⊆ B₀ := by
                intro b hb
                rw [Finset.mem_filter] at hb
                by_contra hbB₀
                exact hpe_ex b (Finset.mem_sdiff.mpr ⟨hb.1, hbB₀⟩) (hpe_eq2 ▸ hb.2)
              have hdef_le := layer_cake_deficit_le_of_sq_subset hA_pos hA_le hB₀_I hp_prime hsub_hi
              have he_def : 2 = (∑ a ∈ A, a.factorization p) - (∑ b ∈ B₀, b.factorization p) := by
                rw [← hR_fac p hp_prime]; exact hpe_eq2.symm
              rcases hp_cases with ⟨rfl, hQ3⟩ | ⟨rfl, hQ2⟩
              · -- `(p = 2, Q = 3)` (`R = 12`, `M ≥ 24`): `I_hi.card ≥ 6` contradicts `2 ≤ 6 - I_hi.card`.
                have hM_ge24 : 24 ≤ M := by rw [hR_pQ, hpe_eq2, hQ3] at h2R; norm_num at h2R; omega
                have hcard_hi : 6 ≤ ((consecInterval x M).filter (fun b => 2 ^ 2 ∣ b)).card :=
                  le_trans (Nat.le_div_iff_mul_le (by norm_num : 0 < 4) |>.mpr (by omega))
                    (card_multiples_Icc_ge x M 4 (by norm_num))
                omega
              · -- `(p = 3, Q = 2)` (`R = 18`, `M ≥ 36`).
                have hM_ge36 : 36 ≤ M := by rw [hR_pQ, hpe_eq2, hQ2] at h2R; norm_num at h2R; omega
                by_cases hM48 : 48 ≤ M
                · obtain ⟨b₁, hb₁_I, hb₁_notB₀, h3_b₁⟩ :=
                    exists_avoiding_multiple_in_consecInterval x M 3 B₀ (by norm_num) (by omega)
                  have hcard_ins : (insert b₁ B₀).card + 1 ≤ 8 := by
                    have h1 := Finset.card_insert_le b₁ B₀; omega
                  obtain ⟨b₂, hb₂_I, hb₂_notIns, h6_b₂⟩ :=
                    exists_avoiding_multiple_in_consecInterval x M 6 (insert b₁ B₀) (by norm_num)
                      (by omega)
                  have hb₂_notB₀ : b₂ ∉ B₀ := fun h => hb₂_notIns (Finset.mem_insert_of_mem h)
                  have hv1 : 1 ≤ b₁.factorization 3 :=
                    ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization
                      (pos_of_mem_consecInterval hb₁_I).ne').mp (by simpa only [pow_one] using h3_b₁)
                  have hv2 : 1 ≤ b₂.factorization 3 :=
                    ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization
                      (pos_of_mem_consecInterval hb₂_I).ne').mp
                      (by simpa only [pow_one] using dvd_trans (by norm_num : 3 ∣ 6) h6_b₂)
                  have hb₂_ne : b₁ ≠ b₂ := fun h => hb₂_notIns (by simp [h])
                  have hQ_b₂ : Q ∣ b₂ := by
                    rw [hQ2]
                    exact dvd_trans (by norm_num : 2 ∣ 6) h6_b₂
                  exact hcover_p_Q b₁ b₂ hb₁_I hb₂_I hb₁_notB₀ hb₂_notB₀ (by omega)
                    (fun h => absurd h hb₂_ne) (Or.inr hQ_b₂)
                · -- `36 ≤ M ≤ 47`: `I_hi = I.filter (9 ∣ ·) ⊆ B₀` has `|I_hi| ≥ 4`, while `|I.filter (18 ∣ ·)| ≤ 3`,
                  -- so `B₀` contains a `9`-multiple NOT divisible by `2`, hence `(B₀.filter (6 ∣ ·)).card ≤ 5 < 6`.
                  let I_hi := (consecInterval x M).filter (fun b => 3 ^ 2 ∣ b)
                  have hIhi_ge4 : 4 ≤ I_hi.card :=
                    le_trans (Nat.le_div_iff_mul_le (by norm_num : 0 < 9) |>.mpr (by omega))
                      (card_multiples_Icc_ge x M 9 (by norm_num))
                  have h18_le3 : ((consecInterval x M).filter (fun b => 18 ∣ b)).card ≤ 3 := by
                    have h1 := card_multiples_Icc_le x M 18 (by omega) (by norm_num)
                    have hdiv : (M - 1) / 18 < 3 := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)
                    omega
                  have hIhi_even_le3 : (I_hi.filter (fun b => 2 ∣ b)).card ≤ 3 := by
                    have hsub : I_hi.filter (fun b => 2 ∣ b) ⊆ (consecInterval x M).filter (fun b => 18 ∣ b) := by
                      intro b hb
                      rw [Finset.mem_filter] at hb ⊢
                      have hbI := (Finset.mem_filter.mp hb.1).1
                      have h9b : 9 ∣ b := by simpa using (Finset.mem_filter.mp hb.1).2
                      have h2b : 2 ∣ b := hb.2
                      exact ⟨hbI, (by norm_num : Nat.Coprime 9 2).mul_dvd_of_dvd_of_dvd h9b h2b⟩
                    exact le_trans (Finset.card_le_card hsub) h18_le3
                  have hnot_sub : ¬ (I_hi ⊆ I_hi.filter (fun b => 2 ∣ b)) := by
                    intro hsub
                    have := Finset.card_le_card hsub
                    omega
                  obtain ⟨b_odd, hb_odd_hi, hb_odd_not⟩ := Finset.not_subset.mp hnot_sub
                  have hb_odd_B₀ : b_odd ∈ B₀ := hsub_hi hb_odd_hi
                  have hb_odd_n2 : ¬ (2 ∣ b_odd) := fun h => hb_odd_not (Finset.mem_filter.mpr ⟨hb_odd_hi, h⟩)
                  have hb_odd_n6 : ¬ (6 ∣ b_odd) := fun h => hb_odd_n2 (dvd_trans (by norm_num : 2 ∣ 6) h)
                  have hB₀6_le5 : (B₀.filter (fun b => 6 ∣ b)).card ≤ 5 := by
                    have hsub_er : B₀.filter (fun b => 6 ∣ b) ⊆ B₀.erase b_odd := by
                      intro b hb
                      rw [Finset.mem_filter] at hb
                      exact Finset.mem_erase.mpr ⟨fun heq => hb_odd_n6 (heq ▸ hb.2), hb.1⟩
                    have hcard_er : (B₀.erase b_odd).card = B₀.card - 1 := Finset.card_erase_of_mem hb_odd_B₀
                    have := Finset.card_pos.mpr ⟨b_odd, hb_odd_B₀⟩
                    exact le_trans (Finset.card_le_card hsub_er) (by omega)
                  have hI6_ge6 : 6 ≤ ((consecInterval x M).filter (fun b => 6 ∣ b)).card :=
                    le_trans (Nat.le_div_iff_mul_le (by norm_num : 0 < 6) |>.mpr (by omega))
                      (card_multiples_Icc_ge x M 6 (by norm_num))
                  have hnot_sub6 : ¬ ((consecInterval x M).filter (fun b => 6 ∣ b) ⊆ B₀.filter (fun b => 6 ∣ b)) := by
                    intro hsub
                    have := Finset.card_le_card hsub
                    omega
                  obtain ⟨b₂, hb₂_flt, hb₂_not⟩ := Finset.not_subset.mp hnot_sub6
                  rw [Finset.mem_filter] at hb₂_flt
                  have hb₂_notB₀ : b₂ ∉ B₀ := fun h => hb₂_not (Finset.mem_filter.mpr ⟨h, hb₂_flt.2⟩)
                  have hcard_ins : (insert b₂ B₀).card + 1 ≤ 8 := by
                    have h1 := Finset.card_insert_le b₂ B₀; omega
                  obtain ⟨b₁, hb₁_I, hb₁_notIns, h3_b₁⟩ :=
                    exists_avoiding_multiple_in_consecInterval x M 3 (insert b₂ B₀) (by norm_num)
                      (by omega)
                  have hb₁_notB₀ : b₁ ∉ B₀ := fun h => hb₁_notIns (Finset.mem_insert_of_mem h)
                  have hv1 : 1 ≤ b₁.factorization 3 :=
                    ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization
                      (pos_of_mem_consecInterval hb₁_I).ne').mp (by simpa only [pow_one] using h3_b₁)
                  have hv2 : 1 ≤ b₂.factorization 3 :=
                    ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization
                      (pos_of_mem_consecInterval hb₂_flt.1).ne').mp
                      (by simpa only [pow_one] using dvd_trans (by norm_num : 3 ∣ 6) hb₂_flt.2)
                  have hb₁_ne : b₁ ≠ b₂ := fun h => hb₁_notIns (by simp [h])
                  have hp_cov : e ≤ b₁.factorization 3 + b₂.factorization 3 := by
                    rw [hpe_eq2]; exact Nat.add_le_add hv1 hv2
                  have hQ_b₂ : Q ∣ b₂ := by
                    rw [hQ2]
                    exact dvd_trans (by norm_num : 2 ∣ 6) hb₂_flt.2
                  have hnot_eq : ¬ (b₁ = b₂) := hb₁_ne
                  clear I_hi hIhi_ge4 hIhi_even_le3 hnot_sub hb_odd_hi hb_odd_not h18_le3 hB₀6_le5 hI6_ge6 hnot_sub6
                  exact hcover_p_Q b₁ b₂ hb₁_I hb₂_flt.1 hb₁_notB₀ hb₂_notB₀ hp_cov
                    (fun h => absurd h hnot_eq) (Or.inr hQ_b₂)

/-! ## Part 5: Master `r = 4` Theorem (`erdos708_upper_six_of_matching_four`) -/

/-- **Unconditional `r = 4` Closure for `g(6) ≤ 8`**:
    any 6-element set `A ⊆ [1, M]` admitting a matching of size `4` into `consecInterval x M`
    has an unconditional cover `B ⊆ consecInterval x M` with `B.card ≤ 8`. -/
theorem erdos708_upper_six_of_matching_four {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hSA : S ⊆ A) (hS_card : S.card = 4)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 8 ∧ IsCover A B := by
  obtain ⟨B₀, R, hB₀_I, hB₀_card, hR_pos, h2R, hR_fac, hle_R⟩ :=
    exists_six_cover_with_gcd_deficit hA_card hA_pos hA_le hSA hS_card hf_mem hf_dvd hf_inj
  obtain ⟨B₁, hB₁_I, hdisj, hB₁_card, hB₁_val⟩ :=
    exists_two_slots_for_R hA_card hA_pos hA_le hB₀_I hB₀_card hR_pos h2R hR_fac
  refine ⟨B₀ ∪ B₁, Finset.union_subset hB₀_I hB₁_I, ?_, ?_⟩
  · have h1 := Finset.card_union_le B₀ B₁
    omega
  · apply isCover_union_of_disjoint_factorization
      (fun a ha => (hA_pos a ha).ne')
      (fun b hb => (pos_of_mem_consecInterval (hB₀_I hb)).ne')
      (fun b hb => (pos_of_mem_consecInterval (hB₁_I hb)).ne')
      hdisj
    intro p hp
    exact le_trans (hle_R p hp) (Nat.add_le_add_left (hB₁_val p hp) _)

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms erdos708_gcd_reduction
#print axioms exists_max_matching_in_consecInterval
#print axioms exists_six_cover_with_gcd_deficit
#print axioms erdos708_upper_six_of_matching_four

end Erdos708