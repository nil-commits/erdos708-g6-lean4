import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators Nat

namespace Erdos708

/-- The interval of `M` consecutive positive integers `{m + 1, ..., m + M}`. -/
def Erdos708Interval (m M : ℕ) : Finset ℕ :=
  Finset.Icc (m + 1) (m + M)

/-- Erdős Problem #708 covering predicate on positive consecutive integers:
    there exists `B ⊆ {m + 1, ..., m + max(A)}` with `|B| ≤ k` and `∏ A ∣ ∏ B`. -/
def Erdos708Covers (A : Finset ℕ) (m k : ℕ) : Prop :=
  ∃ B ⊆ Erdos708Interval m (A.sup id),
    B.card ≤ k ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)

/-- Erdős Problem #708 covering predicate on arbitrary consecutive integers in `ℤ`:
    there exists `B ⊆ {m, m + 1, ..., m + max(A) - 1}` with `|B| ≤ k` and `∏ A ∣ ∏ B` in `ℤ`. -/
def Erdos708CoversInt (A : Finset ℕ) (m : ℤ) (k : ℕ) : Prop :=
  ∃ B ⊆ Finset.Ico m (m + ((A.sup id : ℕ) : ℤ)),
    B.card ≤ k ∧ ((∏ a ∈ A, a : ℕ) : ℤ) ∣ (∏ b ∈ B, b)

lemma erdos708Interval_card (m M : ℕ) : (Erdos708Interval m M).card = M := by
  simp [Erdos708Interval, Nat.card_Icc]

lemma erdos708Interval_pos {m M b : ℕ} (hb : b ∈ Erdos708Interval m M) : 0 < b := by
  simp only [Erdos708Interval, Finset.mem_Icc] at hb
  omega

lemma prod_pos_of_mem_interval {m M : ℕ} {B : Finset ℕ} (hB : B ⊆ Erdos708Interval m M) :
    0 < ∏ b ∈ B, b := by
  apply Finset.prod_pos
  intro b hb
  exact erdos708Interval_pos (hB hb)

lemma prod_pos_of_ge_two {A : Finset ℕ} (hA : ∀ a ∈ A, 2 ≤ a) :
    0 < ∏ a ∈ A, a := by
  apply Finset.prod_pos
  intro a ha
  have := hA a ha
  omega

lemma subset_Icc_one_sup {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) :
    A ⊆ Finset.Icc 1 (A.sup id) := by
  intro a ha
  rw [Finset.mem_Icc]
  exact ⟨hA a ha, Finset.le_sup (f := id) ha⟩

/-- Reduction from arbitrary integer intervals `I ⊂ ℤ` to positive intervals `I ⊂ ℕ_{≥1}`. -/
theorem erdos708CoversInt_of_nat {A : Finset ℕ} {k : ℕ}
    (hA_ne : A.Nonempty) (hA : ∀ a ∈ A, 2 ≤ a) (hk : 1 ≤ k)
    (hNat : ∀ m : ℕ, Erdos708Covers A m k) :
    ∀ m : ℤ, Erdos708CoversInt A m k := by
  intro m
  set M := A.sup id with hM_def
  have hM_pos : 1 ≤ M := by
    obtain ⟨a, ha⟩ := hA_ne
    have h1 : 2 ≤ a := hA a ha
    have h2 : a ≤ M := Finset.le_sup (f := id) ha
    omega
  by_cases hpos : 0 < m
  · -- Positive interval: `m = m₀ + 1`
    lift m - 1 to ℕ using (by omega) with m₀ hm₀
    obtain ⟨B, hBI, hBcard, hBdvd⟩ := hNat m₀
    refine ⟨B.map ⟨Nat.cast, Nat.cast_injective⟩, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨b, hb, rfl⟩
      have hmem := hBI hb
      simp only [Erdos708Interval, Finset.mem_Icc] at hmem
      rw [Finset.mem_Ico]
      dsimp
      omega
    · simpa using hBcard
    · rw [Finset.prod_map]
      simpa using Int.ofNat_dvd.mpr hBdvd
  · by_cases hzero : m + (M : ℤ) ≤ 0
    · -- Entirely negative interval: negate to get a positive interval
      lift -(m + (M : ℤ)) to ℕ using (by omega) with m₀ hm₀
      obtain ⟨B, hBI, hBcard, hBdvd⟩ := hNat m₀
      let f : ℕ → ℤ := fun b => -(b : ℤ)
      have hf_inj : Function.Injective f := fun a b h => by dsimp [f] at h; omega
      refine ⟨B.image f, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
        have hmem := hBI hb
        simp only [Erdos708Interval, Finset.mem_Icc] at hmem
        rw [Finset.mem_Ico]
        dsimp [f]
        omega
      · exact le_trans Finset.card_image_le hBcard
      · rw [Finset.prod_image (fun a _ b _ h => hf_inj h)]
        have hprod : ∏ b ∈ B, f b = (-1 : ℤ) ^ B.card * ((∏ b ∈ B, b : ℕ) : ℤ) := by
          dsimp [f]
          rw [Finset.prod_neg, Nat.cast_prod]
        rw [hprod]
        exact dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr hBdvd) _
    · -- `0 ∈ Finset.Ico m (m + M)`: pick `B = {0}`!
      refine ⟨{0}, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        rw [Finset.mem_Ico]
        omega
      · simpa using hk
      · simp

/-- In any interval of `M` consecutive positive integers `{m + 1, ..., m + M}`,
    there are at least `M / d` multiples of `d ≥ 1`. -/
lemma card_multiples_Icc_ge (m M d : ℕ) (hd : 0 < d) :
    M / d ≤ ((Erdos708Interval m M).filter (fun b => d ∣ b)).card := by
  let f : ℕ → ℕ := fun j => d * (m / d + 1 + j)
  have hmaps : Set.MapsTo f (Finset.range (M / d))
      ((Erdos708Interval m M).filter (fun b => d ∣ b)) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_range] at hj
    rw [Finset.mem_coe, Finset.mem_filter, Erdos708Interval, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d _⟩
    · have h1 : m < d * (m / d + 1) := by
        have := Nat.div_add_mod m d
        have := Nat.mod_lt m hd
        nlinarith
      have h2 : d * (m / d + 1) ≤ d * (m / d + 1 + j) :=
        Nat.mul_le_mul_left d (by omega)
      dsimp [f]
      omega
    · have h1 : d * (m / d) ≤ m := Nat.mul_div_le m d
      have h2 : d * (j + 1) ≤ d * (M / d) := Nat.mul_le_mul_left d (by omega)
      have h3 : d * (M / d) ≤ M := Nat.mul_div_le M d
      have h4 : f j = d * (m / d) + d * (j + 1) := by
        dsimp [f]; ring
      omega
  have hinj : Set.InjOn f (Finset.range (M / d)) := by
    intro j₁ _ j₂ _ h
    dsimp [f] at h
    have h1 := Nat.eq_of_mul_eq_mul_left hd h
    omega
  simpa [Finset.card_range] using Finset.card_le_card_of_injOn f hmaps hinj

/-- In `{1, ..., M}`, the number of multiples of `d ≥ 1` is at most `M / d` (in fact equal). -/
lemma card_multiples_Icc_one_le (M d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 M).filter (fun a => d ∣ a)).card ≤ M / d := by
  let g : ℕ → ℕ := fun a => a / d - 1
  have hmaps : Set.MapsTo g ((Finset.Icc 1 M).filter (fun a => d ∣ a)) (Finset.range (M / d)) := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha
    rcases ha with ⟨⟨ha1, haM⟩, ⟨k, rfl⟩⟩
    rw [Finset.mem_coe, Finset.mem_range]
    have hk_pos : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      subst hk0; simp at ha1
    have hk_le : k ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
    dsimp [g]
    rw [Nat.mul_div_cancel_left k hd]
    omega
  have hinj : Set.InjOn g ((Finset.Icc 1 M).filter (fun a => d ∣ a)) := by
    intro a₁ ha₁ a₂ ha₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha₁ ha₂
    rcases ha₁ with ⟨⟨h1a, _⟩, ⟨k₁, rfl⟩⟩
    rcases ha₂ with ⟨⟨h2a, _⟩, ⟨k₂, rfl⟩⟩
    have hk₁ : 1 ≤ k₁ := Nat.pos_of_mul_pos_left h1a
    have hk₂ : 1 ≤ k₂ := Nat.pos_of_mul_pos_left h2a
    dsimp [g] at h
    rw [Nat.mul_div_cancel_left k₁ hd, Nat.mul_div_cancel_left k₂ hd] at h
    have : k₁ = k₂ := by omega
    rw [this]
  simpa [Finset.card_range] using Finset.card_le_card_of_injOn g hmaps hinj

/-- Product of `M` consecutive integers `{m + 1, ..., m + M}` equals `(m + M)! / m!`. -/
lemma mul_prod_Icc_eq_factorial (m M : ℕ) :
    m ! * ∏ b ∈ Erdos708Interval m M, b = (m + M) ! := by
  induction M with
  | zero =>
    simp [Erdos708Interval]
  | succ M ih =>
    have hIcc : Erdos708Interval m (M + 1) = insert (m + M + 1) (Erdos708Interval m M) := by
      ext x
      simp only [Erdos708Interval, Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m + M + 1 ∉ Erdos708Interval m M := by
      simp only [Erdos708Interval, Finset.mem_Icc]
      omega
    rw [hIcc, Finset.prod_insert hnotmem]
    have h1 : m ! * ((m + M + 1) * ∏ b ∈ Erdos708Interval m M, b) =
        (m + M + 1) * (m ! * ∏ b ∈ Erdos708Interval m M, b) := by ring
    rw [h1, ih, show m + (M + 1) = (m + M) + 1 by omega, Nat.factorial_succ]

/-- `M!` always divides the product of any `M` consecutive positive integers. -/
theorem factorial_dvd_prod_Icc (m M : ℕ) :
    M ! ∣ ∏ b ∈ Erdos708Interval m M, b := by
  have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left M m)
  rw [show m + M - M = m by omega] at hchoose
  rw [← mul_prod_Icc_eq_factorial m M] at hchoose
  have hEq : m ! * (Nat.choose (m + M) M * M !) = m ! * ∏ b ∈ Erdos708Interval m M, b := by
    linarith
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos m) hEq
  exact ⟨Nat.choose (m + M) M, by linarith⟩

/-- Any subset `A ⊆ {1, ..., M}` has product dividing `M!`. -/
lemma prod_subset_Icc_dvd_factorial {A : Finset ℕ} {M : ℕ} (hA : A ⊆ Finset.Icc 1 M) :
    (∏ a ∈ A, a) ∣ M ! := by
  have hfac : ∏ a ∈ Finset.Icc 1 M, a = M ! := by
    have := mul_prod_Icc_eq_factorial 0 M
    simpa [Erdos708Interval] using this
  rw [← hfac]
  exact Finset.prod_dvd_prod_of_subset A (Finset.Icc 1 M) id hA

/-- Trivial bound: the entire interval `I` of length `M = max(A)` always covers `A`. -/
theorem erdos708_trivial_max_bound {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ) :
    Erdos708Covers A m (A.sup id) := by
  refine ⟨Erdos708Interval m (A.sup id), Finset.Subset.rfl, ?_, ?_⟩
  · rw [erdos708Interval_card]
  · exact dvd_trans (prod_subset_Icc_dvd_factorial (subset_Icc_one_sup hA))
      (factorial_dvd_prod_Icc m (A.sup id))

/-- Factorization divisibility criterion for positive products. -/
lemma prod_dvd_prod_of_factorization_le {A B : Finset ℕ}
    (hA : ∀ a ∈ A, a ≠ 0) (hB : ∀ b ∈ B, b ≠ 0)
    (hfac : ∀ p : ℕ, p.Prime → ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B, b.factorization p) :
    (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) := by
  have hA0 : ∏ a ∈ A, a ≠ 0 := Finset.prod_ne_zero_iff.mpr hA
  have hB0 : ∏ b ∈ B, b ≠ 0 := Finset.prod_ne_zero_iff.mpr hB
  rw [← Nat.factorization_le_iff_dvd hA0 hB0]
  intro p
  rw [Nat.factorization_prod hA, Nat.factorization_prod hB]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases hp : p.Prime
  · exact hfac p hp
  · have hzero : ∀ x : ℕ, x.factorization p = 0 := fun x =>
      Nat.factorization_eq_zero_of_not_prime x hp
    simp [hzero]

/-- Elementary deficit covering: if `E ≤ ∑ b ∈ J, b.factorization p`, then some subset
    `C ⊆ J` of size `≤ E` already has `E ≤ ∑ b ∈ C, b.factorization p`. -/
lemma exists_cover_prime_deficit {J : Finset ℕ} {p E : ℕ}
    (hsum : E ≤ ∑ b ∈ J, b.factorization p) :
    ∃ C ⊆ J, C.card ≤ E ∧ E ≤ ∑ b ∈ C, b.factorization p := by
  let J' := J.filter (fun b => 0 < b.factorization p)
  have hJ'_sub : J' ⊆ J := Finset.filter_subset _ _
  have hsum' : ∑ b ∈ J, b.factorization p = ∑ b ∈ J', b.factorization p := by
    symm
    apply Finset.sum_subset hJ'_sub
    intro b hb hbn
    simp only [J', Finset.mem_filter, not_and, not_lt, Nat.le_zero] at hbn
    exact hbn hb
  by_cases hle : J'.card ≤ E
  · exact ⟨J', hJ'_sub, hle, hsum' ▸ hsum⟩
  · push Not at hle
    obtain ⟨C, hCJ', hCcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hle)
    refine ⟨C, Finset.Subset.trans hCJ' hJ'_sub, le_of_eq hCcard, ?_⟩
    calc
      E = C.card := hCcard.symm
      _ = ∑ _b ∈ C, 1 := by simp
      _ ≤ ∑ b ∈ C, b.factorization p := by
        apply Finset.sum_le_sum
        intro b hb
        have := (Finset.mem_filter.mp (hCJ' hb)).2
        omega

/-- Layer-cake identity for `x.factorization p` when `1 ≤ x ≤ M`. -/
lemma factorization_eq_sum_dvd {p x M : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hxM : x ≤ M) :
    x.factorization p = ∑ e ∈ Finset.Icc 1 M, if p ^ e ∣ x then 1 else 0 := by
  have hx0 : x ≠ 0 := by omega
  have hleM : x.factorization p ≤ M := by
    have h1 : x.factorization p < 2 ^ (x.factorization p) := Nat.lt_two_pow_self
    have h2 : 2 ^ (x.factorization p) ≤ p ^ (x.factorization p) :=
      Nat.pow_le_pow_left hp.two_le _
    have h3 : p ^ (x.factorization p) ≤ x :=
      Nat.le_of_dvd (by omega) (Nat.ordProj_dvd x p)
    omega
  have hfilt : (Finset.Icc 1 M).filter (fun e => p ^ e ∣ x) = Finset.Icc 1 (x.factorization p) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨he1, _⟩, hdvd⟩
      exact ⟨he1, (hp.pow_dvd_iff_le_factorization hx0).mp hdvd⟩
    · rintro ⟨he1, hev⟩
      exact ⟨⟨he1, le_trans hev hleM⟩, (hp.pow_dvd_iff_le_factorization hx0).mpr hev⟩
  rw [Finset.sum_boole, Nat.cast_id, hfilt, Nat.card_Icc]
  omega

/-- Layer-cake lower bound for `b.factorization p` for any `b ≥ 1`. -/
lemma sum_dvd_le_factorization {p b M : ℕ} (hp : p.Prime) (hb : 1 ≤ b) :
    (∑ e ∈ Finset.Icc 1 M, if p ^ e ∣ b then 1 else 0) ≤ b.factorization p := by
  have hb0 : b ≠ 0 := by omega
  have hsub : (Finset.Icc 1 M).filter (fun e => p ^ e ∣ b) ⊆ Finset.Icc 1 (b.factorization p) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
    exact ⟨he.1.1, (hp.pow_dvd_iff_le_factorization hb0).mp he.2⟩
  rw [Finset.sum_boole, Nat.cast_id]
  calc
    ((Finset.Icc 1 M).filter (fun e => p ^ e ∣ b)).card
        ≤ (Finset.Icc 1 (b.factorization p)).card := Finset.card_le_card hsub
    _ = b.factorization p := by rw [Nat.card_Icc]; omega

/-- **Top-`r` Prime Covering Lemma (Book Proof)**:
    For any prime `p`, any `S ⊆ {1, ..., M}`, and any interval `I = {m + 1, ..., m + M}`,
    there exists `C ⊆ I` with `C.card ≤ S.card` and
    `∑ a ∈ S, a.factorization p ≤ ∑ b ∈ C, b.factorization p`. -/
theorem exists_cover_prime_by_card {p m M : ℕ} (hp : p.Prime)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 M) :
    ∃ C ⊆ Erdos708Interval m M,
      C.card ≤ S.card ∧ ∑ a ∈ S, a.factorization p ≤ ∑ b ∈ C, b.factorization p := by
  set I := Erdos708Interval m M
  have hScard_le : S.card ≤ I.card := by
    rw [erdos708Interval_card]
    calc S.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hS
    _ = M := by rw [Nat.card_Icc]; omega
  have hpow_ne : (I.powersetCard S.card).Nonempty :=
    Finset.powersetCard_nonempty.mpr hScard_le
  obtain ⟨C, hCmem, hCmax⟩ :=
    Finset.exists_max_image (I.powersetCard S.card) (fun X => ∑ b ∈ X, b.factorization p) hpow_ne
  rw [Finset.mem_powersetCard] at hCmem
  rcases hCmem with ⟨hCI, hCcard⟩
  refine ⟨C, hCI, le_of_eq hCcard, ?_⟩
  -- Key claim: for every `e ≥ 1`, `C` has at least as many multiples of `p^e` as `S`.
  have hlevel : ∀ e ∈ Finset.Icc 1 M,
      (S.filter (fun a => p ^ e ∣ a)).card ≤ (C.filter (fun b => p ^ e ∣ b)).card := by
    intro e he
    by_contra hlt
    push Not at hlt
    have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
    have hS_le_div : (S.filter (fun a => p ^ e ∣ a)).card ≤ M / p ^ e := by
      calc (S.filter (fun a => p ^ e ∣ a)).card
          ≤ ((Finset.Icc 1 M).filter (fun a => p ^ e ∣ a)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ hS)
        _ ≤ M / p ^ e := card_multiples_Icc_one_le M (p ^ e) hpe_pos
    have hdiv_le_I : M / p ^ e ≤ (I.filter (fun b => p ^ e ∣ b)).card :=
      card_multiples_Icc_ge m M (p ^ e) hpe_pos
    have hC_lt_I : (C.filter (fun b => p ^ e ∣ b)).card < (I.filter (fun b => p ^ e ∣ b)).card :=
      lt_of_lt_of_le hlt (le_trans hS_le_div hdiv_le_I)
    have hnot_sub : ¬ (I.filter (fun b => p ^ e ∣ b) ⊆ C.filter (fun b => p ^ e ∣ b)) := by
      intro hsub
      exact not_lt_of_ge (Finset.card_le_card hsub) hC_lt_I
    rw [Finset.not_subset] at hnot_sub
    obtain ⟨b₁, hb₁I, hb₁C⟩ := hnot_sub
    rw [Finset.mem_filter] at hb₁I hb₁C
    have hb₁_not_C : b₁ ∉ C := fun h => hb₁C ⟨h, hb₁I.2⟩
    have hC_lt_card : (C.filter (fun b => p ^ e ∣ b)).card < C.card := by
      calc (C.filter (fun b => p ^ e ∣ b)).card
          < (S.filter (fun a => p ^ e ∣ a)).card := hlt
        _ ≤ S.card := Finset.card_filter_le _ _
        _ = C.card := hCcard.symm
    have hnot_sub2 : ¬ (C ⊆ C.filter (fun b => p ^ e ∣ b)) := by
      intro hsub
      exact not_lt_of_ge (Finset.card_le_card hsub) hC_lt_card
    rw [Finset.not_subset] at hnot_sub2
    obtain ⟨b₀, hb₀C, hb₀_not_dvd⟩ := hnot_sub2
    rw [Finset.mem_filter] at hb₀_not_dvd
    have hb₀_ndvd : ¬ (p ^ e ∣ b₀) := fun h => hb₀_not_dvd ⟨hb₀C, h⟩
    have hb₀_pos : b₀ ≠ 0 := Nat.ne_of_gt (erdos708Interval_pos (hCI hb₀C))
    have hb₁_pos : b₁ ≠ 0 := Nat.ne_of_gt (erdos708Interval_pos hb₁I.1)
    have hv₀ : b₀.factorization p < e := by
      by_contra hge
      push Not at hge
      exact hb₀_ndvd ((hp.pow_dvd_iff_le_factorization hb₀_pos).mpr hge)
    have hv₁ : e ≤ b₁.factorization p :=
      (hp.pow_dvd_iff_le_factorization hb₁_pos).mp hb₁I.2
    -- Swap `b₀` out and `b₁` in!
    let C' := insert b₁ (C.erase b₀)
    have hC'_mem : C' ∈ I.powersetCard S.card := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hb₁I.1
        · exact hCI (Finset.mem_of_mem_erase hx')
      · rw [Finset.card_insert_of_notMem (fun h => hb₁_not_C (Finset.mem_of_mem_erase h)),
            Finset.card_erase_of_mem hb₀C]
        have hC_pos : 1 ≤ C.card := Finset.card_pos.mpr ⟨b₀, hb₀C⟩
        omega
    have hsum_gt : ∑ b ∈ C, b.factorization p < ∑ b ∈ C', b.factorization p := by
      have h1 : ∑ b ∈ C, b.factorization p =
          b₀.factorization p + ∑ b ∈ C.erase b₀, b.factorization p :=
        (Finset.add_sum_erase C (fun b => b.factorization p) hb₀C).symm
      have h2 : ∑ b ∈ C', b.factorization p =
          b₁.factorization p + ∑ b ∈ C.erase b₀, b.factorization p :=
        Finset.sum_insert (fun h => hb₁_not_C (Finset.mem_of_mem_erase h))
      omega
    exact not_lt_of_ge (hCmax C' hC'_mem) hsum_gt
  -- Sum the level inequality over `e ∈ Icc 1 M`.
  calc
    ∑ a ∈ S, a.factorization p
        = ∑ a ∈ S, ∑ e ∈ Finset.Icc 1 M, if p ^ e ∣ a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          have hm := Finset.mem_Icc.mp (hS ha)
          exact factorization_eq_sum_dvd hp hm.1 hm.2
    _ = ∑ e ∈ Finset.Icc 1 M, ∑ a ∈ S, if p ^ e ∣ a then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 M, (S.filter (fun a => p ^ e ∣ a)).card := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_boole, Nat.cast_id]
    _ ≤ ∑ e ∈ Finset.Icc 1 M, (C.filter (fun b => p ^ e ∣ b)).card := Finset.sum_le_sum hlevel
    _ = ∑ e ∈ Finset.Icc 1 M, ∑ b ∈ C, if p ^ e ∣ b then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_boole, Nat.cast_id]
    _ = ∑ b ∈ C, ∑ e ∈ Finset.Icc 1 M, if p ^ e ∣ b then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ b ∈ C, b.factorization p := by
          apply Finset.sum_le_sum
          intro b hb
          exact sum_dvd_le_factorization hp (erdos708Interval_pos (hCI hb))

/-- **Distinct Prime Factors Sum Bound**:
    For every `A ⊆ [2, ∞)` and every `m : ℕ`, `|B| ≤ ∑ a ∈ A, a.primeFactors.card` suffices. -/
theorem erdos708_omega_sum_bound {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ) :
    Erdos708Covers A m (∑ a ∈ A, a.primeFactors.card) := by
  set M := A.sup id
  set I := Erdos708Interval m M
  set P := A.biUnion Nat.primeFactors
  have hS_sub : ∀ p ∈ P, A.filter (fun a => p ∈ a.primeFactors) ⊆ Finset.Icc 1 M :=
    fun p _ => Finset.Subset.trans (Finset.filter_subset _ _) (subset_Icc_one_sup hA)
  have hcover : ∀ p ∈ P, ∃ C ⊆ I,
      C.card ≤ (A.filter (fun a => p ∈ a.primeFactors)).card ∧
      ∑ a ∈ A.filter (fun a => p ∈ a.primeFactors), a.factorization p ≤
        ∑ b ∈ C, b.factorization p := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨a, _, hap⟩
    exact exists_cover_prime_by_card (Nat.prime_of_mem_primeFactors hap) (hS_sub p hp)
  choose f hf_sub hf_card hf_val using hcover
  let B := P.attach.biUnion (fun ⟨p, hp⟩ => f p hp)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbf⟩
    exact hf_sub p hp hbf
  · calc
      B.card ≤ ∑ x ∈ P.attach, (f x.1 x.2).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ P.attach, (A.filter (fun a => x.1 ∈ a.primeFactors)).card :=
        Finset.sum_le_sum (fun x _ => hf_card x.1 x.2)
      _ = ∑ p ∈ P, (A.filter (fun a => p ∈ a.primeFactors)).card :=
        Finset.sum_attach P (fun p => (A.filter (fun a => p ∈ a.primeFactors)).card)
      _ = ∑ p ∈ P, ∑ a ∈ A, if p ∈ a.primeFactors then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p _; rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ a ∈ A, ∑ p ∈ P, if p ∈ a.primeFactors then 1 else 0 := Finset.sum_comm
      _ = ∑ a ∈ A, a.primeFactors.card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext p
        simp only [Finset.mem_filter, P, Finset.mem_biUnion]
        exact ⟨fun h => h.2, fun hp => ⟨⟨a, ha, hp⟩, hp⟩⟩
  · apply prod_dvd_prod_of_factorization_le
    · intro a ha; have := hA a ha; omega
    · intro b hb
      rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbf⟩
      exact Nat.ne_of_gt (erdos708Interval_pos (hf_sub p hp hbf))
    · intro p hp
      by_cases hpP : p ∈ P
      · have hsubB : f p hpP ⊆ B := by
          intro b hb
          exact Finset.mem_biUnion.mpr ⟨⟨p, hpP⟩, Finset.mem_attach _ _, hb⟩
        have hsumA : ∑ a ∈ A, a.factorization p =
            ∑ a ∈ A.filter (fun a => p ∈ a.primeFactors), a.factorization p := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro a ha hnot
          simp only [Finset.mem_filter, not_and] at hnot
          have hnotmem : p ∉ a.primeFactors := hnot ha
          rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnotmem
          exact hnotmem
        rw [hsumA]
        exact le_trans (hf_val p hpP)
          (Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun _ _ _ => Nat.zero_le _))
      · have hzero : ∀ a ∈ A, a.factorization p = 0 := by
          intro a ha
          have hnotmem : p ∉ a.primeFactors := fun h =>
            hpP (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
          rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hnotmem
          exact hnotmem
        rw [Finset.sum_eq_zero hzero]
        exact Nat.zero_le _

/-- **Semiprime / `ω(a) ≤ 2` Exact `2n` Theorem**:
    If every element of `A` has at most 2 distinct prime factors (for instance, primes, prime powers,
    and semiprimes like Erdős–Surányi's extremal family), then `|B| ≤ 2 * |A|` holds unconditionally. -/
theorem erdos708_two_n_of_omega_le_two {A : Finset ℕ}
    (hA : ∀ a ∈ A, 1 ≤ a) (hω : ∀ a ∈ A, a.primeFactors.card ≤ 2) (m : ℕ) :
    Erdos708Covers A m (2 * A.card) := by
  obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_omega_sum_bound hA m
  refine ⟨B, hBI, le_trans hBcard ?_, hBdvd⟩
  calc
    ∑ a ∈ A, a.primeFactors.card ≤ ∑ _a ∈ A, 2 := Finset.sum_le_sum hω
    _ = 2 * A.card := by simp [mul_comm]

#print axioms erdos708CoversInt_of_nat
#print axioms exists_cover_prime_by_card
#print axioms erdos708_omega_sum_bound
#print axioms erdos708_two_n_of_omega_le_two

end Erdos708
