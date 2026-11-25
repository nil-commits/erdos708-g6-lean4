import Erdos708.UpperCore

open scoped BigOperators Nat

namespace Erdos708

/-! ## Prime-Power Bin-Packing and Optimal Large-`max(A)` Linear Bounds -/

/-- If a list is not `Pairwise R`, we can extract two elements violating `R` and the rest
    preserving the product and dropping length by 2. -/
lemma exists_merge_of_not_pairwise {R : ℕ → ℕ → Prop} [DecidableRel R] :
    ∀ (xs : List ℕ), ¬ xs.Pairwise R →
      ∃ (u v : ℕ) (rest : List ℕ),
        ¬ R u v ∧ rest.length + 2 = xs.length ∧
        (u * v) * rest.prod = xs.prod ∧
        (∀ x ∈ rest, x ∈ xs) ∧ u ∈ xs ∧ v ∈ xs
  | [], h => absurd List.Pairwise.nil h
  | a :: tail, h => by
    rw [List.pairwise_cons] at h
    by_cases h1 : ∀ b ∈ tail, R a b
    · have htail : ¬ tail.Pairwise R := fun ht => h ⟨h1, ht⟩
      obtain ⟨u, v, rest, hnotR, hlen, hprod, hmem, hu, hv⟩ :=
        exists_merge_of_not_pairwise tail htail
      refine ⟨u, v, a :: rest, hnotR, by simp [hlen], ?_, ?_,
        List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv⟩
      · simp only [List.prod_cons]
        rw [← hprod]
        ring
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (hmem x hx')
    · push Not at h1
      obtain ⟨b, hb_mem, hnotR⟩ := h1
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb_mem
      refine ⟨a, b, l₁ ++ l₂, hnotR, by simp; omega, ?_, ?_, List.mem_cons_self, ?_⟩
      · simp only [List.prod_cons, List.prod_append]
        ring
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact List.mem_cons_of_mem a (List.mem_append_left _ hx1)
        · exact List.mem_cons_of_mem a (List.mem_append_right _ (List.mem_cons_of_mem b hx2))
      · exact List.mem_cons_of_mem a (List.mem_append_right _ List.mem_cons_self)

/-- Greedy multiplicative bin-packing of a list of integers in `[1, L]`:
    we can merge pairs until all pairwise products strictly exceed `L`. -/
lemma list_bin_pack (L : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), xs.length = n → (∀ x ∈ xs, 1 ≤ x ∧ x ≤ L) →
      ∃ bs : List ℕ,
        (∀ u ∈ bs, 1 ≤ u ∧ u ≤ L) ∧
        bs.prod = xs.prod ∧
        bs.Pairwise (fun u v => L < u * v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hlen hxs
    by_cases hpw : xs.Pairwise (fun u v => L < u * v)
    · exact ⟨xs, hxs, rfl, hpw⟩
    · obtain ⟨u, v, rest, hnotgt, hrest_len, hprod, hmem, hu, hv⟩ :=
        exists_merge_of_not_pairwise xs hpw
      have huv_le : u * v ≤ L := Nat.le_of_not_lt hnotgt
      have huv_ge : 1 ≤ u * v := Nat.mul_pos (hxs u hu).1 (hxs v hv).1
      let xs' := (u * v) :: rest
      have hlen' : xs'.length < n := by
        simp only [xs', List.length_cons]
        omega
      have hxs' : ∀ x ∈ xs', 1 ≤ x ∧ x ≤ L := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨huv_ge, huv_le⟩
        · exact hxs x (hmem x hx')
      obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw⟩ := ih xs'.length hlen' xs' rfl hxs'
      refine ⟨bs, hbs_bnd, ?_, hbs_pw⟩
      rw [hbs_prod]
      simpa [xs'] using hprod

/-- If a list `bs` of length `≥ 2` has every pairwise product `> L`, then
    `(L + 1) ^ bs.length ≤ bs.prod ^ 2`. Pure `ℕ` induction on length (step 2)! -/
lemma pairwise_mul_gt_pow_le_sq (L : ℕ) :
    ∀ (n : ℕ) (bs : List ℕ), bs.length = n → 2 ≤ n →
      bs.Pairwise (fun u v => L < u * v) →
      (L + 1) ^ n ≤ bs.prod ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro bs hlen hn hpw
    match bs with
    | [] => simp at hlen; omega
    | [_] => simp at hlen; omega
    | [u, v] =>
      simp at hlen
      subst hlen
      rw [List.pairwise_cons] at hpw
      have huv : L + 1 ≤ u * v := hpw.1 v List.mem_cons_self
      simp only [List.prod_cons, List.prod_nil, mul_one]
      exact Nat.pow_le_pow_left huv 2
    | [u, v, w] =>
      simp at hlen
      subst hlen
      rw [List.pairwise_cons] at hpw
      have huv : L + 1 ≤ u * v := hpw.1 v List.mem_cons_self
      have huw : L + 1 ≤ u * w := hpw.1 w (List.mem_cons_of_mem v List.mem_cons_self)
      rw [List.pairwise_cons] at hpw
      have hvw : L + 1 ≤ v * w := hpw.2.1 w List.mem_cons_self
      simp only [List.prod_cons, List.prod_nil, mul_one]
      have h1 : (L + 1) * (L + 1) * (L + 1) ≤ (u * v) * (u * w) * (v * w) :=
        Nat.mul_le_mul (Nat.mul_le_mul huv huw) hvw
      have h2 : (L + 1) ^ 3 = (L + 1) * (L + 1) * (L + 1) := by ring
      have h3 : (u * v) * (u * w) * (v * w) = (u * (v * w)) ^ 2 := by ring
      omega
    | u :: v :: w :: t :: rest =>
      let tail := w :: t :: rest
      have htail_len : tail.length < n := by
        dsimp [tail]; simp at hlen ⊢; omega
      have htail_ge : 2 ≤ tail.length := by dsimp [tail]; simp
      rw [List.pairwise_cons] at hpw
      have huv : L + 1 ≤ u * v := hpw.1 v List.mem_cons_self
      rw [List.pairwise_cons] at hpw
      have htail_pw : tail.Pairwise (fun x y => L < x * y) := hpw.2.2
      have hih := ih tail.length htail_len tail rfl htail_ge htail_pw
      have hn_eq : n = tail.length + 2 := by dsimp [tail]; simp at hlen ⊢; omega
      rw [hn_eq, pow_add]
      have hsq : (L + 1) ^ 2 ≤ (u * v) ^ 2 := Nat.pow_le_pow_left huv 2
      have hprod : (u :: v :: tail).prod = (u * v) * tail.prod := by
        simp [List.prod_cons, mul_assoc]
      change (L + 1) ^ tail.length * (L + 1) ^ 2 ≤ (u :: v :: tail).prod ^ 2
      rw [hprod, mul_pow]
      have := Nat.mul_le_mul hih hsq
      linarith

/-- Greedy fresh-multiple covering for a list of divisors `us`:
    if every `u ∈ us` has at least `B₀.card + us.length` multiples in `I`,
    then we can pick a set `B₁ ⊆ I` disjoint from `B₀` with `B₁.card ≤ us.length`
    and `us.prod ∣ ∏ b ∈ B₁, b`. -/
lemma fresh_multiples_cover_list {m M : ℕ} (B₀ : Finset ℕ) :
    ∀ (us : List ℕ),
      (∀ u ∈ us, 1 ≤ u ∧ B₀.card + us.length ≤ M / u) →
      ∃ B₁ ⊆ Erdos708Interval m M,
        Disjoint B₀ B₁ ∧ B₁.card ≤ us.length ∧ us.prod ∣ ∏ b ∈ B₁, b
  | [], _ =>
    ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right _, by simp, by simp⟩
  | u :: rest, hus => by
    have hrest : ∀ x ∈ rest, 1 ≤ x ∧ B₀.card + rest.length ≤ M / x := by
      intro x hx
      have h := hus x (List.mem_cons_of_mem u hx)
      exact ⟨h.1, by simp at h; omega⟩
    obtain ⟨B₁, hB₁I, hdisj, hB₁card, hB₁dvd⟩ := fresh_multiples_cover_list B₀ rest hrest
    have hu := hus u List.mem_cons_self
    have hu_pos : 0 < u := by omega
    have hmult_ge : B₀.card + (rest.length + 1) ≤
        ((Erdos708Interval m M).filter (fun b => u ∣ b)).card := by
      have h1 : B₀.card + (rest.length + 1) ≤ M / u := by simpa using hu.2
      exact le_trans h1 (card_multiples_Icc_ge m M u hu_pos)
    have hused_lt : (B₀ ∪ B₁).card <
        ((Erdos708Interval m M).filter (fun b => u ∣ b)).card := by
      have h1 : (B₀ ∪ B₁).card ≤ B₀.card + B₁.card := Finset.card_union_le B₀ B₁
      omega
    have hnot_sub : ¬ ((Erdos708Interval m M).filter (fun b => u ∣ b) ⊆ B₀ ∪ B₁) := by
      intro hsub
      exact not_lt_of_ge (Finset.card_le_card hsub) hused_lt
    rw [Finset.not_subset] at hnot_sub
    obtain ⟨b, hb_filt, hb_not_used⟩ := hnot_sub
    rw [Finset.mem_filter] at hb_filt
    rw [Finset.mem_union, not_or] at hb_not_used
    refine ⟨insert b B₁, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hb_filt.1
      · exact hB₁I hx'
    · rw [Finset.disjoint_insert_right]
      exact ⟨hb_not_used.1, hdisj⟩
    · rw [Finset.card_insert_of_notMem hb_not_used.2]
      simp; omega
    · rw [List.prod_cons, Finset.prod_insert hb_not_used.2]
      exact mul_dvd_mul hb_filt.2 hB₁dvd

/-- Prime-power decomposition of `a ≥ 1` into large prime powers (`> L`) and small bins (`≤ L`). -/
lemma factor_into_large_and_bins {a L k : ℕ} (ha : 1 ≤ a) (hk : 2 ≤ k)
    (haL : a ^ 2 < (L + 1) ^ (k + 1)) :
    ∃ (bs : List ℕ),
      (∀ u ∈ bs, 1 ≤ u ∧ u ≤ L) ∧
      (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card + bs.length ≤ k ∧
      a = (∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
            p ^ (a.factorization p)) * bs.prod := by
  have ha0 : a ≠ 0 := by omega
  set Pbig := a.primeFactors.filter (fun p => L < p ^ (a.factorization p))
  set Psmall := a.primeFactors.filter (fun p => ¬ (L < p ^ (a.factorization p)))
  have hsplit : a = (∏ p ∈ Pbig, p ^ (a.factorization p)) *
      (∏ p ∈ Psmall, p ^ (a.factorization p)) := by
    have h1 : a = ∏ p ∈ a.primeFactors, p ^ (a.factorization p) := by
      have h := (Nat.prod_factorization_pow_eq_self ha0).symm
      rw [Finsupp.prod, Nat.support_factorization] at h
      exact h
    calc
      a = ∏ p ∈ a.primeFactors, p ^ (a.factorization p) := h1
      _ = (∏ p ∈ Pbig, p ^ (a.factorization p)) * (∏ p ∈ Psmall, p ^ (a.factorization p)) :=
        (Finset.prod_filter_mul_prod_filter_not a.primeFactors
          (fun p => L < p ^ (a.factorization p)) (fun p => p ^ (a.factorization p))).symm
  -- Build list of small prime powers
  let xs : List ℕ := Psmall.toList.map (fun p => p ^ (a.factorization p))
  have hxs_prod : xs.prod = ∏ p ∈ Psmall, p ^ (a.factorization p) := by
    dsimp [xs]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hxs_bnd : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ L := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
    rw [Finset.mem_toList] at hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hp_le : p ^ (a.factorization p) ≤ L := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2
    exact ⟨Nat.one_le_pow _ _ hp_prime.pos, hp_le⟩
  obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw⟩ := list_bin_pack L xs.length xs rfl hxs_bnd
  have ha_eq : a = (∏ p ∈ Pbig, p ^ (a.factorization p)) * bs.prod := by
    rw [hbs_prod, hxs_prod]
    exact hsplit
  have hbig_ge : (L + 1) ^ Pbig.card ≤ ∏ p ∈ Pbig, p ^ (a.factorization p) := by
    calc
      (L + 1) ^ Pbig.card = ∏ _p ∈ Pbig, (L + 1) := by simp
      _ ≤ ∏ p ∈ Pbig, p ^ (a.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        exact (Finset.mem_filter.mp hp).2
  have hbs_pos : 1 ≤ bs.prod := by
    rw [hbs_prod, hxs_prod]
    apply Finset.one_le_prod'
    intro p hp
    exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
  refine ⟨bs, hbs_bnd, ?_, ha_eq⟩
  by_cases ht : 2 ≤ bs.length
  · -- `t ≥ 2`: `(L + 1) ^ (2 * r + t) ≤ a ^ 2 < (L + 1) ^ (k + 1)`
    have hsmall_ge : (L + 1) ^ bs.length ≤ bs.prod ^ 2 :=
      pairwise_mul_gt_pow_le_sq L bs.length bs rfl ht hbs_pw
    have hpow_lt : (L + 1) ^ (2 * Pbig.card + bs.length) < (L + 1) ^ (k + 1) := by
      calc
        (L + 1) ^ (2 * Pbig.card + bs.length)
            = ((L + 1) ^ Pbig.card) ^ 2 * (L + 1) ^ bs.length := by
              rw [pow_add, ← pow_mul, mul_comm Pbig.card 2]
        _ ≤ (∏ p ∈ Pbig, p ^ (a.factorization p)) ^ 2 * bs.prod ^ 2 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hbig_ge 2) hsmall_ge
        _ = a ^ 2 := by rw [← mul_pow, ← ha_eq]
        _ < (L + 1) ^ (k + 1) := haL
    have hL1_gt1 : 1 < L + 1 := by
      by_contra h
      have hL0 : L = 0 := by omega
      subst hL0
      simp at haL
      nlinarith
    have hlt_exp : 2 * Pbig.card + bs.length < k + 1 :=
      (Nat.pow_lt_pow_iff_right hL1_gt1).mp hpow_lt
    omega
  · -- `t ≤ 1`: `(L + 1) ^ (2 * r) ≤ a ^ 2 < (L + 1) ^ (k + 1)`, so `2 * r ≤ k`, hence `r + t ≤ k`!
    have hpow_lt : (L + 1) ^ (2 * Pbig.card) < (L + 1) ^ (k + 1) := by
      have h1 : (L + 1) ^ Pbig.card ≤ a := by
        calc (L + 1) ^ Pbig.card
            ≤ ∏ p ∈ Pbig, p ^ (a.factorization p) := hbig_ge
          _ ≤ (∏ p ∈ Pbig, p ^ (a.factorization p)) * bs.prod :=
              Nat.le_mul_of_pos_right _ hbs_pos
          _ = a := ha_eq.symm
      calc
        (L + 1) ^ (2 * Pbig.card) = ((L + 1) ^ Pbig.card) ^ 2 := by
          rw [← pow_mul, mul_comm Pbig.card 2]
        _ ≤ a ^ 2 := Nat.pow_le_pow_left h1 2
        _ < (L + 1) ^ (k + 1) := haL
    have hL1_gt1 : 1 < L + 1 := by
      by_contra h
      have hL0 : L = 0 := by omega
      subst hL0
      simp at haL
      nlinarith
    have hlt_exp : 2 * Pbig.card < k + 1 :=
      (Nat.pow_lt_pow_iff_right hL1_gt1).mp hpow_lt
    omega

/-- **Master Prime-Power Bin-Packing Theorem**:
    For any `A ⊆ [1, ∞)` with `M = max(A)`, any `m : ℕ`, and any `k ≥ 2`, `L : ℕ` with
    `k * |A| * L ≤ M` and `M ^ 2 < (L + 1) ^ (k + 1)`,
    there exists `B ⊆ {m + 1, ..., m + M}` with `|B| ≤ k * |A|` and `∏ A ∣ ∏ B`. -/
theorem erdos708_binpack_general {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m k L : ℕ)
    (hk : 2 ≤ k) (hL_mul : k * A.card * L ≤ A.sup id)
    (hML : (A.sup id) ^ 2 < (L + 1) ^ (k + 1)) :
    Erdos708Covers A m (k * A.card) := by
  set M := A.sup id
  set I := Erdos708Interval m M
  -- Step 1: For every `a ∈ A`, factor `a` into large prime powers (`> L`) and small bins (`≤ L`).
  have hfac_a : ∀ a ∈ A, ∃ bs : List ℕ,
      (∀ u ∈ bs, 1 ≤ u ∧ u ≤ L) ∧
      (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card + bs.length ≤ k ∧
      a = (∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
            p ^ (a.factorization p)) * bs.prod := by
    intro a ha
    have haM : a ≤ M := Finset.le_sup (f := id) ha
    have haL : a ^ 2 < (L + 1) ^ (k + 1) := lt_of_le_of_lt (Nat.pow_le_pow_left haM 2) hML
    exact factor_into_large_and_bins (hA a ha) hk haL
  choose bsOf hbs_bnd hbs_len hbs_eq using hfac_a
  -- Step 2: Cover all large prime powers (`p ^ v_p(a) > L`) using `exists_cover_prime_by_card`.
  set PbigAll := A.biUnion (fun a => a.primeFactors.filter (fun p => L < p ^ (a.factorization p)))
  have hcover_big : ∀ p ∈ PbigAll, ∃ C ⊆ I,
      C.card ≤ (A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p))).card ∧
      ∑ a ∈ A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p)), a.factorization p
        ≤ ∑ b ∈ C, b.factorization p := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨a, _, hap⟩
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hap).1
    have hsub : A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p)) ⊆
        Finset.Icc 1 M :=
      Finset.Subset.trans (Finset.filter_subset _ _) (subset_Icc_one_sup hA)
    exact exists_cover_prime_by_card hp_prime hsub
  choose Cbig hCbig_sub hCbig_card hCbig_val using hcover_big
  let B₀ : Finset ℕ := PbigAll.attach.biUnion (fun ⟨p, hp⟩ => Cbig p hp)
  have hB₀_sub : B₀ ⊆ I := by
    intro b hb
    rcases Finset.mem_biUnion.mp hb with ⟨⟨p, hp⟩, _, hbc⟩
    exact hCbig_sub p hp hbc
  have hB₀_card : B₀.card ≤
      ∑ a ∈ A, (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card := by
    calc
      B₀.card ≤ ∑ x ∈ PbigAll.attach, (Cbig x.1 x.2).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ PbigAll.attach,
            (A.filter (fun a => x.1 ∈ a.primeFactors ∧ L < x.1 ^ (a.factorization x.1))).card :=
        Finset.sum_le_sum (fun x _ => hCbig_card x.1 x.2)
      _ = ∑ p ∈ PbigAll,
            (A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p))).card :=
        Finset.sum_attach PbigAll
          (fun p => (A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p))).card)
      _ = ∑ p ∈ PbigAll, ∑ a ∈ A,
            if p ∈ a.primeFactors ∧ L < p ^ (a.factorization p) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p _; rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ a ∈ A, ∑ p ∈ PbigAll,
            if p ∈ a.primeFactors ∧ L < p ^ (a.factorization p) then 1 else 0 := Finset.sum_comm
      _ = ∑ a ∈ A, (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext p
        simp only [Finset.mem_filter, PbigAll, Finset.mem_biUnion]
        exact ⟨fun h => h.2, fun hp => ⟨⟨a, ha, hp⟩, hp⟩⟩
  -- Step 3: Collect all small bins into one list `us` and cover via `fresh_multiples_cover_list`.
  let us : List ℕ := (A.attach.toList.map (fun x => bsOf x.1 x.2)).flatten
  have hus_len : us.length = ∑ x ∈ A.attach, (bsOf x.1 x.2).length := by
    dsimp [us]
    rw [List.length_flatten, List.map_map]
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hus_prod : us.prod = ∏ x ∈ A.attach, (bsOf x.1 x.2).prod := by
    dsimp [us]
    rw [List.prod_flatten, List.map_map]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have htot_card : B₀.card + us.length ≤ k * A.card := by
    have hsum_le :
        (∑ a ∈ A, (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card) +
          (∑ x ∈ A.attach, (bsOf x.1 x.2).length) ≤ k * A.card := by
      have h1 : ∑ a ∈ A, (a.primeFactors.filter (fun p => L < p ^ (a.factorization p))).card =
          ∑ x ∈ A.attach, (x.1.primeFactors.filter (fun p => L < p ^ (x.1.factorization p))).card :=
        (Finset.sum_attach A _).symm
      rw [h1, ← Finset.sum_add_distrib]
      calc
        ∑ x ∈ A.attach,
            ((x.1.primeFactors.filter (fun p => L < p ^ (x.1.factorization p))).card +
              (bsOf x.1 x.2).length)
            ≤ ∑ _x ∈ A.attach, k := Finset.sum_le_sum (fun x _ => hbs_len x.1 x.2)
        _ = k * A.card := by simp [mul_comm]
    omega
  have hus_cond : ∀ u ∈ us, 1 ≤ u ∧ B₀.card + us.length ≤ M / u := by
    intro u hu
    dsimp [us] at hu
    rcases List.mem_flatten.mp hu with ⟨bs, hbs_mem, hu_bs⟩
    rcases List.mem_map.mp hbs_mem with ⟨x, _, rfl⟩
    have hbnd := hbs_bnd x.1 x.2 u hu_bs
    refine ⟨hbnd.1, ?_⟩
    have hu_pos : 0 < u := by omega
    have hdiv : k * A.card ≤ M / u := by
      rw [Nat.le_div_iff_mul_le hu_pos]
      calc k * A.card * u ≤ k * A.card * L := Nat.mul_le_mul_left _ hbnd.2
        _ ≤ M := hL_mul
    exact le_trans htot_card hdiv
  obtain ⟨B₁, hB₁_sub, hdisj, hB₁_card, hB₁_dvd⟩ := fresh_multiples_cover_list (m := m) (M := M) B₀ us hus_cond
  -- Step 4: Combine `B = B₀ ∪ B₁` and check cardinality & divisibility!
  refine ⟨B₀ ∪ B₁, Finset.union_subset hB₀_sub hB₁_sub, ?_, ?_⟩
  · calc
      (B₀ ∪ B₁).card ≤ B₀.card + B₁.card := Finset.card_union_le B₀ B₁
      _ ≤ B₀.card + us.length := Nat.add_le_add_left hB₁_card _
      _ ≤ k * A.card := htot_card
  · -- Show `∏ a ∈ A, a = (∏ large prime powers) * us.prod`
    have hprod_A : ∏ a ∈ A, a =
        (∏ a ∈ A, ∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
          p ^ (a.factorization p)) * us.prod := by
      rw [hus_prod, ← Finset.prod_attach A (fun a => a),
          ← Finset.prod_attach A (fun a =>
            ∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
              p ^ (a.factorization p)),
          ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x _
      exact hbs_eq x.1 x.2
    rw [hprod_A, Finset.prod_union hdisj]
    apply mul_dvd_mul _ hB₁_dvd
    -- Show `∏ large prime powers ∣ ∏ b ∈ B₀, b` via `Nat.factorization`!
    have hbig_ne : ∀ a ∈ A,
        (∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
          p ^ (a.factorization p)) ≠ 0 := by
      intro a _
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
    have hL_ne : (∏ a ∈ A, ∏ p ∈ a.primeFactors.filter (fun p => L < p ^ (a.factorization p)),
        p ^ (a.factorization p)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hbig_ne
    have hB₀_ne : (∏ b ∈ B₀, b) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))
    rw [← Nat.factorization_le_iff_dvd hL_ne hB₀_ne]
    intro p
    rw [Nat.factorization_prod hbig_ne,
        Nat.factorization_prod (fun b hb => Nat.ne_of_gt (erdos708Interval_pos (hB₀_sub hb)))]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    -- Compute the `p`-adic valuation of the inner product for each `a ∈ A`
    have hinner : ∀ a ∈ A,
        (∏ q ∈ a.primeFactors.filter (fun q => L < q ^ (a.factorization q)),
          q ^ (a.factorization q)).factorization p =
        if p ∈ a.primeFactors ∧ L < p ^ (a.factorization p) then a.factorization p else 0 := by
      intro a _
      rw [Nat.factorization_prod (fun q hq =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero)]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
      have hterm : ∀ q ∈ a.primeFactors.filter (fun q => L < q ^ (a.factorization q)),
          (q ^ (a.factorization q)).factorization p = if q = p then a.factorization p else 0 := by
        intro q hq
        have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
        rw [Nat.Prime.factorization_pow hq_prime, Finsupp.single_apply]
        by_cases hqp : q = p
        · subst hqp; simp
        · simp [hqp]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      simp only [Finset.mem_filter]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
    by_cases hpP : p ∈ PbigAll
    · have hsubB₀ : Cbig p hpP ⊆ B₀ := by
        intro b hb
        exact Finset.mem_biUnion.mpr ⟨⟨p, hpP⟩, Finset.mem_attach _ _, hb⟩
      exact le_trans (hCbig_val p hpP)
        (Finset.sum_le_sum_of_subset_of_nonneg hsubB₀ (fun _ _ _ => Nat.zero_le _))
    · have hemp : A.filter (fun a => p ∈ a.primeFactors ∧ L < p ^ (a.factorization p)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a ha hcond
        exact hpP (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr hcond⟩)
      rw [hemp, Finset.sum_empty]
      exact Nat.zero_le _

/-- **Explicit Power-Threshold Corollary (`|B| ≤ k * n`)**:
    For any `k ≥ 2`, if `(k * |A|) ^ (k + 1) ≤ (max A) ^ (k - 1)`, then `|B| ≤ k * |A|`.
    Zero floor loss via `(L + 1) * (k * n) > M`! -/
theorem erdos708_binpack_kn {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m k : ℕ)
    (hk : 2 ≤ k) (hM : (k * A.card) ^ (k + 1) ≤ (A.sup id) ^ (k - 1)) :
    Erdos708Covers A m (k * A.card) := by
  by_cases hA_emp : A = ∅
  · subst hA_emp
    exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  have hcard_pos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA_emp)
  set M := A.sup id
  set kn := k * A.card
  have hkn_pos : 0 < kn := Nat.mul_pos (by omega) hcard_pos
  set L := M / kn
  have hL_mul : kn * L ≤ M := Nat.mul_div_le M kn
  have hML : M ^ 2 < (L + 1) ^ (k + 1) := by
    have h1 : M < (L + 1) * kn := by
      have hdm := Nat.div_add_mod M kn
      have hml := Nat.mod_lt M hkn_pos
      change M < (M / kn + 1) * kn
      nlinarith
    have h2 : M ^ (k + 1) < ((L + 1) * kn) ^ (k + 1) :=
      Nat.pow_lt_pow_left h1 (by omega)
    rw [mul_pow] at h2
    have h3 : M ^ 2 * kn ^ (k + 1) ≤ M ^ (k + 1) := by
      have h4 : M ^ 2 * kn ^ (k + 1) ≤ M ^ 2 * M ^ (k - 1) :=
        Nat.mul_le_mul_left (M ^ 2) hM
      have h5 : M ^ 2 * M ^ (k - 1) = M ^ (k + 1) := by
        rw [← pow_add]
        congr 1; omega
      omega
    have h6 : M ^ 2 * kn ^ (k + 1) < (L + 1) ^ (k + 1) * kn ^ (k + 1) :=
      lt_of_le_of_lt h3 h2
    exact Nat.lt_of_mul_lt_mul_right h6
  exact erdos708_binpack_general hA m k L hk hL_mul hML

/-- **Sharp `2n` Bound for Large `max(A)` (`M ≥ 8 n^3`)**:
    Whenever `8 * |A|^3 ≤ max(A)`, Erdős's conjectured bound `|B| ≤ 2 * |A|` holds unconditionally! -/
theorem erdos708_two_n_of_ge_8n3 {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ)
    (hM : 8 * A.card ^ 3 ≤ A.sup id) :
    Erdos708Covers A m (2 * A.card) := by
  apply erdos708_binpack_kn hA m 2 (le_refl 2)
  have h1 : (2 * A.card) ^ (2 + 1) = 8 * A.card ^ 3 := by ring
  simpa [h1] using hM

/-- **Sharp `3n` Bound for `M ≥ 9 n^2`**:
    Whenever `9 * |A|^2 ≤ max(A)`, `|B| ≤ 3 * |A|` holds unconditionally! -/
theorem erdos708_three_n_of_ge_9n2 {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ)
    (hM : 9 * A.card ^ 2 ≤ A.sup id) :
    Erdos708Covers A m (3 * A.card) := by
  apply erdos708_binpack_kn hA m 3 (by omega)
  have h1 : (3 * A.card) ^ (3 + 1) = (9 * A.card ^ 2) ^ 2 := by ring
  rw [h1]
  simpa using Nat.pow_le_pow_left hM 2

/-- **Exact `2n` Bound for Small `max(A)` (`M ≤ 2n`)**:
    Whenever `max(A) ≤ 2 * |A|`, the full interval `I` already gives `|B| ≤ 2 * |A|`. -/
theorem erdos708_two_n_of_le_2n {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) (m : ℕ)
    (hM : A.sup id ≤ 2 * A.card) :
    Erdos708Covers A m (2 * A.card) := by
  obtain ⟨B, hBI, hBcard, hBdvd⟩ := erdos708_trivial_max_bound hA m
  exact ⟨B, hBI, le_trans hBcard hM, hBdvd⟩

#print axioms erdos708_binpack_general
#print axioms erdos708_binpack_kn
#print axioms erdos708_two_n_of_ge_8n3
#print axioms erdos708_three_n_of_ge_9n2
#print axioms erdos708_two_n_of_le_2n

end Erdos708
