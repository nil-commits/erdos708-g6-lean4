import Erdos708.Matching
import Erdos708.UpperBinPack

/-!
# PPL 176 (Erdős Problem #708) — Coprime Multiplicative Packing & Exact Top-`c_p` Foundations

This module formalizes the counterexample-proof foundations replacing separate-prime
ceilings (`⌈v_p(R)/k_p⌉`, broken by Counterexamples A and B) with:
1. **`coprime_packing_slot_of_mul_le`** and **`coprime_packing_slot_of_not_dvd`**:
   sound single-slot realization for any product `D` of pairwise coprime prime powers
   with either `(S.card + 1) * D ≤ M` or `D ≤ M ∧ ∀ b ∈ S, ¬ (D ∣ b)`.
2. **`isCover_union_of_disjoint_factorization`**:
   valuation-based cover criterion over disjoint `B₀ ∪ B₁`.
3. **`exists_cover_of_seed_topC_and_coprime_bins`**:
   Master Top-`c_p` + Coprime Multiplicative Packing Theorem combining:
   - a seed set `B₀ ⊆ consecInterval x M` (e.g. matching witness set `B_M`),
   - multi-slot exact top-`c_p` witness sets `T p ⊆ consecInterval x M \ B₀` for `p ∈ P_multi`, and
   - pairwise coprime multiplicative bins `bins : List ℕ` realized inside `consecInterval x M \ B₀`.
4. **`list_bin_pack_coprime`** & **`exists_bins_from_list_bin_pack`**:
   multiplicative bin-packing preserving `Pairwise Nat.Coprime` so each remaining
   prime power dividing `∏ qs` is absorbed cleanly by a single bin `D ∈ bs`, with
   `(L + 1) ^ bs.length ≤ bs.prod ^ 2` whenever `2 ≤ bs.length`.
-/

open scoped BigOperators Nat

namespace Erdos708

/-- Any positive divisor `D` with `(S.card + 1) * D ≤ M` has a multiple in `consecInterval x M \ S`. -/
theorem coprime_packing_slot_of_mul_le {x M D : ℕ} {S : Finset ℕ}
    (hD : 0 < D) (hbound : (S.card + 1) * D ≤ M) :
    ∃ b ∈ consecInterval x M, b ∉ S ∧ D ∣ b :=
  exists_avoiding_multiple_in_consecInterval x M D S hD hbound

/-- Any positive divisor `D ≤ M` that divides no element of `S` has a multiple in
    `consecInterval x M \ S`. -/
theorem coprime_packing_slot_of_not_dvd {x M D : ℕ} {S : Finset ℕ}
    (hD : 0 < D) (hDM : D ≤ M) (hndvd : ∀ b ∈ S, ¬ (D ∣ b)) :
    ∃ b ∈ consecInterval x M, b ∉ S ∧ D ∣ b := by
  obtain ⟨b, hbI, hDb⟩ := exists_multiple_in_consecInterval x D M hD hDM
  exact ⟨b, hbI, fun hbS => hndvd b hbS hDb, hDb⟩

/-- Valuation-based `IsCover` over a disjoint union `B₀ ∪ B₁`. -/
theorem isCover_union_of_disjoint_factorization {A B₀ B₁ : Finset ℕ}
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B₀, b ≠ 0) (hB1 : ∀ b ∈ B₁, b ≠ 0)
    (hdisj : Disjoint B₀ B₁)
    (hval : ∀ p : ℕ, p.Prime →
      ∑ a ∈ A, a.factorization p ≤
        ∑ b ∈ B₀, b.factorization p + ∑ b ∈ B₁, b.factorization p) :
    IsCover A (B₀ ∪ B₁) := by
  rw [IsCover]
  have hprodA0 : (∏ a ∈ A, a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hA0
  have hB01_0 : ∀ b ∈ B₀ ∪ B₁, b ≠ 0 := by
    intro b hb
    rcases Finset.mem_union.mp hb with hb0 | hb1
    · exact hB0 b hb0
    · exact hB1 b hb1
  have hprodB01_0 : (∏ b ∈ B₀ ∪ B₁, b) ≠ 0 := Finset.prod_ne_zero_iff.mpr hB01_0
  rw [← Nat.factorization_le_iff_dvd hprodA0 hprodB01_0]
  intro p
  rw [factorization_finset_prod A hA0 p, factorization_finset_prod (B₀ ∪ B₁) hB01_0 p,
      Finset.sum_union hdisj]
  by_cases hp : p.Prime
  · exact hval p hp
  · have hzero : ∑ a ∈ A, a.factorization p = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact Nat.factorization_eq_zero_of_not_prime a hp
    rw [hzero]
    exact Nat.zero_le _

private lemma exists_witness_finset_of_bins (x M : ℕ) (B₀ : Finset ℕ) :
    ∀ (bins : List ℕ),
      (∀ D ∈ bins, 0 < D ∧ ((B₀.card + 1) * D ≤ M ∨ (D ≤ M ∧ ∀ b ∈ B₀, ¬ (D ∣ b)))) →
      ∃ B_bins : Finset ℕ, B_bins ⊆ consecInterval x M ∧ Disjoint B₀ B_bins ∧
        B_bins.card ≤ bins.length ∧ ∀ D ∈ bins, ∃ b ∈ B_bins, D ∣ b
  | [], _ => ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_right B₀, by simp, fun _ h => by simp at h⟩
  | D :: ds, h => by
    have hD := h D (by simp)
    have hds : ∀ D' ∈ ds, 0 < D' ∧ ((B₀.card + 1) * D' ≤ M ∨ (D' ≤ M ∧ ∀ b ∈ B₀, ¬ (D' ∣ b))) :=
      fun D' hD' => h D' (by simp [hD'])
    obtain ⟨B_ds, hds_I, hds_disj, hds_card, hds_wit⟩ := exists_witness_finset_of_bins x M B₀ ds hds
    have hD_ex : ∃ b ∈ consecInterval x M, b ∉ B₀ ∧ D ∣ b := by
      rcases hD.2 with hmul | ⟨hDM, hnd⟩
      · exact coprime_packing_slot_of_mul_le hD.1 hmul
      · exact coprime_packing_slot_of_not_dvd hD.1 hDM hnd
    obtain ⟨bD, hbD_I, hbD_notB0, hbD_dvd⟩ := hD_ex
    refine ⟨insert bD B_ds, Finset.insert_subset_iff.mpr ⟨hbD_I, hds_I⟩,
      Finset.disjoint_insert_right.mpr ⟨hbD_notB0, hds_disj⟩, ?_, ?_⟩
    · exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right hds_card 1)
    · intro D' hD'
      rcases List.mem_cons.mp hD' with rfl | hD'ds
      · exact ⟨bD, Finset.mem_insert_self _ _, hbD_dvd⟩
      · obtain ⟨b, hb_mem, hb_dvd⟩ := hds_wit D' hD'ds
        exact ⟨b, Finset.mem_insert_of_mem hb_mem, hb_dvd⟩

/-- Master Top-`c_p` + Coprime Multiplicative Packing Theorem:
    combining a seed `B₀ ⊆ consecInterval x M`, multi-slot sets `T p ⊆ consecInterval x M \ B₀`
    for `p ∈ P_multi`, and pairwise-coprime or individually avoidable bins `bins : List ℕ`
    produces `B ⊆ consecInterval x M` with `B.card ≤ B₀.card + ∑ p ∈ P_multi, (T p).card + bins.length`
    and `IsCover A B`. -/
theorem exists_cover_of_seed_topC_and_coprime_bins {A B₀ P_multi : Finset ℕ} {x M : ℕ}
    (T : ℕ → Finset ℕ) (bins : List ℕ)
    (hA0 : ∀ a ∈ A, a ≠ 0)
    (hB0_I : B₀ ⊆ consecInterval x M)
    (hT_sub : ∀ p ∈ P_multi, T p ⊆ consecInterval x M ∧ Disjoint B₀ (T p))
    (hT_val : ∀ p ∈ P_multi,
      ∑ a ∈ A, a.factorization p ≤
        ∑ b ∈ B₀, b.factorization p + ∑ b ∈ T p, b.factorization p)
    (hbins : ∀ D ∈ bins, 0 < D ∧ ((B₀.card + 1) * D ≤ M ∨ (D ≤ M ∧ ∀ b ∈ B₀, ¬ (D ∣ b))))
    (hother : ∀ p : ℕ, p.Prime → p ∉ P_multi →
      ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B₀, b.factorization p ∨
      ∃ D ∈ bins, ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B₀, b.factorization p + D.factorization p) :
    ∃ B ⊆ consecInterval x M,
      B.card ≤ B₀.card + (∑ p ∈ P_multi, (T p).card) + bins.length ∧ IsCover A B := by
  obtain ⟨B_bins, hbins_I, hbins_disj, hbins_card, hbins_wit⟩ :=
    exists_witness_finset_of_bins x M B₀ bins hbins
  set B₁ : Finset ℕ := P_multi.biUnion T ∪ B_bins
  have hB1_I : B₁ ⊆ consecInterval x M := by
    apply Finset.union_subset
    · intro b hb
      obtain ⟨p, hp, hbp⟩ := Finset.mem_biUnion.mp hb
      exact (hT_sub p hp).1 hbp
    · exact hbins_I
  have hdisj : Disjoint B₀ B₁ := by
    rw [Finset.disjoint_union_right]
    refine ⟨Finset.disjoint_left.mpr ?_, hbins_disj⟩
    intro b hbB0 hbU
    obtain ⟨p, hpP, hbTp⟩ := Finset.mem_biUnion.mp hbU
    exact Finset.disjoint_left.mp (hT_sub p hpP).2 hbB0 hbTp
  have hB1_card : B₁.card ≤ (∑ p ∈ P_multi, (T p).card) + bins.length := by
    exact le_trans (Finset.card_union_le (P_multi.biUnion T) B_bins)
      (Nat.add_le_add Finset.card_biUnion_le hbins_card)
  have hB0_ne : ∀ b ∈ B₀, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hB0_I hb)).ne'
  have hB1_ne : ∀ b ∈ B₁, b ≠ 0 := fun b hb => (pos_of_mem_consecInterval (hB1_I hb)).ne'
  refine ⟨B₀ ∪ B₁, Finset.union_subset hB0_I hB1_I, ?_, ?_⟩
  · have h1 : (B₀ ∪ B₁).card ≤ B₀.card + B₁.card := Finset.card_union_le B₀ B₁
    omega
  · apply isCover_union_of_disjoint_factorization hA0 hB0_ne hB1_ne hdisj
    intro p hp
    by_cases hpM : p ∈ P_multi
    · have hTp_sub : T p ⊆ B₁ :=
        (Finset.subset_biUnion_of_mem T hpM).trans Finset.subset_union_left
      have hsum_le : ∑ b ∈ T p, b.factorization p ≤ ∑ b ∈ B₁, b.factorization p :=
        Finset.sum_le_sum_of_subset hTp_sub
      exact le_trans (hT_val p hpM) (Nat.add_le_add_left hsum_le _)
    · rcases hother p hp hpM with hle | ⟨D, hD_mem, hD_le⟩
      · omega
      · obtain ⟨bD, hbD_mem, hDbD⟩ := hbins_wit D hD_mem
        have hbD_B1 : bD ∈ B₁ := Finset.mem_union_right _ hbD_mem
        have hD_pos : D ≠ 0 := (hbins D hD_mem).1.ne'
        have hbD_ne : bD ≠ 0 := hB1_ne bD hbD_B1
        have hfac_D : D.factorization p ≤ bD.factorization p :=
          (Nat.factorization_le_iff_dvd hD_pos hbD_ne).mpr hDbD p
        have hsingle : bD.factorization p ≤ ∑ b ∈ B₁, b.factorization p :=
          Finset.single_le_sum (f := fun b => b.factorization p) (fun _ _ => Nat.zero_le _) hbD_B1
        exact le_trans hD_le (Nat.add_le_add_left (le_trans hfac_D hsingle) _)

private lemma exists_merge_coprime_aux {R : ℕ → ℕ → Prop} [DecidableRel R] :
    ∀ (xs : List ℕ), xs.Pairwise Nat.Coprime → ¬ xs.Pairwise R →
      ∃ (u v : ℕ) (rest : List ℕ),
        ¬ R u v ∧ rest.length + 2 = xs.length ∧
        (u * v) * rest.prod = xs.prod ∧
        (∀ x ∈ rest, x ∈ xs) ∧ u ∈ xs ∧ v ∈ xs ∧
        (u * v :: rest).Pairwise Nat.Coprime
  | [], _, h => absurd List.Pairwise.nil h
  | a :: tail, hcop, h => by
    rw [List.pairwise_cons] at h hcop
    by_cases h1 : ∀ b ∈ tail, R a b
    · have htail : ¬ tail.Pairwise R := fun ht => h ⟨h1, ht⟩
      obtain ⟨u, v, rest, hnotR, hlen, hprod, hmem, hu, hv, hrest_cop⟩ :=
        exists_merge_coprime_aux tail hcop.2 htail
      rw [List.pairwise_cons] at hrest_cop
      refine ⟨u, v, a :: rest, hnotR, by simp [hlen], ?_, ?_,
        List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv, ?_⟩
      · simp only [List.prod_cons]; rw [← hprod]; ring
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (hmem x hx')
      · rw [List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact (Nat.Coprime.mul_right (hcop.1 u hu) (hcop.1 v hv)).symm
          · exact hrest_cop.1 x hx'
        · rw [List.pairwise_cons]
          exact ⟨fun x hx => hcop.1 x (hmem x hx), hrest_cop.2⟩
    · push Not at h1
      obtain ⟨b, hb_mem, hnotR⟩ := h1
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb_mem
      have hcop_l12 : (l₁ ++ l₂).Pairwise Nat.Coprime := by
        have hsub := hcop.2
        rw [List.pairwise_append] at hsub
        rw [List.pairwise_append]
        have hsub2 := hsub.2.1
        rw [List.pairwise_cons] at hsub2
        refine ⟨hsub.1, hsub2.2, ?_⟩
        intro x hx y hy
        exact hsub.2.2 x hx y (List.mem_cons_of_mem b hy)
      have ha_l12 : ∀ x ∈ l₁ ++ l₂, Nat.Coprime a x := fun x hx => by
        apply hcop.1 x
        rcases List.mem_append.mp hx with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_cons_of_mem b h2)
      have hb_l12 : ∀ x ∈ l₁ ++ l₂, Nat.Coprime b x := fun x hx => by
        have hsub := hcop.2
        rw [List.pairwise_append] at hsub
        rcases List.mem_append.mp hx with h1 | h2
        · exact (hsub.2.2 x h1 b List.mem_cons_self).symm
        · have hsub2 := hsub.2.1
          rw [List.pairwise_cons] at hsub2
          exact hsub2.1 x h2
      refine ⟨a, b, l₁ ++ l₂, hnotR, by simp; omega, ?_, ?_, List.mem_cons_self, ?_, ?_⟩
      · simp only [List.prod_cons, List.prod_append]; ring
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact List.mem_cons_of_mem a (List.mem_append_left _ hx1)
        · exact List.mem_cons_of_mem a (List.mem_append_right _ (List.mem_cons_of_mem b hx2))
      · exact List.mem_cons_of_mem a (List.mem_append_right _ List.mem_cons_self)
      · rw [List.pairwise_cons]
        exact ⟨fun x hx => Nat.Coprime.mul_left (ha_l12 x hx) (hb_l12 x hx), hcop_l12⟩

/-- Multiplicative bin-packing preserving `Pairwise Nat.Coprime`. -/
lemma list_bin_pack_coprime (L : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), xs.length = n → (∀ x ∈ xs, 1 ≤ x ∧ x ≤ L) →
      xs.Pairwise Nat.Coprime →
      ∃ bs : List ℕ,
        (∀ u ∈ bs, 1 ≤ u ∧ u ≤ L) ∧
        bs.prod = xs.prod ∧
        bs.Pairwise (fun u v => L < u * v) ∧
        bs.Pairwise Nat.Coprime := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hlen hxs hcop
    by_cases hpw : xs.Pairwise (fun u v => L < u * v)
    · exact ⟨xs, hxs, rfl, hpw, hcop⟩
    · obtain ⟨u, v, rest, hnotgt, hrest_len, hprod, hmem, _hu, _hv, hnext_cop⟩ :=
        exists_merge_coprime_aux xs hcop hpw
      have huv_le : u * v ≤ L := Nat.le_of_not_lt hnotgt
      have huv_ge : 1 ≤ u * v := Nat.mul_pos (hxs u _hu).1 (hxs v _hv).1
      let xs' := (u * v) :: rest
      have hlen' : xs'.length < n := by
        simp only [xs', List.length_cons]
        omega
      have hxs' : ∀ x ∈ xs', 1 ≤ x ∧ x ≤ L := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨huv_ge, huv_le⟩
        · exact hxs x (hmem x hx')
      obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw, hbs_cop⟩ := ih xs'.length hlen' xs' rfl hxs' hnext_cop
      refine ⟨bs, hbs_bnd, ?_, hbs_pw, hbs_cop⟩
      rw [hbs_prod]
      simpa [xs'] using hprod

private lemma list_prod_ne_zero : ∀ (bs : List ℕ), (∀ D ∈ bs, 1 ≤ D) → bs.prod ≠ 0
  | [], _ => by simp
  | D :: ds, h => by
    rw [List.prod_cons]
    have hD : D ≠ 0 := by have := h D List.mem_cons_self; omega
    have hds : ds.prod ≠ 0 := list_prod_ne_zero ds (fun x hx => h x (List.mem_cons_of_mem D hx))
    exact mul_ne_zero hD hds

private lemma prod_factorization_eq_zero_of_coprime {p : ℕ} (hp : p.Prime) (D : ℕ) (hDp : p ∣ D) :
    ∀ (ds : List ℕ), (∀ x ∈ ds, 1 ≤ x) → (∀ x ∈ ds, Nat.Coprime D x) → ds.prod.factorization p = 0
  | [], _, _ => by simp
  | x :: xs, hx1, hcop => by
    rw [List.prod_cons]
    have hx_ne : x ≠ 0 := by have := hx1 x List.mem_cons_self; omega
    have hxs_ne : xs.prod ≠ 0 := list_prod_ne_zero xs (fun y hy => hx1 y (List.mem_cons_of_mem x hy))
    rw [Nat.factorization_mul hx_ne hxs_ne, Finsupp.add_apply]
    have hx_ndvd : ¬ (p ∣ x) := by
      intro hpx
      have hcop_Dx := hcop x List.mem_cons_self
      have hp_dvd1 : p ∣ Nat.gcd D x := Nat.dvd_gcd hDp hpx
      rw [hcop_Dx.gcd_eq_one] at hp_dvd1
      exact hp.not_dvd_one hp_dvd1
    have hx0 : x.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hx_ndvd
    have hxs0 : xs.prod.factorization p = 0 :=
      prod_factorization_eq_zero_of_coprime hp D hDp xs
        (fun y hy => hx1 y (List.mem_cons_of_mem x hy))
        (fun y hy => hcop y (List.mem_cons_of_mem x hy))
    omega

/-- In a pairwise coprime list `bs` of positive naturals, any prime dividing `bs.prod` has its entire
    valuation concentrated in a single bin `D ∈ bs`. -/
lemma exists_factor_dvd_of_pairwise_coprime {p : ℕ} (hp : p.Prime) :
    ∀ (bs : List ℕ), (∀ D ∈ bs, 1 ≤ D) → bs.Pairwise Nat.Coprime → 0 < bs.prod.factorization p →
      ∃ D ∈ bs, bs.prod.factorization p = D.factorization p
  | [], _, _, h => by simp at h
  | D :: ds, hpos, hcop, h => by
    rw [List.pairwise_cons] at hcop
    have hD_ne : D ≠ 0 := by have := hpos D List.mem_cons_self; omega
    have hds_pos : ∀ x ∈ ds, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem D hx)
    have hds_ne : ds.prod ≠ 0 := list_prod_ne_zero ds hds_pos
    rw [List.prod_cons, Nat.factorization_mul hD_ne hds_ne, Finsupp.add_apply] at h ⊢
    by_cases hDp : p ∣ D
    · have hds0 := prod_factorization_eq_zero_of_coprime hp D hDp ds hds_pos hcop.1
      exact ⟨D, List.mem_cons_self, by omega⟩
    · have hD0 : D.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hDp
      rw [hD0, zero_add] at h ⊢
      obtain ⟨D', hD'ds, hD'eq⟩ := exists_factor_dvd_of_pairwise_coprime hp ds hds_pos hcop.2 h
      exact ⟨D', List.mem_cons_of_mem D hD'ds, hD'eq⟩

/-- End-to-end Top-`c_p` + Multiplicative Bin-Packing Theorem:
    any pairwise coprime list `qs` of prime powers in `[1, L]` (`(B₀.card + 1) * L ≤ M`)
    packs into `bs` (`(L + 1) ^ bs.length ≤ bs.prod ^ 2` when `bs.length ≥ 2`) and realizes
    a cover `B ⊆ consecInterval x M` with `B.card ≤ B₀.card + (∑ p ∈ P_multi, (T p).card) + bs.length`. -/
theorem exists_bins_from_list_bin_pack {A B₀ P_multi : Finset ℕ} {x M L : ℕ}
    (T : ℕ → Finset ℕ) (qs : List ℕ)
    (hA0 : ∀ a ∈ A, a ≠ 0)
    (hB0_I : B₀ ⊆ consecInterval x M)
    (hT_sub : ∀ p ∈ P_multi, T p ⊆ consecInterval x M ∧ Disjoint B₀ (T p))
    (hT_val : ∀ p ∈ P_multi,
      ∑ a ∈ A, a.factorization p ≤
        ∑ b ∈ B₀, b.factorization p + ∑ b ∈ T p, b.factorization p)
    (hqs_bnd : ∀ q ∈ qs, 1 ≤ q ∧ q ≤ L)
    (hqs_cop : qs.Pairwise Nat.Coprime)
    (hLM : (B₀.card + 1) * L ≤ M)
    (hother : ∀ p : ℕ, p.Prime → p ∉ P_multi →
      ∑ a ∈ A, a.factorization p ≤ ∑ b ∈ B₀, b.factorization p + qs.prod.factorization p) :
    ∃ bs : List ℕ,
      (bs.length ≥ 2 → (L + 1) ^ bs.length ≤ bs.prod ^ 2) ∧
      ∃ B ⊆ consecInterval x M,
        B.card ≤ B₀.card + (∑ p ∈ P_multi, (T p).card) + bs.length ∧ IsCover A B := by
  obtain ⟨bs, hbs_bnd, hbs_prod, hbs_pw, hbs_cop⟩ :=
    list_bin_pack_coprime L qs.length qs rfl hqs_bnd hqs_cop
  refine ⟨bs, fun hlen => pairwise_mul_gt_pow_le_sq L bs.length bs rfl hlen hbs_pw, ?_⟩
  apply exists_cover_of_seed_topC_and_coprime_bins T bs hA0 hB0_I hT_sub hT_val
  · intro D hD
    have hDbnd := hbs_bnd D hD
    refine ⟨hDbnd.1, Or.inl (le_trans (Nat.mul_le_mul_left _ hDbnd.2) hLM)⟩
  · intro p hp hpM
    have hq := hother p hp hpM
    by_cases hpos_p : 0 < qs.prod.factorization p
    · rw [← hbs_prod] at hpos_p hq
      obtain ⟨D, hD_mem, hD_eq⟩ :=
        exists_factor_dvd_of_pairwise_coprime hp bs (fun x hx => (hbs_bnd x hx).1) hbs_cop hpos_p
      refine Or.inr ⟨D, hD_mem, ?_⟩
      rwa [← hD_eq]
    · have h0 : qs.prod.factorization p = 0 := by omega
      rw [h0, add_zero] at hq
      exact Or.inl hq

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms coprime_packing_slot_of_mul_le
#print axioms coprime_packing_slot_of_not_dvd
#print axioms isCover_union_of_disjoint_factorization
#print axioms exists_cover_of_seed_topC_and_coprime_bins
#print axioms list_bin_pack_coprime
#print axioms exists_factor_dvd_of_pairwise_coprime
#print axioms exists_bins_from_list_bin_pack

end Erdos708
