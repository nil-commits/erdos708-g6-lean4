import Erdos708.G3AndG6Lower

/-!
# PPL 176 (Erdős Problem #708) — Matching Defect-1 Telescoping GCD Chain & Unique-Multiple Bound

This module develops the matching-based upper-bound machinery for **Erdős Problem #708**
building on `Erdos708.G3AndG6Lower`:
1. `card_mul_le_of_forall_dvd`: if every element of `T` lies in `[1, M]` and is divisible by `d > 0`,
   then `T.card * d ≤ M`.
2. `exists_avoiding_multiple_in_consecInterval`: if `(S.card + 1) * d ≤ M`, there exists a multiple
   of `d` in `consecInterval x M \ S`.
3. `exists_cover_add_one_of_matching` & `erdos708_upper_n_of_matching_pred`:
   **Telescoping GCD Chain Lemma** — for ANY `n ≥ 1`, if a set `A` (`|A| = n`, `A ⊆ [1, M]`)
   admits a matching `f : S ↪ consecInterval x M` of size `n - 1` (`a ∣ f a`), then `A` has an
   unconditional cover `B ⊆ consecInterval x M` of size **`|B| ≤ n`**.
4. `erdos708_upper_six_of_matching_five`: immediate `n = 6, r = 5` specialization (`|B| ≤ 6 ≤ 8`),
   closing 100% of the Hall defect-1 branch for `g(6) ≤ 8`.
5. `lt_two_mul_of_unique_multiple_in_consecInterval`: if `a > 0` has a unique multiple in
   `consecInterval x M`, then `M < 2 * a` (half-interval barrier for the `r = 1` branch).
-/

open scoped BigOperators Nat

namespace Erdos708

/-- If every `a ∈ T` satisfies `0 < a ≤ M` and `d ∣ a` (`0 < d`), then `T.card * d ≤ M`. -/
lemma card_mul_le_of_forall_dvd {T : Finset ℕ} {d M : ℕ} (hd : 0 < d)
    (hT : ∀ a ∈ T, 0 < a ∧ a ≤ M ∧ d ∣ a) :
    T.card * d ≤ M := by
  have himg : T.image (· / d) ⊆ Finset.Icc 1 (M / d) := by
    intro q hq
    obtain ⟨a, haT, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha0, haM, hda⟩ := hT a haT
    rw [Finset.mem_Icc]
    have hdle : d ≤ a := Nat.le_of_dvd ha0 hda
    exact ⟨(Nat.le_div_iff_mul_le hd).mpr (by simpa using hdle), Nat.div_le_div_right haM⟩
  have hinj : Set.InjOn (· / d) T := by
    intro a ha b hb hab
    dsimp only at hab
    have hda := (hT a ha).2.2
    have hdb := (hT b hb).2.2
    calc a = d * (a / d) := (Nat.mul_div_cancel' hda).symm
      _ = d * (b / d) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hdb
  have hcard_icc : (Finset.Icc 1 (M / d)).card = M / d := by
    simp [Nat.card_Icc]
  have hcard_le : T.card ≤ M / d := by
    calc T.card = (T.image (· / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (M / d)).card := Finset.card_le_card himg
      _ = M / d := hcard_icc
  exact (Nat.le_div_iff_mul_le hd).mp hcard_le

/-- If `(S.card + 1) * d ≤ M` (`0 < d`), there exists `b ∈ consecInterval x M` with `b ∉ S` and `d ∣ b`. -/
lemma exists_avoiding_multiple_in_consecInterval (x M d : ℕ) (S : Finset ℕ)
    (hd : 0 < d) (hbound : (S.card + 1) * d ≤ M) :
    ∃ b ∈ consecInterval x M, b ∉ S ∧ d ∣ b := by
  have hle_div : S.card + 1 ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr hbound
  have hcard_flt := card_multiples_Icc_ge x M d hd
  change M / d ≤ ((consecInterval x M).filter (fun b => d ∣ b)).card at hcard_flt
  have hnot_sub : ¬ ((consecInterval x M).filter (fun b => d ∣ b) ⊆ S) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨b, hb_mem, hb_notS⟩ := Finset.not_subset.mp hnot_sub
  rw [Finset.mem_filter] at hb_mem
  exact ⟨b, hb_mem.1, hb_notS, hb_mem.2⟩

private lemma prod_dvd_prod_of_forall_dvd {S : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ a ∈ S, a ∣ f a) :
    (∏ a ∈ S, a) ∣ ∏ a ∈ S, f a := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    exact mul_dvd_mul (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Inductive telescoping GCD chain absorption step:
    maintaining `d` dividing `u` and every `a ∈ V ⊆ S`, either finds an unused multiple
    `w ∈ consecInterval x M \ S.image f` of `d`, or absorbs another matched element `a₀ ∈ S \ V`
    with `d' = Nat.gcd d a₀` until exiting `S.image f`. -/
private lemma exists_chain_exit (S : Finset ℕ) (u x M : ℕ) (f : ℕ → ℕ)
    (hS_pos : ∀ a ∈ S, 0 < a) (hS_le : ∀ a ∈ S, a ≤ M)
    (hu_pos : 0 < u) (hu_le : u ≤ M) (hu_notS : u ∉ S)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) :
    ∀ (k : ℕ) (V : Finset ℕ) (d : ℕ),
      V ⊆ S → (S \ V).card = k → 0 < d → d ∣ u → (∀ a ∈ V, d ∣ a) →
      ∃ w ∈ consecInterval x M, w ∉ S.image f ∧
        d * (∏ a ∈ S \ V, a) ∣ w * (∏ a ∈ S \ V, f a) := by
  intro k
  induction k with
  | zero =>
    intro V d hVS hcard hd_pos hdu hdV
    have hsdiff_empty : S \ V = ∅ := Finset.card_eq_zero.mp hcard
    have hV_eq_S : V = S := Finset.Subset.antisymm hVS (Finset.sdiff_eq_empty_iff_subset.mp hsdiff_empty)
    have hT_all : ∀ a ∈ insert u V, 0 < a ∧ a ≤ M ∧ d ∣ a := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haV
      · exact ⟨hu_pos, hu_le, hdu⟩
      · exact ⟨hS_pos a (hVS haV), hS_le a (hVS haV), hdV a haV⟩
    have hu_notV : u ∉ V := fun h => hu_notS (hVS h)
    have hcard_ins : (insert u V).card = V.card + 1 := Finset.card_insert_of_notMem hu_notV
    have hM_bound : ((V.image f).card + 1) * d ≤ M := by
      have h1 : (V.image f).card ≤ V.card := Finset.card_image_le
      have h2 := card_mul_le_of_forall_dvd hd_pos hT_all
      rw [hcard_ins] at h2
      exact le_trans (Nat.mul_le_mul_right d (Nat.add_le_add_right h1 1)) h2
    obtain ⟨w, hw_mem, hw_notV, hd_w⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d (V.image f) hd_pos hM_bound
    rw [hV_eq_S] at hw_notV
    refine ⟨w, hw_mem, hw_notV, ?_⟩
    rw [hsdiff_empty]
    simpa using hd_w
  | succ k' ih =>
    intro V d hVS hcard hd_pos hdu hdV
    have hT_all : ∀ a ∈ insert u V, 0 < a ∧ a ≤ M ∧ d ∣ a := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haV
      · exact ⟨hu_pos, hu_le, hdu⟩
      · exact ⟨hS_pos a (hVS haV), hS_le a (hVS haV), hdV a haV⟩
    have hu_notV : u ∉ V := fun h => hu_notS (hVS h)
    have hcard_ins : (insert u V).card = V.card + 1 := Finset.card_insert_of_notMem hu_notV
    have hM_bound : ((V.image f).card + 1) * d ≤ M := by
      have h1 : (V.image f).card ≤ V.card := Finset.card_image_le
      have h2 := card_mul_le_of_forall_dvd hd_pos hT_all
      rw [hcard_ins] at h2
      exact le_trans (Nat.mul_le_mul_right d (Nat.add_le_add_right h1 1)) h2
    obtain ⟨b, hb_mem, hb_notV, hd_b⟩ :=
      exists_avoiding_multiple_in_consecInterval x M d (V.image f) hd_pos hM_bound
    by_cases hb_inS : b ∈ S.image f
    · obtain ⟨a₀, ha₀S, ha₀_eq⟩ := Finset.mem_image.mp hb_inS
      have ha₀_notV : a₀ ∉ V := fun h => hb_notV (Finset.mem_image.mpr ⟨a₀, h, ha₀_eq⟩)
      have ha₀_sdiff : a₀ ∈ S \ V := Finset.mem_sdiff.mpr ⟨ha₀S, ha₀_notV⟩
      set V' : Finset ℕ := insert a₀ V
      have hV'S : V' ⊆ S := Finset.insert_subset_iff.mpr ⟨ha₀S, hVS⟩
      have hsdiff_eq : S \ V' = (S \ V).erase a₀ := by
        ext a
        simp [V', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      have hcard' : (S \ V').card = k' := by
        rw [hsdiff_eq, Finset.card_erase_of_mem ha₀_sdiff, hcard]
        omega
      set d' : ℕ := Nat.gcd d a₀
      have hd'_pos : 0 < d' := Nat.gcd_pos_of_pos_right d (hS_pos a₀ ha₀S)
      have hd'_u : d' ∣ u := dvd_trans (Nat.gcd_dvd_left d a₀) hdu
      have hd'V' : ∀ a ∈ V', d' ∣ a := by
        intro a ha
        rcases Finset.mem_insert.mp ha with h_eq | haV
        · rw [h_eq]; exact Nat.gcd_dvd_right d a₀
        · exact dvd_trans (Nat.gcd_dvd_left d a₀) (hdV a haV)
      obtain ⟨w, hw_mem, hw_notS, hdvd_ih⟩ := ih V' d' hV'S hcard' hd'_pos hd'_u hd'V'
      refine ⟨w, hw_mem, hw_notS, ?_⟩
      have ha₀_not_rem : a₀ ∉ S \ V' := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self a₀ V)
      have hsplit_sdiff : S \ V = insert a₀ (S \ V') := by
        rw [hsdiff_eq, Finset.insert_erase ha₀_sdiff]
      have hprodA : ∏ a ∈ S \ V, a = a₀ * ∏ a ∈ S \ V', a := by
        rw [hsplit_sdiff, Finset.prod_insert ha₀_not_rem]
      have hprodF : ∏ a ∈ S \ V, f a = b * ∏ a ∈ S \ V', f a := by
        rw [hsplit_sdiff, Finset.prod_insert ha₀_not_rem, ha₀_eq]
      have hlcm_dvd : Nat.lcm d a₀ ∣ b := Nat.lcm_dvd hd_b (ha₀_eq ▸ hf_dvd a₀ ha₀S)
      have hlg : Nat.lcm d a₀ * d' = d * a₀ := Nat.lcm_mul_gcd d a₀
      rw [hprodA, hprodF]
      calc d * (a₀ * ∏ a ∈ S \ V', a)
          = (d * a₀) * ∏ a ∈ S \ V', a := by ring
        _ = (Nat.lcm d a₀ * d') * ∏ a ∈ S \ V', a := by rw [← hlg]
        _ = Nat.lcm d a₀ * (d' * ∏ a ∈ S \ V', a) := by ring
        _ ∣ b * (w * ∏ a ∈ S \ V', f a) := mul_dvd_mul hlcm_dvd hdvd_ih
        _ = w * (b * ∏ a ∈ S \ V', f a) := by ring
    · refine ⟨b, hb_mem, hb_inS, ?_⟩
      apply mul_dvd_mul hd_b
      exact prod_dvd_prod_of_forall_dvd (fun a ha => hf_dvd a (Finset.sdiff_subset ha))

/-- Adding one unmatched element `u ≤ M` to a matched set `S` (`f : S ↪ consecInterval x M`)
    increases the required cover size by at most `1` (`|B| ≤ S.card + 1`). -/
theorem exists_cover_add_one_of_matching {S : Finset ℕ} {u x M : ℕ} {f : ℕ → ℕ}
    (hS_pos : ∀ a ∈ S, 0 < a) (hS_le : ∀ a ∈ S, a ≤ M)
    (hu_pos : 0 < u) (hu_le : u ≤ M) (hu_notS : u ∉ S)
    (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ B ⊆ consecInterval x M, B.card ≤ S.card + 1 ∧ IsCover (insert u S) B := by
  obtain ⟨w, hw_mem, hw_notImg, hdvd⟩ :=
    exists_chain_exit S u x M f hS_pos hS_le hu_pos hu_le hu_notS hf_dvd
      S.card ∅ u (Finset.empty_subset S) (by simp) hu_pos (dvd_refl u) (fun _ ha => by simp at ha)
  rw [Finset.sdiff_empty] at hdvd
  refine ⟨insert w (S.image f), ?_, ?_, ?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨hw_mem, Finset.image_subset_iff.mpr hf_mem⟩
  · exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right Finset.card_image_le 1)
  · rw [IsCover, Finset.prod_insert hu_notS, Finset.prod_insert hw_notImg, Finset.prod_image hf_inj]
    exact hdvd

/-- Adding one unmatched element `u ≤ M` to a matched set `S` produces a specific witness
    `w ∈ consecInterval x M \ S.image f` such that `insert w (S.image f)` covers `insert u S`. -/
theorem exists_witness_add_one_of_matching {S : Finset ℕ} {u x M : ℕ} {f : ℕ → ℕ}
    (hS_pos : ∀ a ∈ S, 0 < a) (hS_le : ∀ a ∈ S, a ≤ M)
    (hu_pos : 0 < u) (hu_le : u ≤ M) (hu_notS : u ∉ S)
    (_hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ w ∈ consecInterval x M, w ∉ S.image f ∧ IsCover (insert u S) (insert w (S.image f)) := by
  obtain ⟨w, hw_mem, hw_notImg, hdvd⟩ :=
    exists_chain_exit S u x M f hS_pos hS_le hu_pos hu_le hu_notS hf_dvd
      S.card ∅ u (Finset.empty_subset S) (by simp) hu_pos (dvd_refl u) (fun _ ha => by simp at ha)
  rw [Finset.sdiff_empty] at hdvd
  refine ⟨w, hw_mem, hw_notImg, ?_⟩
  rw [IsCover, Finset.prod_insert hu_notS, Finset.prod_insert hw_notImg, Finset.prod_image hf_inj]
  exact hdvd

/-- General matching defect-1 theorem: for any `n ≥ 1` and valid `A` (`|A| = n`, `A ⊆ [1, M]`),
    a bipartite matching `S ⊆ A` of size `n - 1` into `consecInterval x M` guarantees an
    unconditional cover `B ⊆ consecInterval x M` with `|B| ≤ n`. -/
theorem erdos708_upper_n_of_matching_pred {n : ℕ} (hn : 1 ≤ n)
    {A S : Finset ℕ} {x M : ℕ} (hA_card : A.card = n) (hA_pos : ∀ a ∈ A, 0 < a)
    (hA_le : ∀ a ∈ A, a ≤ M) (hSA : S ⊆ A) (hS_card : S.card = n - 1)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ B ⊆ consecInterval x M, B.card ≤ n ∧ IsCover A B := by
  have hcard_sum : (A \ S).card + S.card = A.card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left, Finset.sdiff_union_of_subset hSA]
  have hsdiff_one : (A \ S).card = 1 := by omega
  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hsdiff_one
  have hu_sdiff : u ∈ A \ S := by rw [hu_eq]; exact Finset.mem_singleton_self u
  have hu_A : u ∈ A := (Finset.mem_sdiff.mp hu_sdiff).1
  have hu_notS : u ∉ S := (Finset.mem_sdiff.mp hu_sdiff).2
  have hA_eq : A = insert u S := by
    rw [← Finset.sdiff_union_of_subset hSA, hu_eq, Finset.singleton_union]
  obtain ⟨B, hBI, hBc, hcov⟩ := exists_cover_add_one_of_matching
    (fun a ha => hA_pos a (hSA ha)) (fun a ha => hA_le a (hSA ha))
    (hA_pos u hu_A) (hA_le u hu_A) hu_notS hf_mem hf_dvd hf_inj
  refine ⟨B, hBI, by omega, ?_⟩
  rwa [hA_eq]

/-- Hall defect-1 branch for `g(6) ≤ 8`: any 6-element set admitting a matching of size `5`
    into `consecInterval x M` has an unconditional cover of size `≤ 6` (hence `≤ 8`). -/
theorem erdos708_upper_six_of_matching_five {A S : Finset ℕ} {x M : ℕ}
    (hA_card : A.card = 6) (hA_pos : ∀ a ∈ A, 0 < a) (hA_le : ∀ a ∈ A, a ≤ M)
    (hSA : S ⊆ A) (hS_card : S.card = 5)
    (f : ℕ → ℕ) (hf_mem : ∀ a ∈ S, f a ∈ consecInterval x M)
    (hf_dvd : ∀ a ∈ S, a ∣ f a) (hf_inj : Set.InjOn f S) :
    ∃ B ⊆ consecInterval x M, B.card ≤ 6 ∧ IsCover A B :=
  erdos708_upper_n_of_matching_pred (by omega) hA_card hA_pos hA_le hSA hS_card f hf_mem hf_dvd hf_inj

/-- Foundation for the `r = 1` branch: if `a > 0` has a unique multiple `b₀` in
    `consecInterval x M`, then `M < 2 * a`. -/
theorem lt_two_mul_of_unique_multiple_in_consecInterval {x M a b₀ : ℕ}
    (ha : 0 < a) (hb₀ : b₀ ∈ consecInterval x M) (hdvd : a ∣ b₀)
    (huniq : ∀ b ∈ consecInterval x M, a ∣ b → b = b₀) :
    M < 2 * a := by
  by_contra hle
  have h2a : 2 * a ≤ M := Nat.le_of_not_lt hle
  obtain ⟨b₂, hb₂_mem, hb₂_ne, hb₂_dvd⟩ :=
    exists_second_multiple_in_consecInterval ha h2a hb₀ hdvd
  exact hb₂_ne (huniq b₂ hb₂_mem hb₂_dvd)

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms card_mul_le_of_forall_dvd
#print axioms exists_cover_add_one_of_matching
#print axioms exists_witness_add_one_of_matching
#print axioms erdos708_upper_n_of_matching_pred
#print axioms erdos708_upper_six_of_matching_five
#print axioms lt_two_mul_of_unique_multiple_in_consecInterval

end Erdos708
