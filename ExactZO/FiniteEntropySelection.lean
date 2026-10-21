import ExactZO.QuantizedSigns
import ExactZO.SelectionGeometry
import ExactZO.StageGeometry

/-! The finite entropy direction selection lemma, with no selection premise.
The geometric Gibbs reference in `QuantizedSigns` is a proof variant of the
paper's quadratic reference; both give the same `6δ` entropy budget. -/

noncomputable section
open scoped BigOperators InnerProductSpace
open Finset

namespace ExactZO.FiniteEntropySelection
open QuantizedSigns SelectionHamming SelectionGeometry

set_option maxHeartbeats 1000000 in
/-- Quantizing every linear form gives a common fiber containing far signs. -/
theorem exists_quantized_far_pair {p M : ℕ} (hp : 0 < p)
    (a : Fin M → Fin p → ℝ) (ha : ∀ i, ∑ j, a i j ^ 2 ≤ 1) :
    ∃ x y : SignCube p,
      (p : ℝ) / 4 < (hammingDist x y : ℝ) ∧
      ∀ i, |signSum (a i) x - signSum (a i) y| <
        4 * Real.sqrt (Real.log (128 * max 1 ((M : ℝ) / p))) := by
  classical
  let s : ℝ := max 1 ((M : ℝ) / p)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hbase : 0 < 128 * s := by positivity
  have hlog : 0 < Real.log (128 * s) := Real.log_pos (by nlinarith)
  let t : ℝ := 2 * Real.sqrt (Real.log (128 * s))
  have ht : 0 < t := mul_pos (by norm_num) (Real.sqrt_pos.mpr hlog)
  have ht2 : t ^ 2 / 4 = Real.log (128 * s) := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hlog.le]
  let δ : ℝ := Real.exp (-(t ^ 2 / 4))
  have hδ : δ = 1 / (128 * s) := by
    dsimp [δ]
    rw [ht2, Real.exp_neg, Real.exp_log hbase, one_div]
  have hδsmall : Real.exp (-(t ^ 2 / 4)) ≤ 1 / 2 := by
    change δ ≤ 1 / 2
    rw [hδ]
    exact (div_le_iff₀ hbase).mpr (by nlinarith)
  have hratio : (M : ℝ) ≤ (p : ℝ) * s := by
    have hh : (M : ℝ) / p ≤ s := le_max_right _ _
    exact (div_le_iff₀ hpR).mp hh |>.trans_eq (mul_comm _ _)
  have hbudget : 6 * (M : ℝ) * δ < (p : ℝ) * Real.log 2 / 8 := by
    have hbound : 6 * (M : ℝ) * δ ≤ 3 * (p : ℝ) / 64 := by
      rw [hδ]
      apply (mul_le_mul_iff_of_pos_right hbase).mp
      have hc : (1 / (128 * s)) * (128 * s) = (1 : ℝ) := by field_simp
      calc
        _ = 6 * (M : ℝ) := by rw [mul_assoc, hc, mul_one]
        _ ≤ (3 * (p : ℝ) / 64) * (128 * s) := by nlinarith
    have hh := mul_lt_mul_of_pos_left Real.log_two_gt_d9 hpR
    nlinarith
  let N : ℕ := univ.sup (fun z : Fin M × SignCube p => (quantize t (signSum (a z.1) z.2)).natAbs)
  have hN : ∀ i x, (quantize t (signSum (a i) x)).natAbs ≤ N := by
    intro i x
    exact Finset.le_sup (f := fun z : Fin M × SignCube p =>
      (quantize t (signSum (a z.1) z.2)).natAbs) (mem_univ (i, x))
  let f : SignCube p → Fin M → Option (Bool × Fin N) := fun x i =>
    boundedCode (quantize t (signSum (a i) x)) (hN i x)
  let q : Fin M → Option (Bool × Fin N) → ℝ := fun _ => refMass (t ^ 2 / 2)
  have hq : ∀ i y, 0 < q i y := fun _ y => refMass_pos _ y
  have hq1 : ∀ i, ∑ y, q i y ≤ 1 := by
    intro i
    apply refMass_sum_le_one
    convert hδsmall using 1
    congr 1
    ring
  have hcost : ∀ i, (∑ x, -Real.log (q i (f x i))) / Fintype.card (SignCube p) ≤ 6 * δ := by
    intro i
    exact quantize_reference_cost (signSum (a i)) (fun lmb => sign_mgf (a i) lmb (ha i))
      ht hδsmall N (hN i)
  obtain ⟨b, hb⟩ := SelectionEntropy.exists_large_fiber_product_reference f q hq hq1
    (fun _ => 6 * δ) hcost
  have hsum : (∑ _ : Fin M, 6 * δ) = 6 * (M : ℝ) * δ := by simp; ring
  rw [hsum] at hb
  have hcube : (Fintype.card (SignCube p) : ℝ) = Real.exp ((p : ℝ) * Real.log 2) := by
    simp only [SignCube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlarge : Real.exp ((7 / 8 : ℝ) * p * Real.log 2) <
      ((univ.filter fun x => f x = b).card : ℝ) := by
    apply lt_of_lt_of_le _ hb
    rw [hcube, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨x, hx, y, hy, hfar⟩ := exists_far_pair hp _ hlarge
  refine ⟨x, y, hfar, ?_⟩
  intro i
  have hxy : f x i = f y i := congrFun ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) i
  have hbin : quantize t (signSum (a i) x) = quantize t (signSum (a i) y) := by
    have hh := congrArg decodeCode hxy
    simpa only [f, decode_boundedCode] using hh
  have hh := quantize_same_bin ht hbin
  change _ < 4 * Real.sqrt (Real.log (128 * s))
  dsimp [t] at hh
  linarith

/-- The sign sum is the usual Euclidean inner product. -/
theorem signSum_eq_inner {p : ℕ} (a : X p) (x : SignCube p) :
    signSum a x = ⟪a, signVector x⟫_ℝ := by
  simp [signSum, signVector, sign, PiLp.inner_apply, mul_comm]

/-- Exact dimension version of the manuscript's selection lemma. -/
theorem direction_selection {d M : ℕ} (S : Submodule ℝ (X d))
    (a : Fin M → X d) {R : ℝ} (hR : 0 ≤ R)
    (ha : ∀ i, ‖a i‖ ≤ R) (hp : 0 < Module.finrank ℝ S) :
    ∃ u : X d, ‖u‖ = 1 ∧ u ∈ S ∧ ∀ i,
      |⟪u, a i⟫_ℝ| ≤ 9 * R * Real.sqrt
        (Real.log (Real.exp 1 + (M : ℝ) / Module.finrank ℝ S) / Module.finrank ℝ S) := by
  by_cases hzero : R = 0
  · obtain ⟨u, hu, hmem⟩ := exists_unit_mem S hp
    refine ⟨u, hu, hmem, ?_⟩
    intro i
    have hz : a i = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hzero] using ha i) (norm_nonneg _))
    simp [hz, hzero]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
  let b : Fin M → X (Module.finrank ℝ S) := fun i => R⁻¹ • coordinates S (a i)
  have hb : ∀ i, ‖b i‖ ≤ 1 := by
    intro i
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hRpos).mpr ((coordinates_norm_le S (a i)).trans (ha i))
  have hbsq : ∀ i, ∑ j, b i j ^ 2 ≤ 1 := by
    intro i
    have hh : ‖b i‖ ^ 2 ≤ 1 := by nlinarith [hb i, norm_nonneg (b i)]
    simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hh
  obtain ⟨x, y, hfar, hclose⟩ := exists_quantized_far_pair hp (fun i j => b i j) hbsq
  apply normalize_in_subspace S a hR hp (signVector x - signVector y)
    (signVector_sub_norm_gt_sqrt x y hfar)
  intro i
  have heq : coordinates S (a i) = R • b i := by
    dsimp [b]
    rw [smul_smul, mul_inv_cancel₀ hzero, one_smul]
  rw [heq, real_inner_smul_left, inner_sub_right,
    ← signSum_eq_inner, ← signSum_eq_inner, abs_mul, abs_of_pos hRpos]
  have hh := mul_lt_mul_of_pos_left (hclose i) hRpos
  nlinarith only [hh]

/-- A smaller dimension bound and larger query bound preserve selection. -/
theorem unconditionalStripSelector {d p Q : ℕ} {R τ : ℝ}
    (hp : 0 < p) (hR : 0 ≤ R)
    (hbound : 9 * R * Real.sqrt (Real.log (Real.exp 1 + (Q : ℝ) / p) / p) ≤ τ) :
    StageGeometry.StripSelector (d := d) R τ p Q := by
  intro S hdim points hlength hnorm
  have hs : 0 < Module.finrank ℝ S := hp.trans_le hdim
  obtain ⟨u, hu, hmem, hsmall⟩ := direction_selection S points.get hR
    (fun i => hnorm _ (List.get_mem _ _)) hs
  refine ⟨u, hu, hmem, ?_⟩
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  rw [← hi]
  apply (hsmall i).trans
  apply le_trans _ hbound
  exact selection_threshold_mono hR (by positivity)
    (by exact_mod_cast hlength) (by exact_mod_cast hp) (by exact_mod_cast hdim)

end ExactZO.FiniteEntropySelection
