import ExactZO.Model
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace
namespace ExactZO.RadialCompression
variable {d : ℕ}

def factor (R : ℝ) (x : X d) : ℝ := (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹

def compression (R : ℝ) (x : X d) : X d := factor R x • x

theorem denominator_pos (R : ℝ) (x : X d) : 0 < 1 + ‖x‖ ^ 2 / R ^ 2 := by
  positivity

theorem factor_pos (R : ℝ) (x : X d) : 0 < factor R x :=
  inv_pos.mpr (Real.sqrt_pos.2 (denominator_pos R x))

theorem factor_le_one (R : ℝ) (x : X d) : factor R x ≤ 1 := by
  apply (inv_le_one₀ (Real.sqrt_pos.2 (denominator_pos R x))).2
  apply (Real.le_sqrt (by norm_num) (by positivity)).2
  norm_num
  positivity

theorem compression_norm_lt {R : ℝ} (hR : 0 < R) (x : X d) :
    ‖compression R x‖ < R := by
  have hs := Real.sq_sqrt (le_of_lt (denominator_pos R x))
  have hp := Real.sqrt_pos.2 (denominator_pos R x)
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have he : R ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) = R ^ 2 + ‖x‖ ^ 2 := by
    field_simp
  have hsq : ‖x‖ ^ 2 < (R * Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2)) ^ 2 := by
    rw [mul_pow, hs, he]
    linarith
  have hn : ‖x‖ < R * Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2) :=
    (sq_lt_sq₀ (norm_nonneg x) (by positivity)).mp hsq
  rw [compression, norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos R x)]
  change (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹ * ‖x‖ < R
  rw [inv_mul_eq_div]
  exact (div_lt_iff₀ hp).2 hn

theorem compressed_inner_eq_zero_iff (R : ℝ) (x u : X d) :
    ⟪u, compression R x⟫_ℝ = 0 ↔ ⟪u, x⟫_ℝ = 0 := by
  rw [compression, real_inner_smul_right, mul_eq_zero]
  simp [(factor_pos R x).ne']

/-- The derivative is the scalar contraction minus one radial rank-one term. -/
def derivative (R : ℝ) (x : X d) : X d →L[ℝ] X d :=
  factor R x • ContinuousLinearMap.id ℝ (X d) -
    (factor R x ^ 3 / R ^ 2) • (innerSL ℝ x).smulRight x

theorem factor_hasFDerivAt {R : ℝ} (_hR : 0 < R) (x : X d) :
    HasFDerivAt (factor R) ((-(factor R x ^ 3 / R ^ 2)) • innerSL ℝ x) x := by
  have hp := Real.sqrt_pos.2 (denominator_pos R x)
  have hn : HasFDerivAt (fun y : X d => 1 + ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const ((R ^ 2)⁻¹)).const_add 1 using 1
  have h := hn.sqrt (ne_of_gt (denominator_pos R x))
  have hi := (hasDerivAt_inv (ne_of_gt hp)).comp_hasFDerivAt x h
  convert hi using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul]
  dsimp [factor]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem compression_hasFDerivAt {R : ℝ} (hR : 0 < R) (x : X d) :
    HasFDerivAt (compression R) (derivative R x) x := by
  convert (factor_hasFDerivAt hR x).smul (hasFDerivAt_id x) using 1
  ext v
  simp [derivative, ContinuousLinearMap.smulRight_apply, smul_sub, sub_smul,
    neg_smul, add_comm]
  ring

theorem derivative_on_orthogonal (R : ℝ) (x u : X d)
    (h : ⟪u, compression R x⟫_ℝ = 0) : derivative R x u = factor R x • u := by
  have hz := (compressed_inner_eq_zero_iff R x u).mp h
  have hzx : ⟪x, u⟫_ℝ = 0 := by simpa only [real_inner_comm] using hz
  simp [derivative, hzx]

theorem factor_identity {R : ℝ} (_hR : 0 < R) (x : X d) :
    factor R x ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) = 1 := by
  rw [factor, inv_pow, Real.sq_sqrt (denominator_pos R x).le]
  exact inv_mul_cancel₀ (denominator_pos R x).ne'

theorem derivative_norm_le_one {R : ℝ} (hR : 0 < R) (x : X d) :
    ‖derivative R x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  let c := factor R x ^ 2 / R ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcr : c * ‖x‖ ^ 2 ≤ 1 := by
    have hi := factor_identity hR x
    have he : c * ‖x‖ ^ 2 + factor R x ^ 2 = 1 := by
      calc
        _ = factor R x ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) := by dsimp [c]; ring
        _ = 1 := hi
    nlinarith [sq_nonneg (factor R x)]
  have he : derivative R x v = factor R x • (v - (c * ⟪x, v⟫_ℝ) • x) := by
    simp only [derivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
      smul_sub, smul_smul]
    congr 1
    congr 1
    dsimp [c]
    ring
  have hnorm : ‖v - (c * ⟪x, v⟫_ℝ) • x‖ ≤ ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
    rw [real_inner_comm v x]
    have hn := mul_nonneg hc (sq_nonneg ⟪v, x⟫_ℝ)
    have hb := mul_le_mul_of_nonneg_left hcr hn
    nlinarith
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos R x), one_mul]
  exact (mul_le_mul_of_nonneg_left hnorm (factor_pos R x).le).trans
    (mul_le_of_le_one_left (norm_nonneg v) (factor_le_one R x))

theorem compression_lipschitz {R : ℝ} (hR : 0 < R) (x y : X d) :
    ‖compression R y - compression R x‖ ≤ ‖y - x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (s := Set.univ) (f := compression R) (f' := derivative R)
    (fun z _ => (compression_hasFDerivAt hR z).hasFDerivWithinAt)
    (fun z _ => derivative_norm_le_one hR z) (convex_univ : Convex ℝ (Set.univ : Set (X d)))
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [one_mul] using h

end ExactZO.RadialCompression
