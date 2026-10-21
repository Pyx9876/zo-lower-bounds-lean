import ExactZO.Model
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
The line comparison proof adapts the checked local-library theorem
`ClippedSGD.smooth_upper` (lean-library/ClippedSGD.lean), upgrading its scalar
upper comparison to a two-sided Taylor remainder via mathlib's norm fencing
theorem. Convexity of the objective is not assumed.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace ExactZO
variable {d : ℕ}

/-- The standard coordinate vector; this is public, independent of the objective. -/
def coordinateVector (i : Fin d) : X d := EuclideanSpace.single i 1

@[simp] theorem norm_coordinateVector (i : Fin d) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

@[simp] theorem inner_coordinateVector (x : X d) (i : Fin d) :
    ⟪x, coordinateVector i⟫_ℝ = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

/-- This vector uses exactly the two scalar values shown in each coordinate. -/
def centralDifference (value : X d → ℝ) (h : ℝ) (x : X d) : X d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i =>
    (value (x + h • coordinateVector i) - value (x - h • coordinateVector i)) / (2 * h)

@[simp] theorem centralDifference_apply (value : X d → ℝ) (h : ℝ) (x : X d)
    (i : Fin d) :
    centralDifference value h x i =
      (value (x + h • coordinateVector i) - value (x - h • coordinateVector i)) / (2 * h) := rfl

def fdRadius (d : ℕ) (L ε : ℝ) : ℝ := ε / (4 * L * Real.sqrt d)

theorem Objective.along_line_hasDerivAt (f : Objective d) (x y : X d) (t : ℝ) :
    HasDerivAt (f.value ∘ AffineMap.lineMap x y)
      ⟪f.grad (AffineMap.lineMap x y t), y - x⟫_ℝ t := by
  simpa only [innerSL_apply] using
    (f.hasDeriv (AffineMap.lineMap x y t)).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap

/-- Sharp first-order Taylor error from the actual derivative and global smoothness. -/
theorem smooth_taylor_bound {L : ℝ} (f : Objective d) (hf : Smooth f L)
    (x y : X d) :
    |f.value y - f.value x - ⟪f.grad x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  let A : ℝ := ⟪f.grad x, y - x⟫_ℝ
  let N : ℝ := ‖y - x‖
  let φ : ℝ → ℝ := fun t => f.value (AffineMap.lineMap x y t) - f.value x - t * A
  let B : ℝ → ℝ := fun t => L / 2 * t ^ 2 * N ^ 2
  have hφ (t : ℝ) : HasDerivAt φ
      ⟪f.grad (AffineMap.lineMap x y t) - f.grad x, y - x⟫_ℝ t := by
    convert ((f.along_line_hasDerivAt x y t).sub_const (f.value x)).sub
      ((hasDerivAt_id t).mul_const A) using 1
    simp [A, inner_sub_left]
  have hB (t : ℝ) : HasDerivAt B (L * t * N ^ 2) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (N ^ 2) using 1
    dsimp [B]
    ring
  have bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖⟪f.grad (AffineMap.lineMap x y t) - f.grad x, y - x⟫_ℝ‖ ≤ L * t * N ^ 2 := by
    have hn : ‖f.grad (AffineMap.lineMap x y t) - f.grad x‖ ≤ L * (t * N) := by
      simpa [AffineMap.lineMap_apply_module', norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1, N] using hf (AffineMap.lineMap x y t) x
    have hi := (norm_inner_le_norm (𝕜 := ℝ) (f.grad (AffineMap.lineMap x y t) - f.grad x) (y - x)).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg (y - x)))
    dsimp [N] at *
    nlinarith only [hi]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t _ => (hφ t).continuousAt.continuousWithinAt)
    (fun t _ => (hφ t).hasDerivWithinAt)
    (show ‖φ 0‖ ≤ B 0 by simp [φ, B]) hB bound
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa [φ, B, A, N, Real.norm_eq_abs] using h

/-- The usual descent lemma, with no unproved analytic prerequisite. -/
theorem smooth_upper {L : ℝ} (f : Objective d) (hf : Smooth f L) (x y : X d) :
    f.value y ≤ f.value x + ⟪f.grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  have h := (abs_le.mp (smooth_taylor_bound f hf x y)).2
  linarith

/-- The exact central difference has coordinate error at most `L*h/2`. -/
theorem centralDifference_coordinate_error {L h : ℝ} (f : Objective d)
    (hf : Smooth f L) (hh : 0 < h) (x : X d) (i : Fin d) :
    |centralDifference f.value h x i - f.grad x i| ≤ L * h / 2 := by
  have hp := smooth_taylor_bound f hf x (x + h • coordinateVector i)
  have hm := smooth_taylor_bound f hf x (x - h • coordinateVector i)
  simp only [add_sub_cancel_left, real_inner_smul_right, inner_coordinateVector,
    norm_smul, Real.norm_eq_abs, abs_of_pos hh, norm_coordinateVector, mul_one] at hp
  have hsub : x - h • coordinateVector i - x = -(h • coordinateVector i) := by abel
  rw [hsub, inner_neg_right, real_inner_smul_right, inner_coordinateVector, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos hh, norm_coordinateVector, mul_one] at hm
  rw [centralDifference_apply, abs_le]
  obtain ⟨hp₁, hp₂⟩ := abs_le.mp hp
  obtain ⟨hm₁, hm₂⟩ := abs_le.mp hm
  have hden : 0 < 2 * h := by positivity
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hden]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hden]
    nlinarith

/-- Aggregating the coordinate errors in the Euclidean norm. -/
theorem centralDifference_error {L h : ℝ} (f : Objective d) (hf : Smooth f L)
    (hL : 0 ≤ L) (hh : 0 < h) (x : X d) :
    ‖centralDifference f.value h x - f.grad x‖ ≤ L * h * Real.sqrt d / 2 := by
  have hc : 0 ≤ L * h / 2 := by positivity
  have hcoord (i : Fin d) : ‖(centralDifference f.value h x - f.grad x) i‖ ≤ L * h / 2 := by
    simpa [Real.norm_eq_abs] using centralDifference_coordinate_error f hf hh x i
  have hsq : ‖centralDifference f.value h x - f.grad x‖ ^ 2 ≤
      (d : ℝ) * (L * h / 2) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ i : Fin d, (L * h / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => (sq_le_sq₀ (norm_nonneg _) hc).mpr (hcoord i)
      _ = _ := by simp
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have htarget : 0 ≤ L * h * Real.sqrt d / 2 := by positivity
  nlinarith [sq_nonneg (‖centralDifference f.value h x - f.grad x‖ + L * h * Real.sqrt d / 2)]

theorem fdRadius_pos {L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) :
    0 < fdRadius d L ε := by
  unfold fdRadius
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_pos hε (mul_pos (mul_pos (by norm_num) hL) (Real.sqrt_pos.mpr hd'))

/-- The paper's public radius gives the advertised `ε/8` vector error. -/
theorem centralDifference_error_calibrated {L ε : ℝ} (f : Objective d)
    (hf : Smooth f L) (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) (x : X d) :
    ‖centralDifference f.value (fdRadius d L ε) x - f.grad x‖ ≤ ε / 8 := by
  have hr := centralDifference_error f hf hL.le (fdRadius_pos hd hL hε) x
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd')
  convert hr using 1
  unfold fdRadius
  field_simp [ne_of_gt hL]
  ring

/-- A successful stopping test certifies the actual gradient. -/
theorem centralDifference_stop {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hstop : ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8) :
    ‖f.grad x‖ ≤ ε := by
  have herr := centralDifference_error_calibrated f hf hd hL hε x
  have hn := norm_sub_le (centralDifference f.value (fdRadius d L ε) x)
    (centralDifference f.value (fdRadius d L ε) x - f.grad x)
  rw [sub_sub_cancel] at hn
  linarith

/-- Inexact-gradient descent, proved from the descent lemma rather than assumed. -/
theorem smooth_inexact_step {L : ℝ} (f : Objective d) (hf : Smooth f L)
    (hL : 0 < L) (x g : X d) :
    f.value (x - L⁻¹ • g) ≤ f.value x - ‖f.grad x‖ ^ 2 / (2 * L) +
      ‖g - f.grad x‖ ^ 2 / (2 * L) := by
  have h := smooth_upper f hf x (x - L⁻¹ • g)
  have hsub : x - L⁻¹ • g - x = -(L⁻¹ • g) := by abel
  rw [hsub, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  have hid := norm_sub_sq_real g (f.grad x)
  rw [real_inner_comm (f.grad x) g] at hid
  have heq : f.value x - L⁻¹ * ⟪f.grad x, g⟫_ℝ + L / 2 * (L⁻¹ * ‖g‖) ^ 2 =
      f.value x - ‖f.grad x‖ ^ 2 / (2 * L) + ‖g - f.grad x‖ ^ 2 / (2 * L) := by
    rw [hid]
    field_simp [ne_of_gt hL]
    ring
  linarith [heq]

/-- Every failed stopping test yields the explicit decrease in `prop:upper`. -/
theorem centralDifference_descent {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hcontinue : 7 * ε / 8 < ‖centralDifference f.value (fdRadius d L ε) x‖) :
    f.value (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x) ≤
      f.value x - 35 * ε ^ 2 / (128 * L) := by
  let g := centralDifference f.value (fdRadius d L ε) x
  have herr : ‖g - f.grad x‖ ≤ ε / 8 :=
    centralDifference_error_calibrated f hf hd hL hε x
  have hn := norm_sub_le (g - f.grad x) (-f.grad x)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
  have hg : 3 * ε / 4 < ‖f.grad x‖ := by
    change 7 * ε / 8 < ‖g‖ at hcontinue
    linarith
  have hstep := smooth_inexact_step f hf hL x g
  have he2 : ‖g - f.grad x‖ ^ 2 ≤ (ε / 8) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr herr
  have hg2 : (3 * ε / 4) ^ 2 ≤ ‖f.grad x‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hg.le
  have hden : 0 < 2 * L := by positivity
  have hc : -‖f.grad x‖ ^ 2 / (2 * L) + ‖g - f.grad x‖ ^ 2 / (2 * L) ≤
      -(35 * ε ^ 2 / (128 * L)) := by
    have hraw : -‖f.grad x‖ ^ 2 + ‖g - f.grad x‖ ^ 2 ≤ -(35 * ε ^ 2 / 64) := by
      nlinarith
    have hdv := div_le_div_of_nonneg_right hraw hden.le
    convert hdv using 1 <;> field_simp [ne_of_gt hL] <;> ring
  change f.value (x - L⁻¹ • g) ≤ _
  simp only [neg_div] at hc
  linarith

end ExactZO
