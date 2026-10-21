import ExactZO.SubspaceEstimate
import ExactZO.CoordinateAlgorithm

/-! The residual certificate for the actual full finite-difference vector.
The geometric statements apply to any vector with the proved estimation error;
the final statements supply that error from scalar function values. -/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.SubspaceResidual
open FrameGeometry StageGeometry

variable {d : ℕ}

/-- Component outside the current frame. -/
def residual (U : List (X d)) (g : X d) : X d := g - frameProjection U g

/-- The direction computed from returned function values; total even at zero. -/
def direction (U : List (X d)) (g : X d) : X d := ‖residual U g‖⁻¹ • residual U g

theorem residual_norm_sq {U : List (X d)} (hU : OrthoList U) (g : X d) :
    ‖residual U g‖ ^ 2 = ‖g‖ ^ 2 - ‖coordinateMap U g‖ ^ 2 := by
  have hp : ‖frameProjection U g‖ = ‖coordinateMap U g‖ := frameMap_norm hU _
  rw [residual, norm_sub_sq_real, frameProjection_quadratic, hp]
  ring

theorem estimated_coordinates_le {U : List (X d)} (hU : OrthoList U)
    {a g : X d} {ε : ℝ} (herr : ‖g - a‖ ≤ ε / 16)
    (hstop : ‖coordinateMap U a‖ ≤ ε / 2) : ‖coordinateMap U g‖ ≤ 9 * ε / 16 := by
  have hc := coordinateMap_lipschitz hU g a
  have hn := norm_sub_le (coordinateMap U g - coordinateMap U a) (-coordinateMap U a)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
  linarith

/-- Pythagoras gives a nonzero residual at every failed full stopping test. -/
theorem residual_norm_gt {U : List (X d)} (hU : OrthoList U)
    {a g : X d} {ε : ℝ} (hε : 0 < ε) (herr : ‖g - a‖ ≤ ε / 16)
    (hstop : ‖coordinateMap U a‖ ≤ ε / 2) (hfail : 15 * ε / 16 < ‖g‖) :
    3 * ε / 4 < ‖residual U g‖ := by
  have hc := estimated_coordinates_le hU herr hstop
  have hc2 : ‖coordinateMap U g‖ ^ 2 ≤ (9 * ε / 16) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hc
  have hg2 : (15 * ε / 16) ^ 2 < ‖g‖ ^ 2 := by nlinarith [norm_nonneg g]
  have hp := residual_norm_sq hU g
  by_contra h
  have hr : ‖residual U g‖ ≤ 3 * ε / 4 := le_of_not_gt h
  have hr2 : ‖residual U g‖ ^ 2 ≤ (3 * ε / 4) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hr
  nlinarith

theorem direction_norm {U : List (X d)} {g : X d} (hr : 0 < ‖residual U g‖) :
    ‖direction U g‖ = 1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
    inv_mul_cancel₀ (ne_of_gt hr)]

theorem direction_orthogonal {U : List (X d)} (hU : OrthoList U) (g : X d) :
    ∀ v ∈ U, ⟪direction U g, v⟫_ℝ = 0 := by
  intro v hv
  have hp := (Submodule.mem_orthogonal' (frameSpace U) (residual U g)).mp
    (sub_projection_mem_orthogonal hU g) v (mem_frameSpace hv)
  rw [direction, real_inner_smul_left, hp, mul_zero]

theorem inner_direction {U : List (X d)} (hU : OrthoList U) (g : X d)
    (hr : 0 < ‖residual U g‖) : ⟪g, direction U g⟫_ℝ = ‖residual U g‖ := by
  have hi : ⟪g, residual U g⟫_ℝ = ‖residual U g‖ ^ 2 := by
    rw [residual, inner_sub_right, real_inner_self_eq_norm_sq, frameProjection_quadratic]
    exact (residual_norm_sq hU g).symm
  rw [direction, real_inner_smul_right, hi, pow_two, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hr), one_mul]

theorem direction_slope {U : List (X d)} (hU : OrthoList U)
    {a g : X d} {ε : ℝ} (hε : 0 < ε) (herr : ‖g - a‖ ≤ ε / 16)
    (hr : 3 * ε / 4 < ‖residual U g‖) :
    11 * ε / 16 < ⟪a, direction U g⟫_ℝ := by
  have hr0 : 0 < ‖residual U g‖ := by linarith
  have he := abs_real_inner_le_norm (g - a) (direction U g)
  rw [direction_norm hr0, mul_one] at he
  have he' := (le_abs_self ⟪g - a, direction U g⟫_ℝ).trans (he.trans herr)
  rw [inner_sub_left, inner_direction hU g hr0] at he'
  linarith

/-- The new direction is certified and may be appended to the current frame. -/
theorem residual_certificate {U : List (X d)} (hU : OrthoList U)
    {a g : X d} {ε : ℝ} (hε : 0 < ε) (herr : ‖g - a‖ ≤ ε / 16)
    (hstop : ‖coordinateMap U a‖ ≤ ε / 2) (hfail : 15 * ε / 16 < ‖g‖) :
    3 * ε / 4 < ‖residual U g‖ ∧ ‖direction U g‖ = 1 ∧
      (∀ v ∈ U, ⟪direction U g, v⟫_ℝ = 0) ∧
      11 * ε / 16 < ⟪a, direction U g⟫_ℝ ∧ OrthoList (U ++ [direction U g]) := by
  have hr := residual_norm_gt hU hε herr hstop hfail
  have hn := direction_norm (show 0 < ‖residual U g‖ by linarith)
  have ho := direction_orthogonal hU g
  exact ⟨hr, hn, ho, direction_slope hU hε herr hr, hU.append_unit hn ho⟩

/-- A failed full test excludes zero ambient dimension, without assuming it. -/
theorem dimension_pos_of_failure {ε : ℝ} (hε : 0 < ε) (g : X d)
    (hfail : 15 * ε / 16 < ‖g‖) : 0 < d := by
  by_contra h
  have hd : d = 0 := Nat.eq_zero_of_not_pos h
  subst d
  have hg : g = 0 := by ext i; exact Fin.elim0 i
  rw [hg, norm_zero] at hfail
  linarith

/-- Full coordinate differences at the paper's radius, computed from values. -/
def fullEstimate (value : X d → ℝ) (L ε : ℝ) (x : X d) : X d :=
  centralDifference value (fdRadius d L (ε / 2)) x

theorem fullEstimate_eq_paper_radius (value : X d → ℝ) (L ε : ℝ) (x : X d) :
    fullEstimate value L ε x =
      centralDifference value (SubspaceEstimate.radius d L ε) x := by
  rw [SubspaceEstimate.radius_eq_fdRadius]
  rfl

theorem fullEstimate_error {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    (hL : 0 < L) (hε : 0 < ε) (x : X d) :
    ‖fullEstimate f.value L ε x - f.grad x‖ ≤ ε / 16 := by
  cases d with
  | zero =>
      have hz : fullEstimate f.value L ε x - f.grad x = 0 := by
        ext i
        exact Fin.elim0 i
      rw [hz, norm_zero]
      positivity
  | succ d =>
      have he := centralDifference_error_calibrated f hf (Nat.succ_pos d)
        hL (show 0 < ε / 2 by positivity) x
      simpa only [fullEstimate, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using he

theorem fullEstimate_stop {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hstop : ‖fullEstimate f.value L ε x‖ ≤ 15 * ε / 16) : ‖f.grad x‖ ≤ ε := by
  have he := fullEstimate_error f hf hL hε x
  have hn := norm_sub_le (fullEstimate f.value L ε x) (fullEstimate f.value L ε x - f.grad x)
  rw [sub_sub_cancel] at hn
  linarith

/-- The full residual lemma with the actual estimator and the actual gradient. -/
theorem fullEstimate_residual {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U) (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hstop : ‖coordinateMap U (f.grad x)‖ ≤ ε / 2)
    (hfail : 15 * ε / 16 < ‖fullEstimate f.value L ε x‖) :
    3 * ε / 4 < ‖residual U (fullEstimate f.value L ε x)‖ ∧
      ‖direction U (fullEstimate f.value L ε x)‖ = 1 ∧
      (∀ v ∈ U, ⟪direction U (fullEstimate f.value L ε x), v⟫_ℝ = 0) ∧
      11 * ε / 16 < ⟪f.grad x, direction U (fullEstimate f.value L ε x)⟫_ℝ ∧
      OrthoList (U ++ [direction U (fullEstimate f.value L ε x)]) :=
  residual_certificate hU hε (fullEstimate_error f hf hL hε x) hstop hfail

/-- A full value-only estimate followed by a continuation. -/
def fullEstimateProcedure (L ε : ℝ) (x : X d) (next : X d → ValueProcedure d) :
    ValueProcedure d := ExactZO.estimateProcedure (fdRadius d L (ε / 2)) x next

theorem fullEstimateProcedure_result (L ε : ℝ) (x : X d)
    (next : X d → ValueProcedure d) (f : Objective d) :
    (fullEstimateProcedure L ε x next).result f =
      (next (fullEstimate f.value L ε x)).result f :=
  ExactZO.estimateProcedure_result _ x next f

theorem fullEstimateProcedure_cost (L ε : ℝ) (x : X d)
    (next : X d → ValueProcedure d) (f : Objective d) :
    (fullEstimateProcedure L ε x next).cost f =
      2 * d + (next (fullEstimate f.value L ε x)).cost f :=
  ExactZO.estimateProcedure_cost _ x next f

end ExactZO.SubspaceResidual
