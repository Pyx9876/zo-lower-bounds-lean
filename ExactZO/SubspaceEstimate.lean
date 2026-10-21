import ExactZO.FrameGeometry
import ExactZO.FiniteDifference
import ExactZO.ValueProcedure

/-! The actual central differences on an orthonormal list frame. The translated
restriction is an objective with its actual derivative. Its finite-difference
error and restricted descent reuse the global smoothness estimates. -/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.SubspaceEstimate
open FrameGeometry StageGeometry

variable {d : ℕ}

/-- Restriction of the actual objective to the translated frame. -/
def pullback (f : Objective d) (x : X d) (U : List (X d)) : Objective U.length where
  value z := f.value (x + frameMap U z)
  grad z := coordinateMap U (f.grad (x + frameMap U z))
  hasDeriv z := by
    have hc := (f.hasDeriv (x + frameMap U z)).comp z
      ((frameMap U).hasFDerivAt.const_add x)
    convert hc using 1
    ext v
    exact (frameMap U).adjoint_inner_left v (f.grad (x + frameMap U z))

@[simp] theorem pullback_value (f : Objective d) (x : X d) (U : List (X d))
    (z : X U.length) : (pullback f x U).value z = f.value (x + frameMap U z) := rfl

@[simp] theorem pullback_grad (f : Objective d) (x : X d) (U : List (X d))
    (z : X U.length) :
    (pullback f x U).grad z = coordinateMap U (f.grad (x + frameMap U z)) := rfl

theorem pullback_smooth {L : ℝ} (f : Objective d) (hf : Smooth f L)
    (x : X d) {U : List (X d)} (hU : OrthoList U) : Smooth (pullback f x U) L := by
  intro z w
  calc
    ‖(pullback f x U).grad z - (pullback f x U).grad w‖ ≤
        ‖f.grad (x + frameMap U z) - f.grad (x + frameMap U w)‖ :=
      coordinateMap_lipschitz hU _ _
    _ ≤ L * ‖(x + frameMap U z) - (x + frameMap U w)‖ := hf _ _
    _ = L * ‖z - w‖ := by rw [add_sub_add_left_eq_sub, frameMap_lipschitz hU]

/-- The radius in the subspace-search procedure. -/
def radius (k : ℕ) (L ε : ℝ) : ℝ := ε / (8 * L * Real.sqrt k)

theorem radius_eq_fdRadius (k : ℕ) (L ε : ℝ) :
    radius k L ε = fdRadius k L (ε / 2) := by
  unfold radius fdRadius
  ring

theorem radius_pos {k : ℕ} {L ε : ℝ} (hk : 0 < k) (hL : 0 < L) (hε : 0 < ε) :
    0 < radius k L ε := by
  rw [radius_eq_fdRadius]
  exact fdRadius_pos hk hL (by positivity)

/-- Exactly two scalar function values per frame vector. -/
def estimate (value : X d → ℝ) (U : List (X d)) (h : ℝ) (x : X d) : X U.length :=
  (WithLp.equiv 2 (Fin U.length → ℝ)).symm fun i =>
    (value (x + h • U.get i) - value (x - h • U.get i)) / (2 * h)

@[simp] theorem estimate_apply (value : X d → ℝ) (U : List (X d)) (h : ℝ)
    (x : X d) (i : Fin U.length) :
    estimate value U h x i =
      (value (x + h • U.get i) - value (x - h • U.get i)) / (2 * h) := rfl

theorem estimate_eq_centralDifference (f : Objective d) (U : List (X d))
    (h : ℝ) (x : X d) :
    estimate f.value U h x = centralDifference (pullback f x U).value h 0 := by
  ext i
  simp [estimate_apply, centralDifference_apply, coordinateVector, sub_eq_add_neg]

/-- The error uses global smoothness, including at probes outside the sublevel. -/
theorem estimate_error_of_pos {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U) (hk : 0 < U.length)
    (hL : 0 < L) (hε : 0 < ε) (x : X d) :
    ‖estimate f.value U (radius U.length L ε) x - coordinateMap U (f.grad x)‖ ≤
      ε / 16 := by
  have he := centralDifference_error_calibrated (pullback f x U)
    (pullback_smooth f hf x hU) hk hL (show 0 < ε / 2 by positivity) 0
  rw [estimate_eq_centralDifference, radius_eq_fdRadius]
  simpa only [pullback_grad, map_zero, add_zero, div_div, show (2 : ℝ) * 8 = 16 by norm_num]
    using he

@[simp] theorem estimate_nil (value : X d → ℝ) (h : ℝ) (x : X d) :
    estimate value [] h x = 0 := by
  ext i
  exact Fin.elim0 i

@[simp] theorem coordinateMap_nil (x : X d) : coordinateMap [] x = 0 := by
  ext i
  exact Fin.elim0 i

/-- The empty subspace also satisfies the error bound, with the empty estimate. -/
theorem estimate_error {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U)
    (hL : 0 < L) (hε : 0 < ε) (x : X d) :
    ‖estimate f.value U (radius U.length L ε) x - coordinateMap U (f.grad x)‖ ≤
      ε / 16 := by
  cases U with
  | nil => simp only [estimate_nil, coordinateMap_nil, sub_self, norm_zero]; positivity
  | cons u U => exact estimate_error_of_pos f hf hU (by simp) hL hε x

/-- The finite-difference stopping rule certifies the actual restricted gradient. -/
theorem estimate_stop {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U)
    (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hstop : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7 * ε / 16) :
    ‖coordinateMap U (f.grad x)‖ ≤ ε / 2 := by
  have he := estimate_error f hf hU hL hε x
  have hn := norm_sub_le (estimate f.value U (radius U.length L ε) x)
    (estimate f.value U (radius U.length L ε) x - coordinateMap U (f.grad x))
  rw [sub_sub_cancel] at hn
  linarith

/-- One actual restricted step, with the actual finite-difference error. -/
theorem estimate_step_model {L : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U) (hL : 0 < L) (x : X d)
    (z : X U.length) :
    f.value (x - L⁻¹ • frameMap U z) ≤ f.value x -
      ‖coordinateMap U (f.grad x)‖ ^ 2 / (2 * L) +
      ‖z - coordinateMap U (f.grad x)‖ ^ 2 / (2 * L) := by
  have hs := smooth_inexact_step (pullback f x U) (pullback_smooth f hf x hU) hL 0 z
  simpa only [pullback_value, pullback_grad, sub_eq_add_neg, zero_add, map_zero,
    add_zero, map_neg, map_smul] using hs

/-- Every failed restricted stopping test gives the strict decrease in the paper. -/
theorem estimate_descent {L ε : ℝ} (f : Objective d) (hf : Smooth f L)
    {U : List (X d)} (hU : OrthoList U) (hL : 0 < L) (hε : 0 < ε) (x : X d)
    (hcontinue : 7 * ε / 16 < ‖estimate f.value U (radius U.length L ε) x‖) :
    f.value (x - L⁻¹ • frameMap U (estimate f.value U (radius U.length L ε) x)) <
      f.value x - 35 * ε ^ 2 / (512 * L) := by
  let z := estimate f.value U (radius U.length L ε) x
  let w := coordinateMap U (f.grad x)
  have herr : ‖z - w‖ ≤ ε / 16 := estimate_error f hf hU hL hε x
  have hn := norm_sub_le (z - w) (-w)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hn
  have hw : 3 * ε / 8 < ‖w‖ := by
    change 7 * ε / 16 < ‖z‖ at hcontinue
    linarith
  have he2 : ‖z - w‖ ^ 2 ≤ (ε / 16) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr herr
  have hw2 : (3 * ε / 8) ^ 2 < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hraw : -‖w‖ ^ 2 + ‖z - w‖ ^ 2 < -(35 * ε ^ 2 / 256) := by nlinarith
  have hdv := div_lt_div_of_pos_right hraw (show 0 < 2 * L by positivity)
  have hc : -‖w‖ ^ 2 / (2 * L) + ‖z - w‖ ^ 2 / (2 * L) <
      -(35 * ε ^ 2 / (512 * L)) := by
    convert hdv using 1 <;> field_simp [ne_of_gt hL] <;> ring
  have hs := estimate_step_model f hf hU hL x z
  change f.value (x - L⁻¹ • frameMap U z) < _
  change f.value (x - L⁻¹ • frameMap U z) ≤ f.value x -
    ‖w‖ ^ 2 / (2 * L) + ‖z - w‖ ^ 2 / (2 * L) at hs
  simp only [neg_div] at hc
  linarith

/-- Empty frames terminate immediately; this does not require positive dimension. -/
theorem estimate_nil_stop (value : X d → ℝ) {ε h : ℝ} (hε : 0 ≤ ε) (x : X d) :
    ‖estimate value [] h x‖ ≤ 7 * ε / 16 := by
  simp only [estimate_nil, norm_zero]
  positivity

/-- A concrete value-only procedure, fixed independently of the objective. -/
def estimateProcedure (U : List (X d)) (h : ℝ) (x : X d)
    (next : X U.length → ValueProcedure d) : ValueProcedure d :=
  ValueProcedure.queryVector U.length (fun i => x + h • U.get i) fun positive =>
    ValueProcedure.queryVector U.length (fun i => x - h • U.get i) fun negative =>
      next ((WithLp.equiv 2 (Fin U.length → ℝ)).symm fun i =>
        (positive i - negative i) / (2 * h))

theorem estimateProcedure_result (U : List (X d)) (h : ℝ) (x : X d)
    (next : X U.length → ValueProcedure d) (f : Objective d) :
    (estimateProcedure U h x next).result f = (next (estimate f.value U h x)).result f := by
  simp only [estimateProcedure, ValueProcedure.queryVector_result, estimate]

theorem estimateProcedure_cost (U : List (X d)) (h : ℝ) (x : X d)
    (next : X U.length → ValueProcedure d) (f : Objective d) :
    (estimateProcedure U h x next).cost f =
      2 * U.length + (next (estimate f.value U h x)).cost f := by
  simp only [estimateProcedure, ValueProcedure.queryVector_cost, estimate]
  omega

/-- With an empty frame the procedure asks no values before its continuation. -/
@[simp] theorem estimateProcedure_nil (h : ℝ) (x : X d)
    (next : X 0 → ValueProcedure d) : estimateProcedure [] h x next = next 0 := by
  simp only [estimateProcedure, List.length_nil, ValueProcedure.queryVector]
  congr 1
  exact Subsingleton.elim _ _

end ExactZO.SubspaceEstimate
