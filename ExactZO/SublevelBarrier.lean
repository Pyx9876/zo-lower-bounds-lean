import ExactZO.RadialSecond
import ExactZO.SublevelPotential
import ExactZO.FrameGeometry
import ExactZO.ChainBarrier
import ExactZO.SublevelWrapper

/-! Full-space gradient barrier for the actual sublevel wrapper. The exterior
estimate uses a slightly coarser radial chain bound than the manuscript; it
still gives a gradient norm at least two, exceeding the required 5/8. -/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.SublevelBarrier
open RadialCompression FrameGeometry StageGeometry
variable {d : ℕ}

private theorem radius_ge_32 {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) : 32 ≤ R := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

private theorem mu_bounds {m : ℕ} {R : ℝ} (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) :
    0 ≤ 64 * (m : ℝ) / R ^ 2 ∧ 64 * (m : ℝ) / R ^ 2 ≤ 1 / 16 := by
  constructor
  · positivity
  · apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith

private theorem near_factor {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) (x : X d) (hx : ‖x‖ ≤ R / 2 + 2) :
    (6 / 7 : ℝ) ≤ factor R x := by
  have h32 := radius_ge_32 hm hR hsize
  have hr : ‖x‖ ≤ 9 * R / 16 := by linarith
  have hr2 : ‖x‖ ^ 2 / R ^ 2 ≤ 81 / 256 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith [norm_nonneg x]
  have ha := factor_pos R x
  have hi := factor_identity hR x
  have hh := mul_le_mul_of_nonneg_left hr2 (sq_nonneg (factor R x))
  have ha2 : (36 / 49 : ℝ) < factor R x ^ 2 := by nlinarith
  nlinarith

private theorem near_slope_ratio {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) (x : X d) :
    0 ≤ SublevelPotential.slope (64 * (m : ℝ) / R ^ 2) (R / 2) ‖x‖ / ‖x‖ ∧
    SublevelPotential.slope (64 * (m : ℝ) / R ^ 2) (R / 2) ‖x‖ / ‖x‖ ≤ 3 / 16 := by
  obtain ⟨hμ, hμ₁⟩ := mu_bounds hR hsize
  have h32 := radius_ge_32 hm hR hsize
  have hs := SublevelPotential.slope_bounds hμ (show 64 * (m:ℝ) / R^2 ≤ 1 by linarith)
    (show 0 ≤ R/2 by positivity) (norm_nonneg x)
  refine ⟨div_nonneg hs.1 (norm_nonneg x), ?_⟩
  have hrat := SublevelPotential.slope_ratio_bound hμ (show 0 < R/2 by positivity) (norm_nonneg x)
  have h4 : 2 / (R/2) ≤ 1/8 := by
    apply (div_le_iff₀ (show 0 < R/2 by positivity)).2
    linarith
  linarith

private theorem near_scalar {a p y c q : ℝ} (ha : 6/7 ≤ a) (hp : p ≤ -1)
    (hy : |y| ≤ 1) (hc : |c| ≤ 25/2048) (hq : 0 ≤ q) (hq' : q ≤ 3/16) :
    a * (p-y*c) + q*(y/a) ≤ -(643/1024 : ℝ) := by
  have ha0 : 0 < a := by linarith
  have hyc : |y*c| ≤ 25/2048 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hy hc (abs_nonneg c) (by norm_num : (0:ℝ) ≤ 1)]
  have hpc : p-y*c ≤ -(1-25/2048 : ℝ) := by
    have h := (abs_le.mp hyc).1
    linarith
  have hmain := mul_le_mul_of_nonneg_left hpc ha0.le
  have hmain' := mul_le_mul_of_nonpos_right ha (show -(1-25/2048 : ℝ) ≤ 0 by norm_num)
  have hya : y/a ≤ 7/6 := by
    apply (div_le_iff₀ ha0).2
    have h := (abs_le.mp hy).2
    linarith
  have hqya := mul_le_mul_of_nonneg_left hya hq
  have hqbound := mul_le_mul_of_nonneg_right hq' (show (0:ℝ) ≤ 7/6 by norm_num)
  nlinarith

/-- The frame scalar product corresponding to the weighted chain gradient. -/
theorem compressed_inner_frame (R : ℝ) (U : List (X d)) (x : X d) (p : X U.length) :
    ⟪coordinateMap U (compression R x), p⟫_ℝ = factor R x * ⟪x, frameMap U p⟫_ℝ := by
  rw [coordinateMap]
  rw [(frameMap U).adjoint_inner_left]
  rw [compression, real_inner_smul_left]

/-- The radial component of the derivative is its radial eigenvalue. -/
theorem inner_derivative_radial {R : ℝ} (hR : 0 < R) (x w : X d) :
    ⟪x, derivative R x w⟫_ℝ = factor R x ^ 3 * ⟪x, w⟫_ℝ := by
  simp only [derivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hi := factor_identity hR x
  have hh := congrArg (fun t : ℝ => t * factor R x * ⟪x,w⟫_ℝ) hi
  dsimp only at hh
  field_simp at hh ⊢
  nlinarith only [hh]

private theorem gradient_coordinate_formula {R : ℝ} (hR : 0 < R)
    {U : List (X d)} (hU : OrthoList U) (x : X d) (p : X U.length) (q : ℝ)
    (j : Fin U.length) :
    ⟪U.get j, derivative R x (frameMap U p) + q • x⟫_ℝ =
      factor R x * (p j - coordinateMap U (compression R x) j *
        (⟪coordinateMap U (compression R x), p⟫_ℝ / R^2)) +
      q * (coordinateMap U (compression R x) j / factor R x) := by
  have hj : ⟪U.get j, frameMap U p⟫_ℝ = p j := by
    rw [← coordinateMap_apply, coordinateMap_frameMap_apply hU]
  rw [compressed_inner_frame, coordinateMap_apply, compression, real_inner_smul_right]
  simp only [derivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
    inner_add_right, inner_sub_right, real_inner_smul_right, hj]
  field_simp [(factor_pos R x).ne']
  ring

/-- Near the center an actual unfinished chain coordinate forces a negative
frame component below minus 5/8. -/
theorem near_barrier {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)} (hU : OrthoList U)
    (x : X d) (p : X U.length)
    (hw : |⟪coordinateMap U (compression R x), p⟫_ℝ| ≤ (25/2 : ℝ)*m)
    (hj : ∃ j : Fin U.length, |coordinateMap U (compression R x) j| < 1 ∧ p j ≤ -1)
    (hx : ‖x‖ ≤ R/2+2) :
    (5/8 : ℝ) < ‖derivative R x (frameMap U p) +
      SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x‖ := by
  obtain ⟨j, hy, hp⟩ := hj
  have ha := near_factor hm hR hsize x hx
  obtain ⟨hq, hq'⟩ := near_slope_ratio hm hR hsize x
  have hc : |⟪coordinateMap U (compression R x), p⟫_ℝ / R^2| ≤ 25/2048 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hR)]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith
  have hn := near_scalar ha hp hy.le hc hq hq'
  rw [← gradient_coordinate_formula hR hU x p
    (SublevelPotential.slope (64*(m:ℝ)/R^2) (R/2) ‖x‖ / ‖x‖) j] at hn
  change ⟪U.get j, derivative R x (frameMap U p) +
    SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x⟫_ℝ ≤ _ at hn
  have hu : ‖U.get j‖ = 1 := hU.2 _ (List.get_mem U j)
  have habs := abs_real_inner_le_norm (U.get j)
    (derivative R x (frameMap U p) + SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x)
  rw [hu, one_mul] at habs
  have hneg := neg_le_abs ⟪U.get j, derivative R x (frameMap U p) +
    SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x⟫_ℝ
  linarith

/-- The exterior radial potential dominates the chain radial component even
with the coarser bound a²≤1; no unfinished-coordinate premise is needed. -/
theorem far_barrier {m : ℕ} {R : ℝ} (hR : 0 < R) (U : List (X d))
    (x : X d) (p : X U.length)
    (hw : |⟪coordinateMap U (compression R x), p⟫_ℝ| ≤ (25/2 : ℝ)*m)
    (hx : R/2+2 ≤ ‖x‖) :
    (2 : ℝ) ≤ ‖derivative R x (frameMap U p) +
      SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x‖ := by
  have hr : 0 < ‖x‖ := by linarith
  have hμ : 0 ≤ 64*(m:ℝ)/R^2 := by positivity
  have ha := factor_pos R x
  have ha₁ := factor_le_one R x
  have ha₂ : factor R x ^ 2 ≤ 1 := by nlinarith
  have hw' : -(25/2 : ℝ)*m ≤ factor R x ^ 2 *
      ⟪coordinateMap U (compression R x), p⟫_ℝ := by
    have hh : |factor R x ^ 2 * ⟪coordinateMap U (compression R x), p⟫_ℝ| ≤ (25/2 : ℝ)*m := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hm0 : (0 : ℝ) ≤ (25/2 : ℝ)*m := by positivity
      exact (mul_le_mul_of_nonneg_left hw (sq_nonneg _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha₂ hm0)
    simpa only [neg_mul] using (abs_le.mp hh).1
  have he : ⟪x, derivative R x (frameMap U p) +
      SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x⟫_ℝ =
      factor R x ^ 2 * ⟪coordinateMap U (compression R x), p⟫_ℝ +
        ((64*(m:ℝ)/R^2)*(R/2)+2)*‖x‖ := by
    rw [inner_add_right, inner_derivative_radial hR, compressed_inner_frame]
    simp only [SublevelPotential.gradient, RadialLift.lift, real_inner_smul_right,
      real_inner_self_eq_norm_sq, SublevelPotential.slope_outer hx]
    field_simp
    ring
  have hrr : R/2 ≤ ‖x‖ := by linarith
  have hm := mul_le_mul_of_nonneg_left hrr (mul_nonneg hμ (show 0 ≤ R/2 by positivity))
  have heμ : (64*(m:ℝ)/R^2)*(R/2)*(R/2) = 16*(m:ℝ) := by field_simp; ring
  rw [heμ] at hm
  have hinner := real_inner_le_norm x (derivative R x (frameMap U p) +
      SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x)
  rw [he] at hinner
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- The actual wrapper has a strict full-space gradient barrier whenever any
compressed coordinate is unfinished. -/
theorem gradient_barrier {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)} (hU : OrthoList U)
    (hlen : U.length = m) (x : X d)
    (hx : ∃ i : Fin U.length, |SublevelWrapper.chainPoint R U x i| < 1) :
    (5/8 : ℝ) < ‖SublevelWrapper.gradient m R U x‖ := by
  have hw : |⟪coordinateMap U (compression R x),
      ScalarChain.gradient U.length (SublevelWrapper.chainPoint R U x)⟫_ℝ| ≤ (25/2 : ℝ)*m := by
    calc
      _ ≤ (25/2 : ℝ)*U.length :=
        ScalarChain.gradient_weighted_coarse U.length (SublevelWrapper.chainPoint R U x)
      _ = _ := by rw [hlen]
  have hj := ScalarChain.gradient_exists_barrier U.length (SublevelWrapper.chainPoint R U x) hx
  change (5/8 : ℝ) < ‖derivative R x (frameMap U
    (ScalarChain.gradient U.length (SublevelWrapper.chainPoint R U x))) +
    SublevelPotential.gradient (64*(m:ℝ)/R^2) (R/2) x‖
  by_cases hn : ‖x‖ ≤ R/2+2
  · exact near_barrier hm hR hsize hU x _ hw hj hn
  · have h := far_barrier hR U x (ScalarChain.gradient U.length (SublevelWrapper.chainPoint R U x))
      hw (le_of_lt (lt_of_not_ge hn))
    linarith

/-- The exact zero-coordinate condition used by the resisting-oracle stage. -/
theorem gradient_barrier_of_zero {m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
    (hsize : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)} (hU : OrthoList U)
    (hlen : U.length = m) (x : X d) (hx : ∃ u ∈ U, ⟪u,x⟫_ℝ = 0) :
    (5/8 : ℝ) < ‖(SublevelWrapper.objective m R U hR).grad x‖ := by
  apply gradient_barrier hm hR hsize hU hlen x
  obtain ⟨u, hu, hz⟩ := hx
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hu
  refine ⟨i, ?_⟩
  simp only [SublevelWrapper.chainPoint, coordinateMap_apply, compression,
    real_inner_smul_right, hz, mul_zero, abs_zero]
  norm_num

end ExactZO.SublevelBarrier
