import ExactZO.Model
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual a.e. gradient derivative and the every-segment upper model. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology
set_option maxHeartbeats 800000
namespace ExactZO

/-- The gradient really is differentiable at almost every point in the set;
the totalized derivative at exceptional points is not used as a Hessian. -/
def AEHessianUpper {d : ℕ} (f : Objective d) (H : X d →L[ℝ] X d)
    (U : Set (X d)) : Prop :=
  ∀ᵐ x ∂volume, x ∈ U → DifferentiableAt ℝ f.grad x ∧
    ∀ v, ⟪v, (fderiv ℝ f.grad x) v⟫_ℝ ≤ ⟪v, H v⟫_ℝ

def HessianSublevelClass {d : ℕ} (L Δ E : ℝ) (f : Objective d) : Prop :=
  SmoothClass L Δ f ∧ ∃ H, UpperMatrix L E H ∧ AEHessianUpper f H (StrictSublevel f)

theorem gradient_increment_le_of_quadraticUpper {d : ℕ} {f : Objective d}
    {H : X d →L[ℝ] X d} {x y : X d}
    (hxy : QuadraticUpper f H x y) (hyx : QuadraticUpper f H y x) :
    ⟪f.grad y - f.grad x, y-x⟫_ℝ ≤ ⟪y-x, H (y-x)⟫_ℝ := by
  have hneg : x-y = -(y-x) := by abel
  unfold QuadraticUpper at hxy hyx
  rw [hneg, map_neg, inner_neg_neg, inner_neg_right] at hyx
  rw [inner_sub_left]
  linarith

theorem hessian_upper_of_segment_model {d : ℕ} {f : Objective d}
    {H B : X d →L[ℝ] X d} {U : Set (X d)} (hU : IsOpen U)
    (hmodel : ∀ x y, segment ℝ x y ⊆ U → QuadraticUpper f H x y)
    {x : X d} (hx : x ∈ U) (hB : HasFDerivAt f.grad B x) (v : X d) :
    ⟪v, B v⟫_ℝ ≤ ⟪v, H v⟫_ℝ := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hxb : x ∈ Metric.ball x r := by simpa using hr
  have hpath : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hgrad : HasDerivAt (fun t : ℝ => f.grad (x+t•v)) (B v) 0 := by
    have hB0 : HasFDerivAt f.grad B (x+(0:ℝ)•v) := by simpa using hB
    exact hB0.comp_hasDerivAt 0 hpath
  have hg : HasDerivAt (fun t : ℝ => ⟪v, f.grad (x+t•v)⟫_ℝ) ⟪v, B v⟫_ℝ 0 := by
    simpa only [Function.comp_def, innerSL_apply] using
      (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt 0 hgrad
  have hevent : ∀ᶠ t in 𝓝[>] (0:ℝ), x+t•v ∈ Metric.ball x r := by
    have hc : Continuous (fun t : ℝ => x+t•v) := by fun_prop
    have hz : x+(0:ℝ)•v ∈ Metric.ball x r := by simpa using hxb
    exact ((hc.tendsto 0).eventually (Metric.isOpen_ball.mem_nhds hz)).filter_mono
      nhdsWithin_le_nhds
  apply le_of_tendsto hg.tendsto_slope_zero_right
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht htpos
  change 0 < t at htpos
  have hseg : segment ℝ x (x+t•v) ⊆ U :=
    ((convex_ball x r).segment_subset hxb ht).trans hrU
  have hmono := gradient_increment_le_of_quadraticUpper (hmodel x (x+t•v) hseg)
    (hmodel (x+t•v) x (by simpa only [segment_symm] using hseg))
  simp only [add_sub_cancel_left, map_smul, inner_smul_right, inner_smul_left,
    RCLike.conj_to_real] at hmono
  have hstep : ⟪f.grad (x+t•v)-f.grad x, v⟫_ℝ ≤ t*⟪v,H v⟫_ℝ := by
    nlinarith
  simp only [zero_smul, add_zero, zero_add, smul_eq_mul]
  rw [← inner_sub_right]
  have hs : ⟪v, f.grad (x+t•v)-f.grad x⟫_ℝ ≤ t*⟪v,H v⟫_ℝ := by
    simpa only [real_inner_comm] using hstep
  exact (inv_mul_le_iff₀ htpos).mpr hs

theorem aeHessianUpper_of_segment_model {d : ℕ} {f : Objective d}
    {H : X d →L[ℝ] X d} {U : Set (X d)} {L : ℝ}
    (hL : 0 ≤ L) (hf : Smooth f L) (hU : IsOpen U)
    (hmodel : ∀ x y, segment ℝ x y ⊆ U → QuadraticUpper f H x y) :
    AEHessianUpper f H U := by
  have hlip : LipschitzWith ⟨L,hL⟩ f.grad := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hf x y
  filter_upwards [hlip.ae_differentiableAt (μ := (volume : Measure (X d)))] with x hx
  intro hxU
  exact ⟨hx, fun v => hessian_upper_of_segment_model hU hmodel hxU hx.hasFDerivAt v⟩

theorem sublevelClass_subset_hessianSublevelClass {d : ℕ} {f : Objective d}
    {L Δ E : ℝ} (hL : 0 ≤ L) (hf : SublevelClass L Δ E f) :
    HessianSublevelClass L Δ E f := by
  obtain ⟨hs,H,hH,hmodel⟩ := hf
  exact ⟨hs,H,hH,aeHessianUpper_of_segment_model hL hs.1
    (isOpen_lt f.continuous continuous_const) hmodel⟩

end ExactZO
