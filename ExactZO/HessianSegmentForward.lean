import ExactZO.HessianSegment
import ExactZO.LipschitzFTC
import ExactZO.FinitePiece
import Mathlib.Topology.Compactness.Compact

/-!
An ambient almost everywhere Hessian bound gives an upper model on every closed
segment contained in the open set. Haar disintegration supplies almost every
translated line; compactness and continuity recover the prescribed segment.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology NNReal
set_option maxHeartbeats 800000

namespace ExactZO

/-- Integrate the directional gradient comparison for the actual value function. -/
theorem quadraticUpper_of_directional_gradient_bound {d : ℕ} {f : Objective d}
    {H : X d →L[ℝ] X d} {x v : X d}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1,
      ⟪v, f.grad (x + t • v) - f.grad x⟫_ℝ ≤ t * ⟪v, H v⟫_ℝ) :
    QuadraticUpper f H x (x + v) := by
  let A := ⟪f.grad x, v⟫_ℝ
  let C := ⟪v, H v⟫_ℝ
  let φ : ℝ → ℝ := fun t => f.value (x + t • v) - f.value x - t * A - t ^ 2 / 2 * C
  have hval (t : ℝ) : HasDerivAt (fun u : ℝ => f.value (x + u • v))
      ⟪f.grad (x + t • v), v⟫_ℝ t := by
    simpa only [Function.comp_def, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm] using
      f.along_line_hasDerivAt x (x + v) t
  have hφ (t : ℝ) : HasDerivAt φ
      (⟪f.grad (x + t • v), v⟫_ℝ - A - t * C) t := by
    convert (((hval t).sub_const (f.value x)).sub ((hasDerivAt_id t).mul_const A)).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const C) using 1
    dsimp [φ]
    ring
  have hcomp : φ 1 - φ 0 ≤ 0 * (1 - 0) := by
    apply image_sub_le_of_hasDerivAt_off_finset (∅ : Finset ℝ) (by norm_num)
      (fun t _ => (hφ t).continuousAt.continuousWithinAt)
    intro t ht _
    refine ⟨_, hφ t, ?_⟩
    have hg := hd t ⟨ht.1.le, ht.2.le⟩
    rw [inner_sub_right, real_inner_comm (f.grad (x + t • v)) v,
      real_inner_comm (f.grad x) v] at hg
    dsimp only [A, C]
    linarith
  norm_num only [φ, zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow,
    one_pow, zero_div, sub_self, sub_zero] at hcomp
  unfold QuadraticUpper
  simp only [add_sub_cancel_left]
  dsimp only [A, C] at hcomp
  linarith

/-- Restrict an ambient a.e. bound to almost every translated line, not to an
arbitrarily fixed line. The real derivative is retained in the conclusion. -/
theorem ae_directional_derivative_upper {d : ℕ} {f : Objective d}
    {H : X d →L[ℝ] X d} {U : Set (X d)} (hU : IsOpen U)
    (hH : AEHessianUpper f H U) (v : X d) :
    ∀ᵐ z ∂(volume : Measure (X d)), ∀ᵐ t ∂(volume : Measure ℝ), z + t • v ∈ U →
      ∃ D, HasDerivAt (fun u : ℝ => ⟪v, f.grad (z + u • v)⟫_ℝ) D t ∧
        D ≤ ⟪v, H v⟫_ℝ := by
  let S : Set (X d) := Uᶜ ∪ {z | DifferentiableAt ℝ f.grad z ∧
    ⟪v, (fderiv ℝ f.grad z) v⟫_ℝ ≤ ⟪v, H v⟫_ℝ}
  have hmeas : Measurable (fun z => ⟪v, (fderiv ℝ f.grad z) v⟫_ℝ) :=
    (innerSL ℝ v).continuous.measurable.comp (measurable_fderiv_apply_const ℝ f.grad v)
  have hS : MeasurableSet S := hU.measurableSet.compl.union
    ((measurableSet_of_differentiableAt ℝ f.grad).inter
      (measurableSet_le hmeas measurable_const))
  have hSae : ∀ᵐ z ∂(volume : Measure (X d)), z ∈ S := by
    filter_upwards [hH] with z hz
    by_cases hzU : z ∈ U
    · exact Or.inr ⟨(hz hzU).1, (hz hzU).2 v⟩
    · exact Or.inl hzU
  let T : ℝ →ₗ[ℝ] X d := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v
  have hlines := (ae_ae_add_linearMap_mem_iff T (volume : Measure ℝ)
    (volume : Measure (X d)) hS).mpr hSae
  filter_upwards [hlines] with z hz
  filter_upwards [hz] with t ht htU
  have hgood : DifferentiableAt ℝ f.grad (z + t • v) ∧
      ⟪v, (fderiv ℝ f.grad (z + t • v)) v⟫_ℝ ≤ ⟪v, H v⟫_ℝ := by
    change z + t • v ∈ S at ht
    exact ht.resolve_left (fun hn => hn htU)
  refine ⟨_, ?_, hgood.2⟩
  have hpath : HasDerivAt (fun u : ℝ => z + u • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hgrad := hgood.1.hasFDerivAt.comp_hasDerivAt t hpath
  simpa only [Function.comp_def, innerSL_apply] using
    (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hgrad

/-- A global Lipschitz gradient restricts to a Lipschitz directional gradient. -/
theorem directional_gradient_lipschitz {d : ℕ} {f : Objective d} {L : ℝ}
    (hf : Smooth f L) (x v : X d) :
    LipschitzWith (Real.toNNReal (L * ‖v‖ ^ 2))
      (fun t : ℝ => ⟪v, f.grad (x + t • v)⟫_ℝ) := by
  apply LipschitzWith.of_dist_le'
  intro s t
  rw [dist_eq_norm, ← inner_sub_right]
  calc
    ‖⟪v, f.grad (x + s • v) - f.grad (x + t • v)⟫_ℝ‖ ≤
        ‖v‖ * ‖f.grad (x + s • v) - f.grad (x + t • v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (L * ‖(x + s • v) - (x + t • v)‖) :=
      mul_le_mul_of_nonneg_left (hf _ _) (norm_nonneg _)
    _ = (L * ‖v‖ ^ 2) * dist s t := by
      rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, dist_eq_norm]
      ring

/-- The a.e. linewise derivative bound is enough; exceptional points need not be finite. -/
theorem quadraticUpper_of_ae_directional_bound {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {x v : X d} (hf : Smooth f L)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) 1 →
      ∃ D, HasDerivAt (fun u : ℝ => ⟪v, f.grad (x + u • v)⟫_ℝ) D t ∧
        D ≤ ⟪v, H v⟫_ℝ) :
    QuadraticUpper f H x (x + v) := by
  apply quadraticUpper_of_directional_gradient_bound
  intro t ht
  have h := image_sub_le_of_hasDerivAt_ae ht.1 (directional_gradient_lipschitz hf x v)
    (C := ⟪v, H v⟫_ℝ) ?_
  · simpa only [zero_smul, add_zero, sub_zero, inner_sub_right, mul_comm] using h
  · filter_upwards [hd] with u hu huot
    exact hu ⟨huot.1, huot.2.trans_le ht.2⟩

/-- Every closed segment contained in the open set has the upper model controlled
by the same ambient Hessian upper matrix. No convexity of the open set is assumed. -/
theorem segment_model_of_aeHessianUpper {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {U : Set (X d)}
    (hL : 0 ≤ L) (hf : Smooth f L) (hU : IsOpen U) (hH : AEHessianUpper f H U)
    (x y : X d) (hseg : segment ℝ x y ⊆ U) : QuadraticUpper f H x y := by
  let v := y - x
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • v ∈ U := by
    apply hseg
    rw [segment_eq_image_lineMap]
    refine ⟨t, ht, ?_⟩
    simp only [AffineMap.lineMap_apply_module', v, add_comm]
  have hevent : ∀ᶠ z in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, z + t • v ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc : Continuous (fun p : X d × ℝ => p.1 + p.2 • v) := by fun_prop
    exact (hc.tendsto (x, t)).eventually (hU.mem_nhds (hpath t ht))
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hevent
  let G : Set (X d) := {z | ∀ᵐ t ∂(volume : Measure ℝ), z + t • v ∈ U →
    ∃ D, HasDerivAt (fun u : ℝ => ⟪v, f.grad (z + u • v)⟫_ℝ) D t ∧
      D ≤ ⟪v, H v⟫_ℝ}
  have hG : Dense G := (volume : Measure (X d)).dense_of_ae
    (ae_directional_derivative_upper hU hH v)
  have hclosed : IsClosed {z : X d | QuadraticUpper f H z (z + v)} := by
    simp only [QuadraticUpper, add_sub_cancel_left]
    apply isClosed_le (f.continuous.comp (continuous_id.add continuous_const))
    exact (f.continuous.add ((hf.continuous_grad hL).inner continuous_const)).add continuous_const
  have hVG : V ∩ G ⊆ {z : X d | QuadraticUpper f H z (z + v)} := by
    rintro z ⟨hzV, hzG⟩
    apply quadraticUpper_of_ae_directional_bound hf
    filter_upwards [hzG] with t ht htmem
    exact ht (hVsub hzV t ⟨htmem.1.le, htmem.2.le⟩)
  have hxclosure : x ∈ closure (V ∩ G) := hG.open_subset_closure_inter hVopen hxV
  have hqx := (closure_minimal hVG hclosed) hxclosure
  change QuadraticUpper f H x (x + v) at hqx
  have hev : x + v = y := by dsimp [v]; abel
  rwa [hev] at hqx

theorem hessianSublevelClass_subset_sublevelClass {d : ℕ} {f : Objective d}
    {L Δ E : ℝ} (hL : 0 ≤ L) (hf : HessianSublevelClass L Δ E f) :
    SublevelClass L Δ E f := by
  obtain ⟨hs, H, hH, hAE⟩ := hf
  exact ⟨hs, H, hH, segment_model_of_aeHessianUpper hL hs.1
    (isOpen_lt f.continuous continuous_const) hAE⟩

theorem sublevelClass_iff_hessianSublevelClass {d : ℕ} {f : Objective d}
    {L Δ E : ℝ} (hL : 0 ≤ L) :
    SublevelClass L Δ E f ↔ HessianSublevelClass L Δ E f :=
  ⟨sublevelClass_subset_hessianSublevelClass hL, hessianSublevelClass_subset_sublevelClass hL⟩

theorem aeHessianUpper_iff_segment_model {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {U : Set (X d)}
    (hL : 0 ≤ L) (hf : Smooth f L) (hU : IsOpen U) :
    AEHessianUpper f H U ↔ ∀ x y, segment ℝ x y ⊆ U → QuadraticUpper f H x y :=
  ⟨fun hH => segment_model_of_aeHessianUpper hL hf hU hH,
    aeHessianUpper_of_segment_model hL hf hU⟩

end ExactZO
