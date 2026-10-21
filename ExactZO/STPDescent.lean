import ExactZO.STPCore
import Mathlib.MeasureTheory.Integral.Prod

/-! One-step STP descent from an explicit capped quadratic model and direction
moments. No Gaussian law or Gaussian absolute first moment is asserted here.
Only the accepted value is integrated; rejected values need not be integrable. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace ExactZO.STP

variable {d : ℕ}

/-- The two moment identities used by STP, including genuine integrability.
The probability law is explicit. Instantiating this with a Gaussian measure is
a separate obligation, not a consequence of the following descent theorem. -/
structure DirectionMoments (ν : Measure (X d)) (α : ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  abs_integrable : ∀ g : X d, Integrable (fun a => |⟪g, a⟫_ℝ|) ν
  abs_integral : ∀ g : X d, (∫ a, |⟪g, a⟫_ℝ| ∂ν) = α * ‖g‖
  quadratic_integrable : ∀ H : X d →L[ℝ] X d,
    Integrable (fun a => ⟪a, H a⟫_ℝ) ν
  quadratic_integral : ∀ H : X d →L[ℝ] X d,
    (∫ a, ⟪a, H a⟫_ℝ ∂ν) = LinearMap.trace ℝ (X d) H.toLinearMap

def CappedQuadraticModel (f : Objective d) (H : X d →L[ℝ] X d)
    (x : X d) : Prop :=
  ∀ v, min (f.value (x + v)) (f.value 0) ≤
    f.value x + ⟪f.grad x, v⟫_ℝ + (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ

theorem step_value_continuous (f : Objective d) (h : ℝ) (x : X d) :
    Continuous (fun a => f.value (step f h x a)) := by
  simp_rw [step_value]
  exact continuous_const.min ((f.continuous.comp
    (continuous_const.add (continuous_const.smul continuous_id))).min
    (f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))))

/-- Boundedness between a global lower witness and the current value supplies
integrability without any growth assumption on uphill proposals. -/
theorem step_value_integrable (f : Objective d) {Δ : ℝ} (hgap : HasGap f Δ)
    (h : ℝ) (x : X d) (ν : Measure (X d)) [IsFiniteMeasure ν] :
    Integrable (fun a => f.value (step f h x a)) ν := by
  obtain ⟨lower, hlo, _⟩ := hgap
  apply (integrable_const (|lower| + |f.value x|)).mono'
    (step_value_continuous f h x).aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hl := hlo (step f h x a)
    have := neg_abs_le lower
    linarith [abs_nonneg (f.value x)]
  · have hu := step_monotone f h x a
    linarith [le_abs_self (f.value x), abs_nonneg lower]

/-- Pointwise use of the better of the two signs. -/
theorem step_value_le_quadratic (f : Objective d) (H : X d →L[ℝ] X d)
    (h : ℝ) (x a : X d) (hx : f.value x ≤ f.value 0)
    (hcap : CappedQuadraticModel f H x) :
    f.value (step f h x a) ≤ f.value x - |h| * |⟪f.grad x, a⟫_ℝ| +
      (h ^ 2 / 2) * ⟪a, H a⟫_ℝ := by
  have hp : f.value (step f h x a) ≤
      f.value x + h * ⟪f.grad x, a⟫_ℝ + (h ^ 2 / 2) * ⟪a, H a⟫_ℝ := by
    have hc := hcap (h • a)
    have hs : f.value (step f h x a) ≤
        min (f.value (x + h • a)) (f.value 0) :=
      le_min (step_le_plus f h x a) ((step_monotone f h x a).trans hx)
    calc
      _ ≤ _ := hs.trans hc
      _ = _ := by simp only [map_smul, real_inner_smul_left,
        inner_smul_right]; ring
  have hm : f.value (step f h x a) ≤
      f.value x - h * ⟪f.grad x, a⟫_ℝ + (h ^ 2 / 2) * ⟪a, H a⟫_ℝ := by
    have hc := hcap (-(h • a))
    have hs : f.value (step f h x a) ≤
        min (f.value (x + -(h • a))) (f.value 0) := by
      rw [← sub_eq_add_neg]
      exact le_min (step_le_minus f h x a) ((step_monotone f h x a).trans hx)
    calc
      _ ≤ _ := hs.trans hc
      _ = _ := by simp only [map_neg, map_smul, inner_neg_right,
        inner_neg_neg, inner_neg_left, real_inner_smul_left, inner_smul_right]; ring
  rw [← abs_mul]
  rcases le_total 0 (h * ⟪f.grad x, a⟫_ℝ) with hn | hn
  · rwa [abs_of_nonneg hn]
  · rw [abs_of_nonpos hn]
    linarith

theorem expected_step_le (f : Objective d) {Δ α h : ℝ} (hgap : HasGap f Δ)
    (H : X d →L[ℝ] X d) (x : X d) (ν : Measure (X d))
    (moments : DirectionMoments ν α) (hh : 0 ≤ h)
    (hx : f.value x ≤ f.value 0) (hcap : CappedQuadraticModel f H x) :
    (∫ a, f.value (step f h x a) ∂ν) ≤
      f.value x - α * h * ‖f.grad x‖ +
        (h ^ 2 / 2) * LinearMap.trace ℝ (X d) H.toLinearMap := by
  letI := moments.probability
  have hbound : Integrable (fun a => f.value x - h * |⟪f.grad x, a⟫_ℝ| +
      (h ^ 2 / 2) * ⟪a, H a⟫_ℝ) ν :=
    ((integrable_const _).sub ((moments.abs_integrable _).const_mul h)).add
      ((moments.quadratic_integrable H).const_mul _)
  calc
    _ ≤ ∫ a, (f.value x - h * |⟪f.grad x, a⟫_ℝ| +
        (h ^ 2 / 2) * ⟪a, H a⟫_ℝ) ∂ν := by
      apply integral_mono (step_value_integrable f hgap h x ν) hbound
      intro a
      simpa only [abs_of_nonneg hh] using step_value_le_quadratic f H h x a hx hcap
    _ = _ := by
      have hadd := integral_add ((integrable_const (f.value x)).sub
        ((moments.abs_integrable (f.grad x)).const_mul h))
        ((moments.quadratic_integrable H).const_mul (h ^ 2 / 2))
      simp only [Pi.sub_apply] at hadd
      rw [hadd, integral_sub (integrable_const (f.value x))
          ((moments.abs_integrable (f.grad x)).const_mul h),
        integral_const_mul, integral_const_mul, moments.abs_integral,
        moments.quadratic_integral]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      ring

theorem expected_step_monotone (f : Objective d) {Δ : ℝ} (hgap : HasGap f Δ)
    (h : ℝ) (x : X d) (ν : Measure (X d)) [IsProbabilityMeasure ν] :
    (∫ a, f.value (step f h x a) ∂ν) ≤ f.value x := by
  calc
    _ ≤ ∫ _ : X d, f.value x ∂ν :=
      integral_mono (step_value_integrable f hgap h x ν) (integrable_const _)
        (step_monotone f h x)
    _ = _ := by simp

/-- The elementary numerical margin used in the paper's bad-center argument. -/
theorem stp_descent_constant {ε M α G : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hα : 79 / 100 ≤ α) (hG : ε ≤ G) :
    (39 / 125 : ℝ) * ε ^ 2 / M ≤
      α * (4 * ε / (5 * M)) * G - ((4 * ε / (5 * M)) ^ 2 / 2) * M := by
  have hh : 0 ≤ 4 * ε / (5 * M) := by positivity
  have hα0 : 0 ≤ α := by linarith
  have hl : (79 / 100 : ℝ) * (4 * ε / (5 * M)) * ε ≤
      α * (4 * ε / (5 * M)) * G :=
    mul_le_mul (mul_le_mul_of_nonneg_right hα hh) hG hε.le
      (mul_nonneg hα0 hh)
  have hid : (79 / 100 : ℝ) * (4 * ε / (5 * M)) * ε -
      ((4 * ε / (5 * M)) ^ 2 / 2) * M = (39 / 125 : ℝ) * ε ^ 2 / M := by
    field_simp
    ring
  linarith

theorem expected_step_bad (f : Objective d) {Δ α ε M : ℝ} (hgap : HasGap f Δ)
    (H : X d →L[ℝ] X d) (x : X d) (ν : Measure (X d))
    (moments : DirectionMoments ν α) (hε : 0 < ε) (hM : 0 < M)
    (hα : 79 / 100 ≤ α) (htrace : LinearMap.trace ℝ (X d) H.toLinearMap ≤ M)
    (hx : f.value x ≤ f.value 0) (hcap : CappedQuadraticModel f H x)
    (hbad : ε < ‖f.grad x‖) :
    (∫ a, f.value (step f (4 * ε / (5 * M)) x a) ∂ν) ≤
      f.value x - (39 / 125 : ℝ) * ε ^ 2 / M := by
  have hd := expected_step_le f (h := 4 * ε / (5 * M)) hgap H x ν moments
    (by positivity) hx hcap
  have hq : (4 * ε / (5 * M)) ^ 2 / 2 *
      LinearMap.trace ℝ (X d) H.toLinearMap ≤
      (4 * ε / (5 * M)) ^ 2 / 2 * M :=
    mul_le_mul_of_nonneg_left htrace (by positivity)
  have hc := stp_descent_constant hε hM hα hbad.le
  linarith

/-- Good centers contribute zero required drift; monotonicity handles them. -/
theorem expected_step_drift (f : Objective d) {Δ α ε M : ℝ} (hgap : HasGap f Δ)
    (H : X d →L[ℝ] X d) (x : X d) (ν : Measure (X d))
    (moments : DirectionMoments ν α) (hε : 0 < ε) (hM : 0 < M)
    (hα : 79 / 100 ≤ α) (htrace : LinearMap.trace ℝ (X d) H.toLinearMap ≤ M)
    (hx : f.value x ≤ f.value 0) (hcap : CappedQuadraticModel f H x) :
    (if ε < ‖f.grad x‖ then (39 / 125 : ℝ) * ε ^ 2 / M else 0) ≤
      f.value x - ∫ a, f.value (step f (4 * ε / (5 * M)) x a) ∂ν := by
  letI := moments.probability
  split_ifs with hbad
  · linarith [expected_step_bad f hgap H x ν moments hε hM hα htrace hx hcap hbad]
  · linarith [expected_step_monotone f hgap (4 * ε / (5 * M)) x ν]

theorem sublevel_value_integrable {Ω : Type*} [MeasurableSpace Ω]
    (f : Objective d) {Δ : ℝ} (hgap : HasGap f Δ) (Y : Ω → X d)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hY : AEStronglyMeasurable (fun ω => f.value (Y ω)) μ)
    (hsub : ∀ ω, f.value (Y ω) ≤ f.value 0) :
    Integrable (fun ω => f.value (Y ω)) μ := by
  obtain ⟨lower, hlo, _⟩ := hgap
  apply (integrable_const (|lower| + |f.value 0|)).mono' hY
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [hlo (Y ω), neg_abs_le lower, abs_nonneg (f.value 0)]
  · linarith [hsub ω, le_abs_self (f.value 0), abs_nonneg lower]

theorem step_value_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : Objective d) (h : ℝ) (Y : Ω → X d) (hY : Measurable Y) :
    Measurable (fun p : Ω × X d => f.value (step f h (Y p.1) p.2)) := by
  simp_rw [step_value]
  have hy : Measurable (fun p : Ω × X d => Y p.1) := hY.comp measurable_fst
  have ha : Measurable (fun p : Ω × X d => h • p.2) := measurable_snd.const_smul h
  exact (f.continuous.measurable.comp hy).min
    ((f.continuous.measurable.comp (hy.add ha)).min
      (f.continuous.measurable.comp (hy.sub ha)))

/-- Integrating fixed-center drift over a random center and an independent
fresh direction uses the actual product measure. The bad event is a measurable
set, and all value integrals are justified by the initial sublevel bound. -/
theorem expected_step_product_drift {Ω : Type*} [MeasurableSpace Ω]
    (f : Objective d) {Δ α ε M : ℝ} (hgap : HasGap f Δ)
    (H : X d →L[ℝ] X d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → X d) (hY : Measurable Y)
    (ν : Measure (X d)) (moments : DirectionMoments ν α)
    (hε : 0 < ε) (hM : 0 < M) (hα : 79 / 100 ≤ α)
    (htrace : LinearMap.trace ℝ (X d) H.toLinearMap ≤ M)
    (hsub : ∀ ω, f.value (Y ω) ≤ f.value 0)
    (hcap : ∀ ω, CappedQuadraticModel f H (Y ω))
    (hbad : MeasurableSet {ω | ε < ‖f.grad (Y ω)‖}) :
    ((39 / 125 : ℝ) * ε ^ 2 / M) * μ.real {ω | ε < ‖f.grad (Y ω)‖} ≤
      (∫ ω, f.value (Y ω) ∂μ) -
        ∫ p, f.value (step f (4 * ε / (5 * M)) (Y p.1) p.2) ∂μ.prod ν := by
  letI := moments.probability
  let δ : ℝ := (39 / 125 : ℝ) * ε ^ 2 / M
  let h : ℝ := 4 * ε / (5 * M)
  let B : Set Ω := {ω | ε < ‖f.grad (Y ω)‖}
  have hi : Integrable (fun ω => f.value (Y ω)) μ :=
    sublevel_value_integrable f hgap Y μ
      (f.continuous.measurable.comp hY).aestronglyMeasurable hsub
  have hj : Integrable (fun p : Ω × X d => f.value (step f h (Y p.1) p.2))
      (μ.prod ν) :=
    sublevel_value_integrable (Ω := Ω × X d) f hgap
      (fun p : Ω × X d => step f h (Y p.1) p.2) (μ.prod ν)
      (step_value_joint_measurable f h Y hY).aestronglyMeasurable
      (fun p => (step_monotone f h (Y p.1) p.2).trans (hsub p.1))
  have hb : Integrable (B.indicator (fun _ => δ)) μ :=
    (integrable_const δ).indicator hbad
  have hiineq : (∫ ω, B.indicator (fun _ => δ) ω ∂μ) ≤
      ∫ ω, (f.value (Y ω) - ∫ a, f.value (step f h (Y ω) a) ∂ν) ∂μ := by
    apply integral_mono hb (hi.sub hj.integral_prod_left)
    intro ω
    simpa only [Set.indicator_apply, B, Set.mem_setOf_eq, h, δ] using
      expected_step_drift f hgap H (Y ω) ν moments hε hM hα htrace (hsub ω) (hcap ω)
  rw [integral_indicator_const δ hbad, integral_sub hi hj.integral_prod_left,
    ← integral_prod _ hj] at hiineq
  change μ.real B * δ ≤ _ at hiineq
  rw [mul_comm] at hiineq
  exact hiineq

/-- A same-space fresh-direction interface. The equality of joint laws is an
explicit independence obligation; it is not an assumed descent estimate. -/
theorem expected_step_joint_drift {Ω : Type*} [MeasurableSpace Ω]
    (f : Objective d) {Δ α ε M : ℝ} (hgap : HasGap f Δ)
    (H : X d →L[ℝ] X d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y a : Ω → X d) (hY : Measurable Y) (ha : Measurable a)
    (ν : Measure (X d)) (moments : DirectionMoments ν α)
    (hε : 0 < ε) (hM : 0 < M) (hα : 79 / 100 ≤ α)
    (htrace : LinearMap.trace ℝ (X d) H.toLinearMap ≤ M)
    (hsub : ∀ ω, f.value (Y ω) ≤ f.value 0)
    (hcap : ∀ ω, CappedQuadraticModel f H (Y ω))
    (hbad : MeasurableSet {ω | ε < ‖f.grad (Y ω)‖})
    (hlaw : Measure.map (fun ω => (Y ω, a ω)) μ =
      Measure.map (fun p : Ω × X d => (Y p.1, p.2)) (μ.prod ν)) :
    ((39 / 125 : ℝ) * ε ^ 2 / M) * μ.real {ω | ε < ‖f.grad (Y ω)‖} ≤
      (∫ ω, f.value (Y ω) ∂μ) -
        ∫ ω, f.value (step f (4 * ε / (5 * M)) (Y ω) (a ω)) ∂μ := by
  let h : ℝ := 4 * ε / (5 * M)
  have hk : Measurable (fun p : X d × X d => f.value (step f h p.1 p.2)) :=
    step_value_joint_measurable f h id measurable_id
  have hpair : Measurable (fun ω => (Y ω, a ω)) := hY.prodMk ha
  have hprod : Measurable (fun p : Ω × X d => (Y p.1, p.2)) :=
    (hY.comp measurable_fst).prodMk measurable_snd
  have heq : (∫ p : Ω × X d, f.value (step f h (Y p.1) p.2) ∂μ.prod ν) =
      ∫ ω, f.value (step f h (Y ω) (a ω)) ∂μ := by
    calc
      _ = ∫ z, f.value (step f h z.1 z.2)
          ∂Measure.map (fun p : Ω × X d => (Y p.1, p.2)) (μ.prod ν) :=
        (integral_map hprod.aemeasurable hk.aestronglyMeasurable).symm
      _ = ∫ z, f.value (step f h z.1 z.2)
          ∂Measure.map (fun ω => (Y ω, a ω)) μ := by rw [hlaw]
      _ = _ := integral_map hpair.aemeasurable hk.aestronglyMeasurable
  have hd := expected_step_product_drift f hgap H μ Y hY ν moments
    hε hM hα htrace hsub hcap hbad
  change _ ≤ (∫ ω, f.value (Y ω) ∂μ) -
    ∫ p : Ω × X d, f.value (step f h (Y p.1) p.2) ∂μ.prod ν at hd
  rw [heq] at hd
  exact hd

end ExactZO.STP
