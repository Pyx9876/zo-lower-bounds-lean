import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The scalar fundamental theorem for a Lipschitz function, proved by integrating
forward difference quotients and applying dominated convergence. The derivative
need only exist almost everywhere. No finite exceptional-set assumption is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace ExactZO

/-- A Lipschitz scalar function has an integrable derivative on every interval. -/
theorem intervalIntegrable_deriv_of_lipschitz {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (a b : ℝ) : IntervalIntegrable (deriv g) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (K : ℝ)) volume a b).mono_fun'
    (stronglyMeasurable_deriv g).aestronglyMeasurable
  exact Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hg

/-- FTC2 for a scalar Lipschitz function, with its actual almost everywhere derivative. -/
theorem intervalIntegral_deriv_eq_sub_of_lipschitz {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (a b : ℝ) :
    (∫ t in a..b, deriv g t) = g b - g a := by
  let F : ℝ → ℝ → ℝ := fun h t => h⁻¹ * (g (t + h) - g t)
  have hbound : ∀ h : ℝ, 0 < h → ∀ t, ‖F h t‖ ≤ (K : ℝ) := by
    intro h hh t
    have hdiff : ‖g (t + h) - g t‖ ≤ (K : ℝ) * h := by
      simpa only [dist_eq_norm, add_sub_cancel_left, Real.norm_of_nonneg hh.le] using
        hg.dist_le_mul (t + h) t
    calc
      ‖F h t‖ = h⁻¹ * ‖g (t + h) - g t‖ := by
        dsimp [F]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hh.le)]
      _ ≤ h⁻¹ * ((K : ℝ) * h) := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hh.le)
      _ = K := by field_simp
  have hlimit : Tendsto (fun h => ∫ t in a..b, F h t) (𝓝[>] 0)
      (𝓝 (∫ t in a..b, deriv g t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (K : ℝ))
    · apply Eventually.of_forall
      intro h
      have hc : Continuous (F h) := continuous_const.mul
        ((hg.continuous.comp (continuous_id.add continuous_const)).sub hg.continuous)
      exact hc.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact Eventually.of_forall fun t _ => hbound h hh t
    · exact intervalIntegrable_const
    · filter_upwards [hg.ae_differentiableAt (μ := volume)] with t ht _
      simpa only [F, smul_eq_mul] using ht.hasDerivAt.tendsto_slope_zero_right
  have hprimitive (c : ℝ) : HasDerivAt
      (fun h : ℝ => ∫ t in (0 : ℝ)..(c + h), g t) (g c) 0 := by
    simpa only [Function.comp_def, add_zero, mul_one] using
      ((hg.continuous.integral_hasStrictDerivAt 0 (c + 0)).hasDerivAt.comp 0
        ((hasDerivAt_id 0).const_add c))
  have hshift : HasDerivAt (fun h : ℝ => ∫ t in (a + h)..(b + h), g t)
      (g b - g a) 0 := by
    have h := (hprimitive b).sub (hprimitive a)
    have heq (u : ℝ) : ((∫ t in (0 : ℝ)..(b + u), g t) -
        ∫ t in (0 : ℝ)..(a + u), g t) = ∫ t in (a + u)..(b + u), g t :=
      intervalIntegral.integral_interval_sub_left
        (hg.continuous.intervalIntegrable _ _) (hg.continuous.intervalIntegrable _ _)
    simpa only [heq] using h
  have heq (h : ℝ) : (∫ t in a..b, F h t) =
      h⁻¹ * ((∫ t in (a + h)..(b + h), g t) - ∫ t in a..b, g t) := by
    have htrans : IntervalIntegrable (fun t => g (t + h)) volume a b :=
      (hg.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    dsimp [F]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub htrans (hg.continuous.intervalIntegrable _ _),
      intervalIntegral.integral_comp_add_right]
  have hlimit' : Tendsto (fun h => ∫ t in a..b, F h t) (𝓝[>] 0)
      (𝓝 (g b - g a)) := by
    simpa only [heq, add_zero, zero_add, smul_eq_mul] using hshift.tendsto_slope_zero_right
  exact tendsto_nhds_unique hlimit hlimit'

/-- An almost everywhere upper bound on the actual derivative bounds increments. -/
theorem image_sub_le_of_deriv_ae {g : ℝ → ℝ} {K : ℝ≥0} {a b C : ℝ}
    (hab : a ≤ b) (hg : LipschitzWith K g)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → deriv g t ≤ C) :
    g b - g a ≤ C * (b - a) := by
  have hbound : (deriv g) ≤ᵐ[volume.restrict (Icc a b)] (fun _ => C) := by
    change ∀ᵐ t ∂volume.restrict (Icc a b), deriv g t ≤ C
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hd
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_deriv_of_lipschitz hg a b) intervalIntegrable_const hbound
  simpa only [intervalIntegral_deriv_eq_sub_of_lipschitz hg,
    intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi

/-- Derivative data may be given only almost everywhere in the open interval. -/
theorem image_sub_le_of_hasDerivAt_ae {g : ℝ → ℝ} {K : ℝ≥0} {a b C : ℝ}
    (hab : a ≤ b) (hg : LipschitzWith K g)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → ∃ D, HasDerivAt g D t ∧ D ≤ C) :
    g b - g a ≤ C * (b - a) := by
  apply image_sub_le_of_deriv_ae hab hg
  filter_upwards [hd] with t ht htmem
  obtain ⟨D, hD, hDC⟩ := ht htmem
  simpa only [hD.deriv] using hDC

end ExactZO
