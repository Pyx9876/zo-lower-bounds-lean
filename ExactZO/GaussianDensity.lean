import ExactZO.GaussianProjection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Data.ENNReal.BigOperators

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace ExactZO.Gaussian

/-- The genuine scalar Gaussian PDF multiplied over all coordinates. -/
def coordinatePDFReal (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem coordinatePDFReal_nonneg (d : ℕ) (x : Fin d → ℝ) :
    0 ≤ coordinatePDFReal d x :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

theorem coordinatePDFReal_integrable (d : ℕ) : Integrable (coordinatePDFReal d) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

theorem coordinatePDFReal_measurable (d : ℕ) : Measurable (coordinatePDFReal d) := by
  unfold coordinatePDFReal
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))

/-- This equality is proved on arbitrary measurable rectangles, using the
actual scalar Gaussian densities and finite-product integration. -/
theorem coordinateGaussian_eq_withDensity (d : ℕ) :
    coordinateGaussian d =
      volume.withDensity (fun x => ENNReal.ofReal (coordinatePDFReal d x)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hrect : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hrect,
    ← ofReal_integral_eq_lintegral_ofReal (coordinatePDFReal_integrable d).restrict
      (Filter.Eventually.of_forall (coordinatePDFReal_nonneg d))]
  simp_rw [gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (fun _ => gaussianPDFReal_nonneg 0 1 _))]
  congr 1
  rw [← integral_indicator hrect]
  have hind : (Set.pi Set.univ s).indicator (coordinatePDFReal d) =
      (fun x => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_not_mem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] using hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Set.indicator_of_not_mem hi _
  rw [hind, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_indicator (hs i)

/-- Transporting a density through a measurable equivalence. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hf
      (g := fun a => g (e a)) (hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (Measure.map e μ)
      (f := fun y => f (e.symm y)) (hf.comp e.symm.measurable) hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map (f := fun y => f (e.symm y) * g y)
    ((hf.comp e.symm.measurable).mul hg) e.measurable]
  simp only [Pi.mul_apply, MeasurableEquiv.symm_apply_apply]

/-- Euclidean radial density with the exact scalar normalization. -/
def radialGaussianDensity (d : ℕ) (x : X d) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2))

theorem coordinatePDFReal_radial (d : ℕ) (x : Fin d → ℝ) :
    coordinatePDFReal d x =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖vectorOfCoordinates d x‖ ^ 2 / 2) := by
  have hn : (∑ i, (x i) ^ 2) = ‖vectorOfCoordinates d x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp [PiLp.inner_apply, vectorOfCoordinates, sq]
  simp only [coordinatePDFReal, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [← hn]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The actual product Gaussian transported to `X d` has the usual radial
density with respect to Euclidean volume, including the zero-dimensional case. -/
theorem standardGaussian_eq_withDensity (d : ℕ) :
    standardGaussian d = volume.withDensity (radialGaussianDensity d) := by
  let e : (Fin d → ℝ) ≃ᵐ X d := (EuclideanSpace.measurableEquiv (Fin d)).symm
  have he : (e : (Fin d → ℝ) → X d) = vectorOfCoordinates d := rfl
  have hvol : Measure.map e volume = (volume : Measure (X d)) :=
    (PiLp.volume_preserving_equiv_symm (Fin d)).map_eq
  rw [standardGaussian, coordinateGaussian_eq_withDensity, ← he,
    map_withDensity_equiv e volume _ (coordinatePDFReal_measurable d).ennreal_ofReal, hvol]
  congr 1
  funext x
  rw [coordinatePDFReal_radial]
  change ENNReal.ofReal (_ * Real.exp (-‖e (e.symm x)‖ ^ 2 / 2)) = _
  rw [e.apply_symm_apply]
  rfl


end ExactZO.Gaussian
