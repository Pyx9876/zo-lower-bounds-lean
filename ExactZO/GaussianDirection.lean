import ExactZO.GaussianProjection
import ExactZO.GaussianScalar
import ExactZO.STPDescent
import ExactZO.SubspaceBudget

/-! Exact moments of the genuine Euclidean standard Gaussian.
Projection laws supply integrability as well as values; quadratic moments are
obtained by polarization and a finite orthonormal basis expansion. -/
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ExactZO.Gaussian

variable {d : ℕ}

theorem projection_power_integrable (g : X d) (k : ℕ) :
    Integrable (fun a => ⟪g, a⟫_ℝ ^ k) (standardGaussian d) := by
  have hi := GaussianScalar.integrable_pow 0 ⟨‖g‖ ^ 2, sq_nonneg _⟩ k
  rw [← projection_law g] at hi
  exact hi.comp_aemeasurable (by fun_prop : Measurable (fun a : X d => ⟪g, a⟫_ℝ)).aemeasurable

theorem projection_abs_integrable (g : X d) :
    Integrable (fun a => |⟪g, a⟫_ℝ|) (standardGaussian d) := by
  simpa only [pow_one, Real.norm_eq_abs] using (projection_power_integrable g 1).norm

theorem projection_abs_integral (g : X d) :
    (∫ a, |⟪g, a⟫_ℝ| ∂standardGaussian d) = Real.sqrt (2 / Real.pi) * ‖g‖ := by
  have hi := GaussianScalar.centered_abs_integral ⟨‖g‖ ^ 2, sq_nonneg _⟩
  rw [← projection_law g, integral_map (by fun_prop : Measurable (fun a : X d => ⟪g, a⟫_ℝ)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => |x|)).aestronglyMeasurable] at hi
  simpa only [NNReal.coe_mk, Real.sqrt_sq (norm_nonneg _)] using hi

theorem projection_second_integral (g : X d) :
    (∫ a, ⟪g, a⟫_ℝ ^ 2 ∂standardGaussian d) = ‖g‖ ^ 2 := by
  have hi := GaussianScalar.second_moment 0 ⟨‖g‖ ^ 2, sq_nonneg _⟩
  rw [← projection_law g, integral_map (by fun_prop : Measurable (fun a : X d => ⟪g, a⟫_ℝ)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => x ^ 2)).aestronglyMeasurable] at hi
  simpa using hi

/-- Polarization supplies integrability without assuming independent projections. -/
theorem projection_product_integrable (g h : X d) :
    Integrable (fun a => ⟪g, a⟫_ℝ * ⟪h, a⟫_ℝ) (standardGaussian d) := by
  have hi := ((projection_power_integrable (g + h) 2).sub
    ((projection_power_integrable g 2).add (projection_power_integrable h 2))).div_const 2
  convert hi using 1
  ext a
  change ⟪g, a⟫_ℝ * ⟪h, a⟫_ℝ = (⟪g + h, a⟫_ℝ ^ 2 - (⟪g, a⟫_ℝ ^ 2 + ⟪h, a⟫_ℝ ^ 2)) / 2
  rw [inner_add_left]
  ring

theorem projection_product_integral (g h : X d) :
    (∫ a, ⟪g, a⟫_ℝ * ⟪h, a⟫_ℝ ∂standardGaussian d) = ⟪g, h⟫_ℝ := by
  have heq : (fun a : X d => ⟪g, a⟫_ℝ * ⟪h, a⟫_ℝ) =
      fun a => (⟪g + h, a⟫_ℝ ^ 2 - (⟪g, a⟫_ℝ ^ 2 + ⟪h, a⟫_ℝ ^ 2)) / 2 := by
    funext a
    rw [inner_add_left]
    ring
  have hs := integral_sub (projection_power_integrable (g + h) 2)
    ((projection_power_integrable g 2).add (projection_power_integrable h 2))
  have ha := integral_add (projection_power_integrable g 2) (projection_power_integrable h 2)
  simp only [Pi.add_apply, Pi.sub_apply] at hs ha
  rw [heq, integral_div, hs, ha, projection_second_integral,
    projection_second_integral, projection_second_integral, norm_add_sq_real]
  ring

/-- This identity holds for every continuous linear map, without symmetry or positivity. -/
theorem quadratic_basis_expansion (b : OrthonormalBasis (Fin d) ℝ (X d))
    (H : X d →L[ℝ] X d) (a : X d) :
    ⟪a, H a⟫_ℝ = ∑ i, ⟪b i, a⟫_ℝ * ⟪H.adjoint (b i), a⟫_ℝ := by
  rw [← b.sum_inner_mul_inner a (H a)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm a (b i)]

theorem quadratic_integrable (H : X d →L[ℝ] X d) :
    Integrable (fun a => ⟪a, H a⟫_ℝ) (standardGaussian d) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  simp_rw [quadratic_basis_expansion b H]
  exact integrable_finset_sum _ (fun i _ => projection_product_integrable (b i) (H.adjoint (b i)))

theorem quadratic_integral (H : X d →L[ℝ] X d) :
    (∫ a, ⟪a, H a⟫_ℝ ∂standardGaussian d) = LinearMap.trace ℝ (X d) H.toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  simp_rw [quadratic_basis_expansion b H]
  rw [integral_finset_sum _ (fun i _ => projection_product_integrable (b i) (H.adjoint (b i))),
    SubspaceBudget.trace_eq_sum_quadratic b H]
  apply Finset.sum_congr rfl
  intro i _
  rw [projection_product_integral, ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_comm _ _

/-- The STP moment interface is discharged by an explicit Gaussian probability law. -/
theorem directionMoments (d : ℕ) :
    STP.DirectionMoments (standardGaussian d) (Real.sqrt (2 / Real.pi)) where
  probability := inferInstance
  abs_integrable := projection_abs_integrable
  abs_integral := projection_abs_integral
  quadratic_integrable := quadratic_integrable
  quadratic_integral := quadratic_integral

end ExactZO.Gaussian
