import ExactZO.Model
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace ExactZO.Gaussian

/-- The product of `d` genuine scalar standard Gaussian measures. -/
def coordinateGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance coordinateGaussian_probability (d : ℕ) :
    IsProbabilityMeasure (coordinateGaussian d) := by
  unfold coordinateGaussian
  infer_instance

/-- Identify coordinate tuples with Euclidean vectors without changing coordinates. -/
def vectorOfCoordinates (d : ℕ) : (Fin d → ℝ) → X d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm

theorem vectorOfCoordinates_continuous (d : ℕ) : Continuous (vectorOfCoordinates d) :=
  PiLp.continuous_equiv_symm _ _

/-- The standard Gaussian on Euclidean space, including the zero-dimensional space. -/
def standardGaussian (d : ℕ) : Measure (X d) :=
  Measure.map (vectorOfCoordinates d) (coordinateGaussian d)

instance standardGaussian_probability (d : ℕ) :
    IsProbabilityMeasure (standardGaussian d) := by
  unfold standardGaussian
  exact isProbabilityMeasure_map (vectorOfCoordinates_continuous d).measurable.aemeasurable

/-- Finite-product integration, specialized to the actual Gaussian product. -/
theorem integral_coordinate_product {d : ℕ} (f : Fin d → ℝ → ℂ) :
    (∫ x, ∏ i, f i (x i) ∂coordinateGaussian d) =
      ∏ i, ∫ t, f i t ∂gaussianReal 0 1 := by
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) :=
    inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  exact integral_fintype_prod_eq_prod (Fin d) f

/-- Every linear projection of the finite product is a scalar Gaussian. -/
theorem weighted_sum_law {d : ℕ} (c : Fin d → ℝ) :
    Measure.map (fun x : Fin d → ℝ => ∑ i, c i * x i) (coordinateGaussian d) =
      gaussianReal 0 ⟨∑ i, (c i) ^ 2, Finset.sum_nonneg (fun i _ => sq_nonneg (c i))⟩ := by
  apply Measure.ext_of_charFun
  funext t
  have hm : Measurable (fun x : Fin d → ℝ => ∑ i, c i * x i) :=
    (by fun_prop : Continuous (fun x : Fin d → ℝ => ∑ i, c i * x i)).measurable
  rw [charFun_apply_real, integral_map hm.aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))).aestronglyMeasurable]
  have hexp (x : Fin d → ℝ) :
      Complex.exp ((t : ℂ) * (↑(∑ i, c i * x i) : ℂ) * Complex.I) =
        ∏ i, Complex.exp ((↑((t * c i) * x i) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    ext i
    ring
  simp_rw [hexp]
  rw [integral_coordinate_product (fun i y => Complex.exp ((↑((t * c i) * y) : ℂ) * Complex.I))]
  have heach (i : Fin d) :
      (∫ x, Complex.exp ((↑((t * c i) * x) : ℂ) * Complex.I) ∂gaussianReal 0 1) =
        Complex.exp (-((↑(t * c i) : ℂ) ^ 2) / 2) := by
    simpa only [charFun_apply_real, Complex.ofReal_mul, Complex.ofReal_zero, Complex.ofReal_one, NNReal.coe_one,
      mul_zero, zero_mul, one_mul, zero_sub, neg_div] using
      (charFun_gaussianReal (μ := 0) (v := 1) (t * c i))
  simp_rw [heach]
  rw [← Complex.exp_sum, charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_mk,
    Complex.ofReal_sum, Finset.sum_div, Finset.sum_neg_distrib]
  congr 1
  simp only [Finset.sum_mul, neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- The variance of a Euclidean linear projection is its squared norm. -/
theorem projection_law {d : ℕ} (g : X d) :
    Measure.map (fun a => ⟪g, a⟫_ℝ) (standardGaussian d) =
      gaussianReal 0 ⟨‖g‖ ^ 2, sq_nonneg ‖g‖⟩ := by
  rw [standardGaussian, Measure.map_map (by fun_prop : Measurable (fun a : X d => ⟪g, a⟫_ℝ))
    (vectorOfCoordinates_continuous d).measurable]
  have heq : (fun x : Fin d → ℝ => ⟪g, vectorOfCoordinates d x⟫_ℝ) =
      (fun x => ∑ i, g i * x i) := by
    funext x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    change x i * g i = _
    ring
  change Measure.map (fun x => ⟪g, vectorOfCoordinates d x⟫_ℝ) _ = _
  rw [heq, weighted_sum_law]
  congr 2
  change (∑ i, (g i) ^ 2) = ‖g‖ ^ 2
  rw [← real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, sq]

end ExactZO.Gaussian
