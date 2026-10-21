import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Scalar Gaussian moments used by the concrete STP direction law.
The MGF differentiation proofs are adapted from the locally verified library
`PriceAdaptivity/GaussianMoments.lean`; all moment facts are proved here.
-/

noncomputable section
namespace ExactZO.GaussianScalar
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

lemma mgf_formula (m : ℝ) (v : ℝ≥0) :
    mgf id (gaussianReal m v) = fun t => Real.exp (m*t + v*t^2/2) := by
  funext t
  exact mgf_gaussianReal (by simp) t

lemma integrableExpSet_eq_univ (m : ℝ) (v : ℝ≥0) :
    integrableExpSet id (gaussianReal m v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  change Integrable (fun x : ℝ => Real.exp (t*x)) (gaussianReal m v)
  by_contra h
  have hz : mgf id (gaussianReal m v) t = 0 := integral_undef h
  rw [mgf_formula] at hz
  exact Real.exp_ne_zero _ hz

lemma interior_mem (m t : ℝ) (v : ℝ≥0) :
    t ∈ interior (integrableExpSet id (gaussianReal m v)) := by
  rw [integrableExpSet_eq_univ, interior_univ]
  trivial

lemma integrable_pow (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal m v) :=
  integrable_pow_of_mem_interior_integrableExpSet (interior_mem m 0 v) k

lemma mgf_derivative (m t : ℝ) (v : ℝ≥0) :
    HasDerivAt (mgf id (gaussianReal m v))
      (Real.exp (m*t + v*t^2/2) * (m + v*t)) t := by
  rw [mgf_formula]
  convert (((hasDerivAt_id t).const_mul m).add
    (((hasDerivAt_id t).pow 2).const_mul (v : ℝ) |>.div_const 2)).exp using 1 <;>
    simp only [id_eq] <;> ring

lemma first_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ∂gaussianReal m v) = m := by
  have hh := (hasDerivAt_mgf (interior_mem m 0 v)).unique (mgf_derivative m 0 v)
  simpa using hh

lemma deriv_mgf_formula (m : ℝ) (v : ℝ≥0) :
    deriv (mgf id (gaussianReal m v)) =
      fun t => Real.exp (m*t + v*t^2/2) * (m + v*t) := by
  funext t
  exact (mgf_derivative m t v).deriv

lemma second_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal m v) = m^2 + v := by
  have hp := hasDerivAt_iteratedDeriv_mgf (interior_mem m 0 v) 1
  simp only [iteratedDeriv_one, deriv_mgf_formula] at hp
  have hd := ((mgf_derivative m 0 v).mul
    ((hasDerivAt_const (0 : ℝ) m).add ((hasDerivAt_id (0 : ℝ)).const_mul (v : ℝ))))
  rw [mgf_formula] at hd
  have hh := hp.unique hd
  simpa [pow_two] using hh

lemma integrable_abs (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x|) (gaussianReal m v) := by
  simpa only [pow_one, Real.norm_eq_abs] using (integrable_pow m v 1).norm

/-- The elementary half-line integral behind the Gaussian absolute moment. -/
lemma integral_mul_exp_half :
    (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have hr : ((∫ x : ℝ in Set.Ioi 0,
      x * Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℝ) : ℂ) = (2 * (1 / 2 : ℂ))⁻¹ := by
    rw [← integral_complex_ofReal]
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    push_cast
    rfl
  have hr' : ((∫ x : ℝ in Set.Ioi 0,
      x * Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℝ) : ℂ) = (1 : ℝ) := by
    simpa using hr
  exact Complex.ofReal_injective hr'

lemma standard_abs_integral :
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  have heq : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-x ^ 2 / 2) * |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * |x| ^ 2))) := by
    funext x
    rw [sq_abs]
    rw [show -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [heq, integral_const_mul]
  rw [integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)),
    integral_mul_exp_half, mul_one]
  rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr Real.pi_pos
  have ht := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp
  nlinarith

/-- Scaling the standard law gives the absolute first moment at every variance,
including the degenerate law at variance zero. -/
lemma centered_abs_integral (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) =
      Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  have hvar : (⟨(Real.sqrt (v : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) * 1 = v := by
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
    exact Real.sq_sqrt v.coe_nonneg
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ) * x) =
      gaussianReal 0 v := by
    simpa only [mul_zero, hvar] using gaussianReal_map_const_mul
      (μ := 0) (v := 1) (Real.sqrt (v : ℝ))
  rw [← hmap, integral_map (φ := fun x : ℝ => Real.sqrt (v : ℝ) * x)
    (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ))]
  rw [integral_const_mul, standard_abs_integral, mul_comm]

lemma gaussian_alpha_lower : (79 / 100 : ℝ) ≤ Real.sqrt (2 / Real.pi) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_lt_d2]

end ExactZO.GaussianScalar
