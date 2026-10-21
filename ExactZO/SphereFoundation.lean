import ExactZO.GaussianProjection
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
M7 sphere foundation and coordinate second moments.

The law below is explicitly the normalized genuine standard Gaussian.  This file
proves rotation invariance, concentration on the unit sphere, and coordinate
second moments.  It does
not claim the independent radial factor or the coordinate product split from
`s4:lem:sphere-split`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace ExactZO.Gaussian

variable {d : ℕ}

/-- A scalar projection evaluates the vector characteristic function. -/
theorem charFun_standardGaussian_projection (t : X d) :
    charFun (standardGaussian d) t =
      charFun (gaussianReal 0 ⟨‖t‖ ^ 2, sq_nonneg ‖t‖⟩) 1 := by
  rw [← projection_law t, charFun_apply_real,
    integral_map (by fun_prop : Measurable (fun x : X d => ⟪t, x⟫_ℝ)).aemeasurable
      (by fun_prop : Continuous (fun x : ℝ => Complex.exp (↑(1 : ℝ) * ↑x * Complex.I))).aestronglyMeasurable]
  simp only [charFun_apply, Complex.ofReal_one, one_mul, real_inner_comm t]

/-- The genuine standard Gaussian is invariant under every orthogonal map. -/
theorem standardGaussian_map_linearIsometryEquiv (e : X d ≃ₗᵢ[ℝ] X d) :
    Measure.map e (standardGaussian d) = standardGaussian d := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map e.continuous.measurable.aemeasurable
    (by fun_prop : Continuous (fun x : X d => Complex.exp (↑⟪x, t⟫_ℝ * Complex.I))).aestronglyMeasurable]
  simp_rw [e.inner_map_eq_flip]
  change charFun (standardGaussian d) (e.symm t) = charFun (standardGaussian d) t
  simp only [charFun_standardGaussian_projection, e.symm.norm_map]

/-- Totalized normalization sends zero to zero; zero has probability zero for `d > 0`. -/
def normalizedDirection (x : X d) : X d := ‖x‖⁻¹ • x

theorem normalizedDirection_measurable : Measurable (@normalizedDirection d) := by
  exact measurable_id.norm.inv.smul measurable_id

theorem normalizedDirection_linearIsometryEquiv
    (e : X d ≃ₗᵢ[ℝ] X d) (x : X d) :
    normalizedDirection (e x) = e (normalizedDirection x) := by
  simp only [normalizedDirection, e.norm_map, e.map_smul]

theorem norm_normalizedDirection {x : X d} (hx : x ≠ 0) :
    ‖normalizedDirection x‖ = 1 := by
  rw [normalizedDirection, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- An explicit Euclidean-valued sphere law, defined from Gaussian normalization. -/
def sphereGaussian (d : ℕ) : Measure (X d) :=
  Measure.map normalizedDirection (standardGaussian d)

instance sphereGaussian_probability (d : ℕ) : IsProbabilityMeasure (sphereGaussian d) := by
  exact isProbabilityMeasure_map normalizedDirection_measurable.aemeasurable

/-- Rotation invariance holds as an equality of actual pushed-forward measures. -/
theorem sphereGaussian_map_linearIsometryEquiv (e : X d ≃ₗᵢ[ℝ] X d) :
    Measure.map e (sphereGaussian d) = sphereGaussian d := by
  unfold sphereGaussian
  rw [Measure.map_map e.continuous.measurable normalizedDirection_measurable]
  have heq : (e ∘ normalizedDirection) = (normalizedDirection ∘ e) := by
    funext x
    exact (normalizedDirection_linearIsometryEquiv e x).symm
  rw [heq, ← Measure.map_map normalizedDirection_measurable e.continuous.measurable,
    standardGaussian_map_linearIsometryEquiv]

/-- Positive-dimensional Gaussian vectors are almost surely nonzero. -/
theorem standardGaussian_ae_ne_zero (hd : 0 < d) :
    ∀ᵐ x ∂standardGaussian d, x ≠ 0 := by
  let i : Fin d := ⟨0, hd⟩
  let g : X d := EuclideanSpace.single i 1
  have hg : ‖g‖ = 1 := by simp [g]
  have hprojection :
      Measure.map (fun x : X d => ⟪g, x⟫_ℝ) (standardGaussian d) = gaussianReal 0 1 := by
    simpa only [hg, one_pow, NNReal.mk_one] using projection_law g
  have hscalar : gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
    gaussianReal_absolutelyContinuous 0 (by norm_num) (measure_singleton (0 : ℝ))
  have hpreimage : standardGaussian d ((fun x : X d => ⟪g, x⟫_ℝ) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply (by fun_prop : Measurable (fun x : X d => ⟪g, x⟫_ℝ))
      (measurableSet_singleton 0), hprojection]
    exact hscalar
  have hzero : standardGaussian d ({0} : Set (X d)) = 0 := by
    refine measure_mono_null ?_ hpreimage
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp
  simpa only [ae_iff, Classical.not_not] using hzero

/-- For positive dimension the normalized law is concentrated on the unit sphere. -/
theorem sphereGaussian_ae_norm (hd : 0 < d) :
    ∀ᵐ x ∂sphereGaussian d, ‖x‖ = 1 := by
  rw [sphereGaussian, ae_map_iff normalizedDirection_measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  filter_upwards [standardGaussian_ae_ne_zero hd] with x hx
  exact norm_normalizedDirection hx

theorem sphereGaussian_ae_mem_sphere (hd : 0 < d) :
    ∀ᵐ x ∂sphereGaussian d, x ∈ Metric.sphere (0 : X d) 1 := by
  simpa only [mem_sphere_zero_iff_norm] using sphereGaussian_ae_norm hd

end ExactZO.Gaussian



/-! Coordinate square moments of the actual normalized Gaussian law. -/
namespace ExactZO.Gaussian
open scoped BigOperators
variable {d : ℕ}

theorem coordinate_sq_sum (x : X d) :
    (∑ i, (x i) ^ 2) = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

theorem coordinate_sq_le_norm_sq (x : X d) (i : Fin d) :
    (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← coordinate_sq_sum]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem sphereGaussian_coordinate_sq_integrable (hd : 0 < d) (i : Fin d) :
    Integrable (fun x : X d => (x i) ^ 2) (sphereGaussian d) := by
  refine (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Measurable (fun x : X d => (x i) ^ 2)).aestronglyMeasurable ?_
  filter_upwards [sphereGaussian_ae_norm hd] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [hx, one_pow] using coordinate_sq_le_norm_sq x i

theorem sphereGaussian_coordinate_sq_integral_eq (i j : Fin d) :
    (∫ x, (x i) ^ 2 ∂sphereGaussian d) =
      ∫ x, (x j) ^ 2 ∂sphereGaussian d := by
  let e : X d ≃ₗᵢ[ℝ] X d :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have he (x : X d) : (e x) i = x j := by
    change x ((Equiv.swap i j).symm i) = x j
    exact congrArg (fun k : Fin d => x k) (Equiv.swap_apply_left i j)
  have h := congrArg (fun ν : Measure (X d) => ∫ x, (x i) ^ 2 ∂ν)
    (sphereGaussian_map_linearIsometryEquiv e)
  dsimp only at h
  rw [integral_map e.continuous.measurable.aemeasurable
    (by fun_prop : Continuous (fun x : X d => (x i) ^ 2)).aestronglyMeasurable] at h
  simpa only [he] using h.symm

theorem sphereGaussian_coordinate_sq_integral (hd : 0 < d) (i : Fin d) :
    (∫ x, (x i) ^ 2 ∂sphereGaussian d) = 1 / (d : ℝ) := by
  have hsum : (∑ j : Fin d, ∫ x, (x j) ^ 2 ∂sphereGaussian d) = 1 := by
    rw [← integral_finset_sum _ (fun j _ => sphereGaussian_coordinate_sq_integrable hd j)]
    calc
      (∫ x, ∑ j : Fin d, (x j) ^ 2 ∂sphereGaussian d) =
          ∫ _x : X d, (1 : ℝ) ∂sphereGaussian d := by
        apply integral_congr_ae
        filter_upwards [sphereGaussian_ae_norm hd] with x hx
        rw [coordinate_sq_sum, hx, one_pow]
      _ = 1 := by simp
  have heq : (d : ℝ) * (∫ x, (x i) ^ 2 ∂sphereGaussian d) = 1 := by
    calc
      (d : ℝ) * (∫ x, (x i) ^ 2 ∂sphereGaussian d) =
          ∑ _j : Fin d, ∫ x, (x i) ^ 2 ∂sphereGaussian d := by simp
      _ = ∑ j : Fin d, ∫ x, (x j) ^ 2 ∂sphereGaussian d := by
        apply Finset.sum_congr rfl
        intro j _
        exact sphereGaussian_coordinate_sq_integral_eq i j
      _ = 1 := hsum
  apply (eq_div_iff (by exact_mod_cast Nat.ne_zero_of_lt hd : (d : ℝ) ≠ 0)).2
  nlinarith

end ExactZO.Gaussian

