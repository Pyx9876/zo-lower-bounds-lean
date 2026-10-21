import ExactZO.SphereSplit

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace ExactZO.Gaussian

instance sphereFirstCoordinateLaw_probability (d : ℕ) :
    IsProbabilityMeasure (sphereFirstCoordinateLaw d) := by
  unfold sphereFirstCoordinateLaw
  exact isProbabilityMeasure_map
    (by fun_prop : Measurable (fun u : X (d + 1) => u 0)).aemeasurable

/-- The actual sphere first coordinate has the dimension-exact second moment. -/
theorem sphereFirstCoordinateLaw_second_moment (d : ℕ) :
    (∫ c : ℝ, c ^ 2 ∂sphereFirstCoordinateLaw d) = 1 / ((d : ℝ) + 1) := by
  rw [sphereFirstCoordinateLaw,
    integral_map (by fun_prop : Measurable (fun u : X (d + 1) => u 0)).aemeasurable
      (by fun_prop : Measurable (fun c : ℝ => c ^ 2)).aestronglyMeasurable]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    sphereGaussian_coordinate_sq_integral (Nat.succ_pos d) (0 : Fin (d + 1))

/-- The actual first coordinate is supported on the interval [-1,1], in square form. -/
theorem sphereFirstCoordinateLaw_ae_sq_le_one (d : ℕ) :
    ∀ᵐ c : ℝ ∂sphereFirstCoordinateLaw d, c ^ 2 ≤ 1 := by
  rw [sphereFirstCoordinateLaw,
    ae_map_iff (by fun_prop : Measurable (fun u : X (d + 1) => u 0)).aemeasurable
      (p := fun c : ℝ => c ^ 2 ≤ 1)
      (isClosed_le (continuous_id.pow 2) continuous_const).measurableSet]
  filter_upwards [sphereGaussian_ae_norm (Nat.succ_pos d)] with u hu
  simpa only [hu, one_pow] using coordinate_sq_le_norm_sq u (0 : Fin (d + 1))

/-- Every fixed orthogonal image has the same sphere decomposition. -/
theorem sphereGaussian_succ_split_linearIsometryEquiv (d : ℕ) (hd : 0 < d)
    (e : X (d + 1) ≃ₗᵢ[ℝ] X (d + 1)) :
    sphereGaussian (d + 1) =
      Measure.map (e ∘ sphereSplitMap d)
        ((sphereFirstCoordinateLaw d).prod (sphereGaussian d)) := by
  have h := congrArg (Measure.map e) (sphereGaussian_succ_split d hd)
  rw [sphereGaussian_map_linearIsometryEquiv,
    Measure.map_map e.continuous.measurable (sphereSplitMap_measurable d)] at h
  exact h

/-- The Gaussian direction law is exactly normalized Euclidean sphere volume. -/
theorem sphereGaussian_eq_normalized_sphere_volume (d : ℕ) (hd : 0 < d) :
    sphereGaussian d = ((polarAngularMeasure d) Set.univ)⁻¹ • polarAngularMeasure d := by
  have hf : sphereGaussian d = (polarRadiusMeasure d Set.univ) • polarAngularMeasure d := by
    have h := congrArg (Measure.map Prod.fst) (direction_radius_polar_product d hd)
    rw [Measure.map_map measurable_fst
      (normalizedDirection_measurable.prodMk measurable_norm), Measure.map_fst_prod] at h
    exact h
  have hmass : polarRadiusMeasure d Set.univ * polarAngularMeasure d Set.univ = 1 := by
    have h := congrArg (fun μ : Measure (X d) => μ Set.univ) hf
    simpa only [measure_univ, Measure.smul_apply, smul_eq_mul] using h.symm
  rw [ENNReal.eq_inv_of_mul_eq_one_left hmass] at hf
  exact hf

end ExactZO.Gaussian
