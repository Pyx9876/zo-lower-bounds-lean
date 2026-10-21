import ExactZO.GaussianDensity
import ExactZO.SphereFoundation
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The actual Gaussian direction and radius have their product law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace ExactZO.Gaussian

/-- A density depending only on a measurable image transports to that image. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (T : α → β) (μ : Measure α) (f : β → ℝ≥0∞)
    (hT : Measurable T) (hf : Measurable f) :
    Measure.map T (μ.withDensity (fun x => f (T x))) =
      (Measure.map T μ).withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hT,
    lintegral_withDensity_eq_lintegral_mul μ
      (f := fun x => f (T x)) (hf.comp hT)
      (g := fun x => g (T x)) (hg.comp hT),
    lintegral_withDensity_eq_lintegral_mul (Measure.map T μ) hf hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map (f := fun y => f y * g y) (hf.mul hg) hT]

/-- A product probability measure is the product of its actual marginals,
even when its initially given factors are not normalized. -/
theorem probability_product_eq_marginals {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (L : Measure (α × β)) [IsProbabilityMeasure L]
    (A : Measure α) (B : Measure β) [SFinite A] [SFinite B]
    (hL : L = A.prod B) :
    L = (Measure.map Prod.fst L).prod (Measure.map Prod.snd L) := by
  letI : IsProbabilityMeasure (Measure.map Prod.fst L) :=
    isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (Measure.map Prod.snd L) :=
    isProbabilityMeasure_map measurable_snd.aemeasurable
  have hmass : A Set.univ * B Set.univ = 1 := by
    calc
      A Set.univ * B Set.univ = (A.prod B) (Set.univ ×ˢ Set.univ) :=
        (Measure.prod_prod _ _).symm
      _ = L Set.univ := by rw [← hL]; simp
      _ = 1 := measure_univ
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [hL, Measure.prod_prod, Measure.map_fst_prod, Measure.map_snd_prod,
    Measure.smul_apply, Measure.smul_apply]
  change A s * B t = (B Set.univ * A s) * (A Set.univ * B t)
  calc
    A s * B t = (A Set.univ * B Set.univ) * (A s * B t) := by rw [hmass, one_mul]
    _ = (B Set.univ * A s) * (A Set.univ * B t) := by ac_rfl


/-- The Gaussian radial weight before multiplication by the polar Jacobian. -/
def polarRadialWeight (d : ℕ) (r : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-r.val ^ 2 / 2))

theorem polarRadialWeight_measurable (d : ℕ) : Measurable (polarRadialWeight d) := by
  unfold polarRadialWeight
  fun_prop

theorem radialGaussianDensity_measurable (d : ℕ) : Measurable (radialGaussianDensity d) := by
  unfold radialGaussianDensity
  fun_prop

/-- The actual density restricted to the nonzero subtype. -/
def nonzeroGaussian (d : ℕ) : Measure ({(0 : X d)}ᶜ : Set (X d)) :=
  (volume.comap ((↑) : ({(0 : X d)}ᶜ : Set (X d)) → X d)).withDensity
    (fun x => radialGaussianDensity d x.val)

theorem map_nonzeroGaussian (d : ℕ) (hd : 0 < d) :
    Measure.map ((↑) : ({(0 : X d)}ᶜ : Set (X d)) → X d) (nonzeroGaussian d) =
      standardGaussian d := by
  rw [nonzeroGaussian,
    map_withDensity_comp _ _ _ measurable_subtype_coe (radialGaussianDensity_measurable d),
    map_comap_subtype_coe (measurableSet_singleton _).compl,
    ← restrict_withDensity (measurableSet_singleton _).compl,
    ← standardGaussian_eq_withDensity]
  apply Measure.restrict_eq_self_of_ae_mem
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using standardGaussian_ae_ne_zero hd

/-- The unnormalized sphere factor supplied by the Haar polar formula. -/
def polarAngularMeasure (d : ℕ) : Measure (X d) :=
  Measure.map ((↑) : Metric.sphere (0 : X d) 1 → X d)
    (volume : Measure (X d)).toSphere

/-- The unnormalized radial factor supplied by the Haar polar formula. -/
def polarRadiusMeasure (d : ℕ) : Measure ℝ :=
  Measure.map ((↑) : Set.Ioi (0 : ℝ) → ℝ)
    ((Measure.volumeIoiPow (Module.finrank ℝ (X d) - 1)).withDensity (polarRadialWeight d))

instance polarAngularMeasure_sfinite (d : ℕ) : SFinite (polarAngularMeasure d) := by
  unfold polarAngularMeasure
  infer_instance

instance polarRadiusMeasure_sfinite (d : ℕ) : SFinite (polarRadiusMeasure d) := by
  unfold polarRadiusMeasure
  infer_instance

/-- Polar transport of the actual nonzero Gaussian produces a product. -/
theorem map_polar_nonzeroGaussian (d : ℕ) :
    Measure.map (homeomorphUnitSphereProd (X d)) (nonzeroGaussian d) =
      (volume : Measure (X d)).toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ (X d) - 1)).withDensity (polarRadialWeight d)) := by
  unfold nonzeroGaussian
  have hden : (fun x : ({(0 : X d)}ᶜ : Set (X d)) => radialGaussianDensity d x.val) =
      (fun x => polarRadialWeight d ((homeomorphUnitSphereProd (X d)) x).2) := rfl
  rw [hden, map_withDensity_comp _ _
    (fun z : Metric.sphere (0 : X d) 1 × Set.Ioi (0 : ℝ) => polarRadialWeight d z.2)
    (homeomorphUnitSphereProd (X d)).measurable
    ((polarRadialWeight_measurable d).comp measurable_snd),
    (volume : Measure (X d)).measurePreserving_homeomorphUnitSphereProd.map_eq,
    ← prod_withDensity_right (polarRadialWeight_measurable d)]

/-- The actual direction-radius joint law is a product of two polar factors. -/
theorem direction_radius_polar_product (d : ℕ) (hd : 0 < d) :
    Measure.map (fun x : X d => (normalizedDirection x, ‖x‖)) (standardGaussian d) =
      (polarAngularMeasure d).prod (polarRadiusMeasure d) := by
  let P : X d → X d × ℝ := fun x => (normalizedDirection x, ‖x‖)
  let i : ({(0 : X d)}ᶜ : Set (X d)) → X d := (↑)
  let j : Metric.sphere (0 : X d) 1 × Set.Ioi (0 : ℝ) → X d × ℝ :=
    Prod.map ((↑) : Metric.sphere (0 : X d) 1 → X d) ((↑) : Set.Ioi (0 : ℝ) → ℝ)
  have hP : Measurable P := normalizedDirection_measurable.prodMk measurable_norm
  have hj : Measurable j := measurable_subtype_coe.prodMap measurable_subtype_coe
  have hcomp : P ∘ i = j ∘ homeomorphUnitSphereProd (X d) := rfl
  change Measure.map P (standardGaussian d) = _
  rw [← map_nonzeroGaussian d hd, Measure.map_map hP measurable_subtype_coe, hcomp,
    ← Measure.map_map hj (homeomorphUnitSphereProd (X d)).measurable,
    map_polar_nonzeroGaussian]
  exact (Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe).symm

/-- The direction of the genuine Gaussian is independent of its radius. -/
theorem direction_radius_product (d : ℕ) (hd : 0 < d) :
    Measure.map (fun x : X d => (normalizedDirection x, ‖x‖)) (standardGaussian d) =
      (sphereGaussian d).prod (Measure.map (fun x : X d => ‖x‖) (standardGaussian d)) := by
  let P : X d → X d × ℝ := fun x => (normalizedDirection x, ‖x‖)
  have hP : Measurable P := normalizedDirection_measurable.prodMk measurable_norm
  letI : IsProbabilityMeasure (Measure.map P (standardGaussian d)) :=
    isProbabilityMeasure_map hP.aemeasurable
  have h := probability_product_eq_marginals
    (Measure.map P (standardGaussian d)) (polarAngularMeasure d) (polarRadiusMeasure d)
    (direction_radius_polar_product d hd)
  rw [Measure.map_map measurable_fst hP, Measure.map_map measurable_snd hP] at h
  exact h

end ExactZO.Gaussian
