import ExactZO.GaussianPolar

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace ExactZO.Gaussian

/-- Insert a real first coordinate before a Euclidean tail vector. -/
def prependCoordinate (d : ℕ) (p : ℝ × X d) : X (d + 1) :=
  vectorOfCoordinates (d + 1) (Fin.cons p.1 (fun i => p.2 i))

theorem fin_cons_measurable (d : ℕ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : ℝ × (Fin d → ℝ) → ℝ))
  · simpa only [Fin.cons_succ] using (measurable_pi_apply j).comp measurable_snd

theorem prependCoordinate_measurable (d : ℕ) : Measurable (prependCoordinate d) := by
  exact (vectorOfCoordinates_continuous (d + 1)).measurable.comp
    ((fin_cons_measurable d).comp
      (measurable_fst.prodMk ((EuclideanSpace.measurableEquiv (Fin d)).measurable.comp measurable_snd)))

theorem map_fin_cons_gaussian (d : ℕ) :
    Measure.map (fun p : ℝ × (Fin d → ℝ) => Fin.cons p.1 p.2)
      ((gaussianReal 0 1).prod (coordinateGaussian d)) = coordinateGaussian (d + 1) := by
  have h := (MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => gaussianReal 0 1) 0)).map_eq
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, coordinateGaussian] using h

theorem map_prependCoordinate_gaussian (d : ℕ) :
    Measure.map (prependCoordinate d) ((gaussianReal 0 1).prod (standardGaussian d)) =
      standardGaussian (d + 1) := by
  have hp : (gaussianReal 0 1).prod (standardGaussian d) =
      Measure.map (Prod.map id (vectorOfCoordinates d))
        ((gaussianReal 0 1).prod (coordinateGaussian d)) := by
    simpa only [Measure.map_id, standardGaussian] using
      (Measure.map_prod_map (gaussianReal 0 1) (coordinateGaussian d)
        measurable_id (vectorOfCoordinates_continuous d).measurable)
  rw [hp, Measure.map_map (prependCoordinate_measurable d)
    (measurable_id.prodMap (vectorOfCoordinates_continuous d).measurable)]
  have hcomp : prependCoordinate d ∘ Prod.map id (vectorOfCoordinates d) =
      vectorOfCoordinates (d + 1) ∘ (fun p : ℝ × (Fin d → ℝ) => Fin.cons p.1 p.2) := rfl
  rw [hcomp, ← Measure.map_map (vectorOfCoordinates_continuous (d + 1)).measurable
    (fin_cons_measurable d), map_fin_cons_gaussian]
  rfl

/-- The first-coordinate marginal of the actual sphere law. -/
def sphereFirstCoordinateLaw (d : ℕ) : Measure ℝ :=
  Measure.map (fun u : X (d + 1) => u 0) (sphereGaussian (d + 1))

/-- The classical sphere reconstruction map, with a total square root. -/
def sphereSplitMap (d : ℕ) (p : ℝ × X d) : X (d + 1) :=
  prependCoordinate d (p.1, Real.sqrt (1 - p.1 ^ 2) • p.2)

theorem sphereSplitMap_measurable (d : ℕ) : Measurable (sphereSplitMap d) := by
  unfold sphereSplitMap
  apply (prependCoordinate_measurable d).comp
  fun_prop

theorem prependCoordinate_sq_norm (d : ℕ) (a : ℝ) (x : X d) :
    ‖prependCoordinate d (a, x)‖ ^ 2 = a ^ 2 + ‖x‖ ^ 2 := by
  rw [← coordinate_sq_sum, Fin.sum_univ_succ]
  change a ^ 2 + ∑ i : Fin d, (x i) ^ 2 = _
  rw [coordinate_sq_sum]

theorem normalized_prepend_eq_split (d : ℕ) (a : ℝ) (x : X d) (hx : x ≠ 0) :
    normalizedDirection (prependCoordinate d (a, x)) =
      sphereSplitMap d (a / Real.sqrt (a ^ 2 + ‖x‖ ^ 2), normalizedDirection x) := by
  let s := Real.sqrt (a ^ 2 + ‖x‖ ^ 2)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : 0 ≤ a ^ 2 + ‖x‖ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a])
  have hsq : s ^ 2 = a ^ 2 + ‖x‖ ^ 2 := Real.sq_sqrt ht
  have hn : ‖prependCoordinate d (a, x)‖ = s := by
    have hp := prependCoordinate_sq_norm d a x
    nlinarith [norm_nonneg (prependCoordinate d (a, x))]
  have hratio : 1 - (a / s) ^ 2 = (‖x‖ / s) ^ 2 := by
    field_simp
    nlinarith
  have hroot : Real.sqrt (1 - (a / s) ^ 2) = ‖x‖ / s := by
    rw [hratio, Real.sqrt_sq (div_nonneg hr.le hs.le)]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change ‖prependCoordinate d (a, x)‖⁻¹ * a = a / s
    rw [hn]
    ring
  · change ‖prependCoordinate d (a, x)‖⁻¹ * x j =
      Real.sqrt (1 - (a / s) ^ 2) * (‖x‖⁻¹ * x j)
    rw [hn, hroot]
    field_simp
    ring


end ExactZO.Gaussian

namespace ExactZO.Gaussian

/-- The actual Gaussian norm marginal. -/
def gaussianRadiusLaw (d : ℕ) : Measure ℝ :=
  Measure.map (fun x : X d => ‖x‖) (standardGaussian d)

instance gaussianRadiusLaw_probability (d : ℕ) : IsProbabilityMeasure (gaussianRadiusLaw d) := by
  exact isProbabilityMeasure_map measurable_norm.aemeasurable

/-- Scalar coordinate as a ratio of one coordinate and a tail radius. -/
def gaussianCoordinateRatio (p : ℝ × ℝ) : ℝ :=
  p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

theorem gaussianCoordinateRatio_measurable : Measurable gaussianCoordinateRatio := by
  unfold gaussianCoordinateRatio
  fun_prop

/-- An intermediate law; later identified with the actual sphere coordinate. -/
def gaussianRatioLaw (d : ℕ) : Measure ℝ :=
  Measure.map gaussianCoordinateRatio ((gaussianReal 0 1).prod (gaussianRadiusLaw d))

/-- Joint first Gaussian coordinate, tail radius, and tail direction. -/
def gaussianTriple (d : ℕ) (z : ℝ × X d) : (ℝ × ℝ) × X d :=
  ((z.1, ‖z.2‖), normalizedDirection z.2)

theorem gaussianTriple_measurable (d : ℕ) : Measurable (gaussianTriple d) := by
  exact (measurable_fst.prodMk (measurable_norm.comp measurable_snd)).prodMk
    (normalizedDirection_measurable.comp measurable_snd)

def gaussianRatioDirection (d : ℕ) (z : ℝ × X d) : ℝ × X d :=
  (gaussianCoordinateRatio (z.1, ‖z.2‖), normalizedDirection z.2)

theorem gaussianRatioDirection_measurable (d : ℕ) : Measurable (gaussianRatioDirection d) := by
  exact (gaussianCoordinateRatio_measurable.comp
    (measurable_fst.prodMk (measurable_norm.comp measurable_snd))).prodMk
    (normalizedDirection_measurable.comp measurable_snd)

theorem radius_direction_law (d : ℕ) (hd : 0 < d) :
    Measure.map (fun x : X d => (‖x‖, normalizedDirection x)) (standardGaussian d) =
      (gaussianRadiusLaw d).prod (sphereGaussian d) := by
  have h := congrArg (Measure.map Prod.swap) (direction_radius_product d hd)
  rw [Measure.map_map measurable_swap
    (normalizedDirection_measurable.prodMk measurable_norm), Measure.prod_swap] at h
  exact h

theorem gaussianTriple_law (d : ℕ) (hd : 0 < d) :
    Measure.map (gaussianTriple d) ((gaussianReal 0 1).prod (standardGaussian d)) =
      ((gaussianReal 0 1).prod (gaussianRadiusLaw d)).prod (sphereGaussian d) := by
  have hp : Measure.map
      (fun z : ℝ × X d => (z.1, (‖z.2‖, normalizedDirection z.2)))
      ((gaussianReal 0 1).prod (standardGaussian d)) =
        (gaussianReal 0 1).prod ((gaussianRadiusLaw d).prod (sphereGaussian d)) := by
    simpa only [Measure.map_id, radius_direction_law d hd] using
      (Measure.map_prod_map (gaussianReal 0 1) (standardGaussian d) measurable_id
        (measurable_norm.prodMk normalizedDirection_measurable)).symm
  let e : (ℝ × ℝ) × X d ≃ᵐ ℝ × (ℝ × X d) := MeasurableEquiv.prodAssoc
  calc
    Measure.map (gaussianTriple d) ((gaussianReal 0 1).prod (standardGaussian d)) =
        Measure.map e.symm (Measure.map
          (fun z : ℝ × X d => (z.1, (‖z.2‖, normalizedDirection z.2)))
          ((gaussianReal 0 1).prod (standardGaussian d))) := by
      rw [Measure.map_map (f := fun z : ℝ × X d => (z.1, (‖z.2‖, normalizedDirection z.2)))
        e.symm.measurable
        (measurable_fst.prodMk ((measurable_norm.comp measurable_snd).prodMk
          (normalizedDirection_measurable.comp measurable_snd)))]
      rfl
    _ = Measure.map e.symm
        ((gaussianReal 0 1).prod ((gaussianRadiusLaw d).prod (sphereGaussian d))) := by rw [hp]
    _ = _ := (MeasurePreserving.symm e
      (measurePreserving_prodAssoc (gaussianReal 0 1) (gaussianRadiusLaw d) (sphereGaussian d))).map_eq

theorem gaussianRatioDirection_law (d : ℕ) (hd : 0 < d) :
    Measure.map (gaussianRatioDirection d) ((gaussianReal 0 1).prod (standardGaussian d)) =
      (gaussianRatioLaw d).prod (sphereGaussian d) := by
  calc
    Measure.map (gaussianRatioDirection d) ((gaussianReal 0 1).prod (standardGaussian d)) =
        Measure.map (Prod.map gaussianCoordinateRatio id)
          (Measure.map (gaussianTriple d) ((gaussianReal 0 1).prod (standardGaussian d))) := by
      rw [Measure.map_map (gaussianCoordinateRatio_measurable.prodMap measurable_id)
        (gaussianTriple_measurable d)]
      rfl
    _ = Measure.map (Prod.map gaussianCoordinateRatio id)
        (((gaussianReal 0 1).prod (gaussianRadiusLaw d)).prod (sphereGaussian d)) := by
      rw [gaussianTriple_law d hd]
    _ = _ := by
      simpa only [Measure.map_id, gaussianRatioLaw] using
        (Measure.map_prod_map ((gaussianReal 0 1).prod (gaussianRadiusLaw d)) (sphereGaussian d)
          gaussianCoordinateRatio_measurable measurable_id).symm

theorem sphereGaussian_succ_ratio_reconstruction (d : ℕ) (hd : 0 < d) :
    sphereGaussian (d + 1) =
      Measure.map (sphereSplitMap d) ((gaussianRatioLaw d).prod (sphereGaussian d)) := by
  have hne : ∀ᵐ z ∂((gaussianReal 0 1).prod (standardGaussian d)), z.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae (standardGaussian_ae_ne_zero hd)
  have hae : (normalizedDirection ∘ prependCoordinate d) =ᵐ[
      (gaussianReal 0 1).prod (standardGaussian d)]
        (sphereSplitMap d ∘ gaussianRatioDirection d) := by
    filter_upwards [hne] with z hz
    exact normalized_prepend_eq_split d z.1 z.2 hz
  rw [sphereGaussian, ← map_prependCoordinate_gaussian,
    Measure.map_map normalizedDirection_measurable (prependCoordinate_measurable d),
    Measure.map_congr hae,
    ← Measure.map_map (sphereSplitMap_measurable d) (gaussianRatioDirection_measurable d),
    gaussianRatioDirection_law d hd]

theorem sphereFirstCoordinateLaw_eq_ratio (d : ℕ) (hd : 0 < d) :
    sphereFirstCoordinateLaw d = gaussianRatioLaw d := by
  rw [sphereFirstCoordinateLaw, sphereGaussian_succ_ratio_reconstruction d hd,
    Measure.map_map (by fun_prop : Measurable (fun u : X (d + 1) => u 0))
      (sphereSplitMap_measurable d)]
  change Measure.map Prod.fst ((gaussianRatioLaw d).prod (sphereGaussian d)) = _
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The sphere law splits into its actual first coordinate and an independent
lower-dimensional sphere direction, with the exact square-root reconstruction. -/
theorem sphereGaussian_succ_split (d : ℕ) (hd : 0 < d) :
    sphereGaussian (d + 1) =
      Measure.map (sphereSplitMap d) ((sphereFirstCoordinateLaw d).prod (sphereGaussian d)) := by
  rw [sphereFirstCoordinateLaw_eq_ratio d hd]
  exact sphereGaussian_succ_ratio_reconstruction d hd

/-- The actual Gaussian ratio and tail direction have the required product law. -/
theorem ratio_direction_law (d : ℕ) (hd : 0 < d) :
    Measure.map
      (fun z : ℝ × X d =>
        (z.1 / Real.sqrt (z.1 ^ 2 + ‖z.2‖ ^ 2), normalizedDirection z.2))
      ((gaussianReal 0 1).prod (standardGaussian d)) =
        (sphereFirstCoordinateLaw d).prod (sphereGaussian d) := by
  rw [sphereFirstCoordinateLaw_eq_ratio d hd]
  exact gaussianRatioDirection_law d hd


end ExactZO.Gaussian
