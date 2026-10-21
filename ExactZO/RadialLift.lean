/- Reused from lean-library Minimax/RadialLipschitz.lean at a20965a; source SHA256 7e320a203a082ec19704680cf0e4216bd14828e5eac1c291349aa52a313f5639. Namespace/import adaptation only. -/
import ExactZO.RadialCompression
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Function

noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace ExactZO.RadialLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

def lift (φ : ℝ → ℝ) (x : E) : E := (φ ‖x‖ / ‖x‖) • x

theorem lift_zero (φ : ℝ → ℝ) : lift φ (0 : E) = 0 := by simp [lift]

theorem lift_norm (φ : ℝ → ℝ) (h0 : φ 0 = 0) (hp : ∀ r, 0 ≤ r → 0 ≤ φ r) (x : E) :
    ‖lift φ x‖ = φ ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · have hxx : x = 0 := norm_eq_zero.mp hx
    simp [hxx, lift_zero, h0]
  · rw [lift, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hp _ (norm_nonneg _)) (norm_nonneg _))]
    exact div_mul_cancel₀ _ hx

theorem lift_difference (φ : ℝ → ℝ) (h0 : φ 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ r, 0 ≤ r → 0 ≤ φ r)
    (hb : ∀ r, 0 ≤ r → φ r ≤ C * r)
    (hL : ∀ r t, 0 ≤ r → 0 ≤ t → |φ r - φ t| ≤ C * |r - t|)
    (x y : E) : ‖lift φ x - lift φ y‖ ≤ C * ‖x - y‖ := by
  by_cases hx : x = 0
  · subst x
    simpa [lift_zero, norm_neg, lift_norm φ h0 hp] using hb ‖y‖ (norm_nonneg y)
  by_cases hy : y = 0
  · subst y
    simpa [lift_zero, lift_norm φ h0 hp] using hb ‖x‖ (norm_nonneg x)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let a := φ ‖x‖ / ‖x‖
  let b := φ ‖y‖ / ‖y‖
  have ha0 : 0 ≤ a := div_nonneg (hp _ hr.le) hr.le
  have hb0 : 0 ≤ b := div_nonneg (hp _ ht.le) ht.le
  have haC : a ≤ C := (div_le_iff₀ hr).mpr (hb _ hr.le)
  have hbC : b ≤ C := (div_le_iff₀ ht).mpr (hb _ ht.le)
  have har : a * ‖x‖ = φ ‖x‖ := div_mul_cancel₀ _ hr.ne'
  have hbt : b * ‖y‖ = φ ‖y‖ := div_mul_cancel₀ _ ht.ne'
  have hib : 0 ≤ ‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ := by
    linarith [real_inner_le_norm x y]
  have hscalar : (φ ‖x‖ - φ ‖y‖) ^ 2 ≤ C ^ 2 * (‖x‖ - ‖y‖) ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hL ‖x‖ ‖y‖ hr.le ht.le) 2
    simpa only [mul_pow, sq_abs] using hh
  have hab : a * b ≤ C ^ 2 := by
    simpa only [pow_two] using mul_le_mul haC hbC hb0 hC
  have hangular := mul_le_mul_of_nonneg_right hab hib
  have hid : ‖lift φ x - lift φ y‖ ^ 2 =
      (φ ‖x‖ - φ ‖y‖) ^ 2 + 2 * (a * b) * (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) := by
    change ‖a • x - b • y‖ ^ 2 = _
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha0, abs_of_nonneg hb0, real_inner_smul_left, real_inner_smul_right,
      har, hbt]
    rw [← har, ← hbt]
    ring
  have hsq : ‖lift φ x - lift φ y‖ ^ 2 ≤ (C * ‖x - y‖) ^ 2 := by
    rw [hid, mul_pow, norm_sub_sq_real]
    nlinarith [hscalar, hangular]
  nlinarith [norm_nonneg (lift φ x - lift φ y), mul_nonneg hC (norm_nonneg (x - y))]

theorem hasFDerivAt_norm_of_ne_zero {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hh := (Real.hasDerivAt_sqrt (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne').comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hf : (fun y : E => Real.sqrt (‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  simp only [Function.comp_def] at hh
  rw [hf] at hh
  convert hh using 1
  ext u
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
  ring

/-- A scalar radial function constant near zero has its actual radial gradient
at every point, including zero. -/
theorem radial_hasFDerivAt {f φ : ℝ → ℝ}
    (hd : ∀ r, HasDerivAt f (φ r) r) {R : ℝ} (hR : 0 < R)
    (hf : ∀ r, 0 ≤ r → r ≤ R → f r = f 0) (x : E) :
    HasFDerivAt (fun y : E => f ‖y‖) (innerSL ℝ (lift φ x)) x := by
  by_cases hx : x = 0
  · subst x
    rw [lift_zero, map_zero]
    apply (hasFDerivAt_const (f 0) (0 : E)).congr_of_eventuallyEq
    have hh : ∀ᶠ y : E in 𝓝 0, ‖y‖ < R :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hR))
    filter_upwards [hh] with y hy
    exact hf ‖y‖ (norm_nonneg y) hy.le
  · convert (hd ‖x‖).comp_hasFDerivAt x (hasFDerivAt_norm_of_ne_zero hx) using 1
    ext u
    simp only [lift, innerSL_apply, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, smul_eq_mul]
    ring

theorem radial_contDiff_one {f φ : ℝ → ℝ}
    (hd : ∀ r, HasDerivAt f (φ r) r) {R : ℝ} (hR : 0 < R)
    (hf : ∀ r, 0 ≤ r → r ≤ R → f r = f 0)
    (hc : Continuous (lift φ : E → E)) : ContDiff ℝ 1 (fun y : E => f ‖y‖) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨fun x => innerSL ℝ (lift φ x), (innerSL ℝ).continuous.comp hc,
    radial_hasFDerivAt hd hR hf⟩

theorem radial_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {R : ℝ} (hR : 0 < R)
    (hflat : ∀ r, 0 ≤ r → r ≤ R → f r = f 0) : ContDiff ℝ 2 (fun x : E => f ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    have hh : ∀ᶠ y : E in 𝓝 0, ‖y‖ < R :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hR))
    filter_upwards [hh] with y hy
    exact hflat ‖y‖ (norm_nonneg y) hy.le
  · exact hf.contDiffAt.comp x (contDiffAt_norm ℝ hx)

def liftD (φ : ℝ → ℝ) (d : ℝ) (x : E) : E →L[ℝ] E :=
  (φ ‖x‖ / ‖x‖) • ContinuousLinearMap.id ℝ E +
    ((d * ‖x‖ - φ ‖x‖) / ‖x‖ ^ 3) • (innerSL ℝ x).smulRight x

theorem lift_hasFDerivAt {φ : ℝ → ℝ} {d : ℝ} {x : E} (hx : x ≠ 0)
    (hd : HasDerivAt φ d ‖x‖) : HasFDerivAt (lift φ) (liftD φ d x) x := by
  have hr := (norm_pos_iff.mpr hx).ne'
  have hc := (hd.div (hasDerivAt_id ‖x‖) hr).comp_hasFDerivAt x (hasFDerivAt_norm_of_ne_zero hx)
  convert hc.smul (hasFDerivAt_id x) using 1
  ext u
  simp only [liftD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, innerSL_apply,
    smul_eq_mul, mul_one, id_eq]
  simp only [Function.comp_apply, smul_smul]
  apply congrArg (fun z : ℝ => (φ ‖x‖ / ‖x‖) • u + z • x)
  field_simp [hr]
  ring
  simp

theorem scaled_radial_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hm : Monotone f)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R) :
    ConvexOn ℝ Set.univ (fun x : E => C * f (‖x‖ / R)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hn := norm_add_le (a • x) (b • y)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hn
  have hn' : ‖a • x + b • y‖ / R ≤ a * (‖x‖ / R) + b * (‖y‖ / R) := by
    convert div_le_div_of_nonneg_right hn hR.le using 1 <;> ring
  have hc := hf.2 (Set.mem_univ (‖x‖ / R)) (Set.mem_univ (‖y‖ / R)) ha hb hab
  simp only [smul_eq_mul] at hc
  have hh := mul_le_mul_of_nonneg_left ((hm hn').trans hc) hC
  change C * f (‖a • x + b • y‖ / R) ≤ a * (C * f (‖x‖ / R)) + b * (C * f (‖y‖ / R))
  nlinarith

end ExactZO.RadialLift
