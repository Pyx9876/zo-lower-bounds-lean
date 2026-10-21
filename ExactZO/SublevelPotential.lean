import ExactZO.RadialLift
import ExactZO.ScalarGluing
import ExactZO.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The concrete radial potential of Appendix L, equation sl:eq:potential.
The scalar gluing and radial lifting tools are reused with their full hypotheses.
-/
noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace ExactZO.SublevelPotential
open ScalarGluing

def hinge (c t : ℝ) : ℝ := if t ≤ c then 0 else (t - c) ^ 2 / 2

theorem hinge_hasDerivAt (c t : ℝ) :
    HasDerivAt (hinge c) (max (t - c) 0) t := by
  have h : HasDerivAt (ScalarGluing.join c (fun _ => (0 : ℝ)) (fun x => (x-c)^2/2))
      (ScalarGluing.join c (fun _ => (0 : ℝ)) (fun x => x-c) t) t := by
    apply hasDerivAt_join (fun x => hasDerivAt_const x 0)
    · intro x
      convert (((hasDerivAt_id x).sub_const c).pow 2).div_const 2 using 1 <;> dsimp <;> ring
    · simp
    · simp
  convert h using 1
  by_cases ht : t ≤ c
  · simp [ScalarGluing.join, ht, max_eq_right (show t-c ≤ 0 by linarith)]
  · simp [ScalarGluing.join, ht, max_eq_left (show 0 ≤ t-c by linarith)]

def scalar (μ r₀ t : ℝ) : ℝ :=
  μ * t ^ 2 / 2 + (1 - μ) * hinge r₀ t - hinge (r₀ + 2) t

def slope (μ r₀ t : ℝ) : ℝ :=
  μ * min t r₀ + min (max (t-r₀) 0) 2

theorem slope_pieces (μ r₀ t : ℝ) : slope μ r₀ t =
    if t ≤ r₀ then μ*t else if t ≤ r₀+2 then μ*r₀+t-r₀ else μ*r₀+2 := by
  unfold slope
  split_ifs with h h₂
  · rw [min_eq_left h, max_eq_right (by linarith : t-r₀ ≤ 0)]
    norm_num
  · rw [min_eq_right (by linarith : r₀ ≤ t),
      max_eq_left (by linarith : 0 ≤ t-r₀), min_eq_left (by linarith : t-r₀ ≤ 2)]
    ring
  · rw [min_eq_right (by linarith : r₀ ≤ t),
      max_eq_left (by linarith : 0 ≤ t-r₀), min_eq_right (by linarith : 2 ≤ t-r₀)]

theorem slope_algebra (μ r₀ t : ℝ) : slope μ r₀ t =
    μ*t + (1-μ)*max (t-r₀) 0 - max (t-(r₀+2)) 0 := by
  rw [slope_pieces]
  split_ifs with h h₂
  · rw [max_eq_right (by linarith : t-r₀ ≤ 0),
      max_eq_right (by linarith : t-(r₀+2) ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ t-r₀),
      max_eq_right (by linarith : t-(r₀+2) ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ t-r₀),
      max_eq_left (by linarith : 0 ≤ t-(r₀+2))]
    ring

theorem scalar_hasDerivAt (μ r₀ t : ℝ) :
    HasDerivAt (scalar μ r₀) (slope μ r₀ t) t := by
  rw [slope_algebra]
  convert ((((hasDerivAt_id t).pow 2).const_mul μ).div_const 2).add
    ((hinge_hasDerivAt r₀ t).const_mul (1-μ)) |>.sub (hinge_hasDerivAt (r₀+2) t) using 1 <;> dsimp <;> ring

theorem slope_zero {r₀ : ℝ} (hr : 0 ≤ r₀) (μ : ℝ) : slope μ r₀ 0 = 0 := by
  rw [slope_pieces, if_pos hr]
  ring

theorem min_split (r₀ t : ℝ) :
    min t r₀ + min (max (t-r₀) 0) 2 = min t (r₀+2) := by
  by_cases ht : t ≤ r₀
  · rw [min_eq_left ht, max_eq_right (by linarith : t-r₀ ≤ 0),
      min_eq_left (by norm_num : (0:ℝ) ≤ 2), min_eq_left (by linarith : t ≤ r₀+2)]
    ring
  · by_cases h₂ : t ≤ r₀+2
    · rw [min_eq_right (by linarith : r₀ ≤ t), max_eq_left (by linarith : 0 ≤ t-r₀),
        min_eq_left (by linarith : t-r₀ ≤ 2), min_eq_left h₂]
      ring
    · rw [min_eq_right (by linarith : r₀ ≤ t), max_eq_left (by linarith : 0 ≤ t-r₀),
        min_eq_right (by linarith : 2 ≤ t-r₀), min_eq_right (by linarith : r₀+2 ≤ t)]

theorem slope_difference {μ r₀ r s : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hrs : r ≤ s) : 0 ≤ slope μ r₀ s - slope μ r₀ r ∧
      slope μ r₀ s - slope μ r₀ r ≤ s-r := by
  have ha : 0 ≤ min s r₀ - min r r₀ := sub_nonneg.mpr (min_le_min hrs le_rfl)
  have hb : 0 ≤ min (max (s-r₀) 0) 2 - min (max (r-r₀) 0) 2 :=
    sub_nonneg.mpr (min_le_min (max_le_max (by linarith) le_rfl) le_rfl)
  have hmin : min s (r₀+2) - min r (r₀+2) ≤ s-r := by
    by_cases hs : s ≤ r₀+2
    · rw [min_eq_left hs, min_eq_left (hrs.trans hs)]
    · rw [min_eq_right (by linarith : r₀+2 ≤ s)]
      by_cases hr : r ≤ r₀+2
      · rw [min_eq_left hr]; linarith
      · rw [min_eq_right (by linarith : r₀+2 ≤ r)]; linarith
  have he₁ := min_split r₀ s
  have he₂ := min_split r₀ r
  unfold slope
  constructor
  · nlinarith [mul_nonneg hμ ha]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hμ₁) ha]

theorem slope_lipschitz {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (r s : ℝ) :
    |slope μ r₀ r - slope μ r₀ s| ≤ |r-s| := by
  rcases le_total r s with h | h
  · obtain ⟨h₀,h₁⟩ := slope_difference (r₀ := r₀) hμ hμ₁ h
    rw [abs_of_nonpos (by linarith : slope μ r₀ r - slope μ r₀ s ≤ 0),
      abs_of_nonpos (by linarith : r-s ≤ 0)]
    linarith
  · obtain ⟨h₀,h₁⟩ := slope_difference (r₀ := r₀) hμ hμ₁ h
    rw [abs_of_nonneg h₀, abs_of_nonneg (by linarith : 0 ≤ r-s)]
    exact h₁

theorem slope_bounds {μ r₀ t : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hr : 0 ≤ r₀) (ht : 0 ≤ t) : 0 ≤ slope μ r₀ t ∧ slope μ r₀ t ≤ t := by
  simpa [slope_zero hr μ] using (slope_difference (r₀ := r₀) hμ hμ₁ ht)

theorem scalar_zero {r₀ : ℝ} (hr : 0 ≤ r₀) (μ : ℝ) : scalar μ r₀ 0 = 0 := by
  simp [scalar, hinge, hr, show (0:ℝ) ≤ r₀+2 by linarith]

theorem scalar_inner {μ r₀ t : ℝ} (ht : t ≤ r₀) : scalar μ r₀ t = μ*t^2/2 := by
  simp [scalar, hinge, ht, show t ≤ r₀+2 by linarith]

theorem scalar_mono {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (hr : 0 ≤ r₀) :
    MonotoneOn (scalar μ r₀) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x _ => (scalar_hasDerivAt μ r₀ x).continuousAt.continuousWithinAt)
    (fun x _ => (scalar_hasDerivAt μ r₀ x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(scalar_hasDerivAt μ r₀ x).deriv]
  have hx0 : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  exact (slope_bounds hμ hμ₁ hr hx0.le).1

def value {d : ℕ} (μ r₀ : ℝ) (x : X d) : ℝ := scalar μ r₀ ‖x‖
def gradient {d : ℕ} (μ r₀ : ℝ) (x : X d) : X d := RadialLift.lift (slope μ r₀) x

theorem value_hasFDerivAt {d : ℕ} {r₀ : ℝ} (hr : 0 < r₀) (μ : ℝ) (x : X d) :
    HasFDerivAt (value μ r₀) (innerSL ℝ (gradient μ r₀ x)) x := by
  by_cases hx : x = 0
  · subst x
    have h := (hasStrictFDerivAt_norm_sq (0 : X d)).hasFDerivAt.const_mul (μ / 2)
    have he : value μ r₀ =ᶠ[𝓝 (0 : X d)] fun y => μ * ‖y‖^2 / 2 := by
      have hn : ∀ᶠ y : X d in 𝓝 0, ‖y‖ < r₀ :=
        continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
      filter_upwards [hn] with y hy
      exact scalar_inner hy.le
    have heq : (fun y : X d => μ * ‖y‖^2 / 2) = (fun y : X d => (μ / 2) * ‖y‖^2) := by funext y; ring
    rw [heq] at he
    convert h.congr_of_eventuallyEq he using 1 <;> simp [gradient, RadialLift.lift_zero]
  · convert (scalar_hasDerivAt μ r₀ ‖x‖).comp_hasFDerivAt x
      (RadialLift.hasFDerivAt_norm_of_ne_zero hx) using 1
    ext v
    simp only [gradient, RadialLift.lift, innerSL_apply, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, smul_eq_mul]
    ring

theorem gradient_lipschitz {d : ℕ} {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hr : 0 ≤ r₀) (x y : X d) : ‖gradient μ r₀ x-gradient μ r₀ y‖ ≤ ‖x-y‖ := by
  simpa only [one_mul] using RadialLift.lift_difference (slope μ r₀) (slope_zero hr μ)
    (by norm_num : (0:ℝ) ≤ 1) (fun t ht => (slope_bounds hμ hμ₁ hr ht).1)
    (fun t ht => by simpa using (slope_bounds hμ hμ₁ hr ht).2)
    (fun r s _ _ => by simpa using slope_lipschitz (r₀ := r₀) hμ hμ₁ r s) x y

theorem value_nonneg {d : ℕ} {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hr : 0 ≤ r₀) (x : X d) : 0 ≤ value μ r₀ x := by
  have h := scalar_mono hμ hμ₁ hr (show (0:ℝ) ∈ Set.Ici 0 by simp)
    (norm_nonneg x) (norm_nonneg x)
  simpa [value, scalar_zero hr μ] using h

theorem slope_cap {μ r₀ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) :
    slope μ r₀ t ≤ μ*r₀+2 := by
  unfold slope
  exact add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hμ) (min_le_right _ _)

theorem slope_inner {μ r₀ t : ℝ} (ht : t ≤ r₀) : slope μ r₀ t = μ*t := by
  rw [slope_pieces, if_pos ht]

theorem slope_outer {μ r₀ t : ℝ} (ht : r₀+2 ≤ t) : slope μ r₀ t = μ*r₀+2 := by
  rw [slope_pieces]
  split_ifs <;> linarith

theorem gradient_norm {d : ℕ} {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hr : 0 ≤ r₀) (x : X d) : ‖gradient μ r₀ x‖ = slope μ r₀ ‖x‖ :=
  RadialLift.lift_norm _ (slope_zero hr μ) (fun t ht => (slope_bounds hμ hμ₁ hr ht).1) x

theorem gradient_inner {d : ℕ} {μ r₀ : ℝ} {x : X d} (hx : ‖x‖ ≤ r₀) :
    gradient μ r₀ x = μ • x := by
  by_cases h : x = 0
  · simp [h, gradient, RadialLift.lift_zero]
  · simp only [gradient, RadialLift.lift, slope_inner hx]
    rw [mul_div_cancel_right₀ μ (norm_ne_zero_iff.mpr h)]

theorem gradient_hasFDerivAt_inner {d : ℕ} {μ r₀ : ℝ} {x : X d} (hx : ‖x‖ < r₀) :
    HasFDerivAt (gradient μ r₀) (μ • ContinuousLinearMap.id ℝ (X d)) x := by
  have he : gradient μ r₀ =ᶠ[𝓝 x] fun y => μ • y := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact gradient_inner hy.le
  exact ((hasFDerivAt_id x).const_smul μ).congr_of_eventuallyEq he

theorem value_inner {d : ℕ} {μ r₀ : ℝ} {x : X d} (hx : ‖x‖ ≤ r₀) :
    value μ r₀ x = μ*‖x‖^2/2 := scalar_inner hx

theorem value_outside {d : ℕ} {μ r₀ : ℝ} (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hr : 0 ≤ r₀) {x : X d} (hx : r₀ ≤ ‖x‖) : μ*r₀^2/2 ≤ value μ r₀ x := by
  have h := scalar_mono hμ hμ₁ hr hr (norm_nonneg x) hx
  simpa only [scalar_inner (le_refl r₀), value] using h

theorem slope_ratio_bound {μ r₀ t : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r₀) (ht : 0 ≤ t) :
    slope μ r₀ t / t ≤ μ + 2/r₀ := by
  by_cases ht0 : t = 0
  · rw [ht0, div_zero]
    positivity
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hti : t ≤ r₀
  · rw [slope_inner hti, mul_div_cancel_right₀ _ ht0]
    have hp : 0 ≤ 2/r₀ := by positivity
    linarith
  · have hcap := slope_cap (r₀ := r₀) hμ t
    have hrt : r₀ ≤ t := le_of_lt (lt_of_not_ge hti)
    apply (div_le_iff₀ htpos).mpr
    have hd : 2 ≤ (2/r₀)*t := by
      rw [div_mul_eq_mul_div]
      exact
        (show (2:ℝ) ≤ 2*t/r₀ from (le_div_iff₀ hr).mpr (by linarith))
    have hm := mul_le_mul_of_nonneg_left hrt hμ
    nlinarith

end ExactZO.SublevelPotential
