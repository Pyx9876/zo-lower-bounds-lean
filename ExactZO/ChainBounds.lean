import ExactZO.ScalarChain
import ExactZO.FiniteDifference
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Quantitative bounds for the actual Appendix A chain differential.

The global Lipschitz proof uses the scalar derivatives at every point, including
junctions. The two-variable link bounds have constants `(36, 4)` and `(4, 4)`;
Young's inequality and list induction then give the Euclidean constant 48.
Thus no unproved piecewise-Hessian premise is used for the global bound.

Reuse: `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` in the pinned
mathlib supplies the scalar mean-value step, `PiLp.norm_sq_eq_of_L2` the
coordinate energy identity, and `norm_fderiv_le_of_lipschitz` the actual
Hessian norm bound. `ExactZO.smooth_taylor_bound` supplies the Taylor bound.
The shared library's `Minimax.OwnedEdge.grad_lipschitz` has a different scalar
construction and constants, so it is not a theorem about this chain.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace ExactZO.ScalarChain

section Differential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linkDifferential_abs_le (a b : E →L[ℝ] ℝ) (x v : E) :
    |linkDifferential a b x v| ≤ 9 * |a v| + |b v| := by
  simp only [linkDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc
    _ ≤ |(-outgoing (a x) (b x)) * a v| + |(-incoming (a x) (b x)) * b v| := abs_add_le _ _
    _ = outgoing (a x) (b x) * |a v| + incoming (a x) (b x) * |b v| := by
      rw [abs_mul, abs_mul, abs_neg, abs_neg,
        abs_of_nonneg (outgoing_bounds _ _).1, abs_of_nonneg (incoming_bounds _ _).1]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (outgoing_bounds (a x) (b x)).2 (abs_nonneg (a v)),
      mul_le_mul_of_nonneg_right (incoming_bounds (a x) (b x)).2 (abs_nonneg (b v))]

theorem linksDifferential_abs_le (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x v : E) :
    |linksDifferential a coords x v| ≤ 9 * |a v| + 10 * (coords.map (fun c => |c v|)).sum := by
  induction coords generalizing a with
  | nil => simp [linksDifferential]
  | cons b tail ih =>
    simp only [linksDifferential, ContinuousLinearMap.add_apply, List.map_cons, List.sum_cons]
    have hl := linkDifferential_abs_le a b x v
    have ht := ih b
    have hh := abs_add_le (linkDifferential a b x v) (linksDifferential b tail x v)
    linarith

theorem chainDifferential_abs_le (coords : List (E →L[ℝ] ℝ)) (x v : E) :
    |chainDifferential coords x v| ≤ 10 * (coords.map (fun c => |c v|)).sum := by
  cases coords with
  | nil => simp [chainDifferential]
  | cons a tail =>
    have ht := linksDifferential_abs_le a tail x v
    have hp : |-(phiD (a x) * a v)| ≤ |a v| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (phiD_bounds _).1]
      nlinarith [mul_le_mul_of_nonneg_right (phiD_bounds (a x)).2 (abs_nonneg (a v))]
    have hh := abs_add_le (-(phiD (a x) * a v)) (linksDifferential a tail x v)
    simp only [chainDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, List.map_cons, List.sum_cons]
    linarith
end Differential

theorem gradient_coord_abs_le (m : ℕ) (x : X m) (i : Fin m) : |gradient m x i| ≤ 10 := by
  rw [gradient_coord]
  have h := chainDifferential_abs_le (coordinateMaps m) x (EuclideanSpace.single i 1)
  simpa [coordinateMaps, List.map_ofFn, List.sum_ofFn, EuclideanSpace.single_apply,
    abs_ite] using h

theorem gradient_norm_le (m : ℕ) (x : X m) : ‖gradient m x‖ ≤ 10 * Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  have hs : (∑ i : Fin m, ‖gradient m x i‖ ^ 2) ≤ 100 * m := by
    calc
      _ ≤ ∑ _i : Fin m, (100 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := gradient_coord_abs_le m x i
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (gradient m x i)]
      _ = _ := by simp; ring
  calc
    _ ≤ Real.sqrt (100 * m) := Real.sqrt_le_sqrt hs
    _ = 10 * Real.sqrt m := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 100), show Real.sqrt (100 : ℝ) = 10 by
        rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]

theorem phi_lipschitz (x y : ℝ) : |phi x - phi y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := phi) (f' := phiD) (C := 1)
    (fun t (_ : t ∈ Set.univ) => (phi_hasDerivAt t).hasDerivWithinAt)
    (fun t (_ : t ∈ Set.univ) => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (phiD_bounds t).1] using (phiD_bounds t).2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem signedGate_lipschitz (x y : ℝ) :
    |(psi (-x) + psi x) - (psi (-y) + psi y)| ≤ 4 * |x - y| := by
  have hd (t : ℝ) : HasDerivAt (fun z => psi (-z) + psi z) (-psiD (-t) + psiD t) t := by
    convert ((psi_hasDerivAt (-t)).comp t (hasDerivAt_id t).neg).add (psi_hasDerivAt t) using 1; simp
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => psi (-z) + psi z) (f' := fun t => -psiD (-t) + psiD t) (C := 4)
    (fun t (_ : t ∈ Set.univ) => (hd t).hasDerivWithinAt)
    (fun t (_ : t ∈ Set.univ) => by
      dsimp only
      rw [Real.norm_eq_abs, abs_le]
      have hp := psiD_bounds t
      have hn := psiD_bounds (-t)
      constructor <;> linarith)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem psiD_signed_lipschitz (x y : ℝ) :
    |psiD (-x) - psiD (-y)| + |psiD x - psiD y| ≤ 16 * |x - y| := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [psiD_flat (show -x ≤ 1 / 2 by linarith), psiD_flat (show -y ≤ 1 / 2 by linarith)]
      simpa using psiD_lipschitz x y
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hp := psiD_lipschitz x 0
      have hn := psiD_lipschitz (-y) 0
      rw [psiD_flat (show -x ≤ 1 / 2 by linarith), psiD_flat (show y ≤ 1 / 2 by linarith)]
      simp only [psiD_zero, sub_zero, abs_of_nonneg (psiD_bounds x).1, abs_of_nonneg hx,
        abs_of_nonneg (psiD_bounds (-y)).1, abs_of_nonneg (neg_nonneg.mpr hy')] at hp hn
      rw [zero_sub, abs_neg, sub_zero, abs_of_nonneg (psiD_bounds (-y)).1,
        abs_of_nonneg (psiD_bounds x).1, abs_of_nonneg (show 0 ≤ x - y by linarith)]
      linarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hp := psiD_lipschitz y 0
      have hn := psiD_lipschitz (-x) 0
      rw [psiD_flat (show x ≤ 1 / 2 by linarith), psiD_flat (show -y ≤ 1 / 2 by linarith)]
      simp only [psiD_zero, sub_zero, abs_of_nonneg (psiD_bounds y).1, abs_of_nonneg hy,
        abs_of_nonneg (psiD_bounds (-x)).1, abs_of_nonneg (neg_nonneg.mpr hx')] at hp hn
      rw [zero_sub, abs_neg, sub_zero, abs_of_nonneg (psiD_bounds (-x)).1,
        abs_of_nonneg (psiD_bounds y).1, abs_of_nonpos (show x - y ≤ 0 by linarith)]
      linarith
    · rw [psiD_flat (show x ≤ 1 / 2 by linarith), psiD_flat (show y ≤ 1 / 2 by linarith)]
      simpa only [sub_self, abs_zero, add_zero, neg_sub_neg, abs_sub_comm] using psiD_lipschitz (-x) (-y)

theorem outgoing_lipschitz_left (a c b : ℝ) :
    |outgoing a b - outgoing c b| ≤ 36 * |a - c| := by
  have hn := mul_le_mul_of_nonneg_left (phi_bounds (-b)).2 (abs_nonneg (psiD (-a) - psiD (-c)))
  have hp := mul_le_mul_of_nonneg_left (phi_bounds b).2 (abs_nonneg (psiD a - psiD c))
  have ht := psiD_signed_lipschitz a c
  calc
    _ = |(psiD (-a) - psiD (-c)) * phi (-b) + (psiD a - psiD c) * phi b| := by congr 1; unfold outgoing; ring
    _ ≤ |psiD (-a) - psiD (-c)| * phi (-b) + |psiD a - psiD c| * phi b := by
      simpa only [abs_mul, abs_of_nonneg (phi_bounds (-b)).1, abs_of_nonneg (phi_bounds b).1] using
        abs_add_le ((psiD (-a) - psiD (-c)) * phi (-b)) ((psiD a - psiD c) * phi b)
    _ ≤ _ := by nlinarith

theorem outgoing_lipschitz_right (a b d : ℝ) :
    |outgoing a b - outgoing a d| ≤ 4 * |b - d| := by
  have hn := mul_le_mul_of_nonneg_left (phi_lipschitz (-b) (-d)) (psiD_bounds (-a)).1
  have hp := mul_le_mul_of_nonneg_left (phi_lipschitz b d) (psiD_bounds a).1
  have ht := mul_le_mul_of_nonneg_right (psiD_signed_sum_bounds a).2 (abs_nonneg (b - d))
  simp only [neg_sub_neg, abs_sub_comm d b] at hn
  calc
    _ = |psiD (-a) * (phi (-b) - phi (-d)) + psiD a * (phi b - phi d)| := by congr 1; unfold outgoing; ring
    _ ≤ psiD (-a) * |phi (-b) - phi (-d)| + psiD a * |phi b - phi d| := by
      simpa only [abs_mul, abs_of_nonneg (psiD_bounds (-a)).1, abs_of_nonneg (psiD_bounds a).1] using
        abs_add_le (psiD (-a) * (phi (-b) - phi (-d))) (psiD a * (phi b - phi d))
    _ ≤ _ := by nlinarith

theorem incoming_lipschitz_left (a c b : ℝ) :
    |incoming a b - incoming c b| ≤ 4 * |a - c| := by
  have ht := signedGate_lipschitz a c
  have hp := phiD_bounds b
  calc
    _ = |(psi (-a) + psi a) - (psi (-c) + psi c)| * phiD b := by
      rw [← abs_of_nonneg hp.1, ← abs_mul]; congr 1; unfold incoming; ring
    _ ≤ _ := by nlinarith [abs_nonneg ((psi (-a) + psi a) - (psi (-c) + psi c))]

theorem incoming_lipschitz_right (a b d : ℝ) :
    |incoming a b - incoming a d| ≤ 4 * |b - d| := by
  have ht := phiD_lipschitz b d
  have hp := psi_signed_sum_bounds a
  calc
    _ = (psi (-a) + psi a) * |phiD b - phiD d| := by
      rw [← abs_of_nonneg hp.1, ← abs_mul]; congr 1; unfold incoming; ring
    _ ≤ _ := by nlinarith [abs_nonneg (phiD b - phiD d)]

theorem outgoing_lipschitz (a b c d : ℝ) :
    |outgoing a b - outgoing c d| ≤ 36 * |a - c| + 4 * |b - d| := by
  exact (abs_sub_le (outgoing a b) (outgoing c b) (outgoing c d)).trans
    (add_le_add (outgoing_lipschitz_left a c b) (outgoing_lipschitz_right c b d))

theorem incoming_lipschitz (a b c d : ℝ) :
    |incoming a b - incoming c d| ≤ 4 * |a - c| + 4 * |b - d| := by
  exact (abs_sub_le (incoming a b) (incoming c b) (incoming c d)).trans
    (add_le_add (incoming_lipschitz_left a c b) (incoming_lipschitz_right c b d))

section Difference
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coordEnergy (coords : List (E →L[ℝ] ℝ)) (v : E) : ℝ :=
  (coords.map (fun c => (c v) ^ 2)).sum

theorem coordEnergy_nonneg (coords : List (E →L[ℝ] ℝ)) (v : E) : 0 ≤ coordEnergy coords v := by
  induction coords with
  | nil => simp [coordEnergy]
  | cons a tail ih => simp only [coordEnergy, List.map_cons, List.sum_cons] at *; positivity

theorem linkDifferential_diff_young (a b : E →L[ℝ] ℝ) (x y v : E) :
    |linkDifferential a b x v - linkDifferential a b y v| ≤
      20 * ((a (x-y)) ^ 2 + (a v) ^ 2) + 4 * ((b (x-y)) ^ 2 + (b v) ^ 2) := by
  have ho := mul_le_mul_of_nonneg_right (outgoing_lipschitz (a x) (b x) (a y) (b y)) (abs_nonneg (a v))
  have hi := mul_le_mul_of_nonneg_right (incoming_lipschitz (a x) (b x) (a y) (b y)) (abs_nonneg (b v))
  have ht : |linkDifferential a b x v - linkDifferential a b y v| ≤
      |outgoing (a x) (b x) - outgoing (a y) (b y)| * |a v| +
      |incoming (a x) (b x) - incoming (a y) (b y)| * |b v| := by
    calc
      _ = |-((outgoing (a x) (b x) - outgoing (a y) (b y)) * a v) +
        -((incoming (a x) (b x) - incoming (a y) (b y)) * b v)| := by
          congr 1
          simp only [linkDifferential, ContinuousLinearMap.add_apply,
            ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
      _ ≤ _ := by
        simpa only [abs_neg, abs_mul] using abs_add_le
          (-((outgoing (a x) (b x) - outgoing (a y) (b y)) * a v))
          (-((incoming (a x) (b x) - incoming (a y) (b y)) * b v))
  have h1 := sq_nonneg (|a x - a y| - |a v|)
  have h2 := sq_nonneg (|b x - b y| - |a v|)
  have h3 := sq_nonneg (|a x - a y| - |b v|)
  have h4 := sq_nonneg (|b x - b y| - |b v|)
  simp only [map_sub]
  nlinarith only [ho, hi, ht, h1, h2, h3, h4, sq_abs (a x-a y), sq_abs (b x-b y),
    sq_abs (a v), sq_abs (b v)]

theorem linksDifferential_diff_young (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ))
    (x y v : E) :
    |linksDifferential a coords x v - linksDifferential a coords y v| ≤
      20 * ((a (x-y)) ^ 2 + (a v) ^ 2) +
      24 * (coordEnergy coords (x-y) + coordEnergy coords v) := by
  induction coords generalizing a with
  | nil => simp only [linksDifferential, ContinuousLinearMap.zero_apply, sub_self, abs_zero,
      coordEnergy, List.map_nil, List.sum_nil, add_zero, mul_zero]; positivity
  | cons b tail ih =>
    have hl := linkDifferential_diff_young a b x y v
    have ht := ih b
    have hh := abs_add_le (linkDifferential a b x v - linkDifferential a b y v)
      (linksDifferential b tail x v - linksDifferential b tail y v)
    simp only [linksDifferential, ContinuousLinearMap.add_apply]
    rw [show linkDifferential a b x v + linksDifferential b tail x v -
      (linkDifferential a b y v + linksDifferential b tail y v) =
      (linkDifferential a b x v - linkDifferential a b y v) +
      (linksDifferential b tail x v - linksDifferential b tail y v) by ring]
    simp only [coordEnergy, List.map_cons, List.sum_cons] at *
    linarith

theorem chainDifferential_diff_young (coords : List (E →L[ℝ] ℝ)) (x y v : E) :
    |chainDifferential coords x v - chainDifferential coords y v| ≤
      24 * (coordEnergy coords (x-y) + coordEnergy coords v) := by
  cases coords with
  | nil => simp [chainDifferential, coordEnergy]
  | cons a tail =>
    have ht := linksDifferential_diff_young a tail x y v
    have hp := mul_le_mul_of_nonneg_right (phiD_lipschitz (a x) (a y)) (abs_nonneg (a v))
    have he := sq_nonneg (|a x-a y| - |a v|)
    have hh := abs_add_le (-((phiD (a x)-phiD (a y))*a v))
      (linksDifferential a tail x v-linksDifferential a tail y v)
    rw [show chainDifferential (a::tail) x v - chainDifferential (a::tail) y v =
      -((phiD (a x)-phiD (a y))*a v) + (linksDifferential a tail x v-linksDifferential a tail y v) by
        simp only [chainDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]; ring]
    simp only [abs_neg, abs_mul] at hh
    simp only [coordEnergy, List.map_cons, List.sum_cons, map_sub] at *
    nlinarith only [ht, hp, he, hh, sq_abs (a x-a y), sq_abs (a v), sq_nonneg (a x-a y), sq_nonneg (a v)]
end Difference

theorem coordEnergy_coordinateMaps (m : ℕ) (v : X m) :
    coordEnergy (coordinateMaps m) v = ‖v‖ ^ 2 := by
  simp only [coordEnergy, coordinateMaps, List.map_ofFn, List.sum_ofFn,
    PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rfl

theorem gradient_inner (m : ℕ) (x v : X m) :
    ⟪gradient m x, v⟫_ℝ = chainDifferential (coordinateMaps m) x v := by
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := X m)

theorem gradient_inner_diff_young (m : ℕ) (x y v : X m) :
    |⟪gradient m x - gradient m y, v⟫_ℝ| ≤ 24 * (‖x-y‖ ^ 2 + ‖v‖ ^ 2) := by
  simpa only [inner_sub_left, gradient_inner, coordEnergy_coordinateMaps] using
    chainDifferential_diff_young (coordinateMaps m) x y v

theorem gradient_lipschitz (m : ℕ) (x y : X m) :
    ‖gradient m x - gradient m y‖ ≤ 48 * ‖x-y‖ := by
  by_cases hxy : x = y
  · subst y; simp
  have hr : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hg : gradient m x = gradient m y
  · rw [hg, sub_self, norm_zero]; positivity
  have hs : 0 < ‖gradient m x-gradient m y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hg)
  let r := ‖x-y‖
  let s := ‖gradient m x-gradient m y‖
  let v := (r/s) • (gradient m x-gradient m y)
  have hv : ‖v‖ = r := by
    change ‖(r/s) • (gradient m x-gradient m y)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.le hs.le)]
    exact div_mul_cancel₀ r (ne_of_gt hs)
  have hi : ⟪gradient m x-gradient m y, v⟫_ℝ = r*s := by
    change ⟪gradient m x-gradient m y, (r/s) • (gradient m x-gradient m y)⟫_ℝ = r*s
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    change r/s * s^2 = r*s
    field_simp
    ring
  have hh := gradient_inner_diff_young m x y v
  rw [hi, abs_of_nonneg (mul_nonneg hr.le hs.le), hv] at hh
  change r * s ≤ 24 * (r^2 + r^2) at hh
  change s ≤ 48 * r
  nlinarith

theorem gradient_lipschitzWith (m : ℕ) : LipschitzWith 48 (gradient m) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using gradient_lipschitz m x y

theorem gradient_continuous (m : ℕ) : Continuous (gradient m) :=
  (gradient_lipschitzWith m).continuous

/-- At every point where the chain gradient has a derivative, this actual
Hessian operator has norm at most 48. This theorem does not claim that the
Hessian exists at the scalar piece junctions. -/
theorem hessian_norm_le (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) : ‖B‖ ≤ 48 := by
  rw [← hB.fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ (gradient_lipschitzWith m)

theorem value_contDiff (m : ℕ) : ContDiff ℝ 1 (value m) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => innerSL ℝ (gradient m x), ?_, value_hasFDerivAt m⟩
  exact (innerSL ℝ).continuous.comp (gradient_continuous m)

theorem objective_smooth (m : ℕ) : Smooth (objective m) 48 := gradient_lipschitz m

theorem objective_smoothClass (n : ℕ) :
    SmoothClass 48 ((9 / 4 : ℝ) * (n + 1 - 1 / 2)) (objective (n+1)) :=
  ⟨objective_smooth (n+1), objective_hasGap n⟩

theorem value_taylor_bound (m : ℕ) (x y : X m) :
    |value m y - value m x - ⟪gradient m x, y-x⟫_ℝ| ≤ 24 * ‖y-x‖ ^ 2 := by
  simpa only [objective, show (48 : ℝ)/2 = 24 by norm_num] using
    smooth_taylor_bound (objective m) (objective_smooth m) x y

/-- The Hessian of the actual scalar chain is symmetric whenever the gradient
has a derivative, without requiring a twice-continuously-differentiable
neighborhood or excluding junctions by hypothesis. -/
theorem hessian_symmetric (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) (v w : X m) :
    ⟪B v, w⟫_ℝ = ⟪v, B w⟫_ℝ := by
  have hd := (innerSL ℝ).hasFDerivAt.comp x hB
  have hh := second_derivative_symmetric (value_hasFDerivAt m) hd v w
  change ⟪B v, w⟫_ℝ = ⟪B w, v⟫_ℝ at hh
  rw [real_inner_comm v (B w)] at hh
  exact hh

/-- An inactive gradient coordinate is a global maximum (equal to zero), so
Fermat's theorem makes the corresponding row of every actual Hessian zero. -/
theorem hessian_row_support (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) (i : Fin m) (hi : 5 / 4 ≤ |x i|) (v : X m) :
    B v i = 0 := by
  have hm : IsLocalMax (fun y : X m => gradient m y i) x := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [gradient_support m x i hi]
    exact gradient_nonpos m y i
  have hd := (EuclideanSpace.proj i).hasFDerivAt.comp x hB
  have hh := hm.hasFDerivAt_eq_zero hd
  exact congrArg (fun f : X m →L[ℝ] ℝ => f v) hh

/-- Retain the strict active coordinates. Equality at a scalar support
endpoint is placed in the inactive part, where the Hessian row is zero. -/
def activePart (m : ℕ) (x v : X m) : X m :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm (fun i => if |x i| < 5 / 4 then v i else 0)

@[simp] theorem activePart_apply (m : ℕ) (x v : X m) (i : Fin m) :
    activePart m x v i = if |x i| < 5 / 4 then v i else 0 := rfl

theorem hessian_apply_activePart (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) (v : X m) : B (activePart m x v) = B v := by
  have hz (w : X m) : ⟪B (v-activePart m x v), w⟫_ℝ = 0 := by
    rw [hessian_symmetric m x B hB, PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : |x i| < 5 / 4
    · simp only [PiLp.sub_apply, activePart_apply, if_pos hi, sub_self, inner_zero_left]
    · rw [hessian_row_support m x B hB i (le_of_not_gt hi)]
      simp
  have hz' : B (v-activePart m x v) = 0 := by
    have hh := hz (B (v-activePart m x v))
    exact inner_self_eq_zero.mp hh
  rw [map_sub, sub_eq_zero] at hz'
  exact hz'.symm

theorem activePart_hessian_apply (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) (v : X m) : activePart m x (B v) = B v := by
  ext i
  rw [activePart_apply]
  split_ifs with hi
  · rfl
  · exact (hessian_row_support m x B hB i (le_of_not_gt hi) v).symm

theorem activePart_norm_le (m : ℕ) (x : X m) :
    ‖activePart m x x‖ ≤ (5/4 : ℝ) * Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  have hs : (∑ i : Fin m, ‖activePart m x x i‖ ^ 2) ≤ (25/16 : ℝ) * m := by
    calc
      _ ≤ ∑ _i : Fin m, (25/16 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [activePart_apply]
        split_ifs with hi
        · rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (x i)]
        · norm_num
      _ = _ := by simp; ring
  calc
    _ ≤ Real.sqrt ((25/16 : ℝ) * m) := Real.sqrt_le_sqrt hs
    _ = (5/4 : ℝ) * Real.sqrt m := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 25/16),
        show Real.sqrt (25/16 : ℝ) = 5/4 by
          rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num]

theorem hessian_mul_norm_le (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) : ‖B x‖ ≤ 60 * Real.sqrt m := by
  rw [← hessian_apply_activePart m x B hB x]
  calc
    _ ≤ ‖B‖ * ‖activePart m x x‖ := B.le_opNorm _
    _ ≤ 48 * ((5/4 : ℝ) * Real.sqrt m) :=
      mul_le_mul (hessian_norm_le m x B hB) (activePart_norm_le m x)
        (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem hessian_inner_abs_le (m : ℕ) (x : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (gradient m) B x) : |⟪x, B x⟫_ℝ| ≤ 75 * m := by
  have he : ⟪x, B x⟫_ℝ = ⟪activePart m x x, B x⟫_ℝ := by
    calc
      _ = ⟪B x, x⟫_ℝ := real_inner_comm _ _
      _ = ⟪B (activePart m x x), x⟫_ℝ := by rw [hessian_apply_activePart m x B hB x]
      _ = _ := hessian_symmetric m x B hB _ _
  rw [he]
  calc
    _ ≤ ‖activePart m x x‖ * ‖B x‖ := abs_real_inner_le_norm _ _
    _ ≤ ((5/4 : ℝ) * Real.sqrt m) * (60 * Real.sqrt m) :=
      mul_le_mul (activePart_norm_le m x) (hessian_mul_norm_le m x B hB)
        (norm_nonneg _) (by positivity)
    _ = 75 * m := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)]

end ExactZO.ScalarChain
