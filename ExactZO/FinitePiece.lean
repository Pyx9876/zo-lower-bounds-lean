import ExactZO.FiniteDifference
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Finite exceptional points are eliminated by induction, splitting the interval
at each exceptional point and using continuity at every endpoint. The smooth
open pieces use mathlib's `Convex.image_sub_le_mul_sub_of_deriv_le`.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace ExactZO

/-- A derivative upper bound extends across finitely many exceptional points
when the function is continuous, including at the junctions. -/
theorem image_sub_le_of_hasDerivAt_off_finset (S : Finset ℝ) {φ : ℝ → ℝ}
    {a b C : ℝ} (hab : a ≤ b) (hc : ContinuousOn φ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ S → ∃ D, HasDerivAt φ D t ∧ D ≤ C) :
    φ b - φ a ≤ C * (b - a) := by
  classical
  induction S using Finset.induction_on generalizing a b with
  | empty =>
      apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc
      · intro t ht
        rw [interior_Icc] at ht
        obtain ⟨D, hD, _⟩ := hd t ht (by simp)
        exact hD.differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        obtain ⟨D, hD, hbound⟩ := hd t ht (by simp)
        rwa [hD.deriv]
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩
      · exact hab
  | @insert c S hcS ih =>
      by_cases hcin : c ∈ Ioo a b
      · have hac : φ c - φ a ≤ C * (c - a) := by
          apply ih hcin.1.le (hc.mono (Icc_subset_Icc le_rfl hcin.2.le))
          intro t ht htS
          apply hd t ⟨ht.1, ht.2.trans hcin.2⟩
          simp only [Finset.mem_insert, not_or]
          exact ⟨ne_of_lt ht.2, htS⟩
        have hcb : φ b - φ c ≤ C * (b - c) := by
          apply ih hcin.2.le (hc.mono (Icc_subset_Icc hcin.1.le le_rfl))
          intro t ht htS
          apply hd t ⟨hcin.1.trans ht.1, ht.2⟩
          simp only [Finset.mem_insert, not_or]
          exact ⟨ne_of_gt ht.1, htS⟩
        linarith
      · apply ih hab hc
        intro t ht htS
        apply hd t ht
        simp only [Finset.mem_insert, not_or]
        refine ⟨?_, htS⟩
        intro heq
        exact hcin (heq ▸ ht)

/-- Vector-valued version, obtained by testing against the endpoint difference. -/
theorem norm_sub_le_of_hasDerivAt_off_finset {d : ℕ} (S : Finset ℝ)
    {g : ℝ → X d} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hc : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ S → ∃ w, HasDerivAt g w t ∧ ‖w‖ ≤ C) :
    ‖g b - g a‖ ≤ C * (b - a) := by
  let v := g b - g a
  have hscalar : ⟪v, g b⟫_ℝ - ⟪v, g a⟫_ℝ ≤ (‖v‖ * C) * (b - a) := by
    apply image_sub_le_of_hasDerivAt_off_finset S hab
      (continuousOn_const.inner hc)
    intro t ht htS
    obtain ⟨w, hder, hbound⟩ := hd t ht htS
    refine ⟨⟪v, w⟫_ℝ, ?_, ?_⟩
    · simpa only [Function.comp_def, innerSL_apply] using
        (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hder
    · exact (real_inner_le_norm v w).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg _))
  rw [← inner_sub_right] at hscalar
  change ⟪v, v⟫_ℝ ≤ _ at hscalar
  rw [real_inner_self_eq_norm_sq] at hscalar
  have hnonneg : 0 ≤ C * (b - a) := mul_nonneg hC (sub_nonneg.mpr hab)
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv]
    exact hnonneg
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    change ‖v‖ ≤ _
    nlinarith

/-- The precise linewise derivative hypotheses used by finite-piece transfer.
Only the directional quadratic comparison is needed; symmetric-matrix Loewner
bounds from the paper imply it. No differentiability is imposed at the finite
set of junctions, or at the endpoints. -/
def FinitePieceAlong {d : ℕ} (f : Objective d) (L : ℝ)
    (H : X d →L[ℝ] X d) (x v : X d) : Prop :=
  ∃ S : Finset ℝ, ∃ B : ℝ → (X d →L[ℝ] X d),
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ S →
      HasDerivAt (fun u => f.grad (x + u • v)) (B t v) t ∧
        ‖B t‖ ≤ L ∧ ⟪v, B t v⟫_ℝ ≤ ⟪v, H v⟫_ℝ

/-- A finite exceptional set leaves a regular interior point, so the operator
norm budget itself implies nonnegativity. -/
theorem finitePieceAlong_nonneg {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {x v : X d} (hp : FinitePieceAlong f L H x v) : 0 ≤ L := by
  obtain ⟨S, B, hp⟩ := hp
  obtain ⟨t, ht, htS⟩ := (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_not_mem_finite
    S.finite_toSet
  exact (norm_nonneg (B t)).trans (hp t ht htS).2.1

theorem finitePieceAlong_gradient_norm {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {x v : X d} (hL : 0 ≤ L)
    (hc : Continuous f.grad) (hp : FinitePieceAlong f L H x v) :
    ‖f.grad (x + v) - f.grad x‖ ≤ L * ‖v‖ := by
  obtain ⟨S, B, hp⟩ := hp
  have hline : Continuous (fun t : ℝ => f.grad (x + t • v)) :=
    hc.comp (by fun_prop)
  have h := norm_sub_le_of_hasDerivAt_off_finset S (show (0 : ℝ) ≤ 1 by norm_num)
    (mul_nonneg hL (norm_nonneg v)) hline.continuousOn ?_
  · simpa using h
  · intro t ht htS
    obtain ⟨hder, hnorm, _⟩ := hp t ht htS
    exact ⟨B t v, hder, (B t).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))⟩

/-- Directional gradient growth at every time, not only at the endpoint. -/
theorem finitePieceAlong_directional {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {x v : X d}
    (hc : Continuous f.grad) (hp : FinitePieceAlong f L H x v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ⟪v, f.grad (x + t • v) - f.grad x⟫_ℝ ≤ t * ⟪v, H v⟫_ℝ := by
  obtain ⟨S, B, hp⟩ := hp
  have hline : Continuous (fun t : ℝ => ⟪v, f.grad (x + t • v)⟫_ℝ) :=
    continuous_const.inner (hc.comp (by fun_prop))
  have h := image_sub_le_of_hasDerivAt_off_finset S (C := ⟪v, H v⟫_ℝ) ht.1 hline.continuousOn ?_
  · simpa [inner_sub_right, mul_comm] using h
  · intro u hu huS
    obtain ⟨hder, _, hupper⟩ := hp u ⟨hu.1, hu.2.trans_le ht.2⟩ huS
    refine ⟨⟪v, B u v⟫_ℝ, ?_, hupper⟩
    simpa only [Function.comp_def, innerSL_apply] using
      (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt u hder

/-- The fixed quadratic upper model follows by a second scalar comparison,
now applied to the actual value function along the line. -/
theorem finitePieceAlong_quadraticUpper {d : ℕ} {f : Objective d} {L : ℝ}
    {H : X d →L[ℝ] X d} {x v : X d}
    (hc : Continuous f.grad) (hp : FinitePieceAlong f L H x v) :
    QuadraticUpper f H x (x + v) := by
  let A := ⟪f.grad x, v⟫_ℝ
  let C := ⟪v, H v⟫_ℝ
  let φ : ℝ → ℝ := fun t => f.value (x + t • v) - f.value x - t * A - t ^ 2 / 2 * C
  have hval (t : ℝ) : HasDerivAt (fun u : ℝ => f.value (x + u • v))
      ⟪f.grad (x + t • v), v⟫_ℝ t := by
    simpa only [Function.comp_def, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm] using
      f.along_line_hasDerivAt x (x + v) t
  have hφ (t : ℝ) : HasDerivAt φ
      (⟪f.grad (x + t • v), v⟫_ℝ - A - t * C) t := by
    convert (((hval t).sub_const (f.value x)).sub ((hasDerivAt_id t).mul_const A)).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const C) using 1
    dsimp [φ]
    ring
  have hcomp : φ 1 - φ 0 ≤ 0 * (1 - 0) := by
    apply image_sub_le_of_hasDerivAt_off_finset (∅ : Finset ℝ) (by norm_num)
      (fun t _ => (hφ t).continuousAt.continuousWithinAt)
    intro t ht _
    refine ⟨_, hφ t, ?_⟩
    have hg := finitePieceAlong_directional hc hp (show t ∈ Icc (0 : ℝ) 1 from
      ⟨ht.1.le, ht.2.le⟩)
    rw [inner_sub_right, real_inner_comm (f.grad (x + t • v)) v,
      real_inner_comm (f.grad x) v] at hg
    dsimp only [A, C]
    linarith
  norm_num only [φ, zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow,
    one_pow, zero_div, sub_self, sub_zero] at hcomp
  unfold QuadraticUpper
  simp only [add_sub_cancel_left]
  dsimp only [A, C] at hcomp
  linarith

/-- Appendix A's finite-piece integration conclusion. The derivative and
matrix bounds are local data; both global conclusions are proved. -/
theorem finite_piece_transfer {d : ℕ} (f : Objective d) {L : ℝ}
    (H : X d →L[ℝ] X d) (hc : Continuous f.grad)
    (hp : ∀ x v, FinitePieceAlong f L H x v) :
    Smooth f L ∧ ∀ x y, QuadraticUpper f H x y := by
  have hL := finitePieceAlong_nonneg (hp 0 0)
  constructor
  · intro x y
    have h := finitePieceAlong_gradient_norm hL hc (hp y (x - y))
    simpa only [add_sub_cancel] using h
  · intro x y
    have h := finitePieceAlong_quadraticUpper hc (hp x (y - x))
    simpa only [add_sub_cancel] using h

end ExactZO
