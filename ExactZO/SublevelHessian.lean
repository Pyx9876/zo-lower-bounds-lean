import ExactZO.SublevelWrapper
import ExactZO.CompressedLinePieces

/-! Actual Hessian and directional chain rule for the sublevel wrapper.
Regularity is proved from the actual scalar pieces, and the radial penalty is
quadratic throughout the open inner ball. No a.e. statement is restricted to
an arbitrary line.
-/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.SublevelHessian
open RadialCompression FrameGeometry SublevelWrapper CompressedLinePieces
variable {d : ℕ}

/-- The actual chain Hessian, used only at regular points by the derivative theorems. -/
def chainHessian (R : ℝ) (U : List (X d)) (x : X d) : X U.length →L[ℝ] X U.length :=
  fderiv ℝ (ScalarChain.gradient U.length) (chainPoint R U x)

/-- The chain-rule operator for the actual wrapper gradient in the inner ball. -/
def hessian (m : ℕ) (R : ℝ) (U : List (X d)) (x : X d) : X d →L[ℝ] X d :=
  (derivative R x).comp ((frameMap U).comp
    ((chainHessian R U x).comp ((coordinateMap U).comp (derivative R x)))) +
  (fderiv ℝ (derivative R) x).flip (chainGradient R U x) +
  mu m R • ContinuousLinearMap.id ℝ (X d)

theorem chainPoint_hasFDerivAt {R : ℝ} (hR : 0 < R) (U : List (X d)) (x : X d) :
    HasFDerivAt (chainPoint R U) ((coordinateMap U).comp (derivative R x)) x :=
  (coordinateMap U).hasFDerivAt.comp x (compression_hasFDerivAt hR x)

theorem chainGradient_hasFDerivAt {R : ℝ} (hR : 0 < R) (U : List (X d)) (x : X d)
    (hx : ∀ i : Fin U.length, chainPoint R U x i ∉ scalarJunctions) :
    HasFDerivAt (chainGradient R U)
      ((frameMap U).comp ((chainHessian R U x).comp
        ((coordinateMap U).comp (derivative R x)))) x :=
  (frameMap U).hasFDerivAt.comp x
    ((hessian_exists U.length (chainPoint R U x) hx).comp x (chainPoint_hasFDerivAt hR U x))

/-- Actual Fréchet differentiability of the full wrapper gradient at regular
points of the open inner ball. -/
theorem gradient_hasFDerivAt (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d)) (x : X d)
    (hr : ‖x‖ < R/2)
    (hx : ∀ i : Fin U.length, chainPoint R U x i ∉ scalarJunctions) :
    HasFDerivAt (gradient m R U) (hessian m R U x) x := by
  have hd := ((derivative_contDiff hR).differentiable (by norm_num) x).hasFDerivAt
  exact (hd.clm_apply (chainGradient_hasFDerivAt hR U x hx)).add
    (SublevelPotential.gradient_hasFDerivAt_inner hr)

/-- Complete trilinear symmetry of the explicitly differentiated radial map. -/
theorem secondApply_inner_swap (R : ℝ) (x u v w : X d) :
    ⟪u, secondApply R x v w⟫_ℝ = ⟪v, secondApply R x u w⟫_ℝ := by
  simp only [secondApply_apply, inner_add_right, real_inner_smul_right,
    real_inner_comm x u, real_inner_comm x v, real_inner_comm x w,
    real_inner_comm u v, real_inner_comm u w, real_inner_comm v w]
  ring

/-- The exact directional quadratic chain rule used for the fixed upper model. -/
theorem hessian_quadratic (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d)) (x v : X d) :
    ⟪v, hessian m R U x v⟫_ℝ =
      ⟪coordinateMap U (derivative R x v),
        chainHessian R U x (coordinateMap U (derivative R x v))⟫_ℝ +
      ⟪chainGradient R U x, secondApply R x v v⟫_ℝ + mu m R * ‖v‖^2 := by
  simp only [hessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [second_fderiv_apply hR, secondApply_inner_swap]
  congr 2
  rw [← derivative_symmetric]
  exact ((frameMap U).adjoint_inner_left _ _).symm

/-- The genuine Hessian at a regular inner point equals the explicit operator. -/
theorem fderiv_gradient_eq (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d)) (x : X d)
    (hr : ‖x‖ < R/2)
    (hx : ∀ i : Fin U.length, chainPoint R U x i ∉ scalarJunctions) :
    fderiv ℝ (gradient m R U) x = hessian m R U x :=
  (gradient_hasFDerivAt m hR U x hr hx).fderiv

/-- Every line segment contained in the inner ball admits the actual wrapper
Hessian chain rule away from one finite exceptional set. Zero directions are
handled directly; nonzero directions use the proved polynomial-root result. -/
theorem exists_inner_line_hessian (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d))
    (x v : X d) (hinner : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖x+t•v‖ < R/2) :
    ∃ S : Finset ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ S →
      HasDerivAt (fun s : ℝ => gradient m R U (x+s•v))
        (hessian m R U (x+t•v) v) t := by
  by_cases hv : v = 0
  · subst v
    refine ⟨∅, ?_⟩
    intro t _ _
    simp only [smul_zero, add_zero, map_zero]
    exact hasDerivAt_const t _
  obtain ⟨S, hS⟩ := exists_finite_scalar_junctions hR U x hv
  refine ⟨S, ?_⟩
  intro t ht htS
  have hregular : ∀ i : Fin U.length, chainPoint R U (x+t•v) i ∉ scalarJunctions := by
    intro i
    simpa only [chainPoint, coordinateMap_apply] using hS t htS (U.get i) (List.get_mem U i)
  have hg := gradient_hasFDerivAt m hR U (x+t•v) (hinner t ht) hregular
  have hl : HasDerivAt (fun s : ℝ => x+s•v) v t := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
  exact hg.comp_hasDerivAt t hl

/-- The nonzero-direction form retains regularity explicitly for the separate
Hessian norm and fixed-matrix comparisons used by finite-piece integration. -/
theorem exists_regular_inner_line_hessian (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d))
    (x v : X d) (hv : v ≠ 0) (hinner : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖x+t•v‖ < R/2) :
    ∃ S : Finset ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, t ∉ S →
      (∀ i : Fin U.length, chainPoint R U (x+t•v) i ∉ scalarJunctions) ∧
      HasDerivAt (fun s : ℝ => gradient m R U (x+s•v))
        (hessian m R U (x+t•v) v) t := by
  obtain ⟨S, hS⟩ := exists_finite_scalar_junctions hR U x hv
  refine ⟨S, ?_⟩
  intro t ht htS
  have hregular : ∀ i : Fin U.length, chainPoint R U (x+t•v) i ∉ scalarJunctions := by
    intro i
    simpa only [chainPoint, coordinateMap_apply] using hS t htS (U.get i) (List.get_mem U i)
  refine ⟨hregular, ?_⟩
  have hg := gradient_hasFDerivAt m hR U (x+t•v) (hinner t ht) hregular
  have hl : HasDerivAt (fun s : ℝ => x+s•v) v t := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
  exact hg.comp_hasDerivAt t hl

end ExactZO.SublevelHessian
