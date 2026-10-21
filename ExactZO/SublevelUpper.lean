import ExactZO.SublevelFamily
import ExactZO.SublevelHessian
import ExactZO.SublevelMatrix

/-! The actual fixed-matrix segment model for the S4 sublevel wrapper. -/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.SublevelUpper
open StageGeometry SublevelWrapper SublevelHessian
variable {d m : ℕ} {R : ℝ}

theorem hessian_norm_le (hR : 0 < R) (hscale : 1024*(m:ℝ) ≤ R^2)
    {U : List (X d)} (hU : OrthoList U) (hlen : U.length = m) (x : X d)
    (hr : ‖x‖ < R/2)
    (hx : ∀ i : Fin U.length, chainPoint R U x i ∉ CompressedLinePieces.scalarJunctions) :
    ‖hessian m R U x‖ ≤ 50 := by
  have hLip : LipschitzWith 50 (gradient m R U) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm] using SublevelWrapper.gradient_lipschitz m hR hscale hU hlen x y
  rw [← (gradient_hasFDerivAt m hR U x hr hx).fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hLip

theorem hessian_upper (hR : 0 < R) (U : List (X d)) (hlen : U.length = m)
    (x v : X d)
    (hx : ∀ i : Fin U.length, chainPoint R U x i ∉ CompressedLinePieces.scalarJunctions) :
    ⟪v, hessian m R U x v⟫_ℝ ≤ ⟪v, SublevelMatrix.matrix m R U v⟫_ℝ := by
  rw [hessian_quadratic m hR]
  exact SublevelMatrix.chain_rule_upper hR U hlen x v (chainHessian R U x)
    (CompressedLinePieces.hessian_exists U.length (chainPoint R U x) hx)

theorem finitePieceAlong_inner (hR : 0 < R) (hscale : 1024*(m:ℝ) ≤ R^2)
    {U : List (X d)} (hU : OrthoList U) (hlen : U.length = m) (x v : X d)
    (hinner : ∀ t ∈ Set.Ioo (0:ℝ) 1, ‖x+t•v‖ < R/2) :
    FinitePieceAlong (objective m R U hR) 50 (SublevelMatrix.matrix m R U) x v := by
  by_cases hv : v = 0
  · subst v
    refine ⟨∅, fun _ => 0, ?_⟩
    intro t _ _
    constructor
    · simpa only [objective, smul_zero, add_zero, ContinuousLinearMap.zero_apply]
        using hasDerivAt_const t (gradient m R U x)
    · simp
  obtain ⟨S,hS⟩ := exists_regular_inner_line_hessian m hR U x v hv hinner
  refine ⟨S, fun t => hessian m R U (x+t•v), ?_⟩
  intro t ht htS
  obtain ⟨hreg,hder⟩ := hS t ht htS
  exact ⟨hder, hessian_norm_le hR hscale hU hlen _ (hinner t ht) hreg,
    hessian_upper hR U hlen _ v hreg⟩

theorem upper_model (hm : 1 ≤ m) (hR : 0 < R) (hscale : 1024*(m:ℝ) ≤ R^2)
    {U : List (X d)} (hU : OrthoList U) (hlen : U.length = m) (x y : X d)
    (hseg : segment ℝ x y ⊆ StrictSublevel (objective m R U hR)) :
    QuadraticUpper (objective m R U hR) (SublevelMatrix.matrix m R U) x y := by
  have hinner : ∀ t ∈ Set.Ioo (0:ℝ) 1, ‖x+t•(y-x)‖ < R/2 := by
    intro t ht
    have hmem : x+t•(y-x) ∈ segment ℝ x y := by
      refine ⟨1-t,t,by linarith [ht.2],ht.1.le,by ring,?_⟩
      module
    exact sublevel_inside_inner m hR hm hscale U hlen _ (hseg hmem).le
  have hp := finitePieceAlong_inner hR hscale hU hlen x (y-x) hinner
  have hc := (objective_smoothClass m hR hm hscale hU hlen).1.continuous_grad (by norm_num)
  simpa only [add_sub_cancel] using finitePieceAlong_quadraticUpper hc hp

end ExactZO.SublevelUpper
