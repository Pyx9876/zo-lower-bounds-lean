import ExactZO.SphereFoundation
import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

/-! Explicit measurable Householder alignment; this is not an adaptive law theorem. -/
namespace ExactZO.SphereAlignment

variable {d : ℕ}

/-- Reflection in the hyperplane perpendicular to `b - v`. -/
def householder (b v : X d) : X d ≃ₗᵢ[ℝ] X d :=
  Submodule.reflection (ℝ ∙ (b - v))ᗮ

theorem householder_apply_formula (b v x : X d) :
    householder b v x = x - (2 * (⟪b - v, x⟫_ℝ / ‖b - v‖ ^ 2)) • (b - v) := by
  unfold householder
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, neg_sub]
  simp only [two_smul, two_mul, add_smul, RCLike.ofReal_real_eq_id, id_eq]

/-- Equal norms are exactly the hypothesis used by the alignment lemma. -/
theorem householder_apply_base {b v : X d} (h : ‖b‖ = ‖v‖) :
    householder b v b = v :=
  Submodule.reflection_sub h

theorem householder_self (b : X d) :
    householder b b = LinearIsometryEquiv.refl ℝ (X d) := by
  ext x
  rw [householder_apply_formula]
  simp

/-- This is joint measurability of the actual action, not a measurable choice
in a space of orthogonal transformations. Division is totalized at zero. -/
theorem householder_joint_measurable :
    Measurable (fun p : X d × X d × X d => householder p.1 p.2.1 p.2.2) := by
  simp_rw [householder_apply_formula]
  fun_prop

/-- Every fixed Householder map preserves the actual normalized Gaussian law. -/
theorem sphereGaussian_map_householder (b v : X d) :
    Measure.map (householder b v) (Gaussian.sphereGaussian d) = Gaussian.sphereGaussian d :=
  Gaussian.sphereGaussian_map_linearIsometryEquiv (householder b v)

/-- The first standard unit vector; positive dimension supplies its index. -/
def baseAxis (hd : 0 < d) : X d := EuclideanSpace.single ⟨0, hd⟩ 1

theorem norm_baseAxis (hd : 0 < d) : ‖baseAxis hd‖ = 1 := by
  simp [baseAxis]

/-- A specified target vector determines a concrete orthogonal alignment. -/
def alignUnit (hd : 0 < d) (v : X d) : X d ≃ₗᵢ[ℝ] X d :=
  householder (baseAxis hd) v

theorem alignUnit_apply_base (hd : 0 < d) {v : X d} (hv : ‖v‖ = 1) :
    alignUnit hd v (baseAxis hd) = v := by
  apply householder_apply_base
  rw [norm_baseAxis, hv]

theorem alignUnit_self (hd : 0 < d) :
    alignUnit hd (baseAxis hd) = LinearIsometryEquiv.refl ℝ (X d) :=
  householder_self (baseAxis hd)

theorem alignUnit_joint_measurable (hd : 0 < d) :
    Measurable (fun p : X d × X d => alignUnit hd p.1 p.2) := by
  have hm : Measurable (fun p : X d × X d => (baseAxis hd, p.1, p.2)) :=
    measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
  simpa only [Function.comp_def, alignUnit] using
    (householder_joint_measurable (d := d)).comp hm

theorem sphereGaussian_map_alignUnit (hd : 0 < d) (v : X d) :
    Measure.map (alignUnit hd v) (Gaussian.sphereGaussian d) = Gaussian.sphereGaussian d :=
  sphereGaussian_map_householder (baseAxis hd) v

end ExactZO.SphereAlignment

