import ExactZO.SphereFoundation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

/-! One-dimensional fair sign law. No Haar identification or radial independence. -/
namespace ExactZO.Gaussian
open scoped ENNReal

/-- The positive unit coordinate vector in one-dimensional Euclidean space. -/
def unitAxisOne : X 1 := EuclideanSpace.single (0 : Fin 1) 1

theorem norm_one_eq_unitAxisOne_or_neg {x : X 1} (hx : ‖x‖ = 1) :
    x = unitAxisOne ∨ x = -unitAxisOne := by
  have hsq : (x 0) ^ 2 = 1 := by
    simpa only [Fin.sum_univ_one, hx, one_pow] using coordinate_sq_sum x
  rcases sq_eq_one_iff.mp hsq with hp | hn
  · left
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa only [unitAxisOne, EuclideanSpace.single_apply, if_pos rfl] using hp
  · right
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change x 0 = -1
    exact hn

theorem sphereGaussian_one_ae_sign :
    ∀ᵐ x ∂sphereGaussian 1, x = unitAxisOne ∨ x = -unitAxisOne := by
  filter_upwards [sphereGaussian_ae_norm (by norm_num : 0 < 1)] with x hx
  exact norm_one_eq_unitAxisOne_or_neg hx

theorem sphereGaussian_one_sign_masses_eq :
    sphereGaussian 1 ({unitAxisOne} : Set (X 1)) =
      sphereGaussian 1 ({-unitAxisOne} : Set (X 1)) := by
  have hi := sphereGaussian_map_linearIsometryEquiv
    (d := 1) (LinearIsometryEquiv.neg ℝ)
  have h := Measure.measure_preimage_of_map_eq_self hi
    (measurableSet_singleton unitAxisOne).nullMeasurableSet
  have hp : (fun x : X 1 => -x) ⁻¹' {unitAxisOne} = {-unitAxisOne} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact neg_eq_iff_eq_neg
  simpa only [LinearIsometryEquiv.coe_neg, hp] using h.symm

/-- The actual normalized Gaussian in dimension one is exactly a fair sign:
its two unit endpoints have probability `1/2`, with no mass elsewhere. -/
theorem sphereGaussian_one_fair_sign :
    (∀ᵐ x ∂sphereGaussian 1, x = unitAxisOne ∨ x = -unitAxisOne) ∧
    sphereGaussian 1 ({unitAxisOne} : Set (X 1)) = (1 / 2 : ℝ≥0∞) ∧
    sphereGaussian 1 ({-unitAxisOne} : Set (X 1)) = (1 / 2 : ℝ≥0∞) := by
  have hne : unitAxisOne ≠ -unitAxisOne := by
    intro h
    have hv := congrArg (fun x : X 1 => x 0) h
    change (1 : ℝ) = -1 at hv
    norm_num at hv
  have hsum : sphereGaussian 1 ({unitAxisOne} : Set (X 1)) +
      sphereGaussian 1 ({-unitAxisOne} : Set (X 1)) = 1 := by
    rw [← measure_union (Set.disjoint_singleton.mpr hne) (measurableSet_singleton _)]
    apply (mem_ae_iff_prob_eq_one
      ((measurableSet_singleton unitAxisOne).union (measurableSet_singleton (-unitAxisOne)))).mp
    simpa only [Set.mem_union, Set.mem_singleton_iff] using sphereGaussian_one_ae_sign
  have htotal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at htotal
  have heq := congrArg ENNReal.toReal sphereGaussian_one_sign_masses_eq
  have hm : sphereGaussian 1 ({unitAxisOne} : Set (X 1)) = (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (by norm_num)).mp
    norm_num at htotal ⊢
    linarith
  exact ⟨sphereGaussian_one_ae_sign, hm, sphereGaussian_one_sign_masses_eq.symm.trans hm⟩

end ExactZO.Gaussian

