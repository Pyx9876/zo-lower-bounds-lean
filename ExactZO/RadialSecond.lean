import ExactZO.RadialCompression

/-!
Second derivatives of the actual radial compression. The derivative proof reuses the
argument of the local library `Minimax.RadialCap` (the same map in a different
normalization). The norm estimate below sharpens its `3 / R` bound to the constant
in Appendix A, Lemma `lem:radial`.
-/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.RadialCompression
variable {d : ℕ}

/-- Second derivative with its second input fixed. -/
def secondApply (R : ℝ) (x v : X d) : X d →L[ℝ] X d :=
  (-(factor R x ^ 3 / R ^ 2)) • (innerSL ℝ x).smulRight v -
  ((factor R x ^ 3 / R ^ 2 * ⟪x, v⟫_ℝ) • ContinuousLinearMap.id ℝ (X d) +
    (factor R x ^ 3 / R ^ 2) • (innerSL ℝ v).smulRight x -
    (3 * factor R x ^ 5 / R ^ 4 * ⟪x, v⟫_ℝ) • (innerSL ℝ x).smulRight x)

@[simp] theorem secondApply_apply (R : ℝ) (x u v : X d) :
    secondApply R x v u =
      -(factor R x ^ 3 / R ^ 2) •
        (⟪x, u⟫_ℝ • v + ⟪x, v⟫_ℝ • u + ⟪u, v⟫_ℝ • x) +
      (3 * factor R x ^ 5 / R ^ 4 * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) • x := by
  simp only [secondApply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply, smul_eq_mul, smul_smul, real_inner_comm v u]
  module

theorem compression_contDiff {R : ℝ} (_hR : 0 < R) :
    ContDiff ℝ 2 (compression (d := d) R) := by
  have hd : ContDiff ℝ 2 (fun x : X d => 1 + ‖x‖ ^ 2 / R ^ 2) :=
    contDiff_const.add ((contDiff_id.norm_sq (𝕜 := ℝ)).div_const _)
  have hs := hd.sqrt (fun x => (denominator_pos R x).ne')
  exact (hs.inv (fun x => (Real.sqrt_pos.mpr (denominator_pos R x)).ne')).smul contDiff_id

theorem cubicFactor_hasFDerivAt {R : ℝ} (hR : 0 < R) (x : X d) :
    HasFDerivAt (fun y => factor R y ^ 3 / R ^ 2)
      ((-3 * factor R x ^ 5 / R ^ 4) • innerSL ℝ x) x := by
  convert ((hasDerivAt_pow 3 (factor R x)).comp_hasFDerivAt x (factor_hasFDerivAt hR x)).mul_const ((R ^ 2)⁻¹) using 1
  ext v : 1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply, smul_eq_mul]
  norm_num
  field_simp
  ring

theorem derivative_apply_hasFDerivAt {R : ℝ} (hR : 0 < R) (x v : X d) :
    HasFDerivAt (fun z => derivative R z v) (secondApply R x v) x := by
  have hc := (factor_hasFDerivAt hR x).smul_const v
  have hb := ((cubicFactor_hasFDerivAt hR x).mul
    (innerSL ℝ v).hasFDerivAt).smul (hasFDerivAt_id x)
  convert hc.sub hb using 1
  · funext z
    simp only [derivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply, real_inner_comm v z, smul_smul, id_eq]
  · ext u : 1
    simp only [secondApply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, innerSL_apply, smul_eq_mul, smul_smul, id_eq,
      real_inner_comm v x]
    simp only [neg_mul, neg_div]
    module

theorem derivative_contDiff {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ 1 (derivative (d := d) R) := by
  have he : fderiv ℝ (compression (d := d) R) = derivative R :=
    funext (fun t => (compression_hasFDerivAt hR t).fderiv)
  rw [← he]
  exact (compression_contDiff hR).fderiv_right (by norm_num)

theorem second_fderiv_apply {R : ℝ} (hR : 0 < R) (x u v : X d) :
    fderiv ℝ (derivative R) x u v = secondApply R x v u := by
  have hd := fderiv_clm_apply ((derivative_contDiff hR).differentiable (by norm_num) x)
    (differentiableAt_const (c := v))
  simp only [fderiv_const, ContinuousLinearMap.comp_zero, zero_add] at hd
  rw [(derivative_apply_hasFDerivAt hR x v).fderiv] at hd
  have hv := congrArg (fun T : X d →L[ℝ] X d => T u) hd
  simpa using hv.symm


/-- The rank-one correction can only reduce the diagonal norm relative to the
three-term triangle estimate. -/
theorem diagonal_core_norm_le (x v : X d) {k : ℝ} (hk : 0 ≤ k)
    (hkr : k * ‖x‖ ^ 2 ≤ 1) :
    ‖(2 * ⟪x, v⟫_ℝ) • v + (‖v‖ ^ 2 - 3 * k * ⟪x, v⟫_ℝ ^ 2) • x‖ ≤
      3 * ‖x‖ * ‖v‖ ^ 2 := by
  have hcs : ⟪x, v⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := abs_real_inner_le_norm x v
    have hh := (sq_le_sq₀ (abs_nonneg ⟪x, v⟫_ℝ) (mul_nonneg (norm_nonneg x) (norm_nonneg v))).2 h
    simpa only [sq_abs, mul_pow] using hh
  have h1 := mul_le_mul_of_nonneg_right hkr
    (show 0 ≤ 9 * k * ⟪x, v⟫_ℝ ^ 4 by positivity)
  have h2 := mul_nonneg (show 0 ≤ 6 * k * ‖x‖ ^ 2 * ⟪x, v⟫_ℝ ^ 2 by positivity)
    (sq_nonneg ‖v‖)
  have h3 := mul_nonneg hk (show 0 ≤ ⟪x, v⟫_ℝ ^ 4 by positivity)
  have h4 := mul_le_mul_of_nonneg_right hcs (show 0 ≤ 8 * ‖v‖ ^ 2 by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v x]
  rw [real_inner_comm v x] at h1 h2 h3 h4
  nlinarith only [h1, h2, h3, h4]

/-- The scalar factor has precisely the uniform bound required in the paper. -/
theorem second_scalar_bound {R : ℝ} (hR : 0 < R) (x : X d) :
    3 * (factor R x ^ 3 / R ^ 2) * ‖x‖ ≤ 2 / (Real.sqrt 3 * R) := by
  have ha := factor_pos R x
  have ha1 := factor_le_one R x
  have hi := factor_identity hR x
  have hid : factor R x ^ 2 * ‖x‖ ^ 2 = R ^ 2 * (1 - factor R x ^ 2) := by
    field_simp at hi
    nlinarith only [hi]
  have hp : 0 ≤ (3 * factor R x ^ 2 - 2) ^ 2 * (3 * factor R x ^ 2 + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hm := congrArg (fun t : ℝ => t * factor R x ^ 4) hid
  dsimp only at hm
  have hb : 27 * (factor R x ^ 3 * ‖x‖) ^ 2 ≤ 4 * R ^ 2 := by
    have hh := mul_nonneg hp (sq_nonneg R)
    nlinarith only [hh, hm]
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply (le_div_iff₀ (mul_pos hs3p hR)).2
  have hid' : 3 * (factor R x ^ 3 / R ^ 2) * ‖x‖ * (Real.sqrt 3 * R) =
      (3 * factor R x ^ 3 * ‖x‖ * Real.sqrt 3) / R := by field_simp; ring
  rw [hid']
  apply (div_le_iff₀ hR).2
  have hn : 0 ≤ 3 * factor R x ^ 3 * ‖x‖ * Real.sqrt 3 := by positivity
  apply (sq_le_sq₀ hn (by positivity)).mp
  simp only [mul_pow, hs3]
  nlinarith only [hb]


/-- Polarization transfers a diagonal bound to the operator norm of a symmetric
vector-valued bilinear map over a real inner-product space. -/
theorem norm_bilinear_le_of_diagonal
    (B : X d →L[ℝ] X d →L[ℝ] X d) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u v, B u v = B v u)
    (hb : ∀ u, ‖B u u‖ ≤ C * ‖u‖ ^ 2) : ‖B‖ ≤ C := by
  have hunit : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → ‖B u v‖ ≤ C := by
    intro u v hu hv
    have he : B (u + v) (u + v) - B (u - v) (u - v) = (4 : ℝ) • B u v := by
      simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, hB v u]
      module
    have hn := norm_sub_le (B (u + v) (u + v)) (B (u - v) (u - v))
    rw [he, norm_smul, Real.norm_eq_abs] at hn
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hn
    have h1 := hb (u + v)
    have h2 := hb (u - v)
    have hp : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, hu, hv]
      ring
    have hcp := congrArg (fun t : ℝ => C * t) hp
    dsimp only at hcp
    nlinarith only [hn, h1, h2, hcp]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg u))
  intro v
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu' : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu), inv_mul_cancel₀ hnu.ne']
  have hv' : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnv), inv_mul_cancel₀ hnv.ne']
  have hh := hunit (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) hu' hv'
  simp only [map_smul, ContinuousLinearMap.smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu), abs_of_pos (inv_pos.mpr hnv)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hnu.le hnv.le)
  have he : ‖u‖ * ‖v‖ * (‖v‖⁻¹ * (‖u‖⁻¹ * ‖B u v‖)) = ‖B u v‖ := by
    field_simp
    ring
  rw [he] at hm
  nlinarith only [hm]

theorem second_diagonal_norm_le {R : ℝ} (hR : 0 < R) (x v : X d) :
    ‖secondApply R x v v‖ ≤ 2 / (Real.sqrt 3 * R) * ‖v‖ ^ 2 := by
  have ha := (factor_pos R x).le
  let k := factor R x ^ 2 / R ^ 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hkr : k * ‖x‖ ^ 2 ≤ 1 := by
    have hi := factor_identity hR x
    have he : k * ‖x‖ ^ 2 + factor R x ^ 2 = 1 := by
      calc
        _ = factor R x ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) := by dsimp [k]; ring
        _ = 1 := hi
    nlinarith [sq_nonneg (factor R x)]
  have he : secondApply R x v v = -(factor R x ^ 3 / R ^ 2) •
      ((2 * ⟪x, v⟫_ℝ) • v + (‖v‖ ^ 2 - 3 * k * ⟪x, v⟫_ℝ ^ 2) • x) := by
    rw [secondApply_apply, real_inner_self_eq_norm_sq]
    dsimp [k]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (show 0 ≤ factor R x ^ 3 / R ^ 2 by positivity)]
  calc
    _ ≤ (factor R x ^ 3 / R ^ 2) * (3 * ‖x‖ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (diagonal_core_norm_le x v hk hkr) (by positivity)
    _ = (3 * (factor R x ^ 3 / R ^ 2) * ‖x‖) * ‖v‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (second_scalar_bound hR x) (sq_nonneg _)

theorem second_fderiv_norm_le {R : ℝ} (hR : 0 < R) (x : X d) :
    ‖fderiv ℝ (derivative R) x‖ ≤ 2 / (Real.sqrt 3 * R) := by
  apply norm_bilinear_le_of_diagonal _ (by positivity)
  · intro u v
    simp only [second_fderiv_apply hR, secondApply_apply, real_inner_comm v u]
    module
  · intro u
    rw [second_fderiv_apply hR]
    exact second_diagonal_norm_le hR x u

theorem derivative_lipschitz {R : ℝ} (hR : 0 < R) (x y : X d) :
    ‖derivative R y - derivative R x‖ ≤ 2 / (Real.sqrt 3 * R) * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (s := Set.univ) (f := derivative R) (f' := fderiv ℝ (derivative R))
    (fun z _ => ((derivative_contDiff hR).differentiable (by norm_num) z).hasFDerivAt.hasFDerivWithinAt)
    (fun z _ => second_fderiv_norm_le hR z)
    (convex_univ : Convex ℝ (Set.univ : Set (X d))) (Set.mem_univ x) (Set.mem_univ y)

/-- The explicit second derivative formula for the original compression map. -/
theorem compression_second_fderiv_formula {R : ℝ} (hR : 0 < R) (x u v : X d) :
    fderiv ℝ (fderiv ℝ (compression R)) x u v =
      -(factor R x ^ 3 / R ^ 2) •
        (⟪x, u⟫_ℝ • v + ⟪x, v⟫_ℝ • u + ⟪u, v⟫_ℝ • x) +
      (3 * factor R x ^ 5 / R ^ 4 * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) • x := by
  have he : fderiv ℝ (compression (d := d) R) = derivative R :=
    funext (fun t => (compression_hasFDerivAt hR t).fderiv)
  rw [he, second_fderiv_apply hR, secondApply_apply]

/-- The paper's global bilinear second derivative estimate, including the origin. -/
theorem compression_second_fderiv_norm_le {R : ℝ} (hR : 0 < R) (x u v : X d) :
    ‖fderiv ℝ (fderiv ℝ (compression R)) x u v‖ ≤
      2 / (Real.sqrt 3 * R) * ‖u‖ * ‖v‖ := by
  have he : fderiv ℝ (compression (d := d) R) = derivative R :=
    funext (fun t => (compression_hasFDerivAt hR t).fderiv)
  rw [he]
  exact ((fderiv ℝ (derivative R) x u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (((fderiv ℝ (derivative R) x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (second_fderiv_norm_le hR x) (norm_nonneg u)))
      (norm_nonneg v))

/-- The derivative is self-adjoint, so its use in the gradient chain rule needs
no change to the derivative formula. -/
theorem derivative_symmetric (R : ℝ) (x u v : X d) :
    ⟪derivative R x u, v⟫_ℝ = ⟪u, derivative R x v⟫_ℝ := by
  simp only [derivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x u, real_inner_comm x v]
  ring

end ExactZO.RadialCompression
