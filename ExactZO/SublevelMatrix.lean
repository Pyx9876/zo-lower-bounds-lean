import ExactZO.ChainBounds
import ExactZO.ChainBarrier
import ExactZO.FrameGeometry
import ExactZO.RadialSecond
import ExactZO.FinitePiece

/-! The fixed matrix and quantitative quadratic estimates of Appendix L. -/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.SublevelMatrix
open StageGeometry FrameGeometry RadialCompression
variable {d : ℕ}

def matrix (m : ℕ) (R : ℝ) (U : List (X d)) : X d →L[ℝ] X d :=
  (106 : ℝ) • frameProjection U +
    (1007 * (m : ℝ) / (8 * R^2)) • ContinuousLinearMap.id ℝ (X d)

theorem matrix_quadratic (m : ℕ) (R : ℝ) (U : List (X d)) (v : X d) :
    ⟪v, matrix m R U v⟫_ℝ = 106 * ‖coordinateMap U v‖^2 +
      (1007 * (m : ℝ) / (8 * R^2)) * ‖v‖^2 := by
  simp only [matrix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right,
    frameProjection_quadratic, real_inner_self_eq_norm_sq]

theorem matrix_symmetric (m : ℕ) (R : ℝ) (U : List (X d)) (x y : X d) :
    ⟪matrix m R U x, y⟫_ℝ = ⟪x, matrix m R U y⟫_ℝ := by
  simp only [matrix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, frameProjection_symmetric]

theorem matrix_positive (m : ℕ) (R : ℝ) (U : List (X d)) (x : X d) :
    0 ≤ ⟪x, matrix m R U x⟫_ℝ := by rw [matrix_quadratic]; positivity

theorem matrix_norm (m : ℕ) (R : ℝ) {U : List (X d)} (hU : OrthoList U) :
    ‖matrix m R U‖ ≤ 106 + 1007 * (m : ℝ) / (8*R^2) := by
  have hc : 0 ≤ 1007 * (m : ℝ) / (8*R^2) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [matrix, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  calc
    _ ≤ ‖(106:ℝ) • frameProjection U v‖ + ‖(1007*(m:ℝ)/(8*R^2)) • v‖ := norm_add_le _ _
    _ = 106*‖frameProjection U v‖ + (1007*(m:ℝ)/(8*R^2))*‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
      norm_num
    _ ≤ 106*‖v‖ + (1007*(m:ℝ)/(8*R^2))*‖v‖ := by
      gcongr
      exact frameProjection_norm_le hU v
    _ = _ := by ring

theorem matrix_trace (m : ℕ) (R : ℝ) {U : List (X d)} (hU : OrthoList U)
    (hlen : U.length = m) :
    LinearMap.trace ℝ (X d) (matrix m R U).toLinearMap =
      106*(m:ℝ) + 1007*(d:ℝ)*(m:ℝ)/(8*R^2) := by
  change LinearMap.trace ℝ (X d) ((106:ℝ) • (frameProjection U).toLinearMap +
    (1007*(m:ℝ)/(8*R^2)) • LinearMap.id) = _
  rw [map_add, map_smul, map_smul, frameProjection_trace hU, hlen, LinearMap.trace_id]
  simp only [smul_eq_mul]
  have hd : Module.finrank ℝ (X d) = d := by simp [X]
  rw [hd]
  ring

/-- The radial correction coefficient in the first chain-rule term. -/
def beta (R : ℝ) (x v : X d) : ℝ := factor R x^2 * ⟪x,v⟫_ℝ / R^2

theorem beta_bound {R : ℝ} (hR : 0 < R) (x v : X d) :
    |beta R x v| ≤ ‖v‖/(2*R) := by
  have ha := factor_pos R x
  have hi := factor_identity hR x
  have hr2 : 0 < R^2 := sq_pos_of_pos hR
  have he : factor R x^2 * (R^2+‖x‖^2) = R^2 := by
    field_simp at hi
    nlinarith only [hi]
  have hc : 2*R*(factor R x^2*‖x‖) ≤ R^2 := by
    have hh := mul_nonneg (sq_nonneg (factor R x)) (sq_nonneg (R-‖x‖))
    nlinarith only [he, hh]
  unfold beta
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg R)]
  apply (div_le_iff₀ hr2).mpr
  have hinner := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x v) (sq_nonneg (factor R x))
  have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg v)
  have hd : (‖v‖/(2*R))*R^2 = R*‖v‖/2 := by field_simp; ring
  rw [hd]
  nlinarith

theorem chain_hessian_quadratic {m : ℕ} (y α : X m) (B : X m →L[ℝ] X m)
    (hB : HasFDerivAt (ScalarChain.gradient m) B y) {a β : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ⟪a • α - β • y, B (a • α - β • y)⟫_ℝ ≤
      96*‖α‖^2 + 150*(m:ℝ)*β^2 := by
  have hα : |⟪α, B α⟫_ℝ| ≤ 48*‖α‖^2 := by
    calc
      _ ≤ ‖α‖*‖B α‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖α‖*(48*‖α‖) := mul_le_mul_of_nonneg_left
        ((B.le_opNorm α).trans (mul_le_mul_of_nonneg_right
          (ScalarChain.hessian_norm_le m y B hB) (norm_nonneg α))) (norm_nonneg α)
      _ = _ := by ring
  have hc : |⟪α, B y⟫_ℝ| ≤ 60*Real.sqrt m*‖α‖ := by
    have h := (abs_real_inner_le_norm α (B y)).trans
      (mul_le_mul_of_nonneg_left (ScalarChain.hessian_mul_norm_le m y B hB) (norm_nonneg α))
    nlinarith only [h]
  have hy := ScalarChain.hessian_inner_abs_le m y B hB
  have hs : ⟪y, B α⟫_ℝ = ⟪α, B y⟫_ℝ := by
    rw [← ScalarChain.hessian_symmetric m y B hB, real_inner_comm]
  have he : ⟪a • α - β • y, B (a • α - β • y)⟫_ℝ =
      a^2*⟪α,B α⟫_ℝ - 2*a*β*⟪α,B y⟫_ℝ + β^2*⟪y,B y⟫_ℝ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hs]; ring
  have h₁ : a^2*⟪α,B α⟫_ℝ ≤ 48*‖α‖^2 := by
    have hb : a^2 ≤ 1 := by nlinarith
    calc
      _ ≤ a^2*(48*‖α‖^2) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hα) (sq_nonneg a)
      _ ≤ 1*(48*‖α‖^2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := one_mul _
  have h₂ : -(2*a*β*⟪α,B y⟫_ℝ) ≤ 120*|β| *Real.sqrt m*‖α‖ := by
    calc
      _ ≤ |2*a*β*⟪α,B y⟫_ℝ| := neg_le_abs _
      _ = 2*a*|β| *|⟪α,B y⟫_ℝ| := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha]; norm_num
      _ ≤ 2*a*|β| *(60*Real.sqrt m*‖α‖) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2*1*|β| *(60*Real.sqrt m*‖α‖) := by gcongr
      _ = _ := by ring
  have h₃ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hy) (sq_nonneg β)
  have hsq := sq_nonneg (4*‖α‖-5*Real.sqrt m*|β|)
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hsq' : 120*|β| *Real.sqrt m*‖α‖ ≤ 48*‖α‖^2+75*(m:ℝ)*β^2 := by
    nlinarith [sq_abs β]
  rw [he]
  nlinarith

theorem coordinate_derivative (R : ℝ) (U : List (X d)) (x v : X d) :
    coordinateMap U (derivative R x v) = factor R x • coordinateMap U v -
      beta R x v • coordinateMap U (compression R x) := by
  simp only [derivative, compression, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply, map_sub, map_smul, smul_smul, beta]
  module

theorem coordinate_second (R : ℝ) (U : List (X d)) (x v : X d) :
    coordinateMap U (secondApply R x v v) =
      (-2*factor R x*beta R x v) • coordinateMap U v +
      (3*beta R x v^2-factor R x^2*‖v‖^2/R^2) • coordinateMap U (compression R x) := by
  simp only [secondApply_apply, compression, map_add, map_smul,
    real_inner_self_eq_norm_sq, smul_smul, beta]
  module

theorem second_inner (R : ℝ) (U : List (X d)) (x v : X d) (p : X U.length) :
    ⟪frameMap U p, secondApply R x v v⟫_ℝ =
      -2*factor R x*beta R x v*⟪p, coordinateMap U v⟫_ℝ +
      (3*beta R x v^2-factor R x^2*‖v‖^2/R^2)*⟪coordinateMap U (compression R x),p⟫_ℝ := by
  rw [← (frameMap U).adjoint_inner_right]
  change ⟪p, coordinateMap U (secondApply R x v v)⟫_ℝ = _
  rw [coordinate_second]
  simp only [inner_add_right, real_inner_smul_right, real_inner_comm p]

theorem second_scalar_upper {m : ℕ} {R a β A V c e : ℝ}
    (hR : 0 < R) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hb : |β| ≤ V/(2*R)) (hc : |c| ≤ 10*Real.sqrt m*A)
    (he : |e| ≤ (25/2:ℝ)*m) :
    |(-2*a*β*c)+(3*β^2-a^2*V^2/R^2)*e| ≤
      10*A^2+(195*(m:ℝ)/(8*R^2))*V^2 := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hratio : 0 ≤ V^2/R^2 := by positivity
  have hb2 : β^2 ≤ V^2/(4*R^2) := by
    have hh := (sq_le_sq₀ (abs_nonneg β) (by positivity)).mpr hb
    simpa only [sq_abs, div_pow, mul_pow, show (2:ℝ)^2=4 by norm_num] using hh
  have ht : |3*β^2-a^2*V^2/R^2| ≤ 3*β^2+V^2/R^2 := by
    calc
      _ ≤ |3*β^2|+|a^2*V^2/R^2| := abs_sub _ _
      _ = 3*β^2+a^2*(V^2/R^2) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        ring
      _ ≤ 3*β^2+1*(V^2/R^2) := by gcongr
      _ = _ := by ring
  have ht₁ : |-2*a*β*c| ≤ 20*|β| *Real.sqrt m*A := by
    calc
      _ = 2*a*|β| *|c| := by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha]; norm_num
      _ ≤ 2*a*|β| *(10*Real.sqrt m*A) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2*1*|β| *(10*Real.sqrt m*A) := by gcongr
      _ = _ := by ring
  have ht₂ : |(3*β^2-a^2*V^2/R^2)*e| ≤
      (3*β^2+V^2/R^2)*((25/2:ℝ)*m) := by
    rw [abs_mul]
    exact mul_le_mul ht he (abs_nonneg e) (by positivity)
  have hy : 20*|β| *Real.sqrt m*A ≤ 10*A^2+10*(m:ℝ)*β^2 := by
    have hh := sq_nonneg (A-Real.sqrt m*|β|)
    have hs := Real.sq_sqrt hm
    nlinarith [sq_abs β]
  have hh := abs_add (-2*a*β*c) ((3*β^2-a^2*V^2/R^2)*e)
  have hb' := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ (95/2:ℝ)*m by positivity)
  have halgebra : (95/2:ℝ)*m*(V^2/(4*R^2)) + (25/2:ℝ)*m*(V^2/R^2) =
      (195*(m:ℝ)/(8*R^2))*V^2 := by ring
  nlinarith

theorem chain_second_upper {R : ℝ} (hR : 0 < R) (U : List (X d)) (x v : X d) :
    |⟪frameMap U (ScalarChain.gradient U.length (coordinateMap U (compression R x))),
      secondApply R x v v⟫_ℝ| ≤ 10*‖coordinateMap U v‖^2+
      (195*(U.length:ℝ)/(8*R^2))*‖v‖^2 := by
  rw [second_inner]
  apply second_scalar_upper hR (factor_pos R x).le (factor_le_one R x)
    (norm_nonneg _) (norm_nonneg _) (beta_bound hR x v)
  · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (ScalarChain.gradient_norm_le U.length _) (norm_nonneg _))
  · exact ScalarChain.gradient_weighted_coarse U.length _

theorem chain_rule_upper {m : ℕ} {R : ℝ} (hR : 0 < R) (U : List (X d))
    (hlen : U.length = m) (x v : X d) (B : X U.length →L[ℝ] X U.length)
    (hB : HasFDerivAt (ScalarChain.gradient U.length) B (coordinateMap U (compression R x))) :
    ⟪coordinateMap U (derivative R x v), B (coordinateMap U (derivative R x v))⟫_ℝ +
      ⟪frameMap U (ScalarChain.gradient U.length (coordinateMap U (compression R x))),
        secondApply R x v v⟫_ℝ +
      (64*(m:ℝ)/R^2)*‖v‖^2 ≤ ⟪v, matrix m R U v⟫_ℝ := by
  have hc := chain_hessian_quadratic (coordinateMap U (compression R x))
    (coordinateMap U v) B hB (factor_pos R x).le (factor_le_one R x)
    (β := beta R x v)
  rw [← coordinate_derivative] at hc
  have hs := chain_second_upper hR U x v
  have hlenR : (U.length : ℝ) = m := congrArg Nat.cast hlen
  rw [hlenR] at hc hs
  have hb := beta_bound hR x v
  have hb2 : beta R x v^2 ≤ ‖v‖^2/(4*R^2) := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
    simpa only [sq_abs, div_pow, mul_pow, show (2:ℝ)^2=4 by norm_num] using hh
  have hb' := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ 150*(m:ℝ) by positivity)
  have he : 150*(m:ℝ)*(‖v‖^2/(4*R^2)) +
      (195*(m:ℝ)/(8*R^2))*‖v‖^2 + (64*(m:ℝ)/R^2)*‖v‖^2 =
      (1007*(m:ℝ)/(8*R^2))*‖v‖^2 := by ring
  rw [matrix_quadratic]
  have hl := le_abs_self ⟪frameMap U (ScalarChain.gradient U.length
    (coordinateMap U (compression R x))),secondApply R x v v⟫_ℝ
  linarith

end ExactZO.SublevelMatrix
