import ExactZO.SelectionHamming
import ExactZO.Transfer
import Mathlib.Data.Complex.ExponentialBounds

/-! The elementary constant bounds, orthogonal coordinates, and normalization
used to turn the finite sign-pair construction into a direction in a subspace. -/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.SelectionGeometry

open SelectionHamming

theorem log_exp_one_add_ge_one {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ Real.log (Real.exp 1 + r) := by
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hr)

theorem log_128_lt_five : Real.log (128 : ℝ) < 5 := by
  have heq : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 7) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

theorem log_128_lt_four_log_exp_one_add_one :
    Real.log (128 : ℝ) < 4 * Real.log (Real.exp 1 + 1) := by
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow : (128 : ℝ) < (Real.exp 1 + 1) ^ 4 := by
    calc
      _ < (7 / 2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := by gcongr; linarith
  have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 128) hpow
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

theorem log_quantization_bound {r : ℝ} (hr : 0 ≤ r) :
    Real.log (128 * max 1 r) ≤ 5 * Real.log (Real.exp 1 + r) := by
  by_cases hsmall : r ≤ 1
  · rw [max_eq_left hsmall, mul_one]
    linarith [log_128_lt_five, log_exp_one_add_ge_one hr]
  · have hlarge : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    have hrpos : 0 < r := by linarith
    rw [max_eq_right hlarge, Real.log_mul (by norm_num) (ne_of_gt hrpos)]
    have hbase : Real.log (Real.exp 1 + 1) ≤ Real.log (Real.exp 1 + r) :=
      Real.log_le_log (by positivity) (by linarith)
    have hrlog : Real.log r ≤ Real.log (Real.exp 1 + r) :=
      Real.log_le_log hrpos (by linarith [Real.exp_pos (1 : ℝ)])
    linarith [log_128_lt_four_log_exp_one_add_one]

theorem four_sqrt_five_lt_nine : 4 * Real.sqrt (5 : ℝ) < 9 := by
  have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

theorem quantization_constant_bound {R r p : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hp : 0 < p) :
    4 * R * Real.sqrt (Real.log (128 * max 1 r)) / Real.sqrt p ≤
      9 * R * Real.sqrt (Real.log (Real.exp 1 + r) / p) := by
  have hlog : 0 ≤ Real.log (Real.exp 1 + r) := by
    linarith [log_exp_one_add_ge_one hr]
  have hs := Real.sqrt_le_sqrt (log_quantization_bound hr)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)] at hs
  rw [Real.sqrt_div hlog, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_pos.mpr hp).le
  calc
    _ ≤ 4 * R * (Real.sqrt 5 * Real.sqrt (Real.log (Real.exp 1 + r))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right four_sqrt_five_lt_nine.le
        (mul_nonneg hR (Real.sqrt_nonneg (Real.log (Real.exp 1 + r))))
      nlinarith

/-- The selection threshold improves with larger dimension and fewer points. -/
theorem selection_threshold_mono {R M Q p s : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMQ : M ≤ Q) (hp : 0 < p) (hps : p ≤ s) :
    9 * R * Real.sqrt (Real.log (Real.exp 1 + M / s) / s) ≤
      9 * R * Real.sqrt (Real.log (Real.exp 1 + Q / p) / p) := by
  have hs : 0 < s := hp.trans_le hps
  have hQ : 0 ≤ Q := hM.trans hMQ
  have hratio : M / s ≤ Q / p := div_le_div₀ hQ hMQ hp hps
  have hlog : Real.log (Real.exp 1 + M / s) ≤ Real.log (Real.exp 1 + Q / p) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogQ : 0 ≤ Real.log (Real.exp 1 + Q / p) := by
    linarith [log_exp_one_add_ge_one (div_nonneg hQ hp.le)]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (div_le_div₀ hlogQ hlog hp hps)) (by positivity)

/-- Coordinates are obtained from a genuine linear isometric embedding. -/
def subspaceEmbedding {d : ℕ} (S : Submodule ℝ (X d)) :
    X (Module.finrank ℝ S) →ₗᵢ[ℝ] X d :=
  S.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ S).repr.symm.toLinearIsometry

theorem subspaceEmbedding_mem {d : ℕ} (S : Submodule ℝ (X d))
    (v : X (Module.finrank ℝ S)) : subspaceEmbedding S v ∈ S :=
  ((stdOrthonormalBasis ℝ S).repr.symm v).property

theorem exists_unit_mem {d : ℕ} (S : Submodule ℝ (X d))
    (hp : 0 < Module.finrank ℝ S) : ∃ u : X d, ‖u‖ = 1 ∧ u ∈ S := by
  let i : Fin (Module.finrank ℝ S) := ⟨0, hp⟩
  let v := (stdOrthonormalBasis ℝ S) i
  exact ⟨(v : X d), (stdOrthonormalBasis ℝ S).orthonormal.norm_eq_one i, v.property⟩

def coordinates {d : ℕ} (S : Submodule ℝ (X d)) (a : X d) : X (Module.finrank ℝ S) :=
  (subspaceEmbedding S).toContinuousLinearMap.adjoint a

theorem coordinates_norm_le {d : ℕ} (S : Submodule ℝ (X d)) (a : X d) :
    ‖coordinates S a‖ ≤ ‖a‖ := norm_adjoint_embedding_le (subspaceEmbedding S) a

theorem coordinates_inner {d : ℕ} (S : Submodule ℝ (X d))
    (a : X d) (v : X (Module.finrank ℝ S)) :
    ⟪coordinates S a, v⟫_ℝ = ⟪a, subspaceEmbedding S v⟫_ℝ :=
  (subspaceEmbedding S).toContinuousLinearMap.adjoint_inner_left v a

/-- A nonzero sign difference with the quantization projection bounds yields
the advertised unit direction. The difference is an actual vector, not a
postulated direction with the conclusion already assumed. -/
theorem normalize_in_subspace {d M : ℕ} (S : Submodule ℝ (X d))
    (a : Fin M → X d) {R : ℝ} (hR : 0 ≤ R)
    (hp : 0 < Module.finrank ℝ S) (v : X (Module.finrank ℝ S))
    (hfar : Real.sqrt (Module.finrank ℝ S : ℝ) < ‖v‖)
    (hsmall : ∀ i, |⟪coordinates S (a i), v⟫_ℝ| <
      4 * R * Real.sqrt (Real.log (128 * max 1 ((M : ℝ) / Module.finrank ℝ S)))) :
    ∃ u : X d, ‖u‖ = 1 ∧ u ∈ S ∧ ∀ i,
      |⟪u, a i⟫_ℝ| ≤ 9 * R * Real.sqrt
        (Real.log (Real.exp 1 + (M : ℝ) / Module.finrank ℝ S) / Module.finrank ℝ S) := by
  have hpR : (0 : ℝ) < Module.finrank ℝ S := by exact_mod_cast hp
  have hsqrt : 0 < Real.sqrt (Module.finrank ℝ S : ℝ) := Real.sqrt_pos.mpr hpR
  have hvpos : 0 < ‖v‖ := hsqrt.trans hfar
  let u := subspaceEmbedding S (‖v‖⁻¹ • v)
  refine ⟨u, ?_, subspaceEmbedding_mem _ _, ?_⟩
  · dsimp [u]
    rw [(subspaceEmbedding S).norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvpos), inv_mul_cancel₀ (ne_of_gt hvpos)]
  · intro i
    have heq : |⟪u, a i⟫_ℝ| = |⟪coordinates S (a i), v⟫_ℝ| / ‖v‖ := by
      rw [real_inner_comm]
      change |⟪a i, subspaceEmbedding S (‖v‖⁻¹ • v)⟫_ℝ| = _
      rw [← coordinates_inner, real_inner_smul_right, abs_mul,
        abs_of_pos (inv_pos.mpr hvpos)]
      ring
    rw [heq]
    calc
      _ ≤ (4 * R * Real.sqrt (Real.log (128 * max 1 ((M : ℝ) / Module.finrank ℝ S)))) /
          Real.sqrt (Module.finrank ℝ S : ℝ) :=
        div_le_div₀ (by positivity) (hsmall i).le hsqrt hfar.le
      _ ≤ _ := quantization_constant_bound hR (by positivity) hpR

end ExactZO.SelectionGeometry
