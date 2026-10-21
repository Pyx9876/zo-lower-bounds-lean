import ExactZO.S4Scaling
import ExactZO.SublevelUpper
import ExactZO.Stage
import ExactZO.Simulation
import ExactZO.DimensionFloor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
The updated S4 main-chain constants from `S4_modules/E_lower.tex`.
The concrete analytic wrapper, matrix model, stage transcript, and scaling
are proved. The geometric selector remains explicit until M5 is linked.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.S4Lower

open StageGeometry

def stageLog (m : ℕ) : ℝ := Real.log (Real.exp 1 + (m : ℝ))
def wrapperRadius (d m : ℕ) : ℝ := Real.sqrt ((d : ℝ) / (768 * stageLog m))
def wrapperGap (m : ℕ) : ℝ := (9 / 4 : ℝ) * ((m : ℝ) - 1 / 2)
def wrapperTrace (m : ℕ) : ℝ := 900 * (m : ℝ) * stageLog m

theorem stageLog_ge_one (m : ℕ) : 1 ≤ stageLog m := by
  unfold stageLog
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.exp 1 + (m : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Nat.cast_nonneg (α := ℝ) m])

theorem wrapper_radius_data {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d) :
    0 < wrapperRadius d m ∧
      wrapperRadius d m ^ 2 = (d : ℝ) / (768 * stageLog m) ∧
      1024 * (m : ℝ) ≤ wrapperRadius d m ^ 2 ∧
      32 * m ≤ d ∧ 0 < d / 2 ∧ m + d / 2 ≤ d := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hell := stageLog_ge_one m
  have hellpos : 0 < stageLog m := by linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * stageLog m := by nlinarith
  have h32R : (32 : ℝ) * (m : ℝ) ≤ d := by nlinarith
  have h32 : 32 * m ≤ d := by exact_mod_cast h32R
  have hdpos : (0 : ℝ) < d := by nlinarith
  have hquot : 0 < (d : ℝ) / (768 * stageLog m) := by positivity
  have hsq : wrapperRadius d m ^ 2 = (d : ℝ) / (768 * stageLog m) :=
    Real.sq_sqrt hquot.le
  refine ⟨Real.sqrt_pos.2 hquot, hsq, ?_, h32, by omega, by omega⟩
  rw [hsq]
  apply (le_div_iff₀ (by positivity : 0 < 768 * stageLog m)).mpr
  nlinarith

/-- The elementary logarithm dilation used by the new finite selection rule. -/
theorem log_dilation {c x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) :
    Real.log (Real.exp 1 + c * x) ≤ c * Real.log (Real.exp 1 + x) := by
  have hcpos : 0 < c := by linarith
  have hexppos := Real.exp_pos (1 : ℝ)
  have hbase : 0 < Real.exp 1 + x := by positivity
  have hell : 1 ≤ Real.log (Real.exp 1 + x) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log hexppos (by linarith)
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hcpos
  calc
    Real.log (Real.exp 1 + c * x) ≤ Real.log (c * (Real.exp 1 + x)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log c + Real.log (Real.exp 1 + x) :=
      Real.log_mul (ne_of_gt hcpos) (ne_of_gt hbase)
    _ ≤ c * Real.log (Real.exp 1 + x) := by nlinarith

theorem residual_dimension_budget {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d) :
    0 < d - m - d / 2 + 1 ∧
      (15 : ℝ) * d ≤ 32 * ((d - m - d / 2 + 1 : ℕ) : ℝ) ∧
      (((d / 2) * m : ℕ) : ℝ) / ((d - m - d / 2 + 1 : ℕ) : ℝ) ≤ (16 / 15 : ℝ) * m := by
  obtain ⟨_, _, _, h32, _, hmhd⟩ := wrapper_radius_data hm hdim
  have hp : 0 < d - m - d / 2 + 1 := by omega
  have hpeq : ((d - m - d / 2 + 1 : ℕ) : ℝ) + m + (d / 2 : ℕ) = (d : ℝ) + 1 := by
    exact_mod_cast (show d - m - d / 2 + 1 + m + d / 2 = d + 1 by omega)
  have h32R : (32 : ℝ) * m ≤ d := by exact_mod_cast h32
  have hhalf : (2 : ℝ) * (d / 2 : ℕ) ≤ d := by
    exact_mod_cast (show 2 * (d / 2) ≤ d by omega)
  have hdimR : (15 : ℝ) * d ≤ 32 * ((d - m - d / 2 + 1 : ℕ) : ℝ) := by linarith
  refine ⟨hp, hdimR, ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hp : (0 : ℝ) < (d - m - d / 2 + 1 : ℕ))).mpr
  rw [Nat.cast_mul]
  nlinarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (α := ℝ) m),
    mul_le_mul_of_nonneg_right hdimR (Nat.cast_nonneg (α := ℝ) m)]

/-- The numerical hypothesis of `s4:lem:selection` in the S4 stage regime. -/
theorem selection_radius_bound {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d) :
    9 * wrapperRadius d m * Real.sqrt
      (Real.log (Real.exp 1 + (((d / 2) * m : ℕ) : ℝ) / ((d - m - d / 2 + 1 : ℕ) : ℝ)) /
        ((d - m - d / 2 + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  obtain ⟨hR, hsq, _, _, _, _⟩ := wrapper_radius_data hm hdim
  obtain ⟨hp, hdimR, hratio⟩ := residual_dimension_budget hm hdim
  let p : ℝ := (d - m - d / 2 + 1 : ℕ)
  let Q : ℝ := ((d / 2) * m : ℕ)
  have hpR : 0 < p := by dsimp [p]; exact_mod_cast hp
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  change Q / p ≤ (16 / 15 : ℝ) * m at hratio
  change (15 : ℝ) * d ≤ 32 * p at hdimR
  have hell := stageLog_ge_one m
  have hden : 0 < 768 * stageLog m := by linarith
  have hprod : wrapperRadius d m ^ 2 * (768 * stageLog m) = d :=
    (eq_div_iff (ne_of_gt hden)).mp hsq
  have hlog : Real.log (Real.exp 1 + Q / p) ≤ (16 / 15 : ℝ) * stageLog m := by
    calc
      _ ≤ Real.log (Real.exp 1 + (16 / 15 : ℝ) * m) :=
        Real.log_le_log (by positivity) (by linarith)
      _ ≤ _ := log_dilation (by norm_num) (Nat.cast_nonneg m)
  have hlogpos : 0 ≤ Real.log (Real.exp 1 + Q / p) := by
    have hge : 1 ≤ Real.log (Real.exp 1 + Q / p) := by
      calc
        1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right (div_nonneg hQ hpR.le))
    linarith
  have hprodlog : 81 * wrapperRadius d m ^ 2 * Real.log (Real.exp 1 + Q / p) ≤
      (9 / 80 : ℝ) * d := by
    have hh := mul_le_mul_of_nonneg_left hlog (sq_nonneg (wrapperRadius d m))
    nlinarith
  have hfrac : 81 * wrapperRadius d m ^ 2 * (Real.log (Real.exp 1 + Q / p) / p) ≤
      (6 / 25 : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  have hsqrt := Real.sq_sqrt (div_nonneg hlogpos hpR.le)
  change 9 * wrapperRadius d m * Real.sqrt (Real.log (Real.exp 1 + Q / p) / p) ≤ 1 / 2
  have hsquare : (9 * wrapperRadius d m *
      Real.sqrt (Real.log (Real.exp 1 + Q / p) / p)) ^ 2 ≤ (6 / 25 : ℝ) := by
    calc
      _ = 81 * wrapperRadius d m ^ 2 *
          (Real.sqrt (Real.log (Real.exp 1 + Q / p) / p)) ^ 2 := by ring
      _ = 81 * wrapperRadius d m ^ 2 * (Real.log (Real.exp 1 + Q / p) / p) := by rw [hsqrt]
      _ ≤ _ := hfrac
  nlinarith [sq_nonneg (9 * wrapperRadius d m *
    Real.sqrt (Real.log (Real.exp 1 + Q / p) / p) - 1 / 2)]

/-- The concrete family with the new dimension-dependent S4 radius. -/
def wrapperFamily (d m : ℕ) (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d) :
    Stage.Family d m (wrapperRadius d m) (1 / 2) (5 / 8) :=
  SublevelFamily.family d m (wrapperRadius d m) (by omega)
    (wrapper_radius_data hm hdim).1 (wrapper_radius_data hm hdim).2.2.1

theorem wrapper_base_sublevel {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d)
    (U : List (X d)) (hU : OrthoList U) (hlen : U.length = m) :
    SublevelClass 108 (wrapperGap m) (wrapperTrace m) ((wrapperFamily d m hm hdim).objective U) := by
  obtain ⟨hR, hsq, hlarge, h32, _, _⟩ := wrapper_radius_data hm hdim
  have hell := stageLog_ge_one m
  have hell0 : stageLog m ≠ 0 := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 := ne_of_gt hdpos
  have hden : 0 < 8 * wrapperRadius d m ^ 2 := by positivity
  have hratio : 1007 * (m : ℝ) / (8 * wrapperRadius d m ^ 2) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have htrace_eq : 1007 * (d : ℝ) * (m : ℝ) / (8 * wrapperRadius d m ^ 2) =
      96672 * (m : ℝ) * stageLog m := by
    rw [hsq]
    field_simp
    ring
  have hs := SublevelWrapper.objective_smoothClass m hR (by omega) hlarge hU hlen
  refine ⟨⟨hs.1.mono (by norm_num), hs.2⟩,
    SublevelMatrix.matrix m (wrapperRadius d m) U,
    ⟨SublevelMatrix.matrix_symmetric _ _ _, SublevelMatrix.matrix_positive _ _ _, ?_, ?_⟩,
    SublevelUpper.upper_model (by omega) hR hlarge hU hlen⟩
  · linarith [SublevelMatrix.matrix_norm m (wrapperRadius d m) hU]
  · rw [SublevelMatrix.matrix_trace m (wrapperRadius d m) hU hlen, htrace_eq]
    unfold wrapperTrace
    nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem normalization_108_budget {m : ℕ} (_hm : 2 ≤ m) :
    108 * wrapperGap m / (5 / 8 : ℝ) ^ 2 ≤ 625 * (m : ℝ) := by
  unfold wrapperGap
  norm_num
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem effective_parameters {m : ℕ} {L Δ ε E : ℝ}
    (hm : 2 ≤ m) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2)) :
    let T := L * Δ / ε ^ 2
    let L' := 625 * (m : ℝ) * L / T
    0 < L' ∧ L' ≤ L ∧ L' * wrapperTrace m ≤ L * E ∧
      108 * wrapperGap m / (5 / 8 : ℝ) ^ 2 ≤ L' * Δ / ε ^ 2 := by
  dsimp
  let T := L * Δ / ε ^ 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hε0 := ne_of_gt hε
  have hL0 := ne_of_gt hL
  have hΔ0 := ne_of_gt hΔ
  change 0 < 625 * (m : ℝ) * L / T ∧ _
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hT).mpr
    nlinarith
  · change (625 * (m : ℝ) * L / T) * (900 * (m : ℝ) * stageLog m) ≤ L * E
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hT).mpr
    have ht := mul_le_mul_of_nonneg_left htrace hL.le
    dsimp [T]
    nlinarith
  · have heq : (625 * (m : ℝ) * L / T) * Δ / ε ^ 2 = 625 * (m : ℝ) := by
      dsimp [T]
      field_simp
      ring
    rw [heq]
    exact normalization_108_budget hm

/-- `s4:thm:stages`, conditional on the strip selector. The class inclusion and the adaptive oracle reduction are
proved here; the conclusion is the actual deterministic minimax complexity. -/
theorem deterministic_stage_lower {d m : ℕ} {L Δ ε E : ℝ}
    (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d)
    (selector : StripSelector (d := d) (wrapperRadius d m) (1 / 2)
      (d - m - d / 2 + 1) ((d / 2) * m)) :
    (((d / 2) * m : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε := by
  obtain ⟨_, _, _, _, hhalf, hmhd⟩ := wrapper_radius_data hm hdim
  let L' := 625 * (m : ℝ) * L / (L * Δ / ε ^ 2)
  obtain ⟨hLpos, hLle, hLE, hbudget⟩ := effective_parameters hm hL hΔ hε hsteps htrace
  change 0 < L' at hLpos
  change L' ≤ L at hLle
  change L' * wrapperTrace m ≤ L * E at hLE
  change 108 * wrapperGap m / (5 / 8 : ℝ) ^ 2 ≤ L' * Δ / ε ^ 2 at hbudget
  let s := 108 * ε / (L' * (5 / 8))
  let a := 108 * ε ^ 2 / (L' * (5 / 8) ^ 2)
  obtain ⟨hs, ha, hratio, hscale, hgap⟩ :=
    normalization_parameters hLpos hε (by norm_num : (0 : ℝ) < 5 / 8)
      (by norm_num : (0 : ℝ) < 108) hbudget
  change 0 < s at hs
  change 0 < a at ha
  change a / s = ε / (5 / 8) at hratio
  change a / s ^ 2 = L' / 108 at hscale
  change a * wrapperGap m ≤ Δ at hgap
  let J : X d →ₗᵢ[ℝ] X d := LinearIsometry.id
  have hclass : ∀ F ∈ Stage.familyClass (wrapperFamily d m hm hdim),
      embedObjective J a s F ∈ {f | SublevelClass L Δ E f} := by
    rintro F ⟨U, hU, hlen, rfl⟩
    have hbase := wrapper_base_sublevel hm hdim U hU hlen
    have hscaled := embedObjective_sublevelClass J ha hs (by norm_num : (0 : ℝ) ≤ 108)
      ((wrapperFamily d m hm hdim).objective U) hbase
    rw [hscale, div_mul_cancel₀ L' (by norm_num : (108 : ℝ) ≠ 0)] at hscaled
    exact hscaled.mono hLle hgap hLE
  have hsim := Ndet_le_of_embedding (ε := (5 / 8 : ℝ)) J ha hs hclass
  have hacc : (a / s) * (5 / 8 : ℝ) = ε := by rw [hratio]; ring
  rw [hacc] at hsim
  exact (Stage.stage_lower_bound (wrapperFamily d m hm hdim) (by omega) hhalf selector hmhd).trans hsim

theorem deterministic_stage_lower_value {d m : ℕ} {L Δ ε E : ℝ}
    (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d)
    (selector : StripSelector (d := d) (wrapperRadius d m) (1 / 2)
      (d - m - d / 2 + 1) ((d / 2) * m)) :
    (((d / 2) * m : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (deterministic_stage_lower hm hL hΔ hε hsteps htrace hdim selector).trans
    (Ndet_linear_le_value _ ε)

/-- The accuracy-dependent window supplies all three unsmoothed stage budgets
for every integer `m` with `786432 * m ≤ T`. -/
theorem window_stage_parameters {d m : ℕ} {T E : ℝ} (hT : 0 ≤ T)
    (hwindow : T * Real.log (Real.exp 1 + T) ≤ E) (hEd : E ≤ d)
    (hmT : (786432 : ℝ) * (m : ℝ) ≤ T) :
    625 * (m : ℝ) ≤ T ∧
      562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * T ∧
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hell := stageLog_ge_one m
  have hmle : (m : ℝ) ≤ T := by linarith
  have hlog : stageLog m ≤ Real.log (Real.exp 1 + T) :=
    Real.log_le_log (by positivity) (by linarith)
  have h625 : 625 * (m : ℝ) ≤ T := by linarith
  refine ⟨h625, ?_, ?_⟩
  · have hsquare : 562500 * (m : ℝ) ^ 2 ≤ T ^ 2 := by
      have h750 : 750 * (m : ℝ) ≤ T := by linarith
      have hh := mul_self_le_mul_self (by positivity : 0 ≤ 750 * (m : ℝ)) h750
      nlinarith [sq_nonneg (m : ℝ)]
    calc
      562500 * (m : ℝ) ^ 2 * stageLog m ≤ T ^ 2 * stageLog m :=
        mul_le_mul_of_nonneg_right hsquare (by linarith)
      _ ≤ T ^ 2 * Real.log (Real.exp 1 + T) := mul_le_mul_of_nonneg_left hlog (sq_nonneg T)
      _ ≤ E * T := by nlinarith [mul_le_mul_of_nonneg_right hwindow hT]
  · calc
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ T * stageLog m :=
        mul_le_mul_of_nonneg_right hmT (by linarith)
      _ ≤ T * Real.log (Real.exp 1 + T) := mul_le_mul_of_nonneg_left hlog hT
      _ ≤ E := hwindow
      _ ≤ d := hEd

/-- The new S4 window rate, conditional on geometric selection. The result concerns actual minimax
complexity with unrestricted rank-priced queries and arbitrary outputs. -/
theorem deterministic_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2359296⌉₊ : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε := by
  let T := L * Δ / ε ^ 2
  have hTpos : 0 < T := by dsimp [T]; positivity
  change ((⌈(d : ℝ) * T / 2359296⌉₊ : ℕ) : ℕ∞) ≤ _
  by_cases hsmall : T < 2359296
  · have hceil : ⌈(d : ℝ) * T / 2359296⌉₊ ≤ d := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2359296)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans
      (dimension_floor_sublevel hd hL hΔ hε hE hEd (by linarith))
  · let m := ⌊T / 786432⌋₊
    have hm3 : 3 ≤ m := Nat.le_floor (by dsimp [T] at *; linarith)
    have hm : 2 ≤ m := by omega
    have hmT : (786432 : ℝ) * (m : ℝ) ≤ T := by
      have hf := Nat.floor_le (by positivity : 0 ≤ T / 786432)
      change (m : ℝ) ≤ T / 786432 at hf
      norm_num
      linarith
    obtain ⟨hsteps, htrace, hdim⟩ := window_stage_parameters hTpos.le hwindow hEd hmT
    have hstage := deterministic_stage_lower hm hL hΔ hε
      hsteps htrace hdim (selectors m hm hdim)
    have h32 := (wrapper_radius_data hm hdim).2.2.2.1
    have hd9 : (9 : ℝ) ≤ d := by exact_mod_cast (show 9 ≤ d by omega)
    have hhalf : (4 : ℝ) * d ≤ 9 * ((d / 2 : ℕ) : ℝ) := by
      have hh : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show d ≤ 2 * (d / 2) + 1 by omega)
      linarith
    have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hf : T / 786432 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hround : 3 * T ≤ 3145728 * (m : ℝ) := by linarith
    have hceil : ⌈(d : ℝ) * T / 2359296⌉₊ ≤ (d / 2) * m := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2359296)).mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (α := ℝ) m),
        mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans hstage

theorem deterministic_window_lower_value {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2359296⌉₊ : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (deterministic_window_lower hd hL hΔ hε hE hEd hT hwindow selectors).trans
    (Ndet_linear_le_value _ ε)

/-- The rounded S4 choice supplies all three stage budgets. -/
theorem rounded_stage_parameters {d m : ℕ} {T E : ℝ}
    (hm : 2 ≤ m) (_hT : 0 < T) (hET : E * T ≤ d)
    (hmM : 750 * (m : ℝ) ≤ min T (Real.sqrt (E * T / Real.log (Real.exp 1 + T)))) :
    625 * (m : ℝ) ≤ T ∧
      562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * T ∧
      786432 * (m : ℝ) * stageLog m ≤ d := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmT := hmM.trans (min_le_left _ _)
  have hmS := hmM.trans (min_le_right _ _)
  have hmle : (m : ℝ) ≤ T := by linarith
  have hell := stageLog_ge_one m
  have hlog : stageLog m ≤ Real.log (Real.exp 1 + T) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogpos : 0 < Real.log (Real.exp 1 + T) := by linarith
  have hquot : 0 ≤ E * T / Real.log (Real.exp 1 + T) := by
    by_contra hn
    have hz := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hn)
    rw [hz] at hmS
    linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 750 * (m : ℝ)) hmS
  rw [Real.mul_self_sqrt hquot] at hsq
  have hprod : 562500 * (m : ℝ) ^ 2 * Real.log (Real.exp 1 + T) ≤ E * T := by
    have hh := (le_div_iff₀ hlogpos).mp hsq
    nlinarith
  have htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * T := by
    calc
      _ ≤ 562500 * (m : ℝ) ^ 2 * Real.log (Real.exp 1 + T) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ E * T := hprod
  refine ⟨by linarith, htrace, ?_⟩
  have hdim' : 786432 * (m : ℝ) * stageLog m ≤
      562500 * (m : ℝ) ^ 2 * stageLog m := by
    have hh : 786432 * (m : ℝ) ≤ 562500 * (m : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hh (by linarith)
  exact hdim'.trans (htrace.trans hET)

/-- S4's `1 / 2250` rate. The geometric selector is explicit; the analytic wrapper is constructed
from its concrete value and gradient, without an assumed complexity bound. -/
theorem deterministic_rounded_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε := by
  let T := L * Δ / ε ^ 2
  let M := min T (Real.sqrt (E * T / Real.log (Real.exp 1 + T)))
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hMpos : 0 ≤ M := le_min hTpos.le (Real.sqrt_nonneg _)
  change ((⌈(d : ℝ) * M / 2250⌉₊ : ℕ) : ℕ∞) ≤ _
  by_cases hsmall : M < 2250
  · have hceil : ⌈(d : ℝ) * M / 2250⌉₊ ≤ d := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2250)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans
      (dimension_floor_sublevel hd hL hΔ hε hE hEd (by linarith))
  · let m := ⌊M / 750⌋₊
    have hm3 : 3 ≤ m := Nat.le_floor (by linarith)
    have hm : 2 ≤ m := by omega
    have hmM : 750 * (m : ℝ) ≤ M := by
      have hf := Nat.floor_le (by positivity : 0 ≤ M / 750)
      change (m : ℝ) ≤ M / 750 at hf
      linarith
    obtain ⟨hsteps, htrace, hdim⟩ := rounded_stage_parameters hm hTpos hET hmM
    have hstage := deterministic_stage_lower hm hL hΔ hε
      hsteps htrace hdim (selectors m hm hdim)
    have h32 := (wrapper_radius_data hm hdim).2.2.2.1
    have hd9 : (9 : ℝ) ≤ d := by exact_mod_cast (show 9 ≤ d by omega)
    have hhalf : (4 : ℝ) * d ≤ 9 * ((d / 2 : ℕ) : ℝ) := by
      have hh : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show d ≤ 2 * (d / 2) + 1 by omega)
      linarith
    have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hf : M / 750 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hround : 3 * M ≤ 3000 * (m : ℝ) := by linarith
    have hceil : ⌈(d : ℝ) * M / 2250⌉₊ ≤ (d / 2) * m := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2250)).mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (α := ℝ) m),
        mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans hstage

theorem deterministic_rounded_lower_value {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (deterministic_rounded_lower hd hL hΔ hε hE hEd hT hET selectors).trans
    (Ndet_linear_le_value _ ε)

end ExactZO.S4Lower
