import ExactZO.Stage
import ExactZO.Simulation
import ExactZO.DimensionFloor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
Conditional connection for `wk:prop:fixed-sublevel`: the unsmoothed wrapper
uses normalization 108 and the constants 625, 187500, and 2^18. The analytic
wrapper construction remains explicit in `WrapperProperties`; neither class
membership after scaling nor any complexity lower bound is assumed there.
The strip selector also remains an explicit premise.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.DeterministicLower

open StageGeometry

def stageLog (m : ℕ) : ℝ := Real.log (Real.exp 1 + (m : ℝ))
def wrapperRadius (d m : ℕ) : ℝ := Real.sqrt ((d : ℝ) / (256 * stageLog m))
def wrapperGap (m : ℕ) : ℝ := (9 / 4 : ℝ) * ((m : ℝ) - 1 / 2)
def wrapperTrace (m : ℕ) : ℝ := 300 * (m : ℝ) * stageLog m

/-- These are the unproved analytic properties of the actual unsmoothed
family. The family includes its bounded map, exact prefix identity, and
strict gradient barrier. Each full frame has ONE fixed upper matrix whose
segment model holds throughout its strict initial sublevel. -/
structure WrapperProperties (d m : ℕ) where
  family : Stage.Family d m (wrapperRadius d m) (1 / 2) (5 / 8)
  matrix : List (X d) → (X d →L[ℝ] X d)
  smooth : ∀ U, OrthoList U → U.length = m → Smooth (family.objective U) 50
  gap : ∀ U, OrthoList U → U.length = m → HasGap (family.objective U) (wrapperGap m)
  symmetric : ∀ U, OrthoList U → U.length = m →
    ∀ x y, ⟪matrix U x, y⟫_ℝ = ⟪x, matrix U y⟫_ℝ
  positive : ∀ U, OrthoList U → U.length = m → ∀ x, 0 ≤ ⟪x, matrix U x⟫_ℝ
  norm_bound : ∀ U, OrthoList U → U.length = m →
    ‖matrix U‖ ≤ 106 + 1007 * (m : ℝ) / (8 * wrapperRadius d m ^ 2)
  trace_bound : ∀ U, OrthoList U → U.length = m →
    LinearMap.trace ℝ (X d) (matrix U).toLinearMap ≤
      106 * (m : ℝ) + 1007 * (d : ℝ) * (m : ℝ) / (8 * wrapperRadius d m ^ 2)
  upper_model : ∀ U, OrthoList U → U.length = m →
    ∀ x y, segment ℝ x y ⊆ StrictSublevel (family.objective U) →
      QuadraticUpper (family.objective U) (matrix U) x y

theorem stageLog_ge_one (m : ℕ) : 1 ≤ stageLog m := by
  unfold stageLog
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.exp 1 + (m : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Nat.cast_nonneg (α := ℝ) m])

theorem wrapper_radius_data {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d) :
    0 < wrapperRadius d m ∧
      wrapperRadius d m ^ 2 = (d : ℝ) / (256 * stageLog m) ∧
      1024 * (m : ℝ) ≤ wrapperRadius d m ^ 2 ∧
      32 * m ≤ d ∧ 0 < d / 2 ∧ m + d / 2 ≤ d := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hell := stageLog_ge_one m
  have hellpos : 0 < stageLog m := by linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * stageLog m := by nlinarith
  norm_num at hdim
  have h32R : (32 : ℝ) * (m : ℝ) ≤ d := by nlinarith
  have h32 : 32 * m ≤ d := by exact_mod_cast h32R
  have hdpos : (0 : ℝ) < d := by nlinarith
  have hquot : 0 < (d : ℝ) / (256 * stageLog m) := by positivity
  have hsq : wrapperRadius d m ^ 2 = (d : ℝ) / (256 * stageLog m) :=
    Real.sq_sqrt hquot.le
  refine ⟨Real.sqrt_pos.2 hquot, hsq, ?_, h32, by omega, by omega⟩
  rw [hsq]
  apply (le_div_iff₀ (by positivity : 0 < 256 * stageLog m)).mpr
  nlinarith

theorem wrapper_base_sublevel {d m : ℕ} (w : WrapperProperties d m) (hm : 2 ≤ m)
    (hdim : (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d)
    (U : List (X d)) (hU : OrthoList U) (hlen : U.length = m) :
    SublevelClass 108 (wrapperGap m) (wrapperTrace m) (w.family.objective U) := by
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
      32224 * (m : ℝ) * stageLog m := by
    rw [hsq]
    field_simp
    ring
  refine ⟨⟨(w.smooth U hU hlen).mono (by norm_num), w.gap U hU hlen⟩,
    w.matrix U, ⟨w.symmetric U hU hlen, w.positive U hU hlen, ?_, ?_⟩,
    w.upper_model U hU hlen⟩
  · linarith [w.norm_bound U hU hlen]
  · have ht := w.trace_bound U hU hlen
    rw [htrace_eq] at ht
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
    (htrace : 187500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2)) :
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
  · change (625 * (m : ℝ) * L / T) * (300 * (m : ℝ) * stageLog m) ≤ L * E
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

/-- `wk:prop:fixed-sublevel`, conditional on the explicit wrapper properties
and strip selector. The class inclusion and the adaptive oracle reduction are
proved here; the conclusion is the actual deterministic minimax complexity. -/
theorem deterministic_stage_lower {d m : ℕ} {L Δ ε E : ℝ}
    (w : WrapperProperties d m) (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 187500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d)
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
  have hclass : ∀ F ∈ Stage.familyClass w.family,
      embedObjective J a s F ∈ {f | SublevelClass L Δ E f} := by
    rintro F ⟨U, hU, hlen, rfl⟩
    have hbase := wrapper_base_sublevel w hm hdim U hU hlen
    have hscaled := embedObjective_sublevelClass J ha hs (by norm_num : (0 : ℝ) ≤ 108)
      (w.family.objective U) hbase
    rw [hscale, div_mul_cancel₀ L' (by norm_num : (108 : ℝ) ≠ 0)] at hscaled
    exact hscaled.mono hLle hgap hLE
  have hsim := Ndet_le_of_embedding (ε := (5 / 8 : ℝ)) J ha hs hclass
  have hacc : (a / s) * (5 / 8 : ℝ) = ε := by rw [hratio]; ring
  rw [hacc] at hsim
  exact (Stage.stage_lower_bound w.family (by omega) hhalf selector hmhd).trans hsim

theorem deterministic_stage_lower_value {d m : ℕ} {L Δ ε E : ℝ}
    (w : WrapperProperties d m) (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 187500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d)
    (selector : StripSelector (d := d) (wrapperRadius d m) (1 / 2)
      (d - m - d / 2 + 1) ((d / 2) * m)) :
    (((d / 2) * m : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (deterministic_stage_lower w hm hL hΔ hε hsteps htrace hdim selector).trans
    (Ndet_linear_le_value _ ε)

/-- The accuracy-dependent window supplies all three unsmoothed stage budgets
for every integer `m` with `2^18 * m ≤ T`. -/
theorem window_stage_parameters {d m : ℕ} {T E : ℝ} (hT : 0 ≤ T)
    (hwindow : T * Real.log (Real.exp 1 + T) ≤ E) (hEd : E ≤ d)
    (hmT : (2 : ℝ) ^ 18 * (m : ℝ) ≤ T) :
    625 * (m : ℝ) ≤ T ∧
      187500 * (m : ℝ) ^ 2 * stageLog m ≤ E * T ∧
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hell := stageLog_ge_one m
  have hmle : (m : ℝ) ≤ T := by norm_num at hmT; linarith
  have hlog : stageLog m ≤ Real.log (Real.exp 1 + T) :=
    Real.log_le_log (by positivity) (by linarith)
  have h625 : 625 * (m : ℝ) ≤ T := by norm_num at hmT; linarith
  refine ⟨h625, ?_, ?_⟩
  · have hsquare : 187500 * (m : ℝ) ^ 2 ≤ T ^ 2 := by
      have hh := mul_self_le_mul_self (by positivity : 0 ≤ 625 * (m : ℝ)) h625
      nlinarith [sq_nonneg (m : ℝ)]
    calc
      187500 * (m : ℝ) ^ 2 * stageLog m ≤ T ^ 2 * stageLog m :=
        mul_le_mul_of_nonneg_right hsquare (by linarith)
      _ ≤ T ^ 2 * Real.log (Real.exp 1 + T) := mul_le_mul_of_nonneg_left hlog (sq_nonneg T)
      _ ≤ E * T := by nlinarith [mul_le_mul_of_nonneg_right hwindow hT]
  · calc
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ T * stageLog m :=
        mul_le_mul_of_nonneg_right hmT (by linarith)
      _ ≤ T * Real.log (Real.exp 1 + T) := mul_le_mul_of_nonneg_left hlog hT
      _ ≤ E := hwindow
      _ ≤ d := hEd

/-- Conditional window corollary for the UNSMOOTHED main-class witnesses.
The stronger coefficient `1 / 786432 = 1 / (3 * 2^18)` follows from the
unsmoothed stage conditions. It does not assert the paper's additional
`C^∞` or Hessian-Lipschitz witness promises. Ceil converts the real rate
exactly to the integer-valued complexity, including infinite complexity. -/
theorem deterministic_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (wrappers : ∀ m : ℕ, 2 ≤ m →
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d → WrapperProperties d m)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 786432⌉₊ : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε := by
  let T := L * Δ / ε ^ 2
  have hTpos : 0 < T := by dsimp [T]; positivity
  change ((⌈(d : ℝ) * T / 786432⌉₊ : ℕ) : ℕ∞) ≤ _
  by_cases hsmall : T < 786432
  · have hceil : ⌈(d : ℝ) * T / 786432⌉₊ ≤ d := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 786432)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans
      (dimension_floor_sublevel hd hL hΔ hε hE hEd (by linarith))
  · let m := ⌊T / 262144⌋₊
    have hm3 : 3 ≤ m := Nat.le_floor (by dsimp [T] at *; linarith)
    have hm : 2 ≤ m := by omega
    have hmT : (2 : ℝ) ^ 18 * (m : ℝ) ≤ T := by
      have hf := Nat.floor_le (by positivity : 0 ≤ T / 262144)
      change (m : ℝ) ≤ T / 262144 at hf
      norm_num
      linarith
    obtain ⟨hsteps, htrace, hdim⟩ := window_stage_parameters hTpos.le hwindow hEd hmT
    have hstage := deterministic_stage_lower (wrappers m hm hdim) hm hL hΔ hε
      hsteps htrace hdim (selectors m hm hdim)
    have h32 := (wrapper_radius_data hm hdim).2.2.2.1
    have hd9 : (9 : ℝ) ≤ d := by exact_mod_cast (show 9 ≤ d by omega)
    have hhalf : (4 : ℝ) * d ≤ 9 * ((d / 2 : ℕ) : ℝ) := by
      have hh : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show d ≤ 2 * (d / 2) + 1 by omega)
      linarith
    have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hf : T / 262144 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hround : 3 * T ≤ 1048576 * (m : ℝ) := by linarith
    have hceil : ⌈(d : ℝ) * T / 786432⌉₊ ≤ (d / 2) * m := by
      apply Nat.ceil_le.mpr
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 786432)).mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (α := ℝ) m),
        mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg (α := ℝ) d)]
    exact (ENat.coe_le_coe.mpr hceil).trans hstage

theorem deterministic_window_lower_value {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (wrappers : ∀ m : ℕ, 2 ≤ m →
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d → WrapperProperties d m)
    (selectors : ∀ m : ℕ, 2 ≤ m →
      (2 : ℝ) ^ 18 * (m : ℝ) * stageLog m ≤ d →
      StripSelector (d := d) (wrapperRadius d m) (1 / 2)
        (d - m - d / 2 + 1) ((d / 2) * m)) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 786432⌉₊ : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (deterministic_window_lower hd hL hΔ hε hE hEd hT hwindow wrappers selectors).trans
    (Ndet_linear_le_value _ ε)

end ExactZO.DeterministicLower
