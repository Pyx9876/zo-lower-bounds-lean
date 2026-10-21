import ExactZO.S4Lower
import ExactZO.FiniteEntropySelection

/-! The finite entropy selector removes the last geometric premise from the
S4 deterministic lower bounds. Every conclusion uses the actual oracle complexity. -/
noncomputable section
namespace ExactZO.S4Selection
open StageGeometry S4Lower

theorem stage_selector {d m : ℕ} (hm : 2 ≤ m)
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d) :
    StripSelector (d := d) (wrapperRadius d m) (1 / 2)
      (d - m - d / 2 + 1) ((d / 2) * m) := by
  exact FiniteEntropySelection.unconditionalStripSelector
    (residual_dimension_budget hm hdim).1 (wrapper_radius_data hm hdim).1.le
    (selection_radius_bound hm hdim)

theorem deterministic_stage_lower {d m : ℕ} {L Δ ε E : ℝ}
    (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d)
:
    (((d / 2) * m : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_stage_lower hm hL hΔ hε hsteps htrace hdim (stage_selector hm hdim)

theorem deterministic_stage_lower_value {d m : ℕ} {L Δ ε E : ℝ}
    (hm : 2 ≤ m)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hsteps : 625 * (m : ℝ) ≤ L * Δ / ε ^ 2)
    (htrace : 562500 * (m : ℝ) ^ 2 * stageLog m ≤ E * (L * Δ / ε ^ 2))
    (hdim : (786432 : ℝ) * (m : ℝ) * stageLog m ≤ d)
:
    (((d / 2) * m : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_stage_lower_value hm hL hΔ hε hsteps htrace hdim (stage_selector hm hdim)

theorem deterministic_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
:
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2359296⌉₊ : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_window_lower hd hL hΔ hε hE hEd hT hwindow (fun _ hm hdim => stage_selector hm hdim)

theorem deterministic_window_lower_value {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
:
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2359296⌉₊ : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_window_lower_value hd hL hΔ hε hE hEd hT hwindow (fun _ hm hdim => stage_selector hm hdim)

theorem deterministic_rounded_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
:
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤
      (linearModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_rounded_lower hd hL hΔ hε hE hEd hT hET (fun _ hm hdim => stage_selector hm hdim)

theorem deterministic_rounded_lower_value {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
:
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤
      (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  S4Lower.deterministic_rounded_lower_value hd hL hΔ hε hE hEd hT hET (fun _ hm hdim => stage_selector hm hdim)

end ExactZO.S4Selection
