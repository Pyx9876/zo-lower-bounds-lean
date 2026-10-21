import ExactZO.Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace ExactZO

/-- The positive normalization in the corrected scaling lemma. -/
theorem normalization_parameters {L ε b Lbar D Δ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hb : 0 < b) (hbar : 0 < Lbar)
    (hbudget : Lbar * D / b ^ 2 ≤ L * Δ / ε ^ 2) :
    let s := Lbar * ε / (L * b)
    let a := Lbar * ε ^ 2 / (L * b ^ 2)
    0 < s ∧ 0 < a ∧ a / s = ε / b ∧ a / s ^ 2 = L / Lbar ∧ a * D ≤ Δ := by
  dsimp
  have hL0 := ne_of_gt hL
  have hε0 := ne_of_gt hε
  have hb0 := ne_of_gt hb
  have hbar0 := ne_of_gt hbar
  refine ⟨by positivity, by positivity, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · have h := (div_le_div_iff₀ (sq_pos_of_pos hb) (sq_pos_of_pos hε)).mp hbudget
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hL (sq_pos_of_pos hb))).mpr
    convert h using 1 <;> ring

end ExactZO
