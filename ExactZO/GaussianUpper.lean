import ExactZO.GaussianDirection
import ExactZO.STPIID

/-! An explicit finite Gaussian seed discharges every probability input in the
three-point upper bound. The seed law and algorithm precede the objective. -/
noncomputable section
open MeasureTheory

namespace ExactZO.STP

/-- The actual finite Gaussian experiment has the proved failure probability. -/
theorem gaussian_output_failure {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε)
    (f : Objective d) (hf : SublevelClass L Δ E f) :
    let N := horizon (L * E) Δ ε
    letI : NeZero N := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
    (outputMeasure (iidMeasure (Gaussian.standardGaussian d) N) N).real
      {p | ε < ‖f.grad (output f (4 * ε / (5 * (L * E)))
        (iidDirections N) N p)‖} ≤ 25 / 78 := by
  exact sublevel_output_failure hL hΔ hE hε
    (iidMeasure (Gaussian.standardGaussian d) _) (Gaussian.standardGaussian d)
    (iidDirections _) (iidDirections_measurable _) (Gaussian.directionMoments d)
    GaussianScalar.gaussian_alpha_lower (iid_freshForClass _ _ _ _) f hf

/-- One fixed seed law and value-only method works on the entire class,
with the cap holding for every seed, including null-probability seeds. -/
theorem gaussian_random_costCap {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε) :
    let N := horizon (L * E) Δ ε
    letI : NeZero N := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
    (valueModel d).RandomCostCap
      (seedMethod (iidMeasure (Gaussian.standardGaussian d) N)
        (4 * ε / (5 * (L * E))) (iidDirections N) (iidDirections_measurable N) N)
      (SublevelClass L Δ E) ε (1 / 3) (1 + 2 * N) := by
  exact sublevel_random_costCap hL hΔ hE hε
    (iidMeasure (Gaussian.standardGaussian d) _) (Gaussian.standardGaussian d)
    (iidDirections _) (iidDirections_measurable _) (Gaussian.directionMoments d)
    GaussianScalar.gaussian_alpha_lower (iid_freshForClass _ _ _ _)

/-- Unconditional randomized value-query upper bound for the capped class. -/
theorem gaussian_random_upper {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε) :
    (valueModel d).Nrand (SublevelClass L Δ E) ε (1 / 3) ≤
      ((1 + 2 * horizon (L * E) Δ ε : ℕ) : ℕ∞) := by
  exact sublevel_random_upper hL hΔ hE hε
    (iidMeasure (Gaussian.standardGaussian d) _) (Gaussian.standardGaussian d)
    (iidDirections _) (iidDirections_measurable _) (Gaussian.directionMoments d)
    GaussianScalar.gaussian_alpha_lower (iid_freshForClass _ _ _ _)

/-- The paper's explicit `23 E T` constant, with no probability premises. -/
theorem gaussian_random_upper_twenty_three {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 1 ≤ E) (hε : 0 < ε)
    (hT : 1 ≤ L * Δ / ε ^ 2) :
    (valueModel d).Nrand (SublevelClass L Δ E) ε (1 / 3) ≤
      (⌊23 * E * (L * Δ / ε ^ 2)⌋₊ : ℕ∞) := by
  apply (gaussian_random_upper hL hΔ (by linarith) hε).trans
  exact ENat.coe_le_coe.mpr (Nat.le_floor (sublevel_query_bound hE hT))

end ExactZO.STP
