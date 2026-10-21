import ExactZO.Oracle
import Mathlib.MeasureTheory.Measure.Real

noncomputable section
open MeasureTheory
namespace ExactZO

/-- A random seed law and a history policy are chosen before the objective.
The policy is jointly measurable in the seed and every finite history.
Every seed gives one ordinary deterministic history policy. -/
structure RandomizedMethod {d : ℕ} (M : OracleModel d) where
  Sample : Type
  measurableSpace : MeasurableSpace Sample
  law : @Measure Sample measurableSpace
  probability : @IsProbabilityMeasure Sample measurableSpace law
  policy : Sample → M.Algorithm
  policy_joint_measurable : @OracleModel.JointlyMeasurable d M Sample measurableSpace policy

namespace OracleModel
variable {d : ℕ} (M : OracleModel d)

/-- The bad event includes missing finite termination. Outputs remain free. -/
def randomBad (A : RandomizedMethod M) (f : Objective d) (ε : ℝ) : Set A.Sample :=
  {ω | ¬ ∃ n x, M.Runs (A.policy ω) f n x ∧ ‖f.grad x‖ ≤ ε}

/-- A hard cap holds on every seed and every legal objective. The one law
and policy precede all objectives; the failure event is explicitly measurable. -/
def RandomCostCap (A : RandomizedMethod M) (C : Set (Objective d))
    (ε δ : ℝ) (N : ℕ) : Prop :=
  (∀ f ∈ C, ∀ ω, ∃ n x, n ≤ N ∧ M.Runs (A.policy ω) f n x) ∧
  (∀ f ∈ C, @MeasurableSet A.Sample A.measurableSpace (M.randomBad A f ε) ∧
    A.law.real (M.randomBad A f ε) ≤ δ)

/-- Infimum over finite hard caps, with infinity when no such method exists. -/
def Nrand (C : Set (Objective d)) (ε δ : ℝ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∃ A : RandomizedMethod M, M.RandomCostCap A C ε δ N), (N : ℕ∞)

theorem Nrand_le_of_costCap {C : Set (Objective d)} {ε δ : ℝ} {N : ℕ}
    (A : RandomizedMethod M) (hA : M.RandomCostCap A C ε δ N) :
    M.Nrand C ε δ ≤ N := by
  exact iInf_le_of_le N (iInf_le _ ⟨A, hA⟩)

theorem randomBad_eq_of_runs (A : RandomizedMethod M) (f : Objective d) (ε : ℝ)
    (n : A.Sample → ℕ) (output : A.Sample → X d)
    (hrun : ∀ ω, M.Runs (A.policy ω) f (n ω) (output ω)) :
    M.randomBad A f ε = {ω | ε < ‖f.grad (output ω)‖} := by
  ext ω
  change (¬ ∃ k x, M.Runs (A.policy ω) f k x ∧ ‖f.grad x‖ ≤ ε) ↔ _
  constructor
  · intro h
    by_contra hn
    exact h ⟨n ω, output ω, hrun ω, le_of_not_gt hn⟩
  · rintro hb ⟨k, x, hx, hg⟩
    have he := (RunFrom.unique M hx (hrun ω)).2
    rw [he] at hg
    exact (not_lt_of_ge hg) hb

end OracleModel
end ExactZO
