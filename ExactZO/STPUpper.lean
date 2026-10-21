import ExactZO.CappedModel
import ExactZO.STPDescent
import ExactZO.STPProbability
import ExactZO.RandomModel
import ExactZO.RandomEmbedding
import ExactZO.STPJoint

noncomputable section
open MeasureTheory

namespace ExactZO.STP

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The seed law and direction stream are fixed before all objectives. This is
the precise fresh-direction joint law still required by the conditional bound. -/
def FreshForClass (μ : Measure Ω) (ν : Measure (X d)) (a : ℕ → Ω → X d)
    (h : ℝ) (C : Set (Objective d)) (N : ℕ) : Prop :=
  ∀ f ∈ C, ∀ t < N,
    Measure.map (fun ω => (trajectory f h a t ω, a t ω)) μ =
      Measure.map (fun p : Ω × X d => (trajectory f h a t p.1, p.2)) (μ.prod ν)

/-- A single measurable seed distribution and value-only history policy,
with an independent uniform pre-update output index. -/
def seedMethod (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ)
    (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t)) (N : ℕ) [NeZero N] : RandomizedMethod (valueModel d) where
  Sample := Ω × Fin N
  measurableSpace := inferInstance
  law := outputMeasure μ N
  probability := inferInstance
  policy p := (procedure h (fun t => a t p.1) N p.2.val).algorithm
  policy_joint_measurable := procedure_jointlyMeasurable h a ha N

theorem seedMethod_runs (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ)
    (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t)) (N : ℕ) [NeZero N] (f : Objective d) (p : Ω × Fin N) :
    (valueModel d).Runs ((seedMethod μ h a ha N).policy p) f (1 + 2 * N)
      (output f h a N p) :=
  procedure_runs f h (fun t => a t p.1) N p.2.val p.2.isLt

/-- The class itself supplies the capped model; only the direction moments and
freshness law remain external probability inputs. -/
theorem sublevel_output_failure
    {L Δ E ε α : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (X d))
    (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t))
    (moments : DirectionMoments ν α) (hα : 79 / 100 ≤ α)
    (fresh : FreshForClass μ ν a (4 * ε / (5 * (L * E)))
      (SublevelClass L Δ E) (horizon (L * E) Δ ε))
    (f : Objective d) (hf : SublevelClass L Δ E f) :
    letI : NeZero (horizon (L * E) Δ ε) := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
    (outputMeasure μ (horizon (L * E) Δ ε)).real
      {p | ε < ‖f.grad (output f (4 * ε / (5 * (L * E))) a
        (horizon (L * E) Δ ε) p)‖} ≤ 25 / 78 := by
  letI : NeZero (horizon (L * E) Δ ε) := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
  have hg : Measurable f.grad := (hf.1.1.continuous_grad hL.le).measurable
  obtain ⟨H, hH, hcap⟩ := hf.exists_capped_model hL.le
  apply le_trans (output_failure_le_of_drift μ f _ ε a ha hg hf.1.2
    (decrease_pos (mul_pos hL hE) hε) (horizon (L * E) Δ ε) ?_)
    (horizon_failure_bound (mul_pos hL hE) hΔ hε)
  intro t ht
  exact expected_step_joint_drift f hf.1.2 H μ
    (trajectory f (4 * ε / (5 * (L * E))) a t) (a t)
    (trajectory_measurable f _ a ha t) (ha t) ν moments hε (mul_pos hL hE)
    hα hH.2.2.2 (trajectory_sublevel f _ a t)
    (fun ω v => hcap _ v (trajectory_sublevel f _ a t ω))
    (measurableSet_lt measurable_const ((hg.comp (trajectory_measurable f _ a ha t)).norm))
    (fresh f hf t ht)

theorem sublevel_random_costCap
    {L Δ E ε α : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (X d))
    (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t))
    (moments : DirectionMoments ν α) (hα : 79 / 100 ≤ α)
    (fresh : FreshForClass μ ν a (4 * ε / (5 * (L * E)))
      (SublevelClass L Δ E) (horizon (L * E) Δ ε)) :
    letI : NeZero (horizon (L * E) Δ ε) := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
    (valueModel d).RandomCostCap
      (seedMethod μ (4 * ε / (5 * (L * E))) a ha (horizon (L * E) Δ ε))
      (SublevelClass L Δ E) ε (1 / 3) (1 + 2 * horizon (L * E) Δ ε) := by
  letI : NeZero (horizon (L * E) Δ ε) := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
  constructor
  · intro f _ p
    exact ⟨_, _, le_rfl, seedMethod_runs μ _ a ha _ f p⟩
  · intro f hf
    rw [(valueModel d).randomBad_eq_of_runs _ f ε
      (fun _ => 1 + 2 * horizon (L * E) Δ ε)
      (output f (4 * ε / (5 * (L * E))) a (horizon (L * E) Δ ε))
      (seedMethod_runs μ _ a ha _ f)]
    constructor
    · exact measurableSet_lt measurable_const
        (((hf.1.1.continuous_grad hL.le).measurable.comp
          (output_measurable f _ a ha _)).norm)
    · exact (sublevel_output_failure hL hΔ hE hε μ ν a ha moments hα fresh f hf).trans
        (by norm_num)

/-- Actual randomized value-query complexity, with explicit uninstantiated
direction moments and freshness. The method precedes every objective. -/
theorem sublevel_random_upper
    {L Δ E ε α : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (X d))
    (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t))
    (moments : DirectionMoments ν α) (hα : 79 / 100 ≤ α)
    (fresh : FreshForClass μ ν a (4 * ε / (5 * (L * E)))
      (SublevelClass L Δ E) (horizon (L * E) Δ ε)) :
    (valueModel d).Nrand (SublevelClass L Δ E) ε (1 / 3) ≤
      (1 + 2 * horizon (L * E) Δ ε : ℕ) := by
  letI : NeZero (horizon (L * E) Δ ε) := ⟨ne_of_gt (horizon_pos (mul_pos hL hE) hΔ hε)⟩
  exact (valueModel d).Nrand_le_of_costCap _
    (sublevel_random_costCap hL hΔ hE hε μ ν a ha moments hα fresh)

theorem sublevel_query_bound {L Δ E ε : ℝ} (hE : 1 ≤ E)
    (hT : 1 ≤ L * Δ / ε ^ 2) :
    ((1 + 2 * horizon (L * E) Δ ε : ℕ) : ℝ) ≤ 23 * E * (L * Δ / ε ^ 2) := by
  have he : 10 * (L * E) * Δ / ε ^ 2 = 10 * E * (L * Δ / ε ^ 2) := by ring
  simpa only [horizon, he] using query_bound hE hT

end ExactZO.STP

namespace ExactZO

/-- Zero-rank embedding preserves the seed law and every run. -/
def embedRandomValue {d : ℕ} (A : RandomizedMethod (valueModel d)) :
    RandomizedMethod (linearModel d) where
  Sample := A.Sample
  measurableSpace := A.measurableSpace
  law := A.law
  probability := A.probability
  policy ω := embedValueAlgorithm (A.policy ω)
  policy_joint_measurable := by
    letI := A.measurableSpace
    exact jointlyMeasurable_embedValue A.policy A.policy_joint_measurable

theorem randomCostCap_embedValue {d : ℕ} (A : RandomizedMethod (valueModel d))
    {C : Set (Objective d)} {ε δ : ℝ} {N : ℕ}
    (hA : (valueModel d).RandomCostCap A C ε δ N) :
    (linearModel d).RandomCostCap (embedRandomValue A) C ε δ N := by
  constructor
  · intro f hf ω
    obtain ⟨n, x, hn, hr⟩ := hA.1 f hf ω
    exact ⟨n, x, hn, (runs_embedValue_iff _ _ _ _).mpr hr⟩
  · intro f hf
    have he : (linearModel d).randomBad (embedRandomValue A) f ε =
        (valueModel d).randomBad A f ε := by
      ext ω
      simp only [OracleModel.randomBad, Set.mem_setOf_eq, embedRandomValue, runs_embedValue_iff]
    simpa only [he] using hA.2 f hf

theorem Nrand_linear_le_value {d : ℕ} (C : Set (Objective d)) (ε δ : ℝ) :
    (linearModel d).Nrand C ε δ ≤ (valueModel d).Nrand C ε δ := by
  apply le_iInf
  intro N
  apply le_iInf
  rintro ⟨A, hA⟩
  exact (linearModel d).Nrand_le_of_costCap _ (randomCostCap_embedValue A hA)

end ExactZO
