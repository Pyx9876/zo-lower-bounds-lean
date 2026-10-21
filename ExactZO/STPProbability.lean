import ExactZO.STPProcedure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Uniform pre-update output and finite-horizon expected-decrease summation
for the actual three-point recursion. -/

noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace ExactZO.STP

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The random seed determines the directions, and the core recursion determines
all centers before an independent output index is sampled. -/
def trajectory (f : Objective d) (h : ℝ) (directions : ℕ → Ω → X d)
    (t : ℕ) (ω : Ω) : X d := iterates f h (fun n => directions n ω) t

omit [MeasurableSpace Ω] in
@[simp] theorem trajectory_zero (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d) (ω : Ω) :
    trajectory f h a 0 ω = 0 := rfl

omit [MeasurableSpace Ω] in
@[simp] theorem trajectory_succ (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d) (t : ℕ) (ω : Ω) :
    trajectory f h a (t + 1) ω = step f h (trajectory f h a t ω) (a t ω) := rfl

theorem value_continuous (f : Objective d) : Continuous f.value :=
  continuous_iff_continuousAt.mpr (fun x => (f.hasDeriv x).continuousAt)

theorem step_measurable (f : Objective d) (h : ℝ) {x a : Ω → X d}
    (hx : Measurable x) (ha : Measurable a) : Measurable (fun ω => step f h (x ω) (a ω)) := by
  have hp : Measurable (fun ω => x ω + h • a ω) := hx.add (ha.const_smul h)
  have hm : Measurable (fun ω => x ω - h • a ω) := hx.sub (ha.const_smul h)
  have hf := (value_continuous f).measurable
  unfold step choose
  exact Measurable.ite (measurableSet_lt ((hf.comp hp).min (hf.comp hm)) (hf.comp hx))
    (Measurable.ite (measurableSet_le (hf.comp hp) (hf.comp hm)) hp hm) hx

theorem trajectory_measurable (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (t : ℕ) : Measurable (trajectory f h a t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact step_measurable f h ih (ha t)

omit [MeasurableSpace Ω] in
theorem trajectory_sublevel (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d) (t : ℕ) (ω : Ω) :
    f.value (trajectory f h a t ω) ≤ f.value 0 := iterates_sublevel f h _ t

theorem trajectory_value_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d) (ha : ∀ t, Measurable (a t))
    (lower : ℝ) (hlower : ∀ x, lower ≤ f.value x) (t : ℕ) :
    Integrable (fun ω => f.value (trajectory f h a t ω)) μ := by
  apply (integrable_const (|lower| + |f.value 0|)).mono'
    (((value_continuous f).measurable.comp (trajectory_measurable f h a ha t)).aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [Function.comp_apply]
  have hl := hlower (trajectory f h a t ω)
  have hu := trajectory_sublevel f h a t ω
  constructor <;> linarith [neg_abs_le lower, le_abs_self (f.value 0), abs_nonneg lower,
    abs_nonneg (f.value 0)]

def uniformIndex (N : ℕ) [NeZero N] : Measure (Fin N) := (PMF.uniformOfFintype (Fin N)).toMeasure

instance uniformIndex_isProbability (N : ℕ) [NeZero N] : IsProbabilityMeasure (uniformIndex N) := by
  unfold uniformIndex
  infer_instance

theorem uniformIndex_singleton (N : ℕ) [NeZero N] (i : Fin N) :
    (uniformIndex N).real {i} = 1 / (N : ℝ) := by
  rw [measureReal_def, uniformIndex, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  simp

/-- Independence of the output index from the entire direction seed is encoded
by this product measure. -/
def outputMeasure (μ : Measure Ω) (N : ℕ) [NeZero N] : Measure (Ω × Fin N) :=
  μ.prod (uniformIndex N)

instance outputMeasure_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] : IsProbabilityMeasure (outputMeasure μ N) := by
  unfold outputMeasure
  infer_instance

def output (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d) (N : ℕ)
    (p : Ω × Fin N) : X d := trajectory f h a p.2.val p.1

theorem uniform_failure_average (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (bad : Fin N → Set Ω) (hb : ∀ i, MeasurableSet (bad i)) :
    (outputMeasure μ N).real {p | p.1 ∈ bad p.2} =
      (∑ i : Fin N, μ.real (bad i)) / (N : ℝ) := by
  have he : {p : Ω × Fin N | p.1 ∈ bad p.2} = ⋃ i : Fin N, bad i ×ˢ {i} := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.2, hp, rfl⟩
    · rintro ⟨i, hp, hi⟩
      simpa only [hi] using hp
  have hd : Pairwise (Disjoint on fun i : Fin N => bad i ×ˢ {i}) := by
    intro i j hij
    change Disjoint (bad i ×ˢ {i}) (bad j ×ˢ {j})
    rw [Set.disjoint_left]
    intro p hp hq
    exact hij (hp.2.symm.trans hq.2)
  rw [he, measureReal_iUnion_fintype hd (fun i => (hb i).prod (measurableSet_singleton i))]
  simp only [outputMeasure, measureReal_prod_prod, uniformIndex_singleton, mul_one_div]
  exact (Finset.sum_div _ _ _).symm

theorem output_failure_average (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Objective d) (h ε : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (hg : Measurable f.grad) (N : ℕ) [NeZero N] :
    (outputMeasure μ N).real {p | ε < ‖f.grad (output f h a N p)‖} =
      (∑ i : Fin N, μ.real {ω | ε < ‖f.grad (trajectory f h a i ω)‖}) / (N : ℝ) := by
  exact uniform_failure_average μ N (fun i => {ω | ε < ‖f.grad (trajectory f h a i ω)‖})
    (fun i => measurableSet_lt measurable_const ((hg.comp (trajectory_measurable f h a ha i)).norm))

theorem sum_drift_le (V p : ℕ → ℝ) (δ : ℝ) (N : ℕ)
    (hdrift : ∀ t < N, δ * p t ≤ V t - V (t + 1)) :
    δ * (∑ t ∈ Finset.range N, p t) ≤ V 0 - V N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun t ht => hdrift t (Nat.lt_succ_of_lt ht))
    have hn := hdrift N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ, mul_add]
    linarith

theorem average_drift_le (V p : ℕ → ℝ) {δ Δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) [NeZero N] (hdrift : ∀ t < N, δ * p t ≤ V t - V (t + 1))
    (hgap : V 0 - V N ≤ Δ) :
    (∑ i : Fin N, p i.val) / (N : ℝ) ≤ Δ / ((N : ℝ) * δ) := by
  have hs := (sum_drift_le V p δ N hdrift).trans hgap
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [Fin.sum_univ_eq_sum_range]
  apply (div_le_div_iff₀ hN (mul_pos hN hδ)).mpr
  nlinarith

theorem output_measurable (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (N : ℕ) : Measurable (output f h a N) := by
  exact measurable_from_prod_countable (fun i : Fin N => trajectory_measurable f h a ha i)

omit [MeasurableSpace Ω] in
theorem output_is_procedure_result (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d)
    (N : ℕ) (p : Ω × Fin N) :
    (procedure h (fun t => a t p.1) N p.2.val).result f = output f h a N p := by
  exact procedure_result f h (fun t => a t p.1) N p.2.val p.2.isLt

omit [MeasurableSpace Ω] in
theorem output_procedure_cost (f : Objective d) (h : ℝ) (a : ℕ → Ω → X d)
    (N : ℕ) (p : Ω × Fin N) :
    (procedure h (fun t => a t p.1) N p.2.val).cost f = 1 + 2 * N :=
  procedure_cost f h (fun t => a t p.1) N p.2.val

theorem output_failure_le_of_drift (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Objective d) (h ε : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (hg : Measurable f.grad) {Δ δ : ℝ}
    (hgap : HasGap f Δ) (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hdrift : ∀ t < N,
      δ * μ.real {ω | ε < ‖f.grad (trajectory f h a t ω)‖} ≤
        (∫ ω, f.value (trajectory f h a t ω) ∂μ) -
          ∫ ω, f.value (trajectory f h a (t + 1) ω) ∂μ) :
    (outputMeasure μ N).real {p | ε < ‖f.grad (output f h a N p)‖} ≤ Δ / ((N : ℝ) * δ) := by
  rw [output_failure_average μ f h ε a ha hg N]
  apply average_drift_le (fun t => ∫ ω, f.value (trajectory f h a t ω) ∂μ)
    (fun t => μ.real {ω | ε < ‖f.grad (trajectory f h a t ω)‖}) hδ N hdrift
  obtain ⟨lower, hlower, hstart⟩ := hgap
  have hlast := integral_mono (integrable_const lower)
    (trajectory_value_integrable μ f h a ha lower hlower N)
    (fun ω => hlower (trajectory f h a N ω))
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hlast
  simp only [trajectory_zero, integral_const, measureReal_univ_eq_one, one_smul]
  linarith

def horizon (M Δ ε : ℝ) : ℕ := ⌈10 * M * Δ / ε ^ 2⌉₊
def decrease (M ε : ℝ) : ℝ := (39 / 125 : ℝ) * ε ^ 2 / M

theorem horizon_pos {M Δ ε : ℝ} (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 < ε) :
    0 < horizon M Δ ε := by
  apply Nat.ceil_pos.mpr
  positivity

theorem decrease_pos {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) : 0 < decrease M ε := by
  unfold decrease
  positivity

theorem horizon_failure_bound {M Δ ε : ℝ} (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 < ε) :
    Δ / ((horizon M Δ ε : ℝ) * decrease M ε) ≤ 25 / 78 := by
  have hN := Nat.le_ceil (10 * M * Δ / ε ^ 2)
  change 10 * M * Δ / ε ^ 2 ≤ (horizon M Δ ε : ℝ) at hN
  have hNpos : (0 : ℝ) < horizon M Δ ε := Nat.cast_pos.mpr (horizon_pos hM hΔ hε)
  apply (div_le_iff₀ (mul_pos hNpos (decrease_pos hM hε))).mpr
  unfold decrease
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hh := (div_le_iff₀ he).mp hN
  calc
    Δ ≤ (horizon M Δ ε : ℝ) * ε ^ 2 / (10 * M) := by
      apply (le_div_iff₀ (by positivity : 0 < 10 * M)).mpr
      nlinarith
    _ = 25 / 78 * ((horizon M Δ ε : ℝ) * ((39 / 125 : ℝ) * ε ^ 2 / M)) := by ring

theorem horizon_failure_lt_third {M Δ ε : ℝ} (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 < ε) :
    Δ / ((horizon M Δ ε : ℝ) * decrease M ε) < 1 / 3 :=
  (horizon_failure_bound hM hΔ hε).trans_lt (by norm_num)

theorem query_bound {E T : ℝ} (hE : 1 ≤ E) (hT : 1 ≤ T) :
    ((1 + 2 * ⌈10 * E * T⌉₊ : ℕ) : ℝ) ≤ 23 * E * T := by
  have hET : 1 ≤ E * T := by nlinarith
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 10 * E * T by positivity)
  push_cast
  nlinarith

end ExactZO.STP
