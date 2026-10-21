import ExactZO.STPUpper
import Mathlib.Probability.Independence.Basic

/-! A finite product seed gives every step a genuinely fresh direction.
The construction is independent of the objective and applies to every probability law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

namespace ExactZO.STP

variable {d N : ℕ}

/-- The public horizon determines the finite seed space. -/
abbrev DirectionSeed (d N : ℕ) := Fin N → X d

/-- Each block has the prescribed direction law. -/
def iidMeasure (ν : Measure (X d)) (N : ℕ) : Measure (DirectionSeed d N) :=
  Measure.pi (fun _ : Fin N => ν)

instance iidMeasure_isProbability (ν : Measure (X d)) [IsProbabilityMeasure ν] (N : ℕ) :
    IsProbabilityMeasure (iidMeasure ν N) := by
  unfold iidMeasure
  infer_instance

/-- Padding after the public horizon is irrelevant to the algorithm. -/
def iidDirections (N : ℕ) (t : ℕ) (ω : DirectionSeed d N) : X d :=
  if ht : t < N then ω ⟨t, ht⟩ else 0

theorem iidDirections_measurable (N t : ℕ) : Measurable (iidDirections (d := d) N t) := by
  unfold iidDirections
  split_ifs <;> fun_prop

theorem iidMeasure_map_eval (ν : Measure (X d)) [IsProbabilityMeasure ν]
    (i : Fin N) : Measure.map (fun ω : DirectionSeed d N => ω i) (iidMeasure ν N) = ν := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  change (Measure.pi (fun _ : Fin N => ν)) (Function.eval i ⁻¹' s) = ν s
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem iidDirections_map (ν : Measure (X d)) [IsProbabilityMeasure ν]
    {t : ℕ} (ht : t < N) :
    Measure.map (iidDirections (d := d) N t) (iidMeasure ν N) = ν := by
  change Measure.map (fun ω => if h : t < N then ω ⟨t, h⟩ else 0) (iidMeasure ν N) = ν
  simp only [dif_pos ht]
  exact iidMeasure_map_eval ν (⟨t, ht⟩ : Fin N)

theorem iidMeasure_independent (ν : Measure (X d)) [IsProbabilityMeasure ν] (N : ℕ) :
    iIndepFun (fun i : Fin N => fun ω : DirectionSeed d N => ω i) (iidMeasure ν N) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp only [iidMeasure_map_eval]
  exact Measure.map_id

/-- All directions that the finite algorithm can consume are mutually independent. -/
theorem iidDirections_independent (ν : Measure (X d)) [IsProbabilityMeasure ν] (N : ℕ) :
    iIndepFun (fun i : Fin N => iidDirections (d := d) N i.val) (iidMeasure ν N) := by
  apply (iidMeasure_independent ν N).congr
  intro i
  filter_upwards with ω
  simp [iidDirections, i.isLt]

theorem iid_trajectory_measurable (f : Objective d) (h : ℝ) (N t : ℕ) :
    Measurable (trajectory f h (iidDirections N) t) :=
  trajectory_measurable f h (iidDirections N) (iidDirections_measurable N) t

theorem iid_output_measurable (f : Objective d) (h : ℝ) (N : ℕ) :
    Measurable (output f h (iidDirections N) N) :=
  output_measurable f h (iidDirections N) (iidDirections_measurable N) N

/-- Before step `t`, the recursion depends only on directions with index below `t`. -/
theorem trajectory_eq_of_prefix {Ω : Type*} (f : Objective d) (h : ℝ)
    (a b : ℕ → Ω → X d) (t : ℕ) (ω : Ω)
    (hab : ∀ i < t, a i ω = b i ω) : trajectory f h a t ω = trajectory f h b t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [trajectory_succ, trajectory_succ, ih (fun i hi => hab i (Nat.lt_succ_of_lt hi)),
      hab t (Nat.lt_succ_self t)]

/-- Retain a finite subset of seed blocks and pad the other blocks by zero. -/
def extendSeed (S : Finset (Fin N)) (ω : S → X d) : DirectionSeed d N :=
  fun i => if hi : i ∈ S then ω ⟨i, hi⟩ else 0

theorem extendSeed_measurable (S : Finset (Fin N)) :
    Measurable (extendSeed (d := d) S) := by
  apply measurable_pi_lambda
  intro i
  unfold extendSeed
  split_ifs <;> fun_prop

/-- A measurable function of a prefix is independent of the next coordinate. -/
theorem trajectory_independent_next (ν : Measure (X d)) [IsProbabilityMeasure ν]
    (f : Objective d) (h : ℝ) {t : ℕ} (ht : t < N) :
    IndepFun (trajectory f h (iidDirections N) t) (iidDirections N t) (iidMeasure ν N) := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter (fun i => i.val < t)
  let i : Fin N := ⟨t, ht⟩
  have hi : i ∉ S := by simp [S, i]
  have hdis : Disjoint S {i} := Finset.disjoint_singleton_right.mpr hi
  have hind := (iidMeasure_independent ν N).indepFun_finset S {i} hdis
    (fun j => measurable_pi_apply j)
  let φ : (S → X d) → X d :=
    fun ω => trajectory f h (iidDirections N) t (extendSeed S ω)
  have hφ : Measurable φ :=
    (trajectory_measurable f h (iidDirections N) (iidDirections_measurable N) t).comp
      (extendSeed_measurable S)
  have hj : Measurable (fun ω : ({i} : Finset (Fin N)) → X d =>
      ω ⟨i, Finset.mem_singleton_self i⟩) := measurable_pi_apply _
  have hc := hind.comp hφ hj
  apply hc.congr
  · filter_upwards with ω
    change trajectory f h (iidDirections N) t (extendSeed S (fun j : S => ω j)) =
      trajectory f h (iidDirections N) t ω
    unfold trajectory
    apply trajectory_eq_of_prefix f h
      (fun n (_ : Unit) => iidDirections N n (extendSeed S (fun j : S => ω j)))
      (fun n (_ : Unit) => iidDirections N n ω) t ()
    intro j hjt
    have hjN : j < N := hjt.trans ht
    simp [iidDirections, hjN, extendSeed, S, hjt]
  · filter_upwards with ω
    simp [Function.comp_def, iidDirections, ht, i]

/-- The actual trajectory/next-direction law is the product law required by STP. -/
theorem iid_freshForClass (ν : Measure (X d)) [IsProbabilityMeasure ν]
    (h : ℝ) (C : Set (Objective d)) (N : ℕ) :
    FreshForClass (iidMeasure ν N) ν (iidDirections N) h C N := by
  intro f _ t ht
  have hx := trajectory_measurable f h (iidDirections N) (iidDirections_measurable N) t
  have ha := iidDirections_measurable (d := d) N t
  have hind := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable ha.aemeasurable).mp
    (trajectory_independent_next ν f h ht)
  rw [iidDirections_map ν ht] at hind
  rw [hind]
  simpa only [Measure.map_id, Prod.map_apply, id_eq] using
    (Measure.map_prod_map (iidMeasure ν N) ν hx measurable_id)

end ExactZO.STP
