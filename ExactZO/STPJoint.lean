import ExactZO.STPProbability

noncomputable section
open MeasureTheory

namespace ExactZO

namespace ValueProcedure

@[simp] theorem action_output (x : X d) (hist : (valueModel d).History) :
    (ValueProcedure.output x).action hist = .output x := by
  cases hist <;> rfl

end ValueProcedure

namespace STP

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The branch rule is measurable in all points and scalar replies. In
particular, its scalar arguments need not come from an objective function. -/
theorem choose_measurable {x p q : Ω → X d} {vx vp vq : Ω → ℝ}
    (hx : Measurable x) (hp : Measurable p) (hq : Measurable q)
    (hvx : Measurable vx) (hvp : Measurable vp) (hvq : Measurable vq) :
    Measurable (fun ω => choose (x ω) (p ω) (q ω) (vx ω) (vp ω) (vq ω)) := by
  unfold choose
  exact Measurable.ite (measurableSet_lt (hvp.min hvq) hvx)
    (Measurable.ite (measurableSet_le hvp hvq) hp hq) hx

/-- Replay is measurable for arbitrary finite transcripts. Only their scalar
coordinates must be measurable: their recorded query points are ignored by
the existing `ValueProcedure.action`, even for malformed transcripts. The
remembered output index can itself be any measurable seed function. -/
theorem procedureLoop_action_measurable (h : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (k : Ω → ℕ) (hk : Measurable k)
    (n t ℓ : ℕ) (x : Ω → X d) (vx : Ω → ℝ) (remembered : Ω → X d)
    (hx : Measurable x) (hvx : Measurable vx) (hr : Measurable remembered)
    (entries : Ω → Fin ℓ → (valueModel d).Entry)
    (he : ∀ i, Measurable (fun ω => (entries ω i).2)) :
    Measurable (fun ω =>
      (procedureLoop h (fun j => a j ω) (k ω) n t (x ω) (vx ω) (remembered ω)).action
        (List.ofFn (entries ω))) := by
  induction n generalizing t ℓ x vx remembered with
  | zero =>
      simpa only [procedureLoop, ValueProcedure.action_output] using
        (OracleModel.measurable_action_output (valueModel d)).comp hr
  | succ n ih =>
      have hp : Measurable (fun ω => x ω + h • a t ω) := hx.add ((ha t).const_smul h)
      have hm : Measurable (fun ω => x ω - h • a t ω) := hx.sub ((ha t).const_smul h)
      cases ℓ with
      | zero =>
          simpa only [List.ofFn_zero, procedureLoop, ValueProcedure.action] using
            (OracleModel.measurable_action_query (valueModel d)).comp hp
      | succ ℓ =>
          cases ℓ with
          | zero =>
              simpa only [List.ofFn_succ, List.ofFn_zero, procedureLoop,
                ValueProcedure.action] using
                (OracleModel.measurable_action_query (valueModel d)).comp hm
          | succ ℓ =>
              have hx' : Measurable (fun ω => choose (x ω) (x ω + h • a t ω)
                  (x ω - h • a t ω) (vx ω) (entries ω 0).2
                  (entries ω (Fin.succ 0)).2) :=
                choose_measurable hx hp hm hvx (he 0) (he (Fin.succ 0))
              have hvx' : Measurable (fun ω =>
                  min (vx ω) (min (entries ω 0).2 (entries ω (Fin.succ 0)).2)) :=
                hvx.min ((he 0).min (he (Fin.succ 0)))
              have hr' : Measurable (fun ω => if t = k ω then x ω else remembered ω) :=
                Measurable.ite (measurableSet_eq_fun_of_countable measurable_const hk) hx hr
              have hi := ih (t + 1) ℓ
                (fun ω => choose (x ω) (x ω + h • a t ω) (x ω - h • a t ω)
                  (vx ω) (entries ω 0).2 (entries ω (Fin.succ 0)).2)
                (fun ω => min (vx ω) (min (entries ω 0).2 (entries ω (Fin.succ 0)).2))
                (fun ω => if t = k ω then x ω else remembered ω)
                hx' hvx' hr' (fun ω i => entries ω i.succ.succ) (fun i => he i.succ.succ)
              simpa only [List.ofFn_succ, procedureLoop, ValueProcedure.action] using hi

/-- The complete center-value query followed by the three-point loop is
measurable for every finite transcript, with an arbitrary measurable index. -/
theorem procedure_action_measurable (h : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (k : Ω → ℕ) (hk : Measurable k)
    (N ℓ : ℕ) (entries : Ω → Fin ℓ → (valueModel d).Entry)
    (he : ∀ i, Measurable (fun ω => (entries ω i).2)) :
    Measurable (fun ω => (procedure h (fun j => a j ω) N (k ω)).action
      (List.ofFn (entries ω))) := by
  cases ℓ with
  | zero =>
      simpa only [procedure, List.ofFn_zero, ValueProcedure.action] using
        (measurable_const : Measurable
          (fun _ : Ω => (OracleModel.Action.query (M := valueModel d) (0 : X d))))
  | succ ℓ =>
      have hi := procedureLoop_action_measurable h a ha k hk N 0 ℓ
        (fun _ => 0) (fun ω => (entries ω 0).2) (fun _ => 0)
        measurable_const (he 0) measurable_const
        (fun ω i => entries ω i.succ) (fun i => he i.succ)
      simpa only [procedure, List.ofFn_succ, ValueProcedure.action] using hi

/-- Joint measurability in the entire direction seed, the independent finite
output index, and every coordinate of an arbitrary finite transcript. -/
theorem procedure_jointlyMeasurable (h : ℝ) (a : ℕ → Ω → X d)
    (ha : ∀ t, Measurable (a t)) (N : ℕ) :
    (valueModel d).JointlyMeasurable
      (fun seed : Ω × Fin N => (procedure h (fun j => a j seed.1) N seed.2.val).algorithm) := by
  apply (OracleModel.jointlyMeasurable_iff_fixedLength (valueModel d)).2
  intro ℓ
  exact procedure_action_measurable
    (Ω := (Ω × Fin N) × (Fin ℓ → (valueModel d).Entry)) h
    (fun j p => a j p.1.1) (fun j => (ha j).comp (measurable_fst.comp measurable_fst))
    (fun p => p.1.2.val)
    ((measurable_of_countable (fun i : Fin N => i.val)).comp
      (measurable_snd.comp measurable_fst)) N ℓ (fun p => p.2)
    (fun i => measurable_valueEntry_value.comp ((measurable_pi_apply i).comp measurable_snd))

end STP
end ExactZO
