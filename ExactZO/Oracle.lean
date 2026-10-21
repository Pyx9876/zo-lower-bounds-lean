import ExactZO.Model
import ExactZO.Transcript
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic

/-!
Exact value and linear-information oracles, deterministic finite executions,
and worst-case deterministic complexity. Public parameters are fixed when an
algorithm is chosen. No objective or derivative is an extra algorithm input.
-/

noncomputable section

namespace ExactZO

/-- A query may have any finite width; its cost depends on rank, not width. -/
structure LinearQuery (d : ℕ) where
  width : ℕ
  point : X d
  directions : X width →L[ℝ] X d

def LinearQuery.rank {d : ℕ} (q : LinearQuery d) : ℕ :=
  Module.finrank ℝ (LinearMap.range q.directions.toLinearMap)

def LinearQuery.cost {d : ℕ} (q : LinearQuery d) : ℕ := 1 + q.rank

theorem LinearQuery.cost_pos {d : ℕ} (q : LinearQuery d) : 0 < q.cost := by
  simp [LinearQuery.cost]

theorem LinearQuery.rank_le_width {d : ℕ} (q : LinearQuery d) : q.rank ≤ q.width := by
  simpa [LinearQuery.rank, X] using q.directions.toLinearMap.finrank_range_le

theorem LinearQuery.rank_le_dim {d : ℕ} (q : LinearQuery d) : q.rank ≤ d := by
  simpa [LinearQuery.rank, X] using (LinearMap.range q.directions.toLinearMap).finrank_le

theorem LinearQuery.cost_eq_one_of_zero {d : ℕ} (q : LinearQuery d)
    (h : q.directions = 0) : q.cost = 1 := by
  simp [LinearQuery.cost, LinearQuery.rank, h]

abbrev LinearReply {d : ℕ} (q : LinearQuery d) := ℝ × X q.width

def linearReply {d : ℕ} (f : Objective d) (q : LinearQuery d) : LinearReply q :=
  (f.value q.point, q.directions.adjoint (f.grad q.point))

/-- A value query uses a zero map; its zero-width derivative reply carries no data. -/
def valueQuery {d : ℕ} (x : X d) : LinearQuery d := ⟨0, x, 0⟩

@[simp] theorem valueQuery_rank {d : ℕ} (x : X d) : (valueQuery x).rank = 0 := by
  simp [LinearQuery.rank, valueQuery]

@[simp] theorem valueQuery_cost {d : ℕ} (x : X d) : (valueQuery x).cost = 1 := by
  simp [LinearQuery.cost]

@[simp] theorem linearReply_valueQuery {d : ℕ} (f : Objective d) (x : X d) :
    linearReply f (valueQuery x) = (f.value x, 0) := by
  simp [linearReply, valueQuery]

abbrev LinearQueryCode (d : ℕ) := Σ s : ℕ, X d × (X s →L[ℝ] X d)

def linearQueryEquiv (d : ℕ) : LinearQuery d ≃ LinearQueryCode d where
  toFun q := ⟨q.width, q.point, q.directions⟩
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by rcases q with ⟨s, x, D⟩; rfl

instance linearQueryMeasurableSpace (d : ℕ) : MeasurableSpace (LinearQuery d) :=
  MeasurableSpace.comap (linearQueryEquiv d) inferInstance

def linearQueryMeasurableEquiv (d : ℕ) : LinearQuery d ≃ᵐ LinearQueryCode d :=
  Transcript.equivComap (linearQueryEquiv d)

abbrev LinearEntryCode (d : ℕ) := Σ s : ℕ, X d × (X s →L[ℝ] X d) × ℝ × X s

def linearEntryEquiv (d : ℕ) : Sigma (LinearReply (d := d)) ≃ LinearEntryCode d where
  toFun e := ⟨e.1.width, e.1.point, e.1.directions, e.2.1, e.2.2⟩
  invFun e := ⟨⟨e.1, e.2.1, e.2.2.1⟩, e.2.2.2.1, e.2.2.2.2⟩
  left_inv e := by rcases e with ⟨⟨s, x, D⟩, v, g⟩; rfl
  right_inv e := by rcases e with ⟨s, x, D, v, g⟩; rfl

def valueEntryEquiv (d : ℕ) : (Σ _ : X d, ℝ) ≃ X d × ℝ where
  toFun e := (e.1, e.2)
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The oracle signature also supplies the exact answer and the per-call cost. -/
structure OracleModel (d : ℕ) where
  Query : Type
  Reply : Query → Type
  queryMeasurableSpace : MeasurableSpace Query
  entryMeasurableSpace : MeasurableSpace (Sigma Reply)
  answer : Objective d → (q : Query) → Reply q
  cost : Query → ℕ
  cost_pos : ∀ q, 0 < cost q

def linearModel (d : ℕ) : OracleModel d where
  Query := LinearQuery d
  Reply := LinearReply
  queryMeasurableSpace := inferInstance
  entryMeasurableSpace := MeasurableSpace.comap (linearEntryEquiv d) inferInstance
  answer := linearReply
  cost := LinearQuery.cost
  cost_pos q := by simp [LinearQuery.cost]

def valueModel (d : ℕ) : OracleModel d where
  Query := X d
  Reply _ := ℝ
  queryMeasurableSpace := inferInstance
  entryMeasurableSpace := MeasurableSpace.comap (valueEntryEquiv d) inferInstance
  answer f x := f.value x
  cost _ := 1
  cost_pos _ := by decide

namespace OracleModel

variable {d : ℕ} (M : OracleModel d)

abbrev Entry := Sigma M.Reply
abbrev History := List M.Entry

instance instQueryMeasurableSpace : MeasurableSpace M.Query := M.queryMeasurableSpace

instance instEntryMeasurableSpace : MeasurableSpace M.Entry := M.entryMeasurableSpace

def historyMeasurableSpace : MeasurableSpace M.History :=
  @Transcript.listMeasurableSpace M.Entry M.entryMeasurableSpace

instance instHistoryMeasurableSpace : MeasurableSpace M.History := M.historyMeasurableSpace

def historyCost (h : M.History) : ℕ := (h.map fun entry => M.cost entry.1).sum

def ReplyConsistent (f : Objective d) (h : M.History) : Prop :=
  ∀ entry ∈ h, entry.2 = M.answer f entry.1

theorem history_length_le_cost (h : M.History) : h.length ≤ M.historyCost h := by
  induction h with
  | nil => simp [historyCost]
  | cons entry h ih =>
      simpa [historyCost, Nat.succ_eq_add_one, Nat.add_comm] using
        Nat.add_le_add (M.cost_pos entry.1) ih

inductive Action where
  | query (request : M.Query)
  | output (point : X d)

abbrev Algorithm := M.History → M.Action

def actionEquiv : M.Action ≃ M.Query ⊕ X d where
  toFun
    | .query q => .inl q
    | .output x => .inr x
  invFun
    | .inl q => .query q
    | .inr x => .output x
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

def actionMeasurableSpace : MeasurableSpace M.Action := by
  letI : MeasurableSpace M.Query := M.queryMeasurableSpace
  exact MeasurableSpace.comap (M.actionEquiv) inferInstance

instance instActionMeasurableSpace : MeasurableSpace M.Action := M.actionMeasurableSpace

def actionMeasurableEquiv : M.Action ≃ᵐ M.Query ⊕ X d :=
  Transcript.equivComap M.actionEquiv

theorem measurable_action_query : Measurable (Action.query (M := M) : M.Query → M.Action) :=
  M.actionMeasurableEquiv.symm.measurable.comp measurable_inl

theorem measurable_action_output : Measurable (Action.output (M := M) : X d → M.Action) :=
  M.actionMeasurableEquiv.symm.measurable.comp measurable_inr

theorem measurable_action_elim {β : Type*} [MeasurableSpace β]
    {fq : M.Query → β} {fx : X d → β} (hq : Measurable fq) (hx : Measurable fx) :
    Measurable (fun a : M.Action => match a with
      | .query q => fq q
      | .output x => fx x) := by
  have h := (hq.sumElim hx).comp M.actionMeasurableEquiv.measurable
  convert h using 1
  funext a
  cases a <;> rfl

/-- The spaces in this definition are fixed by oracle metadata, irrespective
of any local convenience instances used by a caller. -/
def JointlyMeasurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (policy : Ω → M.Algorithm) : Prop :=
  @Measurable (Ω × M.History) M.Action
    (@Prod.instMeasurableSpace Ω M.History mΩ M.historyMeasurableSpace)
    M.actionMeasurableSpace (fun p => policy p.1 p.2)

theorem jointlyMeasurable_iff_fixedLength {Ω : Type*} [MeasurableSpace Ω]
    {policy : Ω → M.Algorithm} :
    M.JointlyMeasurable policy ↔
      ∀ n, Measurable (fun p : Ω × (Fin n → M.Entry) => policy p.1 (List.ofFn p.2)) :=
  Transcript.measurable_prod_list_iff

/-- A finite execution. The terminal output can be any point and costs zero. -/
inductive RunFrom (A : M.Algorithm) (f : Objective d) :
    M.History → ℕ → X d → Prop where
  | output {h x} (action : A h = .output x) : RunFrom A f h 0 x
  | query {h q n x} (action : A h = .query q)
      (tail : RunFrom A f (h ++ [⟨q, M.answer f q⟩]) n x) :
      RunFrom A f h (M.cost q + n) x

def Runs (A : M.Algorithm) (f : Objective d) (cost : ℕ) (output : X d) : Prop :=
  M.RunFrom A f [] cost output

/-- A finite run has an actual terminal history. Its cost is exactly the sum
of its calls, every reply is the true reply, and the output is not appended. -/
theorem RunFrom.exists_terminal_history {A : M.Algorithm} {f : Objective d}
    {h : M.History} {n : ℕ} {x : X d} (hr : M.RunFrom A f h n x) :
    ∃ suffix : M.History, A (h ++ suffix) = .output x ∧
      M.historyCost suffix = n ∧ M.ReplyConsistent f suffix := by
  induction hr with
  | output ha =>
      exact ⟨[], by simpa using ha, rfl, by simp [ReplyConsistent]⟩
  | @query h q n x ha ht ih =>
      obtain ⟨suffix, hs, hc, hr⟩ := ih
      refine ⟨⟨q, M.answer f q⟩ :: suffix, ?_, ?_, ?_⟩
      · simpa [List.append_assoc] using hs
      · simpa [historyCost] using congrArg (M.cost q + ·) hc
      · intro entry he
        rcases List.mem_cons.mp he with he | he
        · subst entry
          rfl
        · exact hr entry he

theorem runs_exists_terminal_history {A : M.Algorithm} {f : Objective d}
    {n : ℕ} {x : X d} (hr : M.Runs A f n x) :
    ∃ h : M.History, A h = .output x ∧ M.historyCost h = n ∧
      M.ReplyConsistent f h ∧ h.length ≤ n := by
  obtain ⟨h, ha, hc, hr⟩ := RunFrom.exists_terminal_history M hr
  exact ⟨h, by simpa using ha, hc, hr, hc ▸ M.history_length_le_cost h⟩

/-- All finite runs of a deterministic algorithm on the same function agree. -/
theorem RunFrom.unique {A : M.Algorithm} {f : Objective d} {h : M.History}
    {n m : ℕ} {x y : X d} (hn : M.RunFrom A f h n x)
    (hm : M.RunFrom A f h m y) : n = m ∧ x = y := by
  induction hn generalizing m y with
  | output ha =>
      cases hm with
      | output hb => simpa [ha] using hb
      | query hb _ => simp [ha] at hb
  | query ha ht ih =>
      cases hm with
      | output hb => simp [ha] at hb
      | query hb ht' =>
          have hq := OracleModel.Action.query.inj (ha.symm.trans hb)
          subst hq
          obtain ⟨rfl, rfl⟩ := ih ht'
          exact ⟨rfl, rfl⟩

/-- No finite terminating run means infinite cost. -/
def runCost (A : M.Algorithm) (f : Objective d) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : ∃ x, M.Runs A f n x), (n : ℕ∞)

theorem runCost_eq_of_runs {A : M.Algorithm} {f : Objective d} {n : ℕ} {x : X d}
    (h : M.Runs A f n x) : M.runCost A f = (n : ℕ∞) := by
  apply le_antisymm
  · exact iInf_le_of_le n (iInf_le_of_le ⟨x, h⟩ le_rfl)
  · refine le_iInf fun m => le_iInf fun hm => ?_
    obtain ⟨y, hy⟩ := hm
    have heq := (RunFrom.unique M h hy).1
    exact_mod_cast heq.le

theorem runCost_eq_top_iff {A : M.Algorithm} {f : Objective d} :
    M.runCost A f = ⊤ ↔ ¬ ∃ n x, M.Runs A f n x := by
  constructor
  · intro h ⟨n, x, hn⟩
    rw [M.runCost_eq_of_runs hn] at h
    exact ENat.coe_ne_top n h
  · intro h
    apply le_antisymm le_top
    refine le_iInf fun n => le_iInf fun hn => ?_
    exact (h ⟨n, hn⟩).elim

theorem runCost_le_nat_iff {A : M.Algorithm} {f : Objective d} (N : ℕ) :
    M.runCost A f ≤ (N : ℕ∞) ↔ ∃ n x, M.Runs A f n x ∧ n ≤ N := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ n x, M.Runs A f n x
    · obtain ⟨n, x, hn⟩ := hex
      exact ⟨n, x, hn, ENat.coe_le_coe.mp (by simpa [M.runCost_eq_of_runs hn] using h)⟩
    · rw [M.runCost_eq_top_iff.mpr hex] at h
      exact (ENat.coe_ne_top N (top_le_iff.mp h)).elim
  · rintro ⟨n, x, hn, hN⟩
    rw [M.runCost_eq_of_runs hn]
    exact ENat.coe_le_coe.mpr hN

def TerminatesOn (A : M.Algorithm) (C : Set (Objective d)) : Prop :=
  ∀ f ∈ C, ∃ n x, M.Runs A f n x

/-- The same algorithm terminates and succeeds on every member of the class. -/
def Succeeds (A : M.Algorithm) (C : Set (Objective d)) (ε : ℝ) : Prop :=
  ∀ f ∈ C, ∃ n x, M.Runs A f n x ∧ ‖f.grad x‖ ≤ ε

theorem Succeeds.terminatesOn {A : M.Algorithm} {C : Set (Objective d)} {ε : ℝ}
    (h : M.Succeeds A C ε) : M.TerminatesOn A C := by
  intro f hf
  obtain ⟨n, x, hn, _⟩ := h f hf
  exact ⟨n, x, hn⟩

def worstCost (A : M.Algorithm) (C : Set (Objective d)) : ℕ∞ :=
  ⨆ (f : Objective d) (_ : f ∈ C), M.runCost A f

theorem worstCost_le_nat_iff (A : M.Algorithm) (C : Set (Objective d)) (N : ℕ) :
    M.worstCost A C ≤ (N : ℕ∞) ↔
      ∀ f ∈ C, ∃ n x, M.Runs A f n x ∧ n ≤ N := by
  simp only [worstCost, iSup_le_iff, runCost_le_nat_iff]

theorem worstCost_mono (A : M.Algorithm) {C D : Set (Objective d)} (hCD : C ⊆ D) :
    M.worstCost A C ≤ M.worstCost A D := by
  refine iSup_le fun f => iSup_le fun hf => ?_
  exact le_iSup_of_le f (le_iSup_of_le (hCD hf) le_rfl)

/-- Infimum of worst costs of successful algorithms, with empty infimum equal to infinity. -/
def Ndet (C : Set (Objective d)) (ε : ℝ) : ℕ∞ :=
  ⨅ (A : M.Algorithm) (_ : M.Succeeds A C ε), M.worstCost A C

theorem Ndet_eq_top_of_no_success {C : Set (Objective d)} {ε : ℝ}
    (h : ¬ ∃ A, M.Succeeds A C ε) : M.Ndet C ε = ⊤ := by
  apply le_antisymm le_top
  refine le_iInf fun A => le_iInf fun hA => ?_
  exact (h ⟨A, hA⟩).elim

theorem Ndet_le_of_success {C : Set (Objective d)} {ε : ℝ} {A : M.Algorithm}
    (h : M.Succeeds A C ε) : M.Ndet C ε ≤ M.worstCost A C :=
  iInf_le_of_le A (iInf_le_of_le h le_rfl)

theorem le_Ndet {C : Set (Objective d)} {ε : ℝ} {n : ℕ∞}
    (h : ∀ A, M.Succeeds A C ε → n ≤ M.worstCost A C) : n ≤ M.Ndet C ε :=
  le_iInf fun A => le_iInf (h A)

/-- For a finite integer cap the infimum formulation really yields a single
successful algorithm attaining that cap, including termination on all inputs. -/
theorem Ndet_le_nat_iff (C : Set (Objective d)) (ε : ℝ) (N : ℕ) :
    M.Ndet C ε ≤ (N : ℕ∞) ↔
      ∃ A, M.Succeeds A C ε ∧ M.worstCost A C ≤ (N : ℕ∞) := by
  simp only [← ENat.lt_add_one_iff (ENat.coe_ne_top N), Ndet, iInf_lt_iff,
    exists_prop]

theorem Ndet_mono_class {C D : Set (Objective d)} (hCD : C ⊆ D) (ε : ℝ) :
    M.Ndet C ε ≤ M.Ndet D ε := by
  apply M.le_Ndet
  intro A hA
  exact (M.Ndet_le_of_success (fun f hf => hA f (hCD hf))).trans (M.worstCost_mono A hCD)

end OracleModel

@[simp] theorem valueModel_historyCost {d : ℕ} (h : (valueModel d).History) :
    (valueModel d).historyCost h = h.length := by
  simp [OracleModel.historyCost, valueModel]

/-- Project a query and rescale its point. The derivative map is projected,
not divided by the point scale, as in the paper's oracle simulation. -/
def LinearQuery.project {d e : ℕ} (P : X d →L[ℝ] X e) (σ : ℝ)
    (q : LinearQuery d) : LinearQuery e :=
  ⟨q.width, σ⁻¹ • P q.point, P.comp q.directions⟩

theorem LinearQuery.project_rank_le {d e : ℕ} (P : X d →L[ℝ] X e) (σ : ℝ)
    (q : LinearQuery d) : (q.project P σ).rank ≤ q.rank := by
  change Module.finrank ℝ (LinearMap.range (P.toLinearMap.comp q.directions.toLinearMap)) ≤ _
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le P.toLinearMap (LinearMap.range q.directions.toLinearMap)

theorem LinearQuery.project_cost_le {d e : ℕ} (P : X d →L[ℝ] X e) (σ : ℝ)
    (q : LinearQuery d) : (q.project P σ).cost ≤ q.cost :=
  Nat.add_le_add_left (q.project_rank_le P σ) 1

@[simp] theorem LinearQuery.project_id_rank {d : ℕ} (σ : ℝ) (q : LinearQuery d) :
    (q.project (ContinuousLinearMap.id ℝ (X d)) σ).rank = q.rank := by
  simp [LinearQuery.project, LinearQuery.rank]

@[simp] theorem LinearQuery.project_id_cost {d : ℕ} (σ : ℝ) (q : LinearQuery d) :
    (q.project (ContinuousLinearMap.id ℝ (X d)) σ).cost = q.cost := by
  simp [LinearQuery.cost]

/-- The exact reply conversion is valid under the stated value and gradient
identities; those analytic identities are proved separately for scaled functions. -/
theorem linearReply_project {d e : ℕ} (P : X d →L[ℝ] X e) (σ a b : ℝ)
    (f : Objective d) (F : Objective e)
    (hv : ∀ x, f.value x = a * F.value (σ⁻¹ • P x))
    (hg : ∀ x, f.grad x = b • P.adjoint (F.grad (σ⁻¹ • P x)))
    (q : LinearQuery d) :
    linearReply f q =
      (a * (linearReply F (q.project P σ)).1,
        b • (linearReply F (q.project P σ)).2) := by
  simp [linearReply, LinearQuery.project, hv, hg]

/-- Erasing derivative replies gives a value-only history. -/
def valueHistory {d : ℕ} (h : (linearModel d).History) : (valueModel d).History :=
  h.map fun entry => ⟨entry.1.point, entry.2.1⟩

/-- A value algorithm uses the rank-zero suboracle and ignores derivative data. -/
def embedValueAlgorithm {d : ℕ} (A : (valueModel d).Algorithm) :
    (linearModel d).Algorithm := fun h =>
  match A (valueHistory h) with
  | .query x => .query (valueQuery x)
  | .output x => .output x

theorem runFrom_embedValue {d : ℕ} (A : (valueModel d).Algorithm) (f : Objective d)
    {h : (valueModel d).History} {n : ℕ} {x : X d}
    (hr : (valueModel d).RunFrom A f h n x) :
    ∀ h', valueHistory h' = h →
      (linearModel d).RunFrom (embedValueAlgorithm A) f h' n x := by
  induction hr with
  | output ha =>
      intro h' hh
      apply OracleModel.RunFrom.output
      simp [embedValueAlgorithm, hh, ha]
  | @query h q n x ha ht ih =>
      intro h' hh
      have htail : (linearModel d).RunFrom (embedValueAlgorithm A) f
          (h' ++ [⟨valueQuery q, (linearModel d).answer f (valueQuery q)⟩]) n x := by
        apply ih
        simp [valueHistory, List.map_append, valueQuery, linearModel, linearReply,
          valueModel, ← hh]
      have hquery : embedValueAlgorithm A h' = .query (valueQuery q) := by
        simp [embedValueAlgorithm, hh, ha]
      simpa [linearModel, valueModel] using OracleModel.RunFrom.query hquery htail

theorem runFrom_of_embedValue {d : ℕ} (A : (valueModel d).Algorithm) (f : Objective d)
    {h : (linearModel d).History} {n : ℕ} {x : X d}
    (hr : (linearModel d).RunFrom (embedValueAlgorithm A) f h n x) :
    (valueModel d).RunFrom A f (valueHistory h) n x := by
  induction hr with
  | @output h x ha =>
      apply OracleModel.RunFrom.output
      cases hv : A (valueHistory h) with
      | output y => simpa [embedValueAlgorithm, hv] using ha
      | query q => simp [embedValueAlgorithm, hv] at ha
  | @query h q n x ha ht ih =>
      cases hv : A (valueHistory h) with
      | output y => simp [embedValueAlgorithm, hv] at ha
      | query z =>
          have hq : valueQuery z = q := by simpa [embedValueAlgorithm, hv] using ha
          subst q
          have htail : (valueModel d).RunFrom A f
              (valueHistory h ++ [⟨z, (valueModel d).answer f z⟩]) n x := by
            simpa [valueHistory, List.map_append, valueQuery, linearModel,
              linearReply, valueModel] using ih
          simpa [linearModel, valueModel] using OracleModel.RunFrom.query hv htail

theorem runs_embedValue_iff {d : ℕ} (A : (valueModel d).Algorithm) (f : Objective d)
    (n : ℕ) (x : X d) :
    (linearModel d).Runs (embedValueAlgorithm A) f n x ↔
      (valueModel d).Runs A f n x := by
  constructor
  · exact runFrom_of_embedValue A f
  · intro h
    exact runFrom_embedValue A f h [] rfl

theorem runCost_embedValue {d : ℕ} (A : (valueModel d).Algorithm) (f : Objective d) :
    (linearModel d).runCost (embedValueAlgorithm A) f = (valueModel d).runCost A f := by
  simp only [OracleModel.runCost, runs_embedValue_iff]

theorem succeeds_embedValue_iff {d : ℕ} (A : (valueModel d).Algorithm)
    (C : Set (Objective d)) (ε : ℝ) :
    (linearModel d).Succeeds (embedValueAlgorithm A) C ε ↔
      (valueModel d).Succeeds A C ε := by
  simp only [OracleModel.Succeeds, runs_embedValue_iff]

theorem worstCost_embedValue {d : ℕ} (A : (valueModel d).Algorithm)
    (C : Set (Objective d)) :
    (linearModel d).worstCost (embedValueAlgorithm A) C = (valueModel d).worstCost A C := by
  simp only [OracleModel.worstCost, runCost_embedValue]

theorem Ndet_linear_le_value {d : ℕ} (C : Set (Objective d)) (ε : ℝ) :
    (linearModel d).Ndet C ε ≤ (valueModel d).Ndet C ε := by
  apply OracleModel.le_Ndet
  intro A hA
  rw [← worstCost_embedValue]
  apply OracleModel.Ndet_le_of_success
  exact (succeeds_embedValue_iff A C ε).mpr hA

def valueEntryMeasurableEquiv (d : ℕ) : (valueModel d).Entry ≃ᵐ X d × ℝ :=
  Transcript.equivComap (valueEntryEquiv d)

def linearEntryMeasurableEquiv (d : ℕ) : (linearModel d).Entry ≃ᵐ LinearEntryCode d :=
  Transcript.equivComap (linearEntryEquiv d)

theorem measurable_valueEntry_point {d : ℕ} :
    Measurable (fun e : (valueModel d).Entry => e.1) :=
  measurable_fst.comp (valueEntryMeasurableEquiv d).measurable

theorem measurable_valueEntry_value {d : ℕ} :
    Measurable (fun e : (valueModel d).Entry => e.2) :=
  measurable_snd.comp (valueEntryMeasurableEquiv d).measurable

theorem measurable_valueEntry_mk {d : ℕ} :
    Measurable (fun p : X d × ℝ => (⟨p.1, p.2⟩ : (valueModel d).Entry)) :=
  (valueEntryMeasurableEquiv d).symm.measurable

theorem measurable_linearEntry_point {d : ℕ} :
    Measurable (fun e : (linearModel d).Entry => e.1.point) := by
  have h : Measurable (fun e : LinearEntryCode d => e.2.1) :=
    Transcript.measurable_sigma_iff.mpr (fun _ => measurable_fst)
  exact h.comp (linearEntryMeasurableEquiv d).measurable

theorem measurable_linearEntry_value {d : ℕ} :
    Measurable (fun e : (linearModel d).Entry => e.2.1) := by
  have h : Measurable (fun e : LinearEntryCode d => e.2.2.2.1) :=
    Transcript.measurable_sigma_iff.mpr (fun _ => measurable_snd.snd.fst)
  exact h.comp (linearEntryMeasurableEquiv d).measurable

theorem measurable_valueQuery {d : ℕ} : Measurable (valueQuery : X d → LinearQuery d) := by
  have h : Measurable (fun x : X d =>
      (⟨0, x, (0 : X 0 →L[ℝ] X d)⟩ : LinearQueryCode d)) :=
    (Transcript.measurable_sigma_mk 0).comp (measurable_id.prodMk measurable_const)
  exact (linearQueryMeasurableEquiv d).symm.measurable.comp h

end ExactZO
