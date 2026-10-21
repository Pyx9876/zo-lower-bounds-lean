import ExactZO.ScalingLemma

noncomputable section

namespace ExactZO

variable {d e : ℕ}

/-- Reconstruct one high-dimensional entry by replaying the target algorithm.
Malformed widths and entries supplied after an output use the total fallback
of retaining the reconstructed history. The genuine-run lemmas below always
use the matching-width query branch. -/
def replayStep (A : (linearModel d).Algorithm) (a b : ℝ)
    (h : (linearModel d).History) (entry : (linearModel e).Entry) :
    (linearModel d).History :=
  match A h with
  | .output _ => h
  | .query q =>
      if hw : entry.1.width = q.width then
        h ++ [⟨q, (a * entry.2.1, b • cast (congrArg X hw) entry.2.2)⟩]
      else h

/-- Decode an entire low-dimensional history without recovering a query from
its projection: every high-dimensional query is generated anew by `A`. -/
def replayHistory (A : (linearModel d).Algorithm) (a b : ℝ)
    (h : (linearModel e).History) : (linearModel d).History :=
  h.foldl (replayStep A a b) []

/-- The simulated algorithm depends only on the original algorithm and public
scaling/embedding parameters, never on the unknown source objective. -/
def simulateAlgorithm (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) : (linearModel e).Algorithm := fun h =>
  match A (replayHistory A a (a / s) h) with
  | .query q => .query (q.project J.toContinuousLinearMap.adjoint s)
  | .output x => .output (project J s x)

theorem replayHistory_nil (A : (linearModel d).Algorithm) (a b : ℝ) :
    replayHistory (e := e) A a b [] = [] := rfl

theorem replayHistory_append_answer (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) (F : Objective e)
    (h : (linearModel e).History) (q : LinearQuery d)
    (hq : A (replayHistory A a (a / s) h) = .query q) :
    replayHistory A a (a / s)
      (h ++ [⟨q.project J.toContinuousLinearMap.adjoint s,
        linearReply F (q.project J.toContinuousLinearMap.adjoint s)⟩]) =
      replayHistory A a (a / s) h ++ [⟨q, linearReply (embedObjective J a s F) q⟩] := by
  rw [linearReply_embedObjective]
  simp only [replayHistory, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change replayStep A a (a / s) (replayHistory A a (a / s) h) _ = _
  simp [replayStep, hq, LinearQuery.project]
  rfl

/-- Every finite adaptive target run has a source run with no greater total
rank-based cost. The output is projected even when it was never queried. -/
theorem runFrom_simulateAlgorithm (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) (F : Objective e)
    {h : (linearModel d).History} {n : ℕ} {x : X d}
    (hr : (linearModel d).RunFrom A (embedObjective J a s F) h n x) :
    ∀ h' : (linearModel e).History,
      replayHistory A a (a / s) h' = h →
      ∃ m, m ≤ n ∧ (linearModel e).RunFrom (simulateAlgorithm J a s A) F h' m
        (project J s x) := by
  induction hr with
  | output ha =>
      intro h' hh
      refine ⟨0, le_rfl, OracleModel.RunFrom.output ?_⟩
      simp [simulateAlgorithm, hh, ha]
  | @query h q n x ha ht ih =>
      intro h' hh
      have haction : A (replayHistory A a (a / s) h') = .query q := by
        simpa [hh] using ha
      have hdecode : replayHistory A a (a / s)
          (h' ++ [⟨q.project J.toContinuousLinearMap.adjoint s,
            (linearModel e).answer F (q.project J.toContinuousLinearMap.adjoint s)⟩]) =
          h ++ [⟨q, (linearModel d).answer (embedObjective J a s F) q⟩] := by
        simpa [linearModel, hh] using replayHistory_append_answer J a s A F h' q haction
      obtain ⟨m, hm, hrun⟩ := ih _ hdecode
      refine ⟨(q.project J.toContinuousLinearMap.adjoint s).cost + m,
        Nat.add_le_add (q.project_cost_le _ _) hm, ?_⟩
      have hsquery : simulateAlgorithm J a s A h' =
          .query (q.project J.toContinuousLinearMap.adjoint s) := by
        simp [simulateAlgorithm, haction]
      exact OracleModel.RunFrom.query hsquery hrun

theorem runs_simulateAlgorithm (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) (F : Objective e) {n : ℕ} {x : X d}
    (hr : (linearModel d).Runs A (embedObjective J a s F) n x) :
    ∃ m, m ≤ n ∧ (linearModel e).Runs (simulateAlgorithm J a s A) F m
      (project J s x) :=
  runFrom_simulateAlgorithm J a s A F hr [] rfl

/-- Simulation cannot increase actual run cost, including nontermination
(represented by infinity). -/
theorem runCost_simulateAlgorithm_le (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) (F : Objective e) :
    (linearModel e).runCost (simulateAlgorithm J a s A) F ≤
      (linearModel d).runCost A (embedObjective J a s F) := by
  by_cases hex : ∃ n x, (linearModel d).Runs A (embedObjective J a s F) n x
  · obtain ⟨n, x, hn⟩ := hex
    obtain ⟨m, hm, hrun⟩ := runs_simulateAlgorithm J a s A F hn
    rw [OracleModel.runCost_eq_of_runs _ hn, OracleModel.runCost_eq_of_runs _ hrun]
    exact_mod_cast hm
  · rw [(OracleModel.runCost_eq_top_iff _).mpr hex]
    exact le_top

/-- A successful algorithm on a class containing the embedded objectives
induces a successful algorithm on the source class at the unscaled accuracy. -/
theorem succeeds_simulateAlgorithm (J : X e →ₗᵢ[ℝ] X d) {a s ε : ℝ}
    (ha : 0 < a) (hs : 0 < s) (A : (linearModel d).Algorithm)
    {C : Set (Objective e)} {D : Set (Objective d)}
    (hclass : ∀ F ∈ C, embedObjective J a s F ∈ D)
    (hA : (linearModel d).Succeeds A D ((a / s) * ε)) :
    (linearModel e).Succeeds (simulateAlgorithm J a s A) C ε := by
  intro F hF
  obtain ⟨n, x, hrun, hgrad⟩ := hA _ (hclass F hF)
  obtain ⟨m, _, hm⟩ := runs_simulateAlgorithm J a s A F hrun
  refine ⟨m, project J s x, hm, ?_⟩
  rw [embedObjective_grad_norm J ha.le hs] at hgrad
  exact (mul_le_mul_left (div_pos ha hs)).mp hgrad

theorem terminatesOn_simulateAlgorithm (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) {C : Set (Objective e)} {D : Set (Objective d)}
    (hclass : ∀ F ∈ C, embedObjective J a s F ∈ D)
    (hA : (linearModel d).TerminatesOn A D) :
    (linearModel e).TerminatesOn (simulateAlgorithm J a s A) C := by
  intro F hF
  obtain ⟨n, x, hn⟩ := hA _ (hclass F hF)
  obtain ⟨m, _, hm⟩ := runs_simulateAlgorithm J a s A F hn
  exact ⟨m, project J s x, hm⟩

theorem worstCost_simulateAlgorithm_le (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (A : (linearModel d).Algorithm) {C : Set (Objective e)} {D : Set (Objective d)}
    (hclass : ∀ F ∈ C, embedObjective J a s F ∈ D) :
    (linearModel e).worstCost (simulateAlgorithm J a s A) C ≤
      (linearModel d).worstCost A D := by
  refine iSup_le fun F => iSup_le fun hF => ?_
  exact (runCost_simulateAlgorithm_le J a s A F).trans
    (le_iSup_of_le (embedObjective J a s F) (le_iSup_of_le (hclass F hF) le_rfl))

/-- The algorithm-level reduction yields the deterministic lower-bound
transfer for arbitrary source/target classes with proved embedding inclusion. -/
theorem Ndet_le_of_embedding (J : X e →ₗᵢ[ℝ] X d) {a s ε : ℝ}
    (ha : 0 < a) (hs : 0 < s) {C : Set (Objective e)} {D : Set (Objective d)}
    (hclass : ∀ F ∈ C, embedObjective J a s F ∈ D) :
    (linearModel e).Ndet C ε ≤ (linearModel d).Ndet D ((a / s) * ε) := by
  apply OracleModel.le_Ndet
  intro A hA
  exact (OracleModel.Ndet_le_of_success _
    (succeeds_simulateAlgorithm J ha hs A hclass hA)).trans
      (worstCost_simulateAlgorithm_le J a s A hclass)

end ExactZO
