import ExactZO.SubspaceProcedure
import ExactZO.SubspaceInvariant

/-! Public finite fuel is sufficient for the actual restarted value procedure.
The proof rules out exhausted fuel using the state budget and certifies the
actual terminal point by its computed full finite-difference test. -/
noncomputable section
open scoped InnerProductSpace

namespace ExactZO.SubspaceTermination
open FrameGeometry SubspaceEstimate SubspaceResidual SubspaceProcedure SubspaceInvariant
variable {d : ℕ}

/-- A reset preserves the total number of expansions, including the new move. -/
theorem expansion_index_succ (r q : ℕ) (U : List (X d)) (u : X d) :
    (if U.length + 1 = r then q + 1 else q) * r + (nextFrame r U u).length =
      q * r + U.length + 1 := by
  by_cases h : U.length + 1 = r
  · simp only [h, if_pos, nextFrame, List.length_nil, add_zero, Nat.add_mul, one_mul]
    omega
  · simp [nextFrame, h]
    omega

/-- Every actual finite prefix preserves the state budget, even if its public
fuel is insufficient. Expansion counts agree with complete blocks and the frame. -/
theorem run_preserves_budget {f : Objective d} {H : X d →L[ℝ] X d}
    {L Δ E ε : ℝ} (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {r fuel j q : ℕ} {x : X d} {U : List (X d)}
    (hb : StateBudget f H L E ε r x U j q) :
    ∃ q', StateBudget f H L E ε r
        (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).point
        (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).frame
        (j + (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).restrictedCount) q' ∧
      q' * r + (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).frame.length =
        q * r + U.length + (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).expansionCount := by
  induction fuel generalizing x U j q with
  | zero =>
      exact ⟨q, by simpa only [run, Nat.add_zero] using hb, rfl⟩
  | succ fuel ih =>
      by_cases hr : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7 * ε / 16
      · by_cases hg : ‖fullEstimate f.value L ε x‖ ≤ 15 * ε / 16
        · refine ⟨q, ?_, ?_⟩
          · simpa [run, step, hr, hg, Step.isTerminal, Step.target, Step.frameAfter,
              Step.restrictedCount] using hb
          · simp [run, step, hr, hg, Step.isTerminal, Step.frameAfter, Step.expansionCount]
        · have hrest := estimate_stop f hf.1 hb.ortho hL hε x hr
          obtain ⟨_, hunorm, huorth, huslope, _⟩ :=
            fullEstimate_residual f hf.1 hb.ortho hL hε x hrest (lt_of_not_ge hg)
          let u := direction U (fullEstimate f.value L ε x)
          let P := LineSearch.procedure (LineSearch.publicFuel L Δ ε) L ε x u
          obtain ⟨hcurv, k, hfirst, hresult, hcost, hdec, hconst, hlinecost⟩ :=
            LineSearch.procedure_spec hL hε hf hH hmodel (hb.sublevel hL hE) hunorm huslope
          change 0 < ⟪u, H u⟫_ℝ at hcurv
          change 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) < f.value x - f.value (P.result f) at hdec
          change ε ^ 2 / (10 * ⟪u, H u⟫_ℝ) < 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) at hconst
          have hnext := hb.expansion_move hL hE hH hunorm huorth hcurv (hconst.trans hdec).le
          change StateBudget f H L E ε r (P.result f) (nextFrame r U u) j
            (if U.length + 1 = r then q + 1 else q) at hnext
          obtain ⟨q', hbudget, hcount⟩ := ih hnext
          have hindex := expansion_index_succ r q U u
          refine ⟨q', ?_, ?_⟩
          · simpa [run, step, hr, hg, Step.isTerminal, Step.target, Step.frameAfter,
              Step.restrictedCount, u, P] using hbudget
          · have hcount' : q' * r +
                (run f L ε r (LineSearch.publicFuel L Δ ε) fuel (P.result f) (nextFrame r U u)).frame.length =
                q * r + U.length + (1 +
                  (run f L ε r (LineSearch.publicFuel L Δ ε) fuel (P.result f) (nextFrame r U u)).expansionCount) := by
              omega
            simpa [run, step, hr, hg, Step.isTerminal, Step.target, Step.frameAfter,
              Step.expansionCount, u, P] using hcount'
      · have hdec := estimate_descent f hf.1 hb.ortho hL hε x (lt_of_not_ge hr)
        have hnext := hb.restricted_move (by simpa only [stepDecrease] using hdec.le)
        obtain ⟨q', hbudget, hcount⟩ := ih hnext
        refine ⟨q', ?_, ?_⟩
        · simpa [run, step, hr, Step.isTerminal, Step.target, Step.frameAfter,
            Step.restrictedCount, Nat.add_assoc] using hbudget
        · simpa [run, step, hr, Step.isTerminal, Step.target, Step.frameAfter,
            Step.expansionCount] using hcount

/-- The budget controls every actual move. No stationarity or termination
conclusion is an assumption of this theorem. -/
theorem run_terminates {f : Objective d} {H : X d →L[ℝ] X d}
    {L Δ E ε : ℝ} (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {r fuel j q : ℕ} {x : X d} {U : List (X d)}
    (hb : StateBudget f H L E ε r x U j q)
    (hroom : restrictedLimit L Δ ε + expansionLimit L Δ E ε r <
      fuel + j + q * r + U.length) :
    (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).stopped = true ∧
      ‖f.grad (run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U).point‖ ≤ ε := by
  induction fuel generalizing x U j q with
  | zero =>
      have hcounts := hb.counts_bound hL hE hε hH hf.2
      omega
  | succ fuel ih =>
      by_cases hr : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7 * ε / 16
      · by_cases hg : ‖fullEstimate f.value L ε x‖ ≤ 15 * ε / 16
        · have hgood := fullEstimate_stop f hf.1 hL hε x hg
          simpa [run, step, hr, hg, Step.isTerminal, Step.target] using
            (show true = true ∧ ‖f.grad x‖ ≤ ε from ⟨rfl, hgood⟩)
        · have hrest := estimate_stop f hf.1 hb.ortho hL hε x hr
          obtain ⟨_, hunorm, huorth, huslope, _⟩ :=
            fullEstimate_residual f hf.1 hb.ortho hL hε x hrest (lt_of_not_ge hg)
          let u := direction U (fullEstimate f.value L ε x)
          let P := LineSearch.procedure (LineSearch.publicFuel L Δ ε) L ε x u
          obtain ⟨hcurv, k, hfirst, hresult, hcost, hdec, hconst, hlinecost⟩ :=
            LineSearch.procedure_spec hL hε hf hH hmodel (hb.sublevel hL hE) hunorm huslope
          change 0 < ⟪u, H u⟫_ℝ at hcurv
          change 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) < f.value x - f.value (P.result f) at hdec
          change ε ^ 2 / (10 * ⟪u, H u⟫_ℝ) < 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) at hconst
          have hnext := hb.expansion_move hL hE hH hunorm huorth hcurv (hconst.trans hdec).le
          change StateBudget f H L E ε r (P.result f) (nextFrame r U u) j
            (if U.length + 1 = r then q + 1 else q) at hnext
          have hindex := expansion_index_succ r q U u
          have hroom' : restrictedLimit L Δ ε + expansionLimit L Δ E ε r <
              fuel + j + (if U.length + 1 = r then q + 1 else q) * r +
                (nextFrame r U u).length := by omega
          have hout := ih hnext hroom'
          simpa only [run, step, hr, if_pos, hg, if_neg, Step.isTerminal, Bool.false_eq_true,
            if_false, Step.target, Step.frameAfter, u, P] using hout
      · have hdec := estimate_descent f hf.1 hb.ortho hL hε x (lt_of_not_ge hr)
        have hnext := hb.restricted_move (by simpa only [stepDecrease] using hdec.le)
        have hroom' : restrictedLimit L Δ ε + expansionLimit L Δ E ε r <
            fuel + (j + 1) + q * r + U.length := by omega
        have hout := ih hnext hroom'
        simpa only [run, step, hr, if_neg, Step.isTerminal, Bool.false_eq_true,
          if_false, Step.target, Step.frameAfter] using hout

/-- A concrete algorithm chosen solely from the public parameters. -/
def publicProcedure (L Δ E ε : ℝ) (r : ℕ) : ValueProcedure d :=
  procedure L ε r (totalFuel L Δ E ε r) (LineSearch.publicFuel L Δ ε)

/-- The actual result of the public finite procedure is epsilon-stationary. -/
theorem publicProcedure_stationary {f : Objective d} {H : X d →L[ℝ] X d}
    {L Δ E ε : ℝ} {r : ℕ} (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (hr : 0 < r) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y) :
    ‖f.grad ((publicProcedure (d := d) L Δ E ε r).result f)‖ ≤ ε := by
  have h := run_terminates hL hE hε hf hH hmodel
    (initial f H L E ε hr) (fuel := totalFuel L Δ E ε r) (by simp [totalFuel])
  simpa only [publicProcedure, procedure, loop_result] using h.2

/-- A single public algorithm succeeds on every member of the actual class.
The matrix is obtained only in the proof, never supplied to the procedure. -/
theorem publicProcedure_succeeds {L Δ E ε : ℝ} {r : ℕ}
    (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε) (hr : 0 < r) :
    (valueModel d).Succeeds (publicProcedure (d := d) L Δ E ε r).algorithm
      {f | SublevelClass L Δ E f} ε := by
  intro f hf
  obtain ⟨hsmooth, H, hH, hmodel⟩ := hf
  refine ⟨_, _, (publicProcedure (d := d) L Δ E ε r).runs f, ?_⟩
  exact publicProcedure_stationary hL hE hε hr hsmooth hH hmodel

end ExactZO.SubspaceTermination
