import ExactZO.SubspaceResidual
import ExactZO.LineSearch

/-! A finite exact-value restarted subspace procedure. The procedure is chosen
only from public parameters and public fuel. Its objective-dependent interpreter
records the actual transitions for subsequent descent and trace-budget proofs. -/
noncomputable section
open scoped InnerProductSpace

namespace ExactZO.ValueProcedure
variable {d : ℕ}

def bind : ValueProcedure d → (X d → ValueProcedure d) → ValueProcedure d
  | .output x, next => next x
  | .query q branch, next => .query q (fun value => bind (branch value) next)

theorem bind_result (P : ValueProcedure d) (next : X d → ValueProcedure d)
    (f : Objective d) : (P.bind next).result f = (next (P.result f)).result f := by
  induction P with
  | output x => rfl
  | query q branch ih => exact ih (f.value q)

theorem bind_cost (P : ValueProcedure d) (next : X d → ValueProcedure d)
    (f : Objective d) : (P.bind next).cost f = P.cost f + (next (P.result f)).cost f := by
  induction P with
  | output x => simp [bind, cost, result]
  | query q branch ih =>
      simp only [bind, cost, result, ih]
      omega

end ExactZO.ValueProcedure

namespace ExactZO.SubspaceProcedure
open FrameGeometry SubspaceEstimate SubspaceResidual
variable {d : ℕ}

/-- Reset exactly when the newly appended frame reaches the public block size. -/
def nextFrame (r : ℕ) (U : List (X d)) (u : X d) : List (X d) :=
  if U.length + 1 = r then [] else U ++ [u]

theorem nextFrame_length (r : ℕ) (U : List (X d)) (u : X d) :
    (nextFrame r U u).length = if U.length + 1 = r then 0 else U.length + 1 := by
  unfold nextFrame
  split_ifs <;> simp

theorem nextFrame_length_lt {r : ℕ} (hr : 0 < r) {U : List (X d)}
    (hU : U.length < r) (u : X d) : (nextFrame r U u).length < r := by
  rw [nextFrame_length]
  split_ifs <;> omega

/-- Both loops are genuinely finite: every move consumes one public fuel unit;
line-search finiteness is provided by its own public fuel. -/
def loop (L ε : ℝ) (r lineFuel : ℕ) : ℕ → X d → List (X d) → ValueProcedure d
  | 0, x, _ => .output x
  | fuel + 1, x, U =>
      SubspaceEstimate.estimateProcedure U (radius U.length L ε) x fun z =>
        if ‖z‖ ≤ 7 * ε / 16 then
          fullEstimateProcedure L ε x fun g =>
            if ‖g‖ ≤ 15 * ε / 16 then .output x
            else
              let u := direction U g
              (LineSearch.procedure lineFuel L ε x u).bind fun y =>
                loop L ε r lineFuel fuel y (nextFrame r U u)
        else loop L ε r lineFuel fuel (x - L⁻¹ • frameMap U z) U

/-- The public entry point starts at zero with the empty frame. -/
def procedure (L ε : ℝ) (r totalFuel lineFuel : ℕ) : ValueProcedure d :=
  loop L ε r lineFuel totalFuel 0 []

/-- Actual oracle-dependent transitions used only in the semantic interpreter.
The stored vectors and line cost are computed, never hypotheses to the algorithm. -/
inductive Step (d : ℕ) where
  | terminal (x : X d) (frame : List (X d))
  | restricted (x : X d) (frame : List (X d)) (y : X d)
  | expansion (x : X d) (frame : List (X d)) (u y : X d) (lineCost : ℕ)

namespace Step

def target : Step d → X d
  | .terminal x _ => x
  | .restricted _ _ y => y
  | .expansion _ _ _ y _ => y

def frameAfter (r : ℕ) : Step d → List (X d)
  | .terminal _ U => U
  | .restricted _ U _ => U
  | .expansion _ U u _ _ => nextFrame r U u

def queryCost : Step d → ℕ
  | .terminal _ U => 2 * U.length + 2 * d
  | .restricted _ U _ => 2 * U.length
  | .expansion _ U _ _ lineCost => 2 * U.length + 2 * d + lineCost

def isTerminal : Step d → Bool
  | .terminal _ _ => true
  | _ => false

def restrictedCount : Step d → ℕ
  | .restricted _ _ _ => 1
  | _ => 0

def expansionCount : Step d → ℕ
  | .expansion _ _ _ _ _ => 1
  | _ => 0

end Step

/-- A deterministic interpreter step evaluates precisely the values queried
by the procedure; the objective is not a parameter of `loop` or `procedure`. -/
def step (f : Objective d) (L ε : ℝ) (lineFuel : ℕ)
    (x : X d) (U : List (X d)) : Step d :=
  let z := estimate f.value U (radius U.length L ε) x
  if ‖z‖ ≤ 7 * ε / 16 then
    let g := fullEstimate f.value L ε x
    if ‖g‖ ≤ 15 * ε / 16 then .terminal x U
    else
      let u := direction U g
      let line := LineSearch.procedure lineFuel L ε x u
      .expansion x U u (line.result f) (line.cost f)
  else .restricted x U (x - L⁻¹ • frameMap U z)

structure RunResult (d : ℕ) where
  point : X d
  frame : List (X d)
  cost : ℕ
  trace : List (Step d)
  restrictedCount : ℕ
  expansionCount : ℕ
  /-- True means the actual full finite-difference test stopped the run.
  False records exhausted public fuel; no stationarity claim is made here. -/
  stopped : Bool

def run (f : Objective d) (L ε : ℝ) (r lineFuel : ℕ) :
    ℕ → X d → List (X d) → RunResult d
  | 0, x, U => ⟨x, U, 0, [], 0, 0, false⟩
  | fuel + 1, x, U =>
      let s := step f L ε lineFuel x U
      if s.isTerminal then
        ⟨s.target, s.frameAfter r, s.queryCost, [s],
          s.restrictedCount, s.expansionCount, true⟩
      else
        let tail := run f L ε r lineFuel fuel s.target (s.frameAfter r)
        { tail with
          cost := s.queryCost + tail.cost
          trace := s :: tail.trace
          restrictedCount := s.restrictedCount + tail.restrictedCount
          expansionCount := s.expansionCount + tail.expansionCount }

/-- The interpreter's endpoint is the actual value-procedure endpoint. -/
theorem loop_result (L ε : ℝ) (r lineFuel fuel : ℕ) (x : X d) (U : List (X d))
    (f : Objective d) :
    (loop L ε r lineFuel fuel x U).result f = (run f L ε r lineFuel fuel x U).point := by
  induction fuel generalizing x U with
  | zero => rfl
  | succ fuel ih =>
      by_cases hr : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7 * ε / 16
      · by_cases hg : ‖fullEstimate f.value L ε x‖ ≤ 15 * ε / 16
        · simp [loop, SubspaceEstimate.estimateProcedure_result, fullEstimateProcedure_result,
            run, step, hr, hg, Step.isTerminal, Step.target, ValueProcedure.result]
        · simp [loop, SubspaceEstimate.estimateProcedure_result, fullEstimateProcedure_result,
            ValueProcedure.bind_result, run, step, hr, hg, Step.isTerminal,
            Step.target, Step.frameAfter, ih]
      · simp [loop, SubspaceEstimate.estimateProcedure_result, run, step, hr, Step.isTerminal,
          Step.target, Step.frameAfter, ih]

/-- All actual queries are charged, including terminal full tests and failed
line-search proposals. -/
theorem loop_cost (L ε : ℝ) (r lineFuel fuel : ℕ) (x : X d) (U : List (X d))
    (f : Objective d) :
    (loop L ε r lineFuel fuel x U).cost f = (run f L ε r lineFuel fuel x U).cost := by
  induction fuel generalizing x U with
  | zero => rfl
  | succ fuel ih =>
      by_cases hr : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7 * ε / 16
      · by_cases hg : ‖fullEstimate f.value L ε x‖ ≤ 15 * ε / 16
        · simp [loop, SubspaceEstimate.estimateProcedure_cost, fullEstimateProcedure_cost,
            run, step, hr, hg, Step.isTerminal, Step.queryCost, ValueProcedure.cost]
        · simp [loop, SubspaceEstimate.estimateProcedure_cost, fullEstimateProcedure_cost,
            ValueProcedure.bind_cost, run, step, hr, hg, Step.isTerminal,
            Step.target, Step.frameAfter, Step.queryCost, ih, Nat.add_assoc]
      · simp [loop, SubspaceEstimate.estimateProcedure_cost, run, step, hr, Step.isTerminal,
          Step.target, Step.frameAfter, Step.queryCost, ih]

/-- Query accounting is exactly the sum over the actual execution trace. -/
theorem run_cost_eq_trace (f : Objective d) (L ε : ℝ) (r lineFuel fuel : ℕ)
    (x : X d) (U : List (X d)) :
    (run f L ε r lineFuel fuel x U).cost =
      ((run f L ε r lineFuel fuel x U).trace.map Step.queryCost).sum := by
  induction fuel generalizing x U with
  | zero => rfl
  | succ fuel ih =>
      simp only [run]
      split_ifs <;> simp_all

theorem run_restrictedCount_eq_trace (f : Objective d) (L ε : ℝ) (r lineFuel fuel : ℕ)
    (x : X d) (U : List (X d)) :
    (run f L ε r lineFuel fuel x U).restrictedCount =
      ((run f L ε r lineFuel fuel x U).trace.map Step.restrictedCount).sum := by
  induction fuel generalizing x U with
  | zero => rfl
  | succ fuel ih =>
      simp only [run]
      split_ifs <;> simp_all

theorem run_expansionCount_eq_trace (f : Objective d) (L ε : ℝ) (r lineFuel fuel : ℕ)
    (x : X d) (U : List (X d)) :
    (run f L ε r lineFuel fuel x U).expansionCount =
      ((run f L ε r lineFuel fuel x U).trace.map Step.expansionCount).sum := by
  induction fuel generalizing x U with
  | zero => rfl
  | succ fuel ih =>
      simp only [run]
      split_ifs <;> simp_all

theorem procedure_runs (L ε : ℝ) (r totalFuel lineFuel : ℕ) (f : Objective d) :
    (valueModel d).Runs (procedure (d := d) L ε r totalFuel lineFuel).algorithm f
      (run f L ε r lineFuel totalFuel 0 []).cost
      (run f L ε r lineFuel totalFuel 0 []).point := by
  have h := (procedure (d := d) L ε r totalFuel lineFuel).runs f
  simpa only [procedure, loop_result, loop_cost] using h


end ExactZO.SubspaceProcedure
