import ExactZO.STPCore

noncomputable section
namespace ExactZO.STP
variable {d : ℕ}

/-- Execute every pair of proposals, remembering the requested pre-update
iterate. Only the three scalar replies are used to choose the next point. -/
def procedureLoop (h : ℝ) (a : ℕ → X d) (k : ℕ) :
    ℕ → ℕ → X d → ℝ → X d → ValueProcedure d
  | 0, _, _, _, remembered => .output remembered
  | n + 1, t, x, vx, remembered =>
      .query (x + h • a t) fun vp =>
        .query (x - h • a t) fun vm =>
          procedureLoop h a k n (t + 1)
            (choose x (x + h • a t) (x - h • a t) vx vp vm)
            (min vx (min vp vm)) (if t = k then x else remembered)

/-- Cache the center value once; every one of N updates still makes two
queries even if the center wins or the selected output is already known. -/
def procedure (h : ℝ) (a : ℕ → X d) (N k : ℕ) : ValueProcedure d :=
  .query 0 fun v => procedureLoop h a k N 0 0 v 0

theorem procedureLoop_cost (f : Objective d) (h : ℝ) (a : ℕ → X d)
    (k n t : ℕ) (x : X d) (vx : ℝ) (remembered : X d) :
    (procedureLoop h a k n t x vx remembered).cost f = 2 * n := by
  induction n generalizing t x vx remembered with
  | zero => rfl
  | succ n ih => simp only [procedureLoop, ValueProcedure.cost, ih]; omega

theorem procedure_cost (f : Objective d) (h : ℝ) (a : ℕ → X d) (N k : ℕ) :
    (procedure h a N k).cost f = 1 + 2 * N := by
  simp only [procedure, ValueProcedure.cost, procedureLoop_cost]

theorem procedureLoop_result (f : Objective d) (h : ℝ) (a : ℕ → X d)
    (k n t : ℕ) (remembered : X d) (hk : k < t + n)
    (hpast : k < t → remembered = iterates f h a k) :
    (procedureLoop h a k n t (iterates f h a t)
      (f.value (iterates f h a t)) remembered).result f = iterates f h a k := by
  induction n generalizing t remembered with
  | zero => exact hpast (by omega)
  | succ n ih =>
      simp only [procedureLoop, ValueProcedure.result]
      change (procedureLoop h a k n (t + 1) (step f h (iterates f h a t) (a t))
        (min (f.value (iterates f h a t))
          (min (f.value (iterates f h a t + h • a t))
            (f.value (iterates f h a t - h • a t))))
        (if t = k then iterates f h a t else remembered)).result f = _
      rw [← step_value]
      change (procedureLoop h a k n (t + 1) (iterates f h a (t + 1))
        (f.value (iterates f h a (t + 1))) _).result f = _
      apply ih (t := t + 1) _ (by omega)
      intro hkt
      split_ifs with he
      · subst t; rfl
      · exact hpast (by omega)

theorem procedure_result (f : Objective d) (h : ℝ) (a : ℕ → X d)
    (N k : ℕ) (hk : k < N) :
    (procedure h a N k).result f = iterates f h a k := by
  simp only [procedure, ValueProcedure.result]
  exact procedureLoop_result f h a k N 0 0 (by omega) (by omega)

/-- The policy is fixed by the seed and public parameters before choosing f. -/
theorem procedure_runs (f : Objective d) (h : ℝ) (a : ℕ → X d)
    (N k : ℕ) (hk : k < N) :
    (valueModel d).Runs (procedure h a N k).algorithm f
      (1 + 2 * N) (iterates f h a k) := by
  have hr := (procedure h a N k).runs f
  rwa [procedure_cost, procedure_result f h a N k hk] at hr

end ExactZO.STP
