import ExactZO.Oracle

noncomputable section

namespace ExactZO

/-- A well-founded value-query procedure. Branching uses only returned scalars. -/
inductive ValueProcedure (d : ℕ) where
  | output (point : X d)
  | query (point : X d) (next : ℝ → ValueProcedure d)

namespace ValueProcedure

variable {d : ℕ}

def result (P : ValueProcedure d) (f : Objective d) : X d :=
  match P with
  | .output x => x
  | .query q next => (next (f.value q)).result f

def cost (P : ValueProcedure d) (f : Objective d) : ℕ :=
  match P with
  | .output _ => 0
  | .query q next => 1 + (next (f.value q)).cost f

/-- The policy replays the returned scalars. Query coordinates in malformed
histories are irrelevant; legal runs append the policy's actual query. -/
def action (P : ValueProcedure d) (h : (valueModel d).History) :
    (valueModel d).Action :=
  match h with
  | [] => match P with
    | .output x => .output x
    | .query q _ => .query q
  | entry :: tail => match P with
    | .output x => .output x
    | .query _ next => (next entry.2).action tail
termination_by structural h

def algorithm (P : ValueProcedure d) : (valueModel d).Algorithm := P.action

theorem runFrom_of_action_eq (P : ValueProcedure d) (f : Objective d)
    (A : (valueModel d).Algorithm) (h : (valueModel d).History)
    (ha : ∀ tail, A (h ++ tail) = P.action tail) :
    (valueModel d).RunFrom A f h (P.cost f) (P.result f) := by
  induction P generalizing h with
  | output x =>
      apply OracleModel.RunFrom.output
      simpa [action] using ha []
  | query q next ih =>
      apply OracleModel.RunFrom.query
      · simpa [action] using ha []
      · apply ih (f.value q)
        intro tail
        simpa [List.append_assoc, action, valueModel] using
          ha (⟨q, f.value q⟩ :: tail)

theorem runs (P : ValueProcedure d) (f : Objective d) :
    (valueModel d).Runs P.algorithm f (P.cost f) (P.result f) := by
  apply runFrom_of_action_eq
  intro tail
  rfl

theorem runCost (P : ValueProcedure d) (f : Objective d) :
    (valueModel d).runCost P.algorithm f = (P.cost f : ℕ∞) :=
  OracleModel.runCost_eq_of_runs _ (P.runs f)

/-- Query every member of a fixed finite vector before applying the continuation. -/
def queryVector : (n : ℕ) → (Fin n → X d) → ((Fin n → ℝ) → ValueProcedure d) →
    ValueProcedure d
  | 0, _, next => next Fin.elim0
  | n + 1, points, next => .query (points 0) fun value =>
      queryVector n (fun i => points i.succ) fun values => next (Fin.cons value values)

theorem queryVector_result (n : ℕ) (points : Fin n → X d)
    (next : (Fin n → ℝ) → ValueProcedure d) (f : Objective d) :
    (queryVector n points next).result f = (next (fun i => f.value (points i))).result f := by
  induction n with
  | zero =>
      simp only [queryVector]
      have heq : (Fin.elim0 : Fin 0 → ℝ) = (fun i => f.value (points i)) :=
        Subsingleton.elim _ _
      rw [heq]
  | succ n ih =>
      simp only [queryVector, result]
      rw [ih]
      have heq : Fin.cons (f.value (points 0)) (fun i => f.value (points i.succ)) =
          (fun i => f.value (points i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [heq]

theorem queryVector_cost (n : ℕ) (points : Fin n → X d)
    (next : (Fin n → ℝ) → ValueProcedure d) (f : Objective d) :
    (queryVector n points next).cost f = n + (next (fun i => f.value (points i))).cost f := by
  induction n with
  | zero =>
      simp only [queryVector, zero_add]
      have heq : (Fin.elim0 : Fin 0 → ℝ) = (fun i => f.value (points i)) :=
        Subsingleton.elim _ _
      rw [heq]
  | succ n ih =>
      simp only [queryVector, cost]
      rw [ih]
      have heq : Fin.cons (f.value (points 0)) (fun i => f.value (points i.succ)) =
          (fun i => f.value (points i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [heq]
      omega

end ValueProcedure
end ExactZO
