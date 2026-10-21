import ExactZO.ValueProcedure
import ExactZO.FiniteDifference

noncomputable section

namespace ExactZO

variable {d : ℕ}

/-- A batch consists of all positive coordinate queries followed by all negative
coordinate queries. The continuation receives a vector computed from the replies. -/
def estimateProcedure (h : ℝ) (x : X d) (next : X d → ValueProcedure d) :
    ValueProcedure d :=
  ValueProcedure.queryVector d (fun i => x + h • coordinateVector i) fun positive =>
    ValueProcedure.queryVector d (fun i => x - h • coordinateVector i) fun negative =>
      next ((WithLp.equiv 2 (Fin d → ℝ)).symm fun i => (positive i - negative i) / (2 * h))

theorem estimateProcedure_result (h : ℝ) (x : X d)
    (next : X d → ValueProcedure d) (f : Objective d) :
    (estimateProcedure h x next).result f =
      (next (centralDifference f.value h x)).result f := by
  simp only [estimateProcedure, ValueProcedure.queryVector_result, centralDifference]

theorem estimateProcedure_cost (h : ℝ) (x : X d)
    (next : X d → ValueProcedure d) (f : Objective d) :
    (estimateProcedure h x next).cost f =
      2 * d + (next (centralDifference f.value h x)).cost f := by
  simp only [estimateProcedure, ValueProcedure.queryVector_cost, centralDifference]
  omega

/-- The same finite procedure is fixed from public parameters before choosing f. -/
def coordinateProcedure (L ε : ℝ) : ℕ → X d → ValueProcedure d
  | 0, x => .output x
  | n + 1, x => estimateProcedure (fdRadius d L ε) x fun g =>
      if ‖g‖ ≤ 7 * ε / 8 then .output x
      else coordinateProcedure L ε n (x - L⁻¹ • g)

theorem coordinateProcedure_result_succ (L ε : ℝ) (n : ℕ) (x : X d)
    (f : Objective d) :
    (coordinateProcedure L ε (n + 1) x).result f =
      if ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8 then x
      else (coordinateProcedure L ε n
        (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x)).result f := by
  rw [coordinateProcedure, estimateProcedure_result]
  split <;> rfl

theorem coordinateProcedure_cost_le (L ε : ℝ) (n : ℕ) (x : X d)
    (f : Objective d) : (coordinateProcedure L ε n x).cost f ≤ 2 * d * n := by
  induction n generalizing x with
  | zero => simp [coordinateProcedure, ValueProcedure.cost]
  | succ n ih =>
      rw [coordinateProcedure, estimateProcedure_cost]
      split
      · simp [ValueProcedure.cost]
        nlinarith
      · have h := ih (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x)
        nlinarith

/-- If the budget is exhausted before a stopping test, the full decrease
accumulates. The final stopping estimate, when present, is already a batch. -/
theorem coordinateProcedure_success_or_decrease (L ε c : ℝ) (f : Objective d)
    (hstop : ∀ x, ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8 →
      ‖f.grad x‖ ≤ ε)
    (hstep : ∀ x, ¬ ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8 →
      f.value (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x) ≤ f.value x - c)
    (n : ℕ) (x : X d) :
    ‖f.grad ((coordinateProcedure L ε n x).result f)‖ ≤ ε ∨
      f.value ((coordinateProcedure L ε n x).result f) ≤ f.value x - (n : ℝ) * c := by
  induction n generalizing x with
  | zero => right; simp [coordinateProcedure, ValueProcedure.result]
  | succ n ih =>
      rw [coordinateProcedure_result_succ]
      split
      · rename_i hs
        exact Or.inl (hstop x hs)
      · rename_i hs
        rcases ih (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x) with hg | hd
        · exact Or.inl hg
        · right
          have h := hstep x hs
          push_cast
          linarith

theorem coordinateProcedure_success_of_budget (L ε c Δ : ℝ) (f : Objective d)
    (hgap : HasGap f Δ)
    (hstop : ∀ x, ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8 →
      ‖f.grad x‖ ≤ ε)
    (hstep : ∀ x, ¬ ‖centralDifference f.value (fdRadius d L ε) x‖ ≤ 7 * ε / 8 →
      f.value (x - L⁻¹ • centralDifference f.value (fdRadius d L ε) x) ≤ f.value x - c)
    (n : ℕ) (hn : Δ < (n : ℝ) * c) :
    ‖f.grad ((coordinateProcedure L ε n (0 : X d)).result f)‖ ≤ ε := by
  rcases coordinateProcedure_success_or_decrease L ε c f hstop hstep n 0 with hg | hd
  · exact hg
  · obtain ⟨lower, hlower, hgap⟩ := hgap
    have hl := hlower ((coordinateProcedure L ε n 0).result f)
    linarith

/-- The last, stopping estimate is included in this public budget. -/
def coordinateBudget (L Δ ε : ℝ) : ℕ := 1 + ⌊128 * L * Δ / (35 * ε ^ 2)⌋₊

theorem coordinateBudget_decrease {L Δ ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    Δ < (coordinateBudget L Δ ε : ℝ) * (35 * ε ^ 2 / (128 * L)) := by
  have hc : 0 < 35 * ε ^ 2 / (128 * L) := by positivity
  have h := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one (128 * L * Δ / (35 * ε ^ 2))) hc
  have heq : (128 * L * Δ / (35 * ε ^ 2)) * (35 * ε ^ 2 / (128 * L)) = Δ := by
    field_simp
  rw [heq] at h
  simpa [coordinateBudget, Nat.cast_add, Nat.cast_one, add_comm] using h

theorem coordinateProcedure_stationary {L Δ ε : ℝ} (f : Objective d)
    (hf : SmoothClass L Δ f) (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) :
    ‖f.grad ((coordinateProcedure L ε (coordinateBudget L Δ ε) (0 : X d)).result f)‖ ≤ ε := by
  apply coordinateProcedure_success_of_budget L ε (35 * ε ^ 2 / (128 * L)) Δ f hf.2
  · exact centralDifference_stop f hf.1 hd hL hε
  · intro x hx
    exact centralDifference_descent f hf.1 hd hL hε x (lt_of_not_ge hx)
  · exact coordinateBudget_decrease hL hε

/-- One public-parameter value algorithm succeeds on every globally smooth
objective with the gap budget. No analytic or algorithm-existence premise remains. -/
theorem coordinate_value_upper {L Δ ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε) :
    (valueModel d).Ndet {f | SmoothClass L Δ f} ε ≤
      (2 * d * coordinateBudget L Δ ε : ℕ) := by
  let P := coordinateProcedure L ε (coordinateBudget L Δ ε) (0 : X d)
  apply ((valueModel d).Ndet_le_nat_iff _ _ _).mpr
  refine ⟨P.algorithm, ?_, ?_⟩
  · intro f hf
    exact ⟨P.cost f, P.result f, P.runs f,
      coordinateProcedure_stationary f hf hd hL hε⟩
  · apply ((valueModel d).worstCost_le_nat_iff _ _ _).mpr
    intro f hf
    exact ⟨P.cost f, P.result f, P.runs f, coordinateProcedure_cost_le L ε _ 0 f⟩

theorem coordinateBudget_ten {L Δ ε : ℝ}
    (hT : 1 ≤ L * Δ / ε ^ 2) :
    (2 * d * coordinateBudget L Δ ε : ℕ) ≤ 10 * (d : ℝ) * (L * Δ / ε ^ 2) := by
  have hnonneg : 0 ≤ 128 * L * Δ / (35 * ε ^ 2) := by
    have heq : 128 * L * Δ / (35 * ε ^ 2) = (128 / 35 : ℝ) * (L * Δ / ε ^ 2) := by ring
    rw [heq]
    positivity
  have hfloor := Nat.floor_le hnonneg
  have heq : 128 * L * Δ / (35 * ε ^ 2) = (128 / 35 : ℝ) * (L * Δ / ε ^ 2) := by ring
  rw [heq] at hfloor
  have hK : (coordinateBudget L Δ ε : ℝ) ≤ 1 + (128 / 35 : ℝ) * (L * Δ / ε ^ 2) := by
    simp only [coordinateBudget, Nat.cast_add, Nat.cast_one]
    rw [heq]
    linarith
  have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hn),
    mul_le_mul_of_nonneg_left hT hn]

/-- The real bound 10 d T is expressed as its natural floor because complexity
is an extended natural number in the exact rank-cost model. -/
theorem coordinate_value_upper_ten {L Δ ε : ℝ} (hd : 0 < d)
    (hL : 0 < L) (hε : 0 < ε) (hT : 1 ≤ L * Δ / ε ^ 2) :
    (valueModel d).Ndet {f | SmoothClass L Δ f} ε ≤
      (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞) := by
  apply (coordinate_value_upper hd hL hε).trans
  exact_mod_cast Nat.le_floor (coordinateBudget_ten (d := d) hT)

end ExactZO
