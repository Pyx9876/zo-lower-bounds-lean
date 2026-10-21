import ExactZO.Oracle

/-!
Finite adaptive transcripts may use arbitrary replies until a single fixed
objective is chosen. This extends the real-run replay argument in
`DimensionFloor.exists_replay_history` to adversarially generated prefixes.
The cost cap is public and also bounds the number of calls because every
oracle query has positive integer cost.
-/

noncomputable section

namespace ExactZO
namespace OracleModel

variable {d : ℕ} (M : OracleModel d)

@[simp] theorem historyCost_nil : M.historyCost [] = 0 := rfl

@[simp] theorem historyCost_append (h k : M.History) :
    M.historyCost (h ++ k) = M.historyCost h + M.historyCost k := by
  simp [historyCost, List.map_append, List.sum_append]

@[simp] theorem historyCost_singleton (q : M.Query) (r : M.Reply q) :
    M.historyCost [⟨q, r⟩] = M.cost q := by simp [historyCost]

/-- The queries follow one fixed algorithm, while replies may be arbitrary.
The output is not a history entry and is never charged as a query. -/
inductive Reachable (A : M.Algorithm) : M.History → Prop where
  | nil : Reachable A []
  | query {h : M.History} {q : M.Query}
      (reachable : Reachable A h) (action : A h = .query q) (reply : M.Reply q) :
      Reachable A (h ++ [⟨q, reply⟩])

/-- An arbitrary-reply prefix agreeing with one fixed objective can be placed
before any real continuation on that same objective. -/
theorem Reachable.prepend_run {A : M.Algorithm} {f : Objective d}
    {h : M.History} (hh : M.Reachable A h) (hc : M.ReplyConsistent f h)
    {n : ℕ} {x : X d} (ht : M.RunFrom A f h n x) :
    M.Runs A f (M.historyCost h + n) x := by
  induction hh generalizing n with
  | nil => simpa [Runs] using ht
  | @query h q hh ha reply ih =>
      have hc' : M.ReplyConsistent f h := by
        intro entry he
        exact hc entry (List.mem_append_left _ he)
      have hr : reply = M.answer f q := hc ⟨q, reply⟩ (by simp)
      have hnext : M.RunFrom A f (h ++ [⟨q, M.answer f q⟩]) n x := by
        simpa only [hr] using ht
      have hp : M.RunFrom A f h (M.cost q + n) x := RunFrom.query ha hnext
      simpa [Nat.add_assoc] using ih hc' hp

/-- The complete arbitrary transcript becomes an actual run, with exactly its
sum of rank-based costs, once all replies agree with one fixed objective. -/
theorem Reachable.runs {A : M.Algorithm} {f : Objective d} {h : M.History}
    (hh : M.Reachable A h) (hc : M.ReplyConsistent f h) {x : X d}
    (ho : A h = .output x) : M.Runs A f (M.historyCost h) x := by
  simpa using Reachable.prepend_run M hh hc (RunFrom.output ho)

/-- Caps apply even to histories with adversarial replies, not merely to runs
on members of a legal function class. `B` is a strict cost bound; `Q` is the
maximum number of queries. -/
structure UniversalCap (A : M.Algorithm) (Q B : ℕ) : Prop where
  prefix_cost : ∀ h, M.Reachable A h → M.historyCost h < B
  query_bounds : ∀ h q, M.Reachable A h → A h = .query q →
    M.historyCost h + M.cost q < B ∧ h.length < Q

theorem UniversalCap.mono {A : M.Algorithm} {Q B Q' B' : ℕ}
    (hcap : M.UniversalCap A Q B) (hQ : Q ≤ Q') (hB : B ≤ B') :
    M.UniversalCap A Q' B' := by
  refine ⟨fun h hh => (hcap.prefix_cost h hh).trans_le hB, ?_⟩
  intro h q hh ha
  obtain ⟨hc, hl⟩ := hcap.query_bounds h q hh ha
  exact ⟨hc.trans_le hB, hl.trans_le hQ⟩

/-- Reject a query before asking it when it would exceed the public cost cap.
Rejection returns the fixed point zero and makes no additional oracle call. -/
def capAlgorithm (A : M.Algorithm) (N : ℕ) : M.Algorithm := fun h =>
  match A h with
  | .output x => .output x
  | .query q => if M.historyCost h + M.cost q ≤ N then .query q else .output 0

theorem capAlgorithm_query_iff (A : M.Algorithm) (N : ℕ) (h : M.History) (q : M.Query) :
    M.capAlgorithm A N h = .query q ↔
      A h = .query q ∧ M.historyCost h + M.cost q ≤ N := by
  cases ha : A h with
  | output x => simp [capAlgorithm, ha]
  | query q' =>
      by_cases hb : M.historyCost h + M.cost q' ≤ N
      · simp [capAlgorithm, ha, hb]
        rintro rfl
        exact hb
      · simp [capAlgorithm, ha, hb]
        intro heq
        subst q'
        exact Nat.lt_of_not_ge hb

@[simp] theorem capAlgorithm_output_of_output {A : M.Algorithm} {N : ℕ}
    {h : M.History} {x : X d} (ha : A h = .output x) :
    M.capAlgorithm A N h = .output x := by simp [capAlgorithm, ha]

theorem capAlgorithm_reachable_cost_le (A : M.Algorithm) (N : ℕ)
    {h : M.History} (hh : M.Reachable (M.capAlgorithm A N) h) : M.historyCost h ≤ N := by
  induction hh with
  | nil => simp
  | @query h q hh ha r ih =>
      simpa using ((capAlgorithm_query_iff M A N h q).mp ha).2

theorem capAlgorithm_universalCap (A : M.Algorithm) (N : ℕ) :
    M.UniversalCap (M.capAlgorithm A N) N (N + 1) := by
  refine ⟨fun h hh => Nat.lt_succ_of_le (capAlgorithm_reachable_cost_le M A N hh), ?_⟩
  intro h q hh ha
  have hb := ((capAlgorithm_query_iff M A N h q).mp ha).2
  refine ⟨Nat.lt_succ_of_le hb, ?_⟩
  have hlen := M.history_length_le_cost h
  have hpos := M.cost_pos q
  omega

/-- Real runs whose existing-prefix plus remaining cost fits in the cap are
preserved. Carrying the prefix cost is essential for the induction step. -/
theorem RunFrom.cap_of_budget {A : M.Algorithm} {f : Objective d}
    {h : M.History} {n N : ℕ} {x : X d} (hr : M.RunFrom A f h n x)
    (hb : M.historyCost h + n ≤ N) : M.RunFrom (M.capAlgorithm A N) f h n x := by
  induction hr with
  | output ha => exact RunFrom.output (capAlgorithm_output_of_output M ha)
  | @query h q n x ha ht ih =>
      have hguard : M.historyCost h + M.cost q ≤ N := by omega
      have htailBudget : M.historyCost (h ++ [⟨q, M.answer f q⟩]) + n ≤ N := by
        simpa [Nat.add_assoc] using hb
      exact RunFrom.query ((capAlgorithm_query_iff M A N h q).mpr ⟨ha, hguard⟩)
        (ih htailBudget)

theorem Runs.cap_of_budget {A : M.Algorithm} {f : Objective d} {n N : ℕ} {x : X d}
    (hr : M.Runs A f n x) (hb : n ≤ N) : M.Runs (M.capAlgorithm A N) f n x :=
  RunFrom.cap_of_budget M hr (by simpa using hb)

/-- Budget truncation preserves success on an entire legal class when the
original algorithm has the stated worst-case budget on that class. -/
theorem Succeeds.cap_of_worstCost {A : M.Algorithm} {C : Set (Objective d)}
    {ε : ℝ} {N : ℕ} (hA : M.Succeeds A C ε)
    (hN : M.worstCost A C ≤ (N : ℕ∞)) : M.Succeeds (M.capAlgorithm A N) C ε := by
  intro f hf
  obtain ⟨n, x, hn, hx⟩ := hA f hf
  have hncost : (n : ℕ∞) ≤ M.worstCost A C := by
    rw [← M.runCost_eq_of_runs hn]
    exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
  have hb : n ≤ N := ENat.coe_le_coe.mp (hncost.trans hN)
  exact ⟨n, x, Runs.cap_of_budget M hn hb, hx⟩

end OracleModel
end ExactZO
