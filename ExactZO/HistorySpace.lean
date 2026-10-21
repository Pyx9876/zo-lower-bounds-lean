import ExactZO.Oracle
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
The subspace exposed by a finite rank-priced history. This module uses only
the query points and direction ranges, never the replies or the free output.

The proof of `HistoryGeometry.exists_unit_orthogonal` is minimally reused from
the local research library, `Minimax/CensoredLocalizationCenters.lean:78-87`,
declaration `Minimax.CensoredLocalization.exists_unit_orthogonal`.
Source revision: fb437004894bafcd0d2c7fe3d4249d2ed1f97ae9.
Source file SHA-256: 4067459aed2df8f9119060a69210b021685ea806031ee7259dc78de1e692dea3.
Its full assumptions are retained; the proof is compiled here against the
project's pinned mathlib, without any machine-specific library dependency.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO

/-- One call exposes its point and the range of its direction map. -/
def querySpace {d : ℕ} (q : LinearQuery d) : Submodule ℝ (X d) :=
  Submodule.span ℝ ({q.point} : Set (X d)) ⊔ LinearMap.range q.directions.toLinearMap

/-- The output is deliberately absent from the space charged to the history. -/
def historySpace {d : ℕ} : (linearModel d).History → Submodule ℝ (X d)
  | [] => ⊥
  | entry :: h => querySpace entry.1 ⊔ historySpace h

theorem querySpace_finrank_le_cost {d : ℕ} (q : LinearQuery d) :
    Module.finrank ℝ (querySpace q) ≤ q.cost := by
  classical
  have hp : Module.finrank ℝ (Submodule.span ℝ ({q.point} : Set (X d))) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({q.point} : Set (X d))
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add_right hp q.rank)

theorem historySpace_finrank_le_cost {d : ℕ} (h : (linearModel d).History) :
    Module.finrank ℝ (historySpace h) ≤ (linearModel d).historyCost h := by
  induction h with
  | nil => simp [historySpace, OracleModel.historyCost]
  | cons entry h ih =>
      calc
        Module.finrank ℝ (historySpace (entry :: h)) ≤
            Module.finrank ℝ (querySpace entry.1) + Module.finrank ℝ (historySpace h) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ entry.1.cost + (linearModel d).historyCost h :=
          Nat.add_le_add (querySpace_finrank_le_cost entry.1) ih
        _ = (linearModel d).historyCost (entry :: h) := by
          simp [OracleModel.historyCost, linearModel]

theorem querySpace_le_historySpace_of_mem {d : ℕ} {h : (linearModel d).History}
    {entry : (linearModel d).Entry} (he : entry ∈ h) :
    querySpace entry.1 ≤ historySpace h := by
  induction h with
  | nil => simp at he
  | cons first h ih =>
      rcases List.mem_cons.mp he with hfirst | htail
      · subst entry
        exact le_sup_left
      · exact (ih htail).trans le_sup_right

theorem queryPoint_mem_historySpace {d : ℕ} {h : (linearModel d).History}
    {entry : (linearModel d).Entry} (he : entry ∈ h) :
    entry.1.point ∈ historySpace h := by
  apply querySpace_le_historySpace_of_mem he
  apply (show Submodule.span ℝ ({entry.1.point} : Set (X d)) ≤ querySpace entry.1 from
    le_sup_left)
  exact Submodule.subset_span (by simp)

theorem queryRange_le_historySpace {d : ℕ} {h : (linearModel d).History}
    {entry : (linearModel d).Entry} (he : entry ∈ h) :
    LinearMap.range entry.1.directions.toLinearMap ≤ historySpace h :=
  (show LinearMap.range entry.1.directions.toLinearMap ≤ querySpace entry.1 from
    le_sup_right).trans (querySpace_le_historySpace_of_mem he)

theorem queryDirection_mem_historySpace {d : ℕ} {h : (linearModel d).History}
    {entry : (linearModel d).Entry} (he : entry ∈ h) (v : X entry.1.width) :
    entry.1.directions v ∈ historySpace h :=
  queryRange_le_historySpace he ⟨v, rfl⟩

namespace HistoryGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance historyGeometryNormedSpace : NormedSpace ℝ E :=
  InnerProductSpace.toNormedSpace

/-- Portable minimal source reuse; provenance is recorded in the module header. -/
theorem exists_unit_orthogonal (S : Submodule ℝ E)
    (hdim : Module.finrank ℝ S < Module.finrank ℝ E) :
    ∃ u : E, ‖u‖ = 1 ∧ u ∈ Sᗮ := by
  have hpos : 0 < Module.finrank ℝ Sᗮ := by
    have := S.finrank_add_finrank_orthogonal
    omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  refine ⟨‖x‖⁻¹ • (x : E), ?_, Submodule.smul_mem _ _ x.property⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, Submodule.norm_coe, inv_mul_cancel₀ hn]

end HistoryGeometry

/-- A free output requires only choosing the sign of a hidden unit direction. -/
theorem exists_unit_orthogonal_history_of_cost_lt {d : ℕ}
    {h : (linearModel d).History} (hc : (linearModel d).historyCost h < d)
    (z : X d) :
    ∃ u : X d, ‖u‖ = 1 ∧
      (∀ entry ∈ h, ⟪u, entry.1.point⟫_ℝ = 0 ∧
        ∀ v : X entry.1.width, ⟪u, entry.1.directions v⟫_ℝ = 0) ∧
      ⟪u, z⟫_ℝ ≤ 0 := by
  have hdim : Module.finrank ℝ (historySpace h) < Module.finrank ℝ (X d) := by
    simpa [X] using (historySpace_finrank_le_cost h).trans_lt hc
  obtain ⟨u, hu, horth⟩ := HistoryGeometry.exists_unit_orthogonal (historySpace h) hdim
  have hall : ∀ entry ∈ h, ⟪u, entry.1.point⟫_ℝ = 0 ∧
      ∀ v : X entry.1.width, ⟪u, entry.1.directions v⟫_ℝ = 0 := by
    intro entry he
    refine ⟨(Submodule.mem_orthogonal' _ _).mp horth _ (queryPoint_mem_historySpace he), ?_⟩
    intro v
    exact (Submodule.mem_orthogonal' _ _).mp horth _ (queryDirection_mem_historySpace he v)
  by_cases hz : ⟪u, z⟫_ℝ ≤ 0
  · exact ⟨u, hu, hall, hz⟩
  · refine ⟨-u, by simpa using hu, ?_, ?_⟩
    · intro entry he
      obtain ⟨hp, hv⟩ := hall entry he
      constructor
      · simp only [inner_neg_left, hp, neg_zero]
      · intro v
        simp only [inner_neg_left, hv v, neg_zero]
    · rw [inner_neg_left]
      linarith

end ExactZO
