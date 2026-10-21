import ExactZO.HistorySpace
import Mathlib.Data.List.Pairwise

/-!
Geometry used in `lem:stage` of `appendices/A_tools.tex` and `wk:lem:stage`.
The selector below is precisely the geometric premise: it does not contain
an algorithm, an oracle reply, or the stage lower bound. Pending constraints
reuse the rank-priced subspace estimate from `ExactZO.HistorySpace` after
replacing query points by their images under `z`.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.StageGeometry

def OrthoList {d : ℕ} (U : List (X d)) : Prop :=
  U.Pairwise (fun u v => ⟪u, v⟫_ℝ = 0) ∧ ∀ u ∈ U, ‖u‖ = 1

def StripSelector {d : ℕ} (R τ : ℝ) (p Q : ℕ) : Prop :=
  ∀ S : Submodule ℝ (X d), p ≤ Module.finrank ℝ S →
    ∀ points : List (X d), points.length ≤ Q →
      (∀ a ∈ points, ‖a‖ ≤ R) →
      ∃ u : X d, ‖u‖ = 1 ∧ u ∈ S ∧ ∀ a ∈ points, |⟪u, a⟫_ℝ| ≤ τ

@[simp] theorem orthoList_nil (d : ℕ) : OrthoList ([] : List (X d)) := by
  simp [OrthoList]

theorem OrthoList.append_unit {d : ℕ} {U : List (X d)} (hU : OrthoList U)
    {u : X d} (hu : ‖u‖ = 1) (ho : ∀ v ∈ U, ⟪u, v⟫_ℝ = 0) :
    OrthoList (U ++ [u]) := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hU.1, by simp, ?_⟩
    intro v hv w hw
    simp only [List.mem_singleton] at hw
    subst w
    simpa only [real_inner_comm] using ho v hv
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hU.2 v hv
    · simpa using (List.mem_singleton.mp hv) ▸ hu

def frameSpace {d : ℕ} : List (X d) → Submodule ℝ (X d)
  | [] => ⊥
  | u :: U => Submodule.span ℝ ({u} : Set (X d)) ⊔ frameSpace U

theorem frameSpace_finrank_le_length {d : ℕ} (U : List (X d)) :
    Module.finrank ℝ (frameSpace U) ≤ U.length := by
  classical
  induction U with
  | nil => simp [frameSpace]
  | cons u U ih =>
      have hp : Module.finrank ℝ (Submodule.span ℝ ({u} : Set (X d))) ≤ 1 := by
        simpa using finrank_span_le_card (R := ℝ) ({u} : Set (X d))
      have hh := (Submodule.finrank_add_le_finrank_add_finrank
        (Submodule.span ℝ ({u} : Set (X d))) (frameSpace U)).trans (Nat.add_le_add hp ih)
      simpa [frameSpace, Nat.add_comm] using hh

theorem mem_frameSpace {d : ℕ} {U : List (X d)} {u : X d} (hu : u ∈ U) :
    u ∈ frameSpace U := by
  induction U with
  | nil => simp at hu
  | cons v U ih =>
      rcases List.mem_cons.mp hu with hv | ht
      · subst u
        exact (show Submodule.span ℝ ({v} : Set (X d)) ≤ frameSpace (v :: U) from
          le_sup_left) (Submodule.subset_span (by simp))
      · exact (show frameSpace U ≤ frameSpace (v :: U) from le_sup_right) (ih ht)

def replaceQueryPoint {d : ℕ} (z : X d → X d) (q : LinearQuery d) : LinearQuery d :=
  ⟨q.width, z q.point, q.directions⟩

def compressedHistory {d : ℕ} (z : X d → X d)
    (hist : (linearModel d).History) : (linearModel d).History :=
  hist.map fun entry => ⟨replaceQueryPoint z entry.1, entry.2⟩

theorem compressedHistory_cost {d : ℕ} (z : X d → X d)
    (hist : (linearModel d).History) :
    (linearModel d).historyCost (compressedHistory z hist) =
      (linearModel d).historyCost hist := by
  simp [compressedHistory, OracleModel.historyCost, List.map_map, linearModel,
    LinearQuery.cost, LinearQuery.rank, replaceQueryPoint, Function.comp_def]

def pendingSpace {d : ℕ} (z : X d → X d)
    (hist : (linearModel d).History) : Submodule ℝ (X d) :=
  historySpace (compressedHistory z hist)

theorem pendingSpace_finrank_le_cost {d : ℕ} (z : X d → X d)
    (hist : (linearModel d).History) :
    Module.finrank ℝ (pendingSpace z hist) ≤ (linearModel d).historyCost hist := by
  simpa [pendingSpace, compressedHistory_cost] using
    historySpace_finrank_le_cost (compressedHistory z hist)

theorem compressedPoint_mem_pendingSpace {d : ℕ} (z : X d → X d)
    {hist : (linearModel d).History} {entry : (linearModel d).Entry} (he : entry ∈ hist) :
    z entry.1.point ∈ pendingSpace z hist := by
  exact queryPoint_mem_historySpace
    (List.mem_map.mpr ⟨entry, he, rfl⟩ :
      ⟨replaceQueryPoint z entry.1, entry.2⟩ ∈ compressedHistory z hist)

theorem direction_mem_pendingSpace {d : ℕ} (z : X d → X d)
    {hist : (linearModel d).History} {entry : (linearModel d).Entry} (he : entry ∈ hist)
    (v : X entry.1.width) : entry.1.directions v ∈ pendingSpace z hist := by
  exact queryDirection_mem_historySpace
    (List.mem_map.mpr ⟨entry, he, rfl⟩ :
      ⟨replaceQueryPoint z entry.1, entry.2⟩ ∈ compressedHistory z hist) v

def historyPoints {d : ℕ} (z : X d → X d) (hist : (linearModel d).History) :
    List (X d) := hist.map fun entry => z entry.1.point

theorem select_on_history {d p Q : ℕ} {R τ : ℝ}
    (selector : StripSelector (d := d) R τ p Q)
    (z : X d → X d) (hz : ∀ x, ‖z x‖ ≤ R)
    (S : Submodule ℝ (X d)) (hS : p ≤ Module.finrank ℝ S)
    (hist : (linearModel d).History) (hQ : hist.length ≤ Q) :
    ∃ u : X d, ‖u‖ = 1 ∧ u ∈ S ∧
      ∀ entry ∈ hist, |⟪u, z entry.1.point⟫_ℝ| ≤ τ := by
  have hlen : (historyPoints z hist).length ≤ Q := by simpa [historyPoints] using hQ
  have hnorm : ∀ a ∈ historyPoints z hist, ‖a‖ ≤ R := by
    intro a ha
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp ha
    exact hz entry.1.point
  obtain ⟨u, hu, hmem, hstrip⟩ := selector S hS (historyPoints z hist) hlen hnorm
  exact ⟨u, hu, hmem, fun entry he => hstrip _ (List.mem_map.mpr ⟨entry, he, rfl⟩)⟩

/-- The current direction map is not included: its reply is formed after selection. -/
def closingSpace {d : ℕ} (z : X d → X d) (U : List (X d))
    (pending : (linearModel d).History) (current : X d) : Submodule ℝ (X d) :=
  (frameSpace U ⊔ pendingSpace z pending) ⊔
    Submodule.span ℝ ({z current} : Set (X d))

theorem closingSpace_finrank_le {d : ℕ} (z : X d → X d) (U : List (X d))
    (pending : (linearModel d).History) (current : X d) :
    Module.finrank ℝ (closingSpace z U pending current) ≤
      U.length + (linearModel d).historyCost pending + 1 := by
  classical
  have hp : Module.finrank ℝ (Submodule.span ℝ ({z current} : Set (X d))) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({z current} : Set (X d))
  have hbase := (Submodule.finrank_add_le_finrank_add_finrank
    (frameSpace U) (pendingSpace z pending)).trans
    (Nat.add_le_add (frameSpace_finrank_le_length U) (pendingSpace_finrank_le_cost z pending))
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add hbase hp)

theorem select_closing_direction {d m h Q : ℕ} {R τ : ℝ}
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q)
    (hmhd : m + h ≤ d) (z : X d → X d) (hz : ∀ x, ‖z x‖ ≤ R)
    (U : List (X d)) (hU : OrthoList U) (hlen : U.length < m)
    (pending closed : (linearModel d).History)
    (hpend : (linearModel d).historyCost pending < h) (hclosed : closed.length ≤ Q)
    (current : X d) :
    ∃ u : X d, ‖u‖ = 1 ∧
      (∀ v ∈ U, ⟪u, v⟫_ℝ = 0) ∧
      (∀ entry ∈ pending, ⟪u, z entry.1.point⟫_ℝ = 0 ∧ entry.1.directions.adjoint u = 0) ∧
      ⟪u, z current⟫_ℝ = 0 ∧
      (∀ entry ∈ closed, |⟪u, z entry.1.point⟫_ℝ| ≤ τ) ∧
      OrthoList (U ++ [u]) := by
  let S := closingSpace z U pending current
  have hdim : d - m - h + 1 ≤ Module.finrank ℝ Sᗮ := by
    have hb := closingSpace_finrank_le z U pending current
    have hd : Module.finrank ℝ S + Module.finrank ℝ Sᗮ = d := by
      simpa [X] using S.finrank_add_finrank_orthogonal
    change Module.finrank ℝ S ≤ _ at hb
    omega
  obtain ⟨u, hu, horth, hstrip⟩ := select_on_history selector z hz Sᗮ hdim closed hclosed
  have hframe : ∀ v ∈ U, ⟪u, v⟫_ℝ = 0 := by
    intro v hv
    apply (Submodule.mem_orthogonal' S u).mp horth
    exact (show frameSpace U ≤ S from le_sup_left.trans le_sup_left) (mem_frameSpace hv)
  have hpending : ∀ entry ∈ pending,
      ⟪u, z entry.1.point⟫_ℝ = 0 ∧ entry.1.directions.adjoint u = 0 := by
    intro entry he
    have hdir : ∀ v : X entry.1.width, ⟪u, entry.1.directions v⟫_ℝ = 0 := by
      intro v
      apply (Submodule.mem_orthogonal' S u).mp horth
      exact (show pendingSpace z pending ≤ S from le_sup_right.trans le_sup_left)
        (direction_mem_pendingSpace z he v)
    constructor
    · apply (Submodule.mem_orthogonal' S u).mp horth
      exact (show pendingSpace z pending ≤ S from le_sup_right.trans le_sup_left)
        (compressedPoint_mem_pendingSpace z he)
    · apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      rw [entry.1.directions.adjoint_inner_left]
      exact hdir _
  have hcurrent : ⟪u, z current⟫_ℝ = 0 := by
    apply (Submodule.mem_orthogonal' S u).mp horth
    exact (show Submodule.span ℝ ({z current} : Set (X d)) ≤ S from le_sup_right)
      (Submodule.subset_span (by simp))
  exact ⟨u, hu, hframe, hpending, hcurrent, hstrip, hU.append_unit hu hframe⟩

/-- Complete a partial frame; every added direction obeys the strips on all
past points. Existing frame vectors are preserved in their original order. -/
theorem complete_frame {d m h Q : ℕ} {R τ : ℝ}
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q)
    (hmhd : m + h ≤ d) (z : X d → X d) (hz : ∀ x, ‖z x‖ ≤ R)
    (U : List (X d)) (hU : OrthoList U) (hlen : U.length ≤ m)
    (hist : (linearModel d).History) (hQ : hist.length ≤ Q) :
    ∃ tail : List (X d), (U ++ tail).length = m ∧ OrthoList (U ++ tail) ∧
      ∀ u ∈ tail, ∀ entry ∈ hist, |⟪u, z entry.1.point⟫_ℝ| ≤ τ := by
  have aux : ∀ n : ℕ, ∀ V : List (X d), OrthoList V → V.length + n = m →
      ∃ tail : List (X d), (V ++ tail).length = m ∧ OrthoList (V ++ tail) ∧
        ∀ u ∈ tail, ∀ entry ∈ hist, |⟪u, z entry.1.point⟫_ℝ| ≤ τ := by
    intro n
    induction n with
    | zero =>
        intro V hV hvlen
        refine ⟨[], ?_, ?_, ?_⟩
        · simpa using hvlen
        · simpa using hV
        · simp
    | succ n ih =>
        intro V hV hvlen
        have hvlt : V.length < m := by omega
        have hdim : d - m - h + 1 ≤ Module.finrank ℝ (frameSpace V)ᗮ := by
          have hb := frameSpace_finrank_le_length V
          have hd : Module.finrank ℝ (frameSpace V) +
              Module.finrank ℝ (frameSpace V)ᗮ = d := by
            simpa [X] using (frameSpace V).finrank_add_finrank_orthogonal
          omega
        obtain ⟨u, hu, horth, hstrip⟩ :=
          select_on_history selector z hz (frameSpace V)ᗮ hdim hist hQ
        have hperp : ∀ v ∈ V, ⟪u, v⟫_ℝ = 0 := by
          intro v hv
          exact (Submodule.mem_orthogonal' _ _).mp horth v (mem_frameSpace hv)
        have hnext : (V ++ [u]).length + n = m := by
          simp only [List.length_append, List.length_singleton]
          omega
        obtain ⟨tail, hlength, hfull, htail⟩ := ih (V ++ [u]) (hV.append_unit hu hperp) hnext
        refine ⟨u :: tail, ?_, ?_, ?_⟩
        · simpa only [List.append_assoc, List.singleton_append] using hlength
        · simpa only [List.append_assoc, List.singleton_append] using hfull
        · intro v hv entry he
          rcases List.mem_cons.mp hv with hv | hv
          · subst v
            exact hstrip entry he
          · exact htail v hv entry he
  exact aux (m - U.length) U hU (by omega)

end ExactZO.StageGeometry
