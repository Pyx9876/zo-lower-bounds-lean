import ExactZO.SubspaceCost
import ExactZO.SubspaceTermination
import ExactZO.SubspaceOptimize
import ExactZO.CoordinateAlgorithm

/-! Actual deterministic complexity bounds for the restarted subspace procedure.
All fuel and capacity parameters are public. The hidden objective and its
curvature matrix occur only in the correctness and cost proofs. -/
noncomputable section

namespace ExactZO.SubspaceUpper
open StageGeometry SubspaceInvariant SubspaceProcedure SubspaceTermination SubspaceOptimize

theorem publicProcedure_cost {d r : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hT : 1 ≤ L*Δ/ε^2)
    (f : Objective d) (hf : SublevelClass L Δ E f) :
    ((publicProcedure (d := d) L Δ E ε r).cost f : ℝ) <
      40*(d:ℝ)*E*(L*Δ/ε^2)/r+30*((d:ℝ)+L*Δ/ε^2)*r := by
  obtain ⟨hsmooth,H,hH,hmodel⟩ := hf
  let out := run f L ε r (LineSearch.publicFuel L Δ ε) (totalFuel L Δ E ε r) 0 []
  obtain ⟨q,hb,hn⟩ := run_preserves_budget hL hE hε hsmooth hH hmodel
    (initial f H L E ε (by omega : 0 < r)) (fuel := totalFuel L Δ E ε r)
  change StateBudget f H L E ε r out.point out.frame (0+out.restrictedCount) q at hb
  have hc := hb.counts_real hL hE hε hH hsmooth.2
  change q*r+out.frame.length=0*r+([] : List (X d)).length+out.expansionCount at hn
  simp only [zero_mul,List.length_nil,zero_add] at hn
  have hj : (out.restrictedCount:ℝ) ≤ 512*(L*Δ/ε^2)/35 := by
    simpa only [zero_add,timeParameter] using hc.1
  have he : (out.expansionCount:ℝ) ≤ 10*E*(L*Δ/ε^2)/r+(r:ℝ)/4 := by
    simpa only [hn,timeParameter] using hc.2
  have hl := (SubspaceCost.run_ledger hL hε hr hrd hsmooth hH hmodel
    (totalFuel L Δ E ε r) 0 [] (orthoList_nil d) (by simpa using hr) le_rfl).2
  change (out.cost:ℝ) ≤ _ at hl
  obtain ⟨lower,hlo,hgap⟩ := hsmooth.2
  have hgap' : f.value 0-f.value out.point ≤ Δ := by linarith [hlo out.point]
  have hm := mul_le_mul_of_nonneg_left hgap' (by positivity : 0 ≤ 8*L/ε^2)
  have hledger : (out.cost:ℝ) ≤
      2*((d:ℝ)+(r:ℝ)-1)*(out.expansionCount+1)+
      2*((r:ℝ)-1)*out.restrictedCount+8*(L*Δ/ε^2)+2*out.expansionCount := by
    have hid : (8*L/ε^2)*Δ=8*(L*Δ/ε^2) := by ring
    rw [hid] at hm
    linarith
  have bound := SubspaceBudget.capacity_ledger_bound
    (show (1:ℝ) ≤ d by exact_mod_cast hr.trans hrd)
    (show (1:ℝ) ≤ r by exact_mod_cast hr)
    (show (r:ℝ) ≤ d by exact_mod_cast hrd) hT
    (Nat.cast_nonneg out.expansionCount) hj he hledger
  simpa only [publicProcedure,procedure,loop_cost] using bound

/-- The fixed-capacity bound is for one algorithm uniformly over the whole class. -/
theorem capacity_value_upper {d r : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hT : 1 ≤ L*Δ/ε^2) :
    (valueModel d).Ndet {f | SublevelClass L Δ E f} ε ≤
      (⌊40*(d:ℝ)*E*(L*Δ/ε^2)/r+30*((d:ℝ)+L*Δ/ε^2)*r⌋₊ : ℕ∞) := by
  let P : ValueProcedure d := publicProcedure L Δ E ε r
  apply ((valueModel d).Ndet_le_nat_iff _ _ _).mpr
  refine ⟨P.algorithm,publicProcedure_succeeds hL hE hε (by omega),?_⟩
  apply ((valueModel d).worstCost_le_nat_iff _ _ _).mpr
  intro f hf
  exact ⟨P.cost f,P.result f,P.runs f,
    Nat.le_floor (publicProcedure_cost hL hE hε hr hrd hT f hf).le⟩

theorem subspace_value_upper {d : ℕ} {L Δ E ε : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hε : 0 < ε) (hT : 1 ≤ L*Δ/ε^2) :
    (valueModel d).Ndet {f | SublevelClass L Δ E f} ε ≤
      (⌊100*scale d E (L*Δ/ε^2)⌋₊ : ℕ∞) := by
  obtain ⟨hr,hrd,_,_⟩ := capacity_bounds hd hE hEd hT
  have h := capacity_value_upper hL (by linarith : 0 < E) hε hr hrd hT
  apply h.trans
  exact_mod_cast Nat.floor_mono (optimized_cost hd hE hEd hT)

/-- The minimum uses two actual public algorithms; each endpoint is a proved bound. -/
theorem deterministic_value_upper {d : ℕ} {L Δ E ε : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hε : 0 < ε) (hT : 1 ≤ L*Δ/ε^2) :
    (valueModel d).Ndet {f | SublevelClass L Δ E f} ε ≤
      min (⌊10*(d:ℝ)*(L*Δ/ε^2)⌋₊ : ℕ∞)
        (⌊100*scale d E (L*Δ/ε^2)⌋₊ : ℕ∞) := by
  apply le_min
  · exact ((valueModel d).Ndet_mono_class
      (fun _ hf => sublevelClass_subset_smoothClass hf) ε).trans
      (coordinate_value_upper_ten (by omega) hL hε hT)
  · exact subspace_value_upper hd hL hE hEd hε hT

theorem deterministic_linear_upper {d : ℕ} {L Δ E ε : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hε : 0 < ε) (hT : 1 ≤ L*Δ/ε^2) :
    (linearModel d).Ndet {f | SublevelClass L Δ E f} ε ≤
      min (⌊10*(d:ℝ)*(L*Δ/ε^2)⌋₊ : ℕ∞)
        (⌊100*scale d E (L*Δ/ε^2)⌋₊ : ℕ∞) :=
  (Ndet_linear_le_value _ ε).trans (deterministic_value_upper hd hL hE hEd hε hT)

theorem subspace_value_upper_small_time {d : ℕ} {L Δ E ε : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hε : 0 < ε) (hT : 1 ≤ L*Δ/ε^2) (hTd : L*Δ/ε^2 ≤ d) :
    (valueModel d).Ndet {f | SublevelClass L Δ E f} ε ≤
      (⌊100*Real.sqrt 2*d*Real.sqrt (E*(L*Δ/ε^2))⌋₊ : ℕ∞) := by
  apply (subspace_value_upper hd hL hE hEd hε hT).trans
  have h := scale_le_dimension_sqrt hd hE hT hTd
  exact_mod_cast Nat.floor_mono (show 100*scale d E (L*Δ/ε^2) ≤
    100*Real.sqrt 2*d*Real.sqrt (E*(L*Δ/ε^2)) by nlinarith)

end ExactZO.SubspaceUpper
