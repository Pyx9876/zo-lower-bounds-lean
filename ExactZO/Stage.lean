import ExactZO.StageGeometry
import ExactZO.TranscriptCap

/-!
The stage argument with explicit geometric selection and prefix-family
assumptions. The adaptive transcript, closing-call replies, and final fixed
function are constructed rather than assumed as a realizability certificate.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO
namespace Stage

open StageGeometry

abbrev History (d : ℕ) := (linearModel d).History

/-- The analytic family assumptions in Appendix A, `lem:stage`. -/
structure Family (d m : ℕ) (R τ b : ℝ) where
  objective : List (X d) → Objective d
  z : X d → X d
  prefixObjective : List (X d) → Objective d
  coefficient : List (X d) → X d → ℝ
  z_bound : ∀ x, ‖z x‖ ≤ R
  prefix_formula : ∀ pre u tail x, OrthoList (pre ++ u :: tail) →
    (pre ++ u :: tail).length = m → ⟪u, z x⟫_ℝ = 0 →
    (∀ v ∈ tail, |⟪v, z x⟫_ℝ| ≤ τ) →
    (objective (pre ++ u :: tail)).value x = (prefixObjective pre).value x ∧
    (objective (pre ++ u :: tail)).grad x =
      (prefixObjective pre).grad x - coefficient pre x • u
  barrier : ∀ U x, OrthoList U → U.length = m →
    (∃ u ∈ U, ⟪u, z x⟫_ℝ = 0) → b < ‖(objective U).grad x‖

variable {d m : ℕ} {R τ b : ℝ}

def Small (fam : Family d m R τ b) (U : List (X d)) (hist : History d) : Prop :=
  ∀ u ∈ U, ∀ entry ∈ hist, |⟪u, fam.z entry.1.point⟫_ℝ| ≤ τ

theorem Small.mono_history {fam : Family d m R τ b} {U : List (X d)}
    {hist hist' : History d} (hs : Small fam U hist)
    (hsub : ∀ e ∈ hist', e ∈ hist) : Small fam U hist' := by
  intro u hu e he
  exact hs u hu e (hsub e he)

theorem Small.cons {fam : Family d m R τ b} {U : List (X d)} {u : X d}
    {hist : History d} (hu : ∀ e ∈ hist, |⟪u, fam.z e.1.point⟫_ℝ| ≤ τ)
    (hs : Small fam U hist) : Small fam (u :: U) hist := by
  intro v hv e he
  rcases List.mem_cons.mp hv with hv | hv
  · subst v
    exact hu e he
  · exact hs v hv e he

def closingReply (fam : Family d m R τ b) (pre : List (X d))
    (u : X d) (q : LinearQuery d) : LinearReply q :=
  ((fam.prefixObjective pre).value q.point,
    q.directions.adjoint ((fam.prefixObjective pre).grad q.point - fam.coefficient pre q.point • u))

theorem trueReply_closing (fam : Family d m R τ b) (pre tail : List (X d))
    (u : X d) (q : LinearQuery d) (ho : OrthoList (pre ++ u :: tail))
    (hl : (pre ++ u :: tail).length = m) (hz : ⟪u, fam.z q.point⟫_ℝ = 0)
    (hs : ∀ v ∈ tail, |⟪v, fam.z q.point⟫_ℝ| ≤ τ) :
    linearReply (fam.objective (pre ++ u :: tail)) q = closingReply fam pre u q := by
  obtain ⟨hv, hg⟩ := fam.prefix_formula pre u tail q.point ho hl hz hs
  simp only [linearReply, closingReply, hv, hg]

theorem trueReply_pending (fam : Family d m R τ b) (pre tail : List (X d))
    (u : X d) (q : LinearQuery d) (ho : OrthoList (pre ++ u :: tail))
    (hl : (pre ++ u :: tail).length = m) (hz : ⟪u, fam.z q.point⟫_ℝ = 0)
    (hs : ∀ v ∈ tail, |⟪v, fam.z q.point⟫_ℝ| ≤ τ)
    (hV : q.directions.adjoint u = 0) :
    linearReply (fam.objective (pre ++ u :: tail)) q = linearReply (fam.prefixObjective pre) q := by
  rw [trueReply_closing fam pre tail u q ho hl hz hs]
  simp only [closingReply, linearReply, map_sub, map_smul, hV, smul_zero, sub_zero]

/-- Closed replies are valid for every later strip-small completion. Pending
replies are the current prefix, and each completed stage has paid at least `h`. -/
structure Invariant (fam : Family d m R τ b) (h : ℕ) (hist : History d) where
  frame : List (X d)
  closed : History d
  pending : History d
  ortho : OrthoList frame
  split : hist = closed ++ pending
  load : (linearModel d).historyCost pending < h
  paid : h * frame.length + (linearModel d).historyCost pending ≤
    (linearModel d).historyCost hist
  closed_correct : ∀ tail, OrthoList (frame ++ tail) → (frame ++ tail).length = m →
    Small fam tail closed → (linearModel d).ReplyConsistent (fam.objective (frame ++ tail)) closed
  pending_correct : ∀ entry ∈ pending, entry.2 = linearReply (fam.prefixObjective frame) entry.1

theorem initial (fam : Family d m R τ b) {h : ℕ} (hh : 0 < h) :
    Nonempty (Invariant fam h []) := by
  refine ⟨⟨[], [], [], ?_, rfl, hh, by simp, ?_, ?_⟩⟩
  · simp [OrthoList]
  · intro tail ho hl hs e he
    simp at he
  · intro e he
    simp at he

theorem Invariant.frame_length_lt {fam : Family d m R τ b} {h : ℕ} {hist : History d}
    (s : Invariant fam h hist) (hb : (linearModel d).historyCost hist < h * m) :
    s.frame.length < m := by
  by_contra hn
  have hm : m ≤ s.frame.length := Nat.le_of_not_gt hn
  have hm' := Nat.mul_le_mul_left h hm
  have hp := s.paid
  omega

theorem Invariant.closed_length_le {fam : Family d m R τ b} {h : ℕ}
    {hist : History d} (s : Invariant fam h hist) : s.closed.length ≤ hist.length := by
  have heq := congrArg List.length s.split
  simp only [List.length_append] at heq
  omega

def Invariant.append_pending {fam : Family d m R τ b} {h : ℕ} {hist : History d}
    (s : Invariant fam h hist) (q : LinearQuery d)
    (hq : (linearModel d).historyCost s.pending + q.cost < h) :
    Invariant fam h (hist ++ [⟨q, linearReply (fam.prefixObjective s.frame) q⟩]) where
  frame := s.frame
  closed := s.closed
  pending := s.pending ++ [⟨q, linearReply (fam.prefixObjective s.frame) q⟩]
  ortho := s.ortho
  split := by simp only [s.split, List.append_assoc]
  load := by simpa only [OracleModel.historyCost_append, OracleModel.historyCost_singleton] using hq
  paid := by
    simpa only [OracleModel.historyCost_append, OracleModel.historyCost_singleton, Nat.add_assoc]
      using Nat.add_le_add_right s.paid q.cost
  closed_correct := s.closed_correct
  pending_correct := by
    intro entry he
    rcases List.mem_append.mp he with he | he
    · exact s.pending_correct entry he
    · have he' : entry = ⟨q, linearReply (fam.prefixObjective s.frame) q⟩ := by simpa using he
      subst entry
      rfl

theorem Invariant.consistent_completion {fam : Family d m R τ b} {h : ℕ}
    {hist : History d} (s : Invariant fam h hist) (u : X d) (tail : List (X d))
    (ho : OrthoList (s.frame ++ u :: tail)) (hl : (s.frame ++ u :: tail).length = m)
    (hu : ∀ e ∈ s.closed, |⟪u, fam.z e.1.point⟫_ℝ| ≤ τ)
    (ht : Small fam tail hist)
    (hp : ∀ e ∈ s.pending, ⟪u, fam.z e.1.point⟫_ℝ = 0 ∧ e.1.directions.adjoint u = 0) :
    (linearModel d).ReplyConsistent (fam.objective (s.frame ++ u :: tail)) hist := by
  have hcsub : ∀ e ∈ s.closed, e ∈ hist := by
    intro e he
    rw [s.split]
    exact List.mem_append_left _ he
  have hpsub : ∀ e ∈ s.pending, e ∈ hist := by
    intro e he
    rw [s.split]
    exact List.mem_append_right _ he
  have hclosed := s.closed_correct (u :: tail) ho hl
    (Small.cons hu (ht.mono_history hcsub))
  intro e he
  rw [s.split] at he
  rcases List.mem_append.mp he with he | he
  · exact hclosed e he
  · calc
      e.2 = linearReply (fam.prefixObjective s.frame) e.1 := s.pending_correct e he
      _ = linearReply (fam.objective (s.frame ++ u :: tail)) e.1 :=
        (trueReply_pending fam s.frame tail u e.1 ho hl (hp e he).1
          (fun v hv => ht v hv e (hpsub e he)) (hp e he).2).symm

def Invariant.close {fam : Family d m R τ b} {h : ℕ} {hist : History d}
    (s : Invariant fam h hist) (hh : 0 < h) (q : LinearQuery d) (u : X d)
    (hclose : h ≤ (linearModel d).historyCost s.pending + q.cost)
    (hframe : OrthoList (s.frame ++ [u]))
    (hp : ∀ e ∈ s.pending, ⟪u, fam.z e.1.point⟫_ℝ = 0 ∧ e.1.directions.adjoint u = 0)
    (hx : ⟪u, fam.z q.point⟫_ℝ = 0)
    (hu : ∀ e ∈ s.closed, |⟪u, fam.z e.1.point⟫_ℝ| ≤ τ) :
    Invariant fam h (hist ++ [⟨q, closingReply fam s.frame u q⟩]) where
  frame := s.frame ++ [u]
  closed := hist ++ [⟨q, closingReply fam s.frame u q⟩]
  pending := []
  ortho := hframe
  split := by simp
  load := hh
  paid := by
    simp only [OracleModel.historyCost_nil, Nat.add_zero, OracleModel.historyCost_append,
      OracleModel.historyCost_singleton, List.length_append, List.length_singleton]
    have hpaid := s.paid
    change h * (s.frame.length + 1) ≤ (linearModel d).historyCost hist + q.cost
    nlinarith
  closed_correct := by
    intro tail ho hl hs
    have ho' : OrthoList (s.frame ++ u :: tail) := by
      simpa only [List.append_assoc, List.singleton_append] using ho
    have hl' : (s.frame ++ u :: tail).length = m := by
      simpa only [List.append_assoc, List.singleton_append] using hl
    have hc := s.consistent_completion u tail ho' hl' hu
      (hs.mono_history (fun e he => List.mem_append_left _ he)) hp
    have hcq : linearReply (fam.objective (s.frame ++ u :: tail)) q =
        closingReply fam s.frame u q :=
      trueReply_closing fam s.frame tail u q ho' hl' hx
        (fun v hv => hs v hv ⟨q, closingReply fam s.frame u q⟩ (by simp))
    intro e he
    change e.2 = linearReply (fam.objective ((s.frame ++ [u]) ++ tail)) e.1
    simp only [List.append_assoc, List.singleton_append]
    rcases List.mem_append.mp he with he | he
    · exact hc e he
    · have he' : e = ⟨q, closingReply fam s.frame u q⟩ := by simpa using he
      subst e
      exact hcq.symm
  pending_correct := by simp

theorem Invariant.advance {fam : Family d m R τ b} {h Q : ℕ} {hist : History d}
    (s : Invariant fam h hist) (hh : 0 < h)
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q) (hmhd : m + h ≤ d)
    (q : LinearQuery d) (hbudget : (linearModel d).historyCost hist + q.cost < h * m)
    (hQ : hist.length ≤ Q) :
    ∃ reply : LinearReply q, Nonempty (Invariant fam h (hist ++ [⟨q, reply⟩])) := by
  by_cases hpend : (linearModel d).historyCost s.pending + q.cost < h
  · exact ⟨linearReply (fam.prefixObjective s.frame) q, ⟨s.append_pending q hpend⟩⟩
  · have hlen : s.frame.length < m := s.frame_length_lt (by omega)
    obtain ⟨u, hunit, horth, hp, hx, hu, hframe⟩ :=
      select_closing_direction selector hmhd fam.z fam.z_bound s.frame s.ortho hlen
        s.pending s.closed s.load (s.closed_length_le.trans hQ) q.point
    exact ⟨closingReply fam s.frame u q,
      ⟨s.close hh q u (Nat.le_of_not_gt hpend) hframe hp hx hu⟩⟩

theorem Invariant.finish {fam : Family d m R τ b} {h Q : ℕ} {hist : History d}
    (s : Invariant fam h hist)
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q) (hmhd : m + h ≤ d)
    (hbudget : (linearModel d).historyCost hist < h * m) (hQ : hist.length ≤ Q)
    (x : X d) :
    ∃ U, OrthoList U ∧ U.length = m ∧
      (linearModel d).ReplyConsistent (fam.objective U) hist ∧ b < ‖(fam.objective U).grad x‖ := by
  have hlen := s.frame_length_lt hbudget
  obtain ⟨u, hunit, horth, hp, hx, hu, hframe⟩ :=
    select_closing_direction selector hmhd fam.z fam.z_bound s.frame s.ortho hlen
      s.pending s.closed s.load (s.closed_length_le.trans hQ) x
  have hlen' : (s.frame ++ [u]).length ≤ m := by simpa using Nat.succ_le_of_lt hlen
  obtain ⟨tail, htlen, htframe, hsmall⟩ :=
    complete_frame selector hmhd fam.z fam.z_bound (s.frame ++ [u]) hframe hlen' hist hQ
  have hU : OrthoList (s.frame ++ u :: tail) := by
    simpa only [List.append_assoc, List.singleton_append] using htframe
  have hlength : (s.frame ++ u :: tail).length = m := by
    simpa only [List.append_assoc, List.singleton_append] using htlen
  refine ⟨s.frame ++ u :: tail, hU, hlength,
    s.consistent_completion u tail hU hlength hu hsmall hp, ?_⟩
  exact fam.barrier _ x hU hlength ⟨u, by simp, hx⟩

def BadRun (fam : Family d m R τ b) (A : (linearModel d).Algorithm) : Prop :=
  ∃ U n x, OrthoList U ∧ U.length = m ∧
    (linearModel d).Runs A (fam.objective U) n x ∧ b < ‖(fam.objective U).grad x‖

/-- Finite induction constructs the adaptive transcript. No realizability
statement or completed-frame witness is assumed in this induction. -/
theorem simulate (fam : Family d m R τ b) {h Q : ℕ} (hh : 0 < h)
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q) (hmhd : m + h ≤ d)
    (A : (linearModel d).Algorithm) (hcap : (linearModel d).UniversalCap A Q (h * m))
    (fuel : ℕ) {hist : History d} (hlen : hist.length + fuel = Q)
    (hreach : (linearModel d).Reachable A hist) (s : Invariant fam h hist) : BadRun fam A := by
  induction fuel generalizing hist with
  | zero =>
      cases ha : A hist with
      | query q =>
          have hq := (hcap.query_bounds hist q hreach ha).2
          omega
      | output x =>
          obtain ⟨U, ho, hm, hc, hb⟩ := s.finish selector hmhd (hcap.prefix_cost hist hreach)
            (by omega) x
          exact ⟨U, (linearModel d).historyCost hist, x, ho, hm,
            OracleModel.Reachable.runs _ hreach hc ha, hb⟩
  | succ fuel ih =>
      cases ha : A hist with
      | output x =>
          obtain ⟨U, ho, hm, hc, hb⟩ := s.finish selector hmhd (hcap.prefix_cost hist hreach)
            (by omega) x
          exact ⟨U, (linearModel d).historyCost hist, x, ho, hm,
            OracleModel.Reachable.runs _ hreach hc ha, hb⟩
      | query q =>
          obtain ⟨hcost, hcalls⟩ := hcap.query_bounds hist q hreach ha
          obtain ⟨reply, ⟨s'⟩⟩ := s.advance hh selector hmhd q hcost (by omega)
          apply ih (hist := hist ++ [⟨q, reply⟩])
          · simp only [List.length_append, List.length_singleton]
            omega
          · exact OracleModel.Reachable.query hreach ha reply
          · exact s'

/-- Appendix A's transcript-wide stage argument, including closing calls and
an arbitrary unqueried output. -/
theorem stage_failure (fam : Family d m R τ b) {h Q : ℕ} (hh : 0 < h)
    (selector : StripSelector (d := d) R τ (d - m - h + 1) Q) (hmhd : m + h ≤ d)
    (A : (linearModel d).Algorithm) (hcap : (linearModel d).UniversalCap A Q (h * m)) :
    BadRun fam A := by
  obtain ⟨s⟩ := initial fam hh
  exact simulate fam hh selector hmhd A hcap Q (by simp) OracleModel.Reachable.nil s

/-- Only full orthonormal frames index the legal family. -/
def familyClass (fam : Family d m R τ b) : Set (Objective d) :=
  {f | ∃ U, OrthoList U ∧ U.length = m ∧ f = fam.objective U}

/-- The stage lower bound with a budget promise only on the legal family,
as in `wk:lem:stage`. Its sole external mathematical assumptions are the
geometric selector and the explicitly stated analytic family properties. -/
theorem stage_lower_bound (fam : Family d m R τ b) {h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (selector : StripSelector (d := d) R τ (d - m - h + 1) (h * m))
    (hmhd : m + h ≤ d) :
    ((h * m : ℕ) : ℕ∞) ≤ (linearModel d).Ndet (familyClass fam) b := by
  let M := linearModel d
  apply OracleModel.le_Ndet
  intro A hA
  by_contra hnot
  have hc : M.worstCost A (familyClass fam) < ((h * m : ℕ) : ℕ∞) := lt_of_not_ge hnot
  have hpos : 0 < h * m := Nat.mul_pos hh hm
  let N := h * m - 1
  have hN : N + 1 = h * m := by omega
  have hbudget : M.worstCost A (familyClass fam) ≤ (N : ℕ∞) := by
    apply (ENat.lt_add_one_iff (ENat.coe_ne_top N)).mp
    have heq : (N : ℕ∞) + 1 = ((h * m : ℕ) : ℕ∞) := by exact_mod_cast hN
    rw [heq]
    exact hc
  have hs := OracleModel.Succeeds.cap_of_worstCost M hA hbudget
  have hcap : M.UniversalCap (M.capAlgorithm A N) (h * m) (h * m) := by
    have hbase := M.capAlgorithm_universalCap A N
    apply OracleModel.UniversalCap.mono M hbase
    · omega
    · omega
  obtain ⟨U, n, x, hU, hlen, hrun, hbad⟩ := stage_failure fam hh selector hmhd
    (M.capAlgorithm A N) hcap
  obtain ⟨n', y, hyrun, hgood⟩ := hs (fam.objective U) ⟨U, hU, hlen, rfl⟩
  have heq : y = x := (OracleModel.RunFrom.unique M hyrun hrun).2
  subst y
  exact (not_lt_of_ge hgood) hbad

end Stage
end ExactZO
