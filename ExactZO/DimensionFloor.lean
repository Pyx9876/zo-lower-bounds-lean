import ExactZO.Oracle
import ExactZO.HistorySpace
import Mathlib.Analysis.InnerProductSpace.Projection

/-! The unconditional deterministic dimension lower bound, including a single
fixed quadratic witness and replay of the actual adaptive oracle execution. -/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO
namespace DimensionFloor

def constantObjective (d : ℕ) (c : ℝ) : Objective d where
  value _ := c
  grad _ := 0
  hasDeriv x := by simpa only [map_zero] using (hasFDerivAt_const (𝕜 := ℝ) c x)

theorem constant_fixedClass {d : ℕ} {L Δ E : ℝ} (hL : 0 ≤ L)
    (hΔ : 0 ≤ Δ) (hE : 0 ≤ E) (c : ℝ) :
    FixedClass L Δ E (constantObjective d c) := by
  refine ⟨⟨?_, c, ?_, ?_⟩, 0, ?_, ?_⟩
  · intro x y
    simp only [constantObjective, sub_self, norm_zero]
    exact mul_nonneg hL (norm_nonneg _)
  · intro x
    exact le_rfl
  · simpa [constantObjective] using hΔ
  · simp [UpperMatrix, hL, mul_nonneg hL hE]
  · intro x y
    simp [QuadraticUpper, constantObjective]

def quadratic {d : ℕ} (L r : ℝ) (u : X d) : Objective d where
  value x := L / 2 * (⟪u, x⟫_ℝ - r) ^ 2
  grad x := (L * (⟪u, x⟫_ℝ - r)) • u
  hasDeriv x := by
    have hl : HasFDerivAt (fun y => ⟪u, y⟫_ℝ - r) (innerSL ℝ u) x :=
      (innerSL ℝ u).hasFDerivAt.sub_const r
    have h := (hl.mul hl).const_mul (L / 2)
    convert h using 1
    · ext z
      simp only [pow_two]
    · ext z
      simp only [ContinuousLinearMap.smul_apply, innerSL_apply, real_inner_smul_left,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.mulLeftRight_apply,
        smul_eq_mul]
      ring

def upperMap {d : ℕ} (L : ℝ) (u : X d) : X d →L[ℝ] X d :=
  L • (innerSL ℝ u).smulRight u

@[simp] theorem upperMap_apply {d : ℕ} (L : ℝ) (u x : X d) :
    upperMap L u x = (L * ⟪u, x⟫_ℝ) • u := by
  simp [upperMap, smul_smul]

theorem rankOne_trace {d : ℕ} (u : X d) :
    LinearMap.trace ℝ (X d) ((innerSL ℝ u).smulRight u).toLinearMap = ‖u‖ ^ 2 := by
  let a : X d →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap
  let b : ℝ →ₗ[ℝ] X d := LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) u
  have hab : ((innerSL ℝ u).smulRight u).toLinearMap = b.comp a := rfl
  rw [hab, LinearMap.trace_comp_comm']
  have hba : a.comp b = ⟪u, u⟫_ℝ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro t
    simp only [a, b, LinearMap.comp_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, ContinuousLinearMap.coe_coe, innerSL_apply,
      real_inner_smul_right, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  rw [hba, map_smul, LinearMap.trace_id]
  simp only [Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one,
    real_inner_self_eq_norm_sq]

theorem quadratic_upper {d : ℕ} (L r : ℝ) (u x y : X d) :
    QuadraticUpper (quadratic L r u) (upperMap L u) x y := by
  apply le_of_eq
  simp only [quadratic, upperMap_apply, real_inner_smul_left,
    real_inner_smul_right, inner_sub_right, inner_sub_left,
    real_inner_comm y u, real_inner_comm x u]
  ring

theorem upperMap_valid {d : ℕ} {L E : ℝ} (hL : 0 ≤ L) (hE : 1 ≤ E)
    (u : X d) (hu : ‖u‖ = 1) : UpperMatrix L E (upperMap L u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [upperMap_apply, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm x u]
    ring
  · intro x
    simp only [upperMap_apply, real_inner_smul_right]
    rw [real_inner_comm x u, mul_assoc]
    exact mul_nonneg hL (mul_self_nonneg _)
  · apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro x
    have hi := abs_real_inner_le_norm u x
    simp only [hu, one_mul] at hi
    simpa [upperMap_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL, hu]
      using mul_le_mul_of_nonneg_left hi hL
  · have ht : LinearMap.trace ℝ (X d) (upperMap L u).toLinearMap = L := by
      change LinearMap.trace ℝ (X d) (L • ((innerSL ℝ u).smulRight u).toLinearMap) = L
      rw [map_smul, rankOne_trace, hu]
      simp
    rw [ht]
    nlinarith

theorem quadratic_smooth {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (r : ℝ)
    (u : X d) (hu : ‖u‖ = 1) : Smooth (quadratic L r u) L := by
  intro x y
  have heq : (quadratic L r u).grad x - (quadratic L r u).grad y =
      (L * ⟪u, x - y⟫_ℝ) • u := by
    simp only [quadratic, ← sub_smul, inner_sub_right]
    congr 1
    ring
  rw [heq]
  have hi := abs_real_inner_le_norm u (x - y)
  simp only [hu, one_mul] at hi
  simpa [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL, hu]
    using mul_le_mul_of_nonneg_left hi hL

theorem quadratic_fixedClass {d : ℕ} {L Δ E r : ℝ} (hL : 0 ≤ L)
    (hE : 1 ≤ E) (hr : L / 2 * r ^ 2 ≤ Δ) (u : X d) (hu : ‖u‖ = 1) :
    FixedClass L Δ E (quadratic L r u) := by
  refine ⟨⟨quadratic_smooth hL r u hu, 0, ?_, ?_⟩,
    upperMap L u, upperMap_valid hL hE u hu, quadratic_upper L r u⟩
  · intro x
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · simpa [quadratic] using hr

/-- The actual run determines a finite history which can be replayed on every
single fixed objective agreeing with all of its exact replies. -/
theorem exists_replay_history {d : ℕ} (M : OracleModel d) {A : M.Algorithm}
    {f : Objective d} {h : M.History} {n : ℕ} {x : X d}
    (hr : M.RunFrom A f h n x) :
    ∃ suffix : M.History, M.historyCost suffix = n ∧
      M.ReplyConsistent f suffix ∧
      ∀ g : Objective d, M.ReplyConsistent g suffix → M.RunFrom A g h n x := by
  induction hr with
  | output ha =>
      exact ⟨[], rfl, by simp [OracleModel.ReplyConsistent],
        fun g _ => OracleModel.RunFrom.output ha⟩
  | @query h q n x ha ht ih =>
      obtain ⟨suffix, hc, hf, hg⟩ := ih
      refine ⟨⟨q, M.answer f q⟩ :: suffix, ?_, ?_, ?_⟩
      · simpa [OracleModel.historyCost] using congrArg (M.cost q + ·) hc
      · intro entry he
        rcases List.mem_cons.mp he with he | he
        · subst entry
          rfl
        · exact hf entry he
      · intro g hgr
        have heq := hgr ⟨q, M.answer f q⟩ (List.mem_cons_self ..)
        have ht' := hg g (fun e he => hgr e (List.mem_cons_of_mem _ he))
        apply OracleModel.RunFrom.query ha
        simpa only [← heq] using ht'

theorem quadratic_gradient_barrier {d : ℕ} {L r ε : ℝ} (hL : 0 ≤ L)
    (hr : 0 ≤ r) (hb : ε < L * r) (u x : X d) (hu : ‖u‖ = 1)
    (hx : ⟪u, x⟫_ℝ ≤ 0) : ε < ‖(quadratic L r u).grad x‖ := by
  have hn : L * (⟪u, x⟫_ℝ - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hL (by linarith)
  simp only [quadratic, norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonpos hn]
  have hh := mul_nonpos_of_nonneg_of_nonpos hL hx
  nlinarith

theorem quadratic_reply_eq_constant {d : ℕ} {L Δ r : ℝ} (u : X d)
    (hr : L / 2 * r ^ 2 = Δ) (q : LinearQuery d)
    (hx : ⟪u, q.point⟫_ℝ = 0)
    (hV : ∀ v, ⟪u, q.directions v⟫_ℝ = 0) :
    linearReply (quadratic L r u) q = linearReply (constantObjective d Δ) q := by
  have hAdj : q.directions.adjoint u = 0 := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    simpa only [inner_zero_left] using hV v
  apply Prod.ext
  · simpa only [linearReply, quadratic, constantObjective, hx, zero_sub, neg_sq] using hr
  · simp only [linearReply, quadratic, constantObjective, map_smul, hAdj, smul_zero, map_zero]

theorem sqrt_radius_data {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    0 ≤ Real.sqrt (2 * Δ / L) ∧
      L / 2 * (Real.sqrt (2 * Δ / L)) ^ 2 = Δ ∧
      ε < L * Real.sqrt (2 * Δ / L) := by
  have hr := Real.sqrt_nonneg (2 * Δ / L)
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * Δ / L by positivity)
  have hgap : L / 2 * Real.sqrt (2 * Δ / L) ^ 2 = Δ := by
    rw [hr2]
    field_simp
    ring
  refine ⟨hr, hgap, ?_⟩
  have hT' := (lt_div_iff₀ (sq_pos_of_pos hε)).mp hT
  have hbar : (L * Real.sqrt (2 * Δ / L)) ^ 2 = 2 * L * Δ := by
    rw [mul_pow, hr2]
    field_simp
    ring
  nlinarith [mul_nonneg hL.le hr]

/-- A legal constant-function run supplies a finite history. If its cost is
below `d`, a single fixed quadratic reproduces that history and defeats its
output. No termination assumption on fake replies is required. -/
theorem lower_bound_of_radius {d : ℕ} {L Δ E ε r : ℝ} (hL : 0 ≤ L)
    (hΔ : 0 ≤ Δ) (hE : 1 ≤ E) (hr : 0 ≤ r)
    (hgap : L / 2 * r ^ 2 = Δ) (hbarrier : ε < L * r) :
    (d : ℕ∞) ≤ (linearModel d).Ndet {f | FixedClass L Δ E f} ε := by
  let M := linearModel d
  let C : Set (Objective d) := {f | FixedClass L Δ E f}
  apply OracleModel.le_Ndet
  intro A hA
  by_contra hnot
  have hcost : M.worstCost A C < (d : ℕ∞) := lt_of_not_ge hnot
  let f₀ := constantObjective d Δ
  have hf₀ : f₀ ∈ C := constant_fixedClass hL hΔ (by linarith) Δ
  obtain ⟨n, z, hrun, _⟩ := hA f₀ hf₀
  have hncost : (n : ℕ∞) ≤ M.worstCost A C := by
    rw [← M.runCost_eq_of_runs hrun]
    exact le_iSup_of_le f₀ (le_iSup_of_le hf₀ le_rfl)
  have hn : n < d := ENat.coe_lt_coe.mp (hncost.trans_lt hcost)
  obtain ⟨hist, hhistcost, hconst, hreplay⟩ := exists_replay_history M hrun
  obtain ⟨u, hu, horth, hz⟩ := exists_unit_orthogonal_history_of_cost_lt
    (show (linearModel d).historyCost hist < d by
      change M.historyCost hist < d
      rw [hhistcost]
      exact hn) z
  let g := quadratic L r u
  have hg : g ∈ C := quadratic_fixedClass hL hE hgap.le u hu
  have htrue : M.ReplyConsistent g hist := by
    intro entry he
    calc
      entry.2 = M.answer f₀ entry.1 := hconst entry he
      _ = M.answer g entry.1 :=
        (quadratic_reply_eq_constant u hgap entry.1 (horth entry he).1
          (horth entry he).2).symm
  have hgrun : M.Runs A g n z := hreplay g htrue
  obtain ⟨m, y, hyrun, hgood⟩ := hA g hg
  have hyz : y = z := (OracleModel.RunFrom.unique M hyrun hgrun).2
  rw [hyz] at hgood
  exact (not_lt_of_ge hgood) (quadratic_gradient_barrier hL hr hbarrier u z hu hz)

end DimensionFloor

/-- Appendix A, `lem:dimension-floor`, for the fixed quadratic-upper-model class. -/
theorem dimension_floor_fixed {d : ℕ} {L Δ E ε : ℝ} (_hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (_hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (linearModel d).Ndet {f | FixedClass L Δ E f} ε := by
  obtain ⟨hr, hgap, hb⟩ := DimensionFloor.sqrt_radius_data hL hΔ hε hT
  exact DimensionFloor.lower_bound_of_radius hL.le hΔ.le hE hr hgap hb

theorem dimension_floor_sublevel {d : ℕ} {L Δ E ε : ℝ} (hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (linearModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (dimension_floor_fixed hd hL hΔ hε hE hEd hT).trans
    ((linearModel d).Ndet_mono_class (fun _ hf => fixedClass_subset_sublevelClass hf) ε)

theorem dimension_floor_smooth {d : ℕ} {L Δ E ε : ℝ} (hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (linearModel d).Ndet {f | SmoothClass L Δ f} ε :=
  (dimension_floor_sublevel hd hL hΔ hε hE hEd hT).trans
    ((linearModel d).Ndet_mono_class (fun _ hf => sublevelClass_subset_smoothClass hf) ε)

theorem dimension_floor_value_fixed {d : ℕ} {L Δ E ε : ℝ} (hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (valueModel d).Ndet {f | FixedClass L Δ E f} ε :=
  (dimension_floor_fixed hd hL hΔ hε hE hEd hT).trans (Ndet_linear_le_value _ ε)

theorem dimension_floor_value_sublevel {d : ℕ} {L Δ E ε : ℝ} (hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (valueModel d).Ndet {f | SublevelClass L Δ E f} ε :=
  (dimension_floor_sublevel hd hL hΔ hε hE hEd hT).trans (Ndet_linear_le_value _ ε)

theorem dimension_floor_value_smooth {d : ℕ} {L Δ E ε : ℝ} (hd : 1 ≤ d)
    (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hE : 1 ≤ E) (hEd : E ≤ d)
    (hT : (1 / 2 : ℝ) < L * Δ / ε ^ 2) :
    (d : ℕ∞) ≤ (valueModel d).Ndet {f | SmoothClass L Δ f} ε :=
  (dimension_floor_smooth hd hL hΔ hε hE hEd hT).trans (Ndet_linear_le_value _ ε)

end ExactZO
