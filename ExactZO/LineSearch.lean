import ExactZO.CappedModel
import ExactZO.ValueProcedure
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean

/-! Doubling Armijo search on the actual objective, with inverse-curvature
progress and an amortized count including the rejected proposal. -/
noncomputable section
open Set
open scoped InnerProductSpace
set_option maxHeartbeats 800000

namespace ExactZO.LineSearch
variable {d : ℕ}

def stepSize (L ε : ℝ) (j : ℕ) : ℝ := (2 : ℝ) ^ j * ε / (2 * L)
def proposal (L ε : ℝ) (x u : X d) (j : ℕ) : X d := x - stepSize L ε j • u
def Armijo (f : Objective d) (x u : X d) (ε t : ℝ) : Prop :=
  f.value (x - t • u) ≤ f.value x - ε * t / 4

def FirstFailure (f : Objective d) (L ε : ℝ) (x u : X d) (k : ℕ) : Prop :=
  (∀ i < k, Armijo f x u ε (stepSize L ε i)) ∧
    ¬ Armijo f x u ε (stepSize L ε k)

theorem stepSize_pos {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (j : ℕ) :
    0 < stepSize L ε j := by unfold stepSize; positivity

theorem stepSize_succ (L ε : ℝ) (j : ℕ) :
    stepSize L ε (j + 1) = 2 * stepSize L ε j := by
  unfold stepSize
  rw [pow_succ]
  ring

theorem capped_ray_upper {f : Objective d} {H : X d →L[ℝ] X d}
    (hc : Continuous f.grad) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0) (t : ℝ) :
    cappedValue f (x - t • u) ≤ f.value x - t * ⟪f.grad x, u⟫_ℝ +
      (1 / 2 : ℝ) * t ^ 2 * ⟪u, H u⟫_ℝ := by
  have h := cappedValue_quadraticUpper f H hc hpos hmodel x (-(t • u)) hx
  convert h using 1 <;> simp only [sub_eq_add_neg, inner_neg_right, inner_neg_left, map_neg, inner_neg_neg,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem curvature_le {H : X d →L[ℝ] X d} {L E : ℝ}
    (hH : UpperMatrix L E H) {u : X d} (hu : ‖u‖ = 1) : ⟪u, H u⟫_ℝ ≤ L := by
  calc
    ⟪u, H u⟫_ℝ ≤ ‖u‖ * ‖H u‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖H‖ * ‖u‖) := mul_le_mul_of_nonneg_left (H.le_opNorm u) (norm_nonneg _)
    _ = ‖H‖ := by rw [hu]; ring
    _ ≤ L := hH.2.2.1

theorem curvature_pos {f : Objective d} {H : X d →L[ℝ] X d} {L Δ E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) : 0 < ⟪u, H u⟫_ℝ := by
  by_contra hn
  have hzero : ⟪u, H u⟫_ℝ = 0 := le_antisymm (le_of_not_gt hn) (hH.2.1 u)
  obtain ⟨lower, hlo, _⟩ := hf.2
  have ha : 0 < ⟪f.grad x, u⟫_ℝ := by linarith
  let t := (f.value x - lower + 1) / ⟪f.grad x, u⟫_ℝ
  have hcap := capped_ray_upper (hf.1.continuous_grad hL.le) hH.2.1 hmodel hx (u := u) t
  have hloCap : lower ≤ cappedValue f (x - t • u) := le_min (hlo _) (hlo _)
  have ht : t * ⟪f.grad x, u⟫_ℝ = f.value x - lower + 1 :=
    div_mul_cancel₀ _ (ne_of_gt ha)
  rw [hzero] at hcap
  nlinarith

theorem armijo_of_curvature_product {f : Objective d} {H : X d →L[ℝ] X d} {L E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : Smooth f L) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ)
    {t : ℝ} (ht : 0 < t) (hprod : t * ⟪u, H u⟫_ℝ ≤ 7 * ε / 8) :
    Armijo f x u ε t := by
  have hcap := capped_ray_upper (hf.continuous_grad hL.le) hH.2.1 hmodel hx (u := u) t
  have hs := mul_lt_mul_of_pos_left hslope ht
  have hp := mul_le_mul_of_nonneg_left hprod ht.le
  have hstrict : cappedValue f (x - t • u) < f.value x - ε * t / 4 := by nlinarith
  unfold cappedValue at hstrict
  rcases min_lt_iff.mp hstrict with hactual | hcapbad
  · exact hactual.le
  · have hh : 0 < ε * t := mul_pos hε ht
    linarith

theorem armijo_of_step_le {f : Objective d} {H : X d →L[ℝ] X d} {L E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : Smooth f L) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ)
    (hlam : 0 < ⟪u, H u⟫_ℝ) {t : ℝ} (ht : 0 < t)
    (hsmall : t ≤ 7 * ε / (8 * ⟪u, H u⟫_ℝ)) : Armijo f x u ε t := by
  apply armijo_of_curvature_product hL hε hf hH hmodel hx hslope ht
  have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hlam)).mp hsmall
  nlinarith

theorem initial_pass {f : Objective d} {H : X d →L[ℝ] X d} {L E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : Smooth f L) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0) (hu : ‖u‖ = 1)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) :
    Armijo f x u ε (stepSize L ε 0) := by
  apply armijo_of_curvature_product hL hε hf hH hmodel hx hslope (stepSize_pos hL hε 0)
  have h := mul_le_mul_of_nonneg_left (curvature_le hH hu) (stepSize_pos hL hε 0).le
  have heq : stepSize L ε 0 * L = ε / 2 := by unfold stepSize; field_simp; ring
  rw [heq] at h
  linarith

theorem accepted_gap_charge {f : Objective d} {Δ ε t : ℝ} (hgap : HasGap f Δ)
    {x u : X d} (hx : f.value x ≤ f.value 0) (hpass : Armijo f x u ε t) :
    ε * t / 4 ≤ f.value x - f.value (x - t • u) ∧
      f.value x - f.value (x - t • u) ≤ Δ := by
  obtain ⟨lower, hlo, hgap⟩ := hgap
  have hh := hlo (x - t • u)
  constructor <;> unfold Armijo at hpass <;> linarith

theorem accepted_power_budget {f : Objective d} {L Δ ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hgap : HasGap f Δ)
    {x u : X d} (hx : f.value x ≤ f.value 0) {j : ℕ}
    (hpass : Armijo f x u ε (stepSize L ε j)) :
    (2 : ℝ) ^ j ≤ 8 * L * Δ / ε ^ 2 := by
  have hc := (accepted_gap_charge hgap hx hpass).1.trans (accepted_gap_charge hgap hx hpass).2
  have heq : ε * stepSize L ε j / 4 = (2 : ℝ) ^ j * ε ^ 2 / (8 * L) := by
    unfold stepSize
    ring
  rw [heq] at hc
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 8 * L)).mp hc

theorem exists_failure {f : Objective d} {L Δ ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hgap : HasGap f Δ)
    {x u : X d} (hx : f.value x ≤ f.value 0) :
    ∃ k : ℕ, ¬ Armijo f x u ε (stepSize L ε k) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (8 * L * Δ / ε ^ 2) (by norm_num : (1 : ℝ) < 2)
  exact ⟨k, fun h => (not_le_of_gt hk) (accepted_power_budget hL hε hgap hx h)⟩

theorem exists_first_failure {f : Objective d} {H : X d →L[ℝ] X d} {L Δ E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0) (hu : ‖u‖ = 1)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) :
    ∃ j : ℕ, FirstFailure f L ε x u (j + 1) := by
  classical
  have hex := exists_failure hL hε hf.2 hx (u := u)
  let k := Nat.find hex
  have hbad : ¬ Armijo f x u ε (stepSize L ε k) := Nat.find_spec hex
  have hbefore : ∀ i < k, Armijo f x u ε (stepSize L ε i) := by
    intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    rw [hk0] at hbad
    exact hbad (initial_pass hL hε hf.1 hH hmodel hx hu hslope)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact ⟨j, by simpa only [hj] using (show FirstFailure f L ε x u k from ⟨hbefore, hbad⟩)⟩

theorem inverse_curvature_decrease {f : Objective d} {H : X d →L[ℝ] X d} {L Δ E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) {j : ℕ}
    (hpass : Armijo f x u ε (stepSize L ε j))
    (hfail : ¬ Armijo f x u ε (stepSize L ε (j + 1))) :
    7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) < f.value x - f.value (proposal L ε x u j) ∧
      ε ^ 2 / (10 * ⟪u, H u⟫_ℝ) < 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) := by
  have hlam := curvature_pos hL hε hf hH hmodel hx hslope
  have hlarge : 7 * ε / (8 * ⟪u, H u⟫_ℝ) < stepSize L ε (j + 1) := by
    apply lt_of_not_ge
    intro hn
    exact hfail (armijo_of_step_le hL hε hf.1 hH hmodel hx hslope hlam
      (stepSize_pos hL hε (j + 1)) hn)
  rw [stepSize_succ] at hlarge
  have hh := mul_lt_mul_of_pos_left hlarge (by positivity : 0 < ε / 8)
  have heq : ε / 8 * (7 * ε / (8 * ⟪u, H u⟫_ℝ)) =
      7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) := by ring
  rw [heq] at hh
  constructor
  · have hcharge := (accepted_gap_charge hf.2 hx hpass).1
    dsimp only [proposal]
    nlinarith
  · apply (div_lt_div_iff₀ (by positivity : 0 < 10 * ⟪u, H u⟫_ℝ)
      (by positivity : 0 < 64 * ⟪u, H u⟫_ℝ)).mpr
    nlinarith [mul_pos (sq_pos_of_pos hε) hlam]

theorem index_le_power (j : ℕ) : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [Nat.cast_succ, pow_succ]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith

theorem proposal_count_bound {f : Objective d} {L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) {x u : X d} {j : ℕ}
    (hpass : Armijo f x u ε (stepSize L ε j)) :
    (j + 2 : ℕ) ≤ 8 * L * (f.value x - f.value (proposal L ε x u j)) / ε ^ 2 + 1 := by
  have hcharge : ε * stepSize L ε j / 4 ≤ f.value x - f.value (proposal L ε x u j) := by
    unfold Armijo at hpass
    dsimp only [proposal]
    linarith
  have heq : ε * stepSize L ε j / 4 = (2 : ℝ) ^ j * ε ^ 2 / (8 * L) := by
    unfold stepSize
    ring
  rw [heq] at hcharge
  have hpow : (2 : ℝ) ^ j ≤ 8 * L * (f.value x - f.value (proposal L ε x u j)) / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 8 * L)).mp hcharge
  have hi := index_le_power j
  push_cast
  linarith

/-- The full analytic doubling lemma: the actual first failure exists, the
preceding accepted point has strict inverse-curvature progress, and all j+2
proposals (including the failed one) satisfy the amortized cost bound. -/
theorem doubling_line_search {f : Objective d} {H : X d →L[ℝ] X d} {L Δ E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0) (hu : ‖u‖ = 1)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) :
    0 < ⟪u, H u⟫_ℝ ∧ ∃ j : ℕ, FirstFailure f L ε x u (j + 1) ∧
      7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) < f.value x - f.value (proposal L ε x u j) ∧
      ε ^ 2 / (10 * ⟪u, H u⟫_ℝ) < 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) ∧
      (j + 2 : ℕ) ≤ 8 * L * (f.value x - f.value (proposal L ε x u j)) / ε ^ 2 + 1 := by
  refine ⟨curvature_pos hL hε hf hH hmodel hx hslope, ?_⟩
  obtain ⟨j, hj⟩ := exists_first_failure hL hε hf hH hmodel hx hu hslope
  have hpass := hj.1 j (by omega)
  obtain ⟨hdec, hconst⟩ := inverse_curvature_decrease hL hε hf hH hmodel hx hslope hpass hj.2
  exact ⟨j, hj, hdec, hconst, proposal_count_bound hL hε hpass⟩

/-- A finite implementation. The center value is a returned scalar; neither
f nor H is available to the policy. Exhausted fuel returns the last accepted point. -/
def procedureLoop (L ε : ℝ) (x u : X d) (center : ℝ) :
    ℕ → ℕ → X d → ValueProcedure d
  | 0, _, previous => .output previous
  | fuel + 1, j, previous => .query (proposal L ε x u j) fun value =>
      if value ≤ center - ε * stepSize L ε j / 4 then
        procedureLoop L ε x u center fuel (j + 1) (proposal L ε x u j)
      else .output previous

/-- The center query is always charged, including when it duplicates a known value. -/
def procedure (fuel : ℕ) (L ε : ℝ) (x u : X d) : ValueProcedure d :=
  .query x fun center => procedureLoop L ε x u center fuel 0 x

/-- Exact behavior up to the first failure. The rejected proposal is included. -/
theorem procedureLoop_first_failure (f : Objective d) (L ε : ℝ) (x u : X d)
    (fuel start k : ℕ) (previous : X d)
    (hstart : start ≤ k) (hfuel : k < start + fuel)
    (hpass : ∀ i, start ≤ i → i < k → Armijo f x u ε (stepSize L ε i))
    (hfail : ¬ Armijo f x u ε (stepSize L ε k)) :
    (procedureLoop L ε x u (f.value x) fuel start previous).result f =
        (if start = k then previous else proposal L ε x u (k - 1)) ∧
      (procedureLoop L ε x u (f.value x) fuel start previous).cost f = k - start + 1 := by
  induction fuel generalizing start previous with
  | zero => omega
  | succ fuel ih =>
      by_cases heq : start = k
      · subst start
        have hfalse : ¬ f.value (proposal L ε x u k) ≤ f.value x - ε * stepSize L ε k / 4 := hfail
        simp [procedureLoop, ValueProcedure.result, ValueProcedure.cost, hfalse]
      · have hlt : start < k := by omega
        have htrue : f.value (proposal L ε x u start) ≤ f.value x - ε * stepSize L ε start / 4 :=
          hpass start le_rfl hlt
        have hrec := ih (start + 1) (proposal L ε x u start) (by omega) (by omega)
          (fun i hi hik => hpass i (by omega) hik)
        simp only [procedureLoop, ValueProcedure.result, ValueProcedure.cost, if_pos htrue]
        constructor
        · rw [hrec.1, if_neg heq]
          by_cases hnext : start + 1 = k
          · have hprev : k - 1 = start := by omega
            simp only [if_pos hnext, hprev]
          · simp only [if_neg hnext]
        · rw [hrec.2]
          omega

theorem procedure_first_failure (f : Objective d) (L ε : ℝ) (x u : X d)
    {fuel j : ℕ} (hfirst : FirstFailure f L ε x u (j + 1)) (hfuel : j + 1 < fuel) :
    (procedure fuel L ε x u).result f = proposal L ε x u j ∧
      (procedure fuel L ε x u).cost f = j + 3 := by
  have h := procedureLoop_first_failure f L ε x u fuel 0 (j + 1) x (by omega)
    (by omega) (fun i _ hi => hfirst.1 i hi) hfirst.2
  dsimp only [procedure, ValueProcedure.result, ValueProcedure.cost]
  constructor
  · simpa using h.1
  · rw [h.2]
    omega

/-- A public budget suffices for this finite implementation. The loop itself
only takes fuel; it does not inspect the gap, the matrix, or the objective. -/
def publicFuel (L Δ ε : ℝ) : ℕ := ⌊8 * L * Δ / ε ^ 2⌋₊ + 1

theorem first_failure_lt_publicFuel {f : Objective d} {L Δ ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hgap : HasGap f Δ)
    {x u : X d} (hx : f.value x ≤ f.value 0) {j : ℕ}
    (hfirst : FirstFailure f L ε x u (j + 1)) : j + 1 < publicFuel L Δ ε := by
  have hp := accepted_power_budget hL hε hgap hx (hfirst.1 j (by omega))
  have hidx : ((j + 1 : ℕ) : ℝ) ≤ 8 * L * Δ / ε ^ 2 := by
    push_cast
    exact (index_le_power j).trans hp
  have hn : j + 1 ≤ ⌊8 * L * Δ / ε ^ 2⌋₊ := Nat.le_floor hidx
  exact Nat.lt_succ_of_le hn

/-- Actual value-oracle execution with exact cost, one center plus every
accepted proposal and the first failed proposal. -/
theorem procedure_runs_first_failure (f : Objective d) (L ε : ℝ) (x u : X d)
    {fuel j : ℕ} (hfirst : FirstFailure f L ε x u (j + 1)) (hfuel : j + 1 < fuel) :
    (valueModel d).Runs (procedure fuel L ε x u).algorithm f
      (j + 3) (proposal L ε x u j) := by
  have hr := (procedure fuel L ε x u).runs f
  obtain ⟨hresult, hcost⟩ := procedure_first_failure f L ε x u hfirst hfuel
  rwa [hresult, hcost] at hr

/-- The finite value-query implementation inherits the analytic conclusion.
The cost here includes its center query, so the constant is +2. -/
theorem procedure_spec {f : Objective d} {H : X d →L[ℝ] X d} {L Δ E ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    {x u : X d} (hx : f.value x ≤ f.value 0) (hu : ‖u‖ = 1)
    (hslope : 11 * ε / 16 < ⟪f.grad x, u⟫_ℝ) :
    let P := procedure (publicFuel L Δ ε) L ε x u
    0 < ⟪u, H u⟫_ℝ ∧ ∃ j : ℕ, FirstFailure f L ε x u (j + 1) ∧
      P.result f = proposal L ε x u j ∧ P.cost f = j + 3 ∧
      7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) < f.value x - f.value (P.result f) ∧
      ε ^ 2 / (10 * ⟪u, H u⟫_ℝ) < 7 * ε ^ 2 / (64 * ⟪u, H u⟫_ℝ) ∧
      (P.cost f : ℝ) ≤ 8 * L * (f.value x - f.value (P.result f)) / ε ^ 2 + 2 := by
  dsimp only
  obtain ⟨hlam, j, hfirst, hdec, hconst, hcount⟩ :=
    doubling_line_search hL hε hf hH hmodel hx hu hslope
  obtain ⟨hresult, hcost⟩ := procedure_first_failure f L ε x u hfirst
    (first_failure_lt_publicFuel hL hε hf.2 hx hfirst)
  refine ⟨hlam, j, hfirst, hresult, hcost, ?_, hconst, ?_⟩
  · rwa [hresult]
  · rw [hcost, hresult]
    push_cast at hcount ⊢
    linarith

end ExactZO.LineSearch
