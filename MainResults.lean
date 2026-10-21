import ExactZO

/-! Public entry points for the checked complexity results.

The deterministic bounds concern actual oracle complexities, with no wrapper
or selector premises. `HessianSublevelClass` and `SublevelClass` are equivalent
under the stated global smoothness assumptions. The random upper bound uses an
explicit finite Gaussian seed and has no probability premises. Its policy is
jointly measurable in seed and transcript. The randomized lower bound is still
unproved. Unknown-trace methods, expected random
costs, and additional regularity promises about hard witnesses are not covered.

`main_det_statement` is proved by `main_det_verified`. The other declarations
ending in `_statement` are unproved proposition definitions recording targets;
none is used as an assumption to establish an advertised result. -/

noncomputable section
open MeasureTheory

namespace ExactZO.MainResults

/-- Both bounds use the same one of the two actual oracle models. -/
def SupportedOracle {d : ℕ} (M : OracleModel d) : Prop :=
  M = linearModel d ∨ M = valueModel d

/-- Unconditional coordinate-method upper bound for the unrestricted smooth
class. The natural floor states the real bound without discarding infinity. -/
theorem reader_unrestricted_upper {d : ℕ} {L Δ ε : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hε : 0 < ε)
    (hT : 1 ≤ L * Δ / ε ^ 2) (M : OracleModel d) (hM : SupportedOracle M) :
    M.Ndet (SmoothClass L Δ) ε ≤
      (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞) := by
  have hu := coordinate_value_upper_ten (d := d) (by omega) hL hε hT
  rcases hM with rfl | rfl
  · exact (Ndet_linear_le_value _ ε).trans hu
  · exact hu

/-- All-parameter upper bound using the coordinate or actual subspace method. -/
theorem main_det_upper {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Ndet (SublevelClass L Δ E) ε ≤
      min (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞)
        (⌊100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
          ((d : ℝ) + L * Δ / ε ^ 2))⌋₊ : ℕ∞) := by
  rcases hM with rfl | rfl
  · exact SubspaceUpper.deterministic_linear_upper hd hL hE hEd hε hT
  · exact SubspaceUpper.deterministic_value_upper hd hL hE hEd hε hT

/-- New S4 min lower bound, with the finite entropy selector and wrapper proved. -/
theorem main_det_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤ M.Ndet (SublevelClass L Δ E) ε := by
  rcases hM with rfl | rfl
  · exact S4Selection.deterministic_rounded_lower hd hL hΔ hε hE hEd hT hET
  · exact S4Selection.deterministic_rounded_lower_value hd hL hΔ hε hE hEd hT hET

/-- The dimension floor is an actual complexity lower bound. -/
theorem main_det_dimension_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (M : OracleModel d) (hM : SupportedOracle M) :
    (d : ℕ∞) ≤ M.Ndet (SublevelClass L Δ E) ε := by
  rcases hM with rfl | rfl
  · exact dimension_floor_sublevel hd hL hΔ hε hE hEd (by linarith)
  · exact dimension_floor_value_sublevel hd hL hΔ hε hE hEd (by linarith)

/-- Both deterministic bounds for the same oracle in the main regime. -/
theorem main_det_two_sided {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    (((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤ M.Ndet (SublevelClass L Δ E) ε) ∧
    M.Ndet (SublevelClass L Δ E) ε ≤
      min (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞)
        (⌊100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
          ((d : ℝ) + L * Δ / ε ^ 2))⌋₊ : ℕ∞) :=
  ⟨main_det_lower hd hL hΔ hε hE hEd hT hET M hM,
    main_det_upper hd hL hε hE hEd hT M hM⟩

/-- A window lower bound without the restriction `E * T ≤ d`. -/
theorem main_det_general_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (M : OracleModel d) (hM : SupportedOracle M) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2359296⌉₊ : ℕ) : ℕ∞) ≤
      M.Ndet (SublevelClass L Δ E) ε := by
  rcases hM with rfl | rfl
  · exact S4Selection.deterministic_window_lower hd hL hΔ hε hE hEd hT hwindow
  · exact S4Selection.deterministic_window_lower_value hd hL hΔ hε hE hEd hT hwindow

/-- The min in the S4 lower bound equals `T` in the matching window. -/
theorem lower_min_eq_time {T E : ℝ} (hT : 1 ≤ T)
    (hwindow : T * Real.log (Real.exp 1 + T) ≤ E) :
    min T (Real.sqrt (E * T / Real.log (Real.exp 1 + T))) = T := by
  have hTp : 0 < T := by linarith
  have hexp : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hlog : 0 < Real.log (Real.exp 1 + T) := Real.log_pos (by linarith)
  apply min_eq_left
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_right hwindow hTp.le]

/-- The stronger `1/2250` lower bound uses both matching-window inequalities. -/
theorem main_det_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (hcap : E ≤ (d : ℝ) / (L * Δ / ε ^ 2))
    (M : OracleModel d) (hM : SupportedOracle M) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2250⌉₊ : ℕ) : ℕ∞) ≤
      M.Ndet (SublevelClass L Δ E) ε := by
  have hET : E * (L * Δ / ε ^ 2) ≤ d :=
    (le_div_iff₀ (by linarith : 0 < L * Δ / ε ^ 2)).mp hcap
  simpa only [lower_min_eq_time hT hwindow] using
    main_det_lower hd hL hΔ hε hE hEd hT hET M hM

/-- Class equality transports both bounds to the a.e. Hessian class. -/
theorem sublevelClass_eq_hessianSublevelClass {d : ℕ} {L Δ E : ℝ} (hL : 0 ≤ L) :
    (SublevelClass L Δ E : Set (Objective d)) = HessianSublevelClass L Δ E := by
  ext f
  exact sublevelClass_iff_hessianSublevelClass hL

/-- All-parameter upper bound for the paper's a.e. Hessian class. -/
theorem main_det_hessian_upper {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Ndet (HessianSublevelClass L Δ E) ε ≤
      min (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞)
        (⌊100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
          ((d : ℝ) + L * Δ / ε ^ 2))⌋₊ : ℕ∞) := by
  rw [← sublevelClass_eq_hessianSublevelClass hL.le]
  exact main_det_upper hd hL hε hE hEd hT M hM

/-- Main-regime lower bound for the paper's a.e. Hessian class. -/
theorem main_det_hessian_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    ((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤ M.Ndet (HessianSublevelClass L Δ E) ε := by
  rw [← sublevelClass_eq_hessianSublevelClass hL.le]
  exact main_det_lower hd hL hΔ hε hE hEd hT hET M hM

/-- The deterministic pair for the actual Hessian class and the same oracle. -/
theorem main_det_hessian_two_sided {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    (((⌈(d : ℝ) * min (L * Δ / ε ^ 2)
      (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
      2250⌉₊ : ℕ) : ℕ∞) ≤ M.Ndet (HessianSublevelClass L Δ E) ε) ∧
    M.Ndet (HessianSublevelClass L Δ E) ε ≤
      min (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞)
        (⌊100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
          ((d : ℝ) + L * Δ / ε ^ 2))⌋₊ : ℕ∞) := by
  rw [← sublevelClass_eq_hessianSublevelClass hL.le]
  exact main_det_two_sided hd hL hΔ hε hE hEd hT hET M hM

/-- Matching-window lower bound for the a.e. Hessian class. -/
theorem main_det_hessian_window_lower {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hwindow : (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E)
    (hcap : E ≤ (d : ℝ) / (L * Δ / ε ^ 2))
    (M : OracleModel d) (hM : SupportedOracle M) :
    ((⌈(d : ℝ) * (L * Δ / ε ^ 2) / 2250⌉₊ : ℕ) : ℕ∞) ≤
      M.Ndet (HessianSublevelClass L Δ E) ε := by
  rw [← sublevelClass_eq_hessianSublevelClass hL.le]
  exact main_det_window_lower hd hL hΔ hε hE hEd hT hwindow hcap M hM

/-- Actual hard-cap randomized complexity, using a finite standard Gaussian
seed fixed before every objective. All probability inputs have been proved. -/
theorem main_random_upper {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 0 < E) (hε : 0 < ε)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Nrand (SublevelClass L Δ E) ε (1 / 3) ≤
      ((1 + 2 * STP.horizon (L * E) Δ ε : ℕ) : ℕ∞) := by
  have hu := STP.gaussian_random_upper (d := d) hL hΔ hE hε
  rcases hM with rfl | rfl
  · exact (Nrand_linear_le_value _ ε (1 / 3)).trans hu
  · exact hu

/-- The numerical `23 E T` bound with no uninstantiated probability inputs. -/
theorem main_random_upper_twenty_three {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 1 ≤ E) (hε : 0 < ε)
    (hT : 1 ≤ L * Δ / ε ^ 2)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Nrand (SublevelClass L Δ E) ε (1 / 3) ≤
      (⌊23 * E * (L * Δ / ε ^ 2)⌋₊ : ℕ∞) := by
  apply (main_random_upper hL hΔ (by linarith) hε M hM).trans
  exact ENat.coe_le_coe.mpr (Nat.le_floor (STP.sublevel_query_bound hE hT))

/-- The same unconditional bound for the paper's equivalent Hessian class. -/
theorem main_random_hessian_upper {d : ℕ} {L Δ E ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hE : 1 ≤ E) (hε : 0 < ε)
    (hT : 1 ≤ L * Δ / ε ^ 2)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Nrand (HessianSublevelClass L Δ E) ε (1 / 3) ≤
      (⌊23 * E * (L * Δ / ε ^ 2)⌋₊ : ℕ∞) := by
  rw [← sublevelClass_eq_hessianSublevelClass hL.le]
  exact main_random_upper_twenty_three hL hΔ hE hε hT M hM

/-- In the main regime, the second upper rate is `100 sqrt(2) d sqrt(E T)`. -/
theorem main_det_upper_main_regime {d : ℕ} {L Δ ε E : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (hε : 0 < ε)
    (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ L * Δ / ε ^ 2)
    (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    M.Ndet (SublevelClass L Δ E) ε ≤
      min (⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ : ℕ∞)
        (⌊100 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (E * (L * Δ / ε ^ 2))⌋₊ : ℕ∞) := by
  have hTd : L * Δ / ε ^ 2 ≤ d := by
    have hp : 0 ≤ L * Δ / ε ^ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hE hp]
  have hv := SubspaceUpper.subspace_value_upper_small_time hd hL hE hEd hε hT hTd
  refine le_min ((le_min_iff.mp (main_det_upper hd hL hε hE hEd hT M hM)).1) ?_
  rcases hM with rfl | rfl
  · exact (Ndet_linear_le_value _ ε).trans hv
  · exact hv

/-- Standard positive parameters of the public main results. -/
def MainParameters (d : ℕ) (L Δ ε E : ℝ) : Prop :=
  1 ≤ d ∧ 0 < L ∧ 0 < Δ ∧ 0 < ε ∧ 1 ≤ E ∧ E ≤ d ∧ 1 ≤ L * Δ / ε ^ 2

/-- Complete deterministic complexity statement, proved below. Every real
inequality is about a finite natural witness for the actual ENat complexity.
The extra regularity promises about hard witnesses are not asserted. -/
def main_det_statement : Prop :=
  ∀ (d : ℕ) (L Δ ε E : ℝ), MainParameters d L Δ ε E →
    ∀ M : OracleModel d, SupportedOracle M →
      ∃ n : ℕ, M.Ndet (SublevelClass L Δ E) ε = (n : ℕ∞) ∧
        d ≤ n ∧
        (n : ℝ) ≤ min (10 * (d : ℝ) * (L * Δ / ε ^ 2))
          (100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
            ((d : ℝ) + L * Δ / ε ^ 2))) ∧
        (E * (L * Δ / ε ^ 2) ≤ d →
          (d : ℝ) * min (L * Δ / ε ^ 2)
            (Real.sqrt (E * (L * Δ / ε ^ 2) /
              Real.log (Real.exp 1 + L * Δ / ε ^ 2))) / 2250 ≤ n) ∧
        ((L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E →
          (d : ℝ) * (L * Δ / ε ^ 2) / 2359296 ≤ n) ∧
        ((L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E →
          E ≤ (d : ℝ) / (L * Δ / ε ^ 2) →
          (d : ℝ) * (L * Δ / ε ^ 2) / 2250 ≤ n)

/-- A finite ENat upper bound first yields a natural complexity witness;
only then are floors and ceilings converted to real inequalities. -/
theorem main_det_verified : main_det_statement := by
  intro d L Δ ε E hp M hM
  rcases hp with ⟨hd, hL, hΔ, hε, hE, hEd, hT⟩
  have hu := main_det_upper hd hL hε hE hEd hT M hM
  have hfin : M.Ndet (SublevelClass L Δ E) ε ≠ ⊤ :=
    ne_of_lt (((le_min_iff.mp hu).1).trans_lt (ENat.coe_lt_top _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hu1 : n ≤ ⌊10 * (d : ℝ) * (L * Δ / ε ^ 2)⌋₊ := by
    apply ENat.coe_le_coe.mp
    simpa only [hn] using (le_min_iff.mp hu).1
  have hu2 : n ≤ ⌊100 * Real.sqrt ((d : ℝ) * E * (L * Δ / ε ^ 2) *
      ((d : ℝ) + L * Δ / ε ^ 2))⌋₊ := by
    apply ENat.coe_le_coe.mp
    simpa only [hn] using (le_min_iff.mp hu).2
  have hdN := main_det_dimension_lower hd hL hΔ hε hE hEd hT M hM
  rw [← hn] at hdN
  refine ⟨n, hn.symm, ENat.coe_le_coe.mp hdN, ?_, ?_, ?_, ?_⟩
  · apply le_min
    · exact (Nat.cast_le.mpr hu1).trans (Nat.floor_le (by positivity))
    · exact (Nat.cast_le.mpr hu2).trans (Nat.floor_le (by positivity))
  · intro hET
    have hl := main_det_lower hd hL hΔ hε hE hEd hT hET M hM
    rw [← hn] at hl
    exact Nat.ceil_le.mp (ENat.coe_le_coe.mp hl)
  · intro hwindow
    have hl := main_det_general_window_lower hd hL hΔ hε hE hEd hT hwindow M hM
    rw [← hn] at hl
    exact Nat.ceil_le.mp (ENat.coe_le_coe.mp hl)
  · intro hwindow hcap
    have hl := main_det_window_lower hd hL hΔ hε hE hEd hT hwindow hcap M hM
    rw [← hn] at hl
    exact Nat.ceil_le.mp (ENat.coe_le_coe.mp hl)

/-- Finite main-regime two-sided complexity for the actual Hessian class. -/
theorem main_det_hessian_finite {d : ℕ} {L Δ ε E : ℝ}
    (hp : MainParameters d L Δ ε E) (hET : E * (L * Δ / ε ^ 2) ≤ d)
    (M : OracleModel d) (hM : SupportedOracle M) :
    ∃ n : ℕ, M.Ndet (HessianSublevelClass L Δ E) ε = (n : ℕ∞) ∧
      d ≤ n ∧
      (d : ℝ) * min (L * Δ / ε ^ 2)
        (Real.sqrt (E * (L * Δ / ε ^ 2) / Real.log (Real.exp 1 + L * Δ / ε ^ 2))) /
        2250 ≤ n ∧
      (n : ℝ) ≤ min (10 * (d : ℝ) * (L * Δ / ε ^ 2))
        (100 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (E * (L * Δ / ε ^ 2))) := by
  obtain ⟨n, hn, hdn, _, hl, _, _⟩ := main_det_verified d L Δ ε E hp M hM
  rcases hp with ⟨hd, hL, hΔ, hε, hE, hEd, hT⟩
  refine ⟨n, ?_, hdn, hl hET, ?_⟩
  · rwa [← sublevelClass_eq_hessianSublevelClass hL.le]
  · have hu := main_det_upper_main_regime hd hL hε hE hEd hT hET M hM
    rw [hn] at hu
    rcases le_min_iff.mp hu with ⟨hu1, hu2⟩
    apply le_min
    · exact (Nat.cast_le.mpr (ENat.coe_le_coe.mp hu1)).trans (Nat.floor_le (by positivity))
    · exact (Nat.cast_le.mpr (ENat.coe_le_coe.mp hu2)).trans (Nat.floor_le (by positivity))

/-- UNPROVED hard-cap target with the new all-time randomized lower rate.
The Gaussian upper bound uses the jointly measurable seed/transcript model.
Sphere splitting has been proved. The adaptive-projection and oracle-simulation
arguments needed for the random lower bound remain unproved. The expected-cost model and class A are not covered. -/
def main_random_statement : Prop :=
  ∀ (d : ℕ) (L Δ ε E : ℝ), MainParameters d L Δ ε E →
    ∀ M : OracleModel d, SupportedOracle M →
      ∃ n : ℕ, M.Nrand (SublevelClass L Δ E) ε (1 / 3) = (n : ℕ∞) ∧
        (n : ℝ) ≤ 23 * E * (L * Δ / ε ^ 2) ∧
        min (d : ℝ) (E * (L * Δ / ε ^ 2)) / 12 ≤ n

/-- UNPROVED full matching-window target, including the same-oracle ratio.
The deterministic window bounds and the random upper bound are proved above.
The random lower bound remains open in the jointly measurable policy model.
Both finite costs are explicitly named. -/
def main_window_statement : Prop :=
  ∀ (d : ℕ) (L Δ ε E : ℝ), MainParameters d L Δ ε E →
    (L * Δ / ε ^ 2) * Real.log (Real.exp 1 + L * Δ / ε ^ 2) ≤ E →
    E ≤ (d : ℝ) / (L * Δ / ε ^ 2) →
    ∀ M : OracleModel d, SupportedOracle M →
      ∃ nd nr : ℕ,
        M.Ndet (SublevelClass L Δ E) ε = (nd : ℕ∞) ∧
        M.Nrand (SublevelClass L Δ E) ε (1 / 3) = (nr : ℕ∞) ∧
        0 < nr ∧
        (d : ℝ) * (L * Δ / ε ^ 2) / 2250 ≤ nd ∧
        (nd : ℝ) ≤ 10 * (d : ℝ) * (L * Δ / ε ^ 2) ∧
        E * (L * Δ / ε ^ 2) / 12 ≤ nr ∧
        (nr : ℝ) ≤ 23 * E * (L * Δ / ε ^ 2) ∧
        (d : ℝ) / (51750 * E) ≤ (nd : ℝ) / (nr : ℝ) ∧
        (nd : ℝ) / (nr : ℝ) ≤ 120 * (d : ℝ) / E

/-- UNPROVED full target corresponding to `thm:reader-unrestricted`.
Only its upper half is established by `reader_unrestricted_upper` above. -/
def reader_unrestricted_statement : Prop :=
  ∀ (d : ℕ) (L Δ ε : ℝ), 1 ≤ d → 0 < L → 0 < Δ → 0 < ε →
    1 ≤ L * Δ / ε ^ 2 →
    L * Δ / ε ^ 2 ≤ (d : ℝ) / Real.log (Real.exp 1 * (d : ℝ)) →
    ∀ M : OracleModel d, SupportedOracle M →
      ∃ n : ℕ, M.Ndet (SmoothClass L Δ) ε = (n : ℕ∞) ∧
        (d : ℝ) * (L * Δ / ε ^ 2) / 750 ≤ n ∧
        (n : ℝ) ≤ 10 * (d : ℝ) * (L * Δ / ε ^ 2)

end ExactZO.MainResults
