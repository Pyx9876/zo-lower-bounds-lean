import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-! The numerical capacity choice for the deterministic subspace bound.
These statements concern real arithmetic and rounding only. -/
noncomputable section
set_option maxHeartbeats 600000

namespace ExactZO.SubspaceOptimize

def balance (d : ℕ) (E T : ℝ) : ℝ := (d : ℝ) * E * T / (d + T)
def scale (d : ℕ) (E T : ℝ) : ℝ := Real.sqrt ((d : ℝ) * E * T * (d + T))
def capacity (d : ℕ) (E T : ℝ) : ℕ := ⌈Real.sqrt (balance d E T)⌉₊

theorem denominator_pos {d : ℕ} {T : ℝ} (hd : 1 ≤ d) (hT : 1 ≤ T) :
    0 < (d : ℝ) + T := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem balance_lower {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hT : 1 ≤ T) : 1 / 2 ≤ balance d E T := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hT0 : 0 ≤ T := by linarith
  have hdt : (d : ℝ) ≤ d * T := by nlinarith
  have htd : T ≤ d * T := by nlinarith
  have hN : (d : ℝ) * T ≤ d * E * T := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hd0 hT0)
    nlinarith
  unfold balance
  apply (le_div_iff₀ (denominator_pos hd hT)).2
  nlinarith

theorem balance_upper {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : E ≤ d) (hT : 1 ≤ T) : balance d E T < (d : ℝ) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hN : (d : ℝ) * E * T ≤ d ^ 2 * T := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hd0.le hT0)
    nlinarith
  have hcube : 0 < (d : ℝ) ^ 2 * d := mul_pos (sq_pos_of_pos hd0) hd0
  unfold balance
  apply (div_lt_iff₀ (denominator_pos hd hT)).2
  nlinarith

theorem ceil_sqrt_le_twice {A : ℝ} (hA : 1 / 2 ≤ A) :
    (⌈Real.sqrt A⌉₊ : ℝ) ≤ 2 * Real.sqrt A := by
  have hs0 := Real.sqrt_nonneg A
  have hs2 := Real.sq_sqrt (show 0 ≤ A by linarith)
  by_cases hs : Real.sqrt A ≤ 1
  · have hc : ⌈Real.sqrt A⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hs)
    have hc' : (⌈Real.sqrt A⌉₊ : ℝ) ≤ 1 := by exact_mod_cast hc
    nlinarith
  · have hc := Nat.ceil_lt_add_one hs0
    linarith

theorem capacity_bounds {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ T) :
    1 ≤ capacity d E T ∧ capacity d E T ≤ d ∧
      Real.sqrt (balance d E T) ≤ (capacity d E T : ℝ) ∧
      (capacity d E T : ℝ) ≤ 2 * Real.sqrt (balance d E T) := by
  have hlo := balance_lower hd hE hT
  have hhi := balance_upper hd hEd hT
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hspos : 0 < Real.sqrt (balance d E T) := Real.sqrt_pos.2 (by linarith)
  have hsd : Real.sqrt (balance d E T) < d :=
    (Real.sqrt_lt' (by linarith)).2 hhi
  exact ⟨Nat.one_le_ceil_iff.mpr hspos, Nat.ceil_le.mpr hsd.le,
    Nat.le_ceil _, ceil_sqrt_le_twice hlo⟩

theorem scale_eq_denominator_mul_sqrt {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hT : 1 ≤ T) :
    scale d E T = ((d : ℝ) + T) * Real.sqrt (balance d E T) := by
  have hb := denominator_pos hd hT
  have ha : 0 ≤ balance d E T := le_trans (by norm_num) (balance_lower hd hE hT)
  have hN : 0 ≤ (d : ℝ) * E * T := by positivity
  have hprod : ((d : ℝ) + T) * (Real.sqrt (balance d E T)) ^ 2 = d * E * T := by
    rw [Real.sq_sqrt ha]
    unfold balance
    field_simp
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hb.le (Real.sqrt_nonneg _))).mp
  change (Real.sqrt ((d : ℝ) * E * T * (d + T))) ^ 2 = _
  rw [Real.sq_sqrt (mul_nonneg hN hb.le)]
  calc
    (d : ℝ) * E * T * (d + T) =
        (((d : ℝ) + T) * (Real.sqrt (balance d E T)) ^ 2) * (d + T) := by rw [hprod]
    _ = (((d : ℝ) + T) * Real.sqrt (balance d E T)) ^ 2 := by ring

theorem numerator_div_sqrt_eq_scale {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hT : 1 ≤ T) :
    (d : ℝ) * E * T / Real.sqrt (balance d E T) = scale d E T := by
  have hb := denominator_pos hd hT
  have ha : 0 < balance d E T := lt_of_lt_of_le (by norm_num) (balance_lower hd hE hT)
  have hs : 0 < Real.sqrt (balance d E T) := Real.sqrt_pos.2 ha
  rw [scale_eq_denominator_mul_sqrt hd hE hT]
  apply (div_eq_iff (ne_of_gt hs)).2
  have hsq := Real.sq_sqrt ha.le
  unfold balance at hsq
  have hmul := (eq_div_iff (ne_of_gt hb)).mp hsq
  change (Real.sqrt (balance d E T)) ^ 2 * ((d : ℝ) + T) = d * E * T at hmul
  nlinarith

theorem optimized_cost {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ T) :
    40 * (d : ℝ) * E * T / capacity d E T +
      30 * ((d : ℝ) + T) * capacity d E T ≤ 100 * scale d E T := by
  obtain ⟨_, _, hsr, hrs⟩ := capacity_bounds hd hE hEd hT
  have hb := denominator_pos hd hT
  have ha : 0 < balance d E T := lt_of_lt_of_le (by norm_num) (balance_lower hd hE hT)
  have hs : 0 < Real.sqrt (balance d E T) := Real.sqrt_pos.2 ha
  have hN : 0 ≤ (d : ℝ) * E * T := by positivity
  have hdiv := div_le_div_of_nonneg_left hN hs hsr
  rw [numerator_div_sqrt_eq_scale hd hE hT] at hdiv
  have hmul := mul_le_mul_of_nonneg_left hrs hb.le
  have hscale := scale_eq_denominator_mul_sqrt hd hE hT
  calc
    40 * (d : ℝ) * E * T / capacity d E T +
        30 * ((d : ℝ) + T) * capacity d E T =
      40 * ((d : ℝ) * E * T / capacity d E T) +
        30 * (((d : ℝ) + T) * capacity d E T) := by ring
    _ ≤ 100 * scale d E T := by nlinarith

theorem scale_le_dimension_sqrt {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hT : 1 ≤ T) (hTd : T ≤ d) :
    scale d E T ≤ Real.sqrt 2 * d * Real.sqrt (E * T) := by
  have hET : 0 ≤ E * T := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have htarget : 0 ≤ Real.sqrt 2 * d * Real.sqrt (E * T) := by positivity
  unfold scale
  apply (Real.sqrt_le_left htarget).2
  have hmono := mul_le_mul_of_nonneg_left hTd (mul_nonneg hd0 hET)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hET]
  nlinarith

theorem optimized_cost_small_time {d : ℕ} {E T : ℝ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hEd : E ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    40 * (d : ℝ) * E * T / capacity d E T +
      30 * ((d : ℝ) + T) * capacity d E T ≤
      100 * Real.sqrt 2 * d * Real.sqrt (E * T) := by
  have hcost := optimized_cost hd hE hEd hT
  have hscale := scale_le_dimension_sqrt hd hE hT hTd
  nlinarith

end ExactZO.SubspaceOptimize
