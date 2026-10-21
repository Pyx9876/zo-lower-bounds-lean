import ExactZO.Model
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The finite Hamming-ball step of S4's dimension-sensitive strip selection.
The weighted sign-cube sum is the binomial generating function, without any
probability or asymptotic counting premise. -/

noncomputable section
open scoped BigOperators

namespace ExactZO.SelectionHamming

abbrev SignCube (p : ℕ) := Fin p → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def signVector {p : ℕ} (x : SignCube p) : X p := (WithLp.equiv 2 (Fin p → ℝ)).symm (fun i => sign (x i))

theorem hamming_weight_product {p : ℕ} (x y : SignCube p) (q : ℝ) :
    q ^ hammingDist x y = ∏ i, if x i ≠ y i then q else 1 := by
  classical
  rw [hammingDist, ← Finset.prod_const, Finset.prod_filter]

theorem hamming_weight_sum {p : ℕ} (x : SignCube p) (q : ℝ) :
    ∑ y : SignCube p, q ^ hammingDist x y = (1 + q) ^ p := by
  classical
  simp_rw [hamming_weight_product]
  rw [← Fintype.prod_sum (fun (i : Fin p) (b : Bool) => if x i ≠ b then q else 1)]
  have hb : ∀ i : Fin p, (∑ b : Bool, if x i ≠ b then q else 1) = 1 + q := by
    intro i
    cases x i <;> simp [Fintype.sum_bool, add_comm]
  simp_rw [hb]
  simp

theorem third_pow_eq_exp (n : ℕ) :
    (1 / 3 : ℝ) ^ n = Real.exp (-(n : ℝ) * Real.log 3) := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  simp [one_div]

theorem log_hamming_constant :
    Real.log (4 / 3 : ℝ) < (7 / 8 : ℝ) * Real.log 2 - (1 / 4 : ℝ) * Real.log 3 := by
  have hpow : Real.log ((2 : ℝ) ^ 9) < Real.log ((3 : ℝ) ^ 6) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hpow
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.log_div (by norm_num) (by norm_num), hfour]
  norm_num at hpow
  linarith

/-- Every subset of a Hamming ball of radius `p/4` has fewer than
`exp ((7/8) p log 2)` elements. -/
theorem hamming_ball_card_lt {p : ℕ} (hp : 0 < p) (x : SignCube p)
    (A : Finset (SignCube p))
    (hA : ∀ y ∈ A, (hammingDist x y : ℝ) ≤ (p : ℝ) / 4) :
    (A.card : ℝ) < Real.exp ((7 / 8 : ℝ) * p * Real.log 2) := by
  classical
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hpoint : ∀ y ∈ A,
      Real.exp (-(p : ℝ) / 4 * Real.log 3) ≤ (1 / 3 : ℝ) ^ hammingDist x y := by
    intro y hy
    rw [third_pow_eq_exp]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hA y hy) hlog3]
  have hweighted : (A.card : ℝ) * Real.exp (-(p : ℝ) / 4 * Real.log 3) ≤
      (4 / 3 : ℝ) ^ p := by
    calc
      _ = ∑ _y ∈ A, Real.exp (-(p : ℝ) / 4 * Real.log 3) := by simp
      _ ≤ ∑ y ∈ A, (1 / 3 : ℝ) ^ hammingDist x y := Finset.sum_le_sum hpoint
      _ ≤ ∑ y : SignCube p, (1 / 3 : ℝ) ^ hammingDist x y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (by intros; positivity)
      _ = _ := by rw [hamming_weight_sum]; norm_num
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hstrict : (4 / 3 : ℝ) ^ p <
      Real.exp ((7 / 8 : ℝ) * p * Real.log 2) * Real.exp (-(p : ℝ) / 4 * Real.log 3) := by
    rw [← Real.exp_add, ← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3), ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_left log_hamming_constant hpR]
  exact (mul_lt_mul_iff_of_pos_right (Real.exp_pos _)).mp (hweighted.trans_lt hstrict)

/-- The large common fiber used in finite partial coloring contains two
sign vectors farther apart than one quarter of the coordinates. -/
theorem exists_far_pair {p : ℕ} (hp : 0 < p) (A : Finset (SignCube p))
    (hlarge : Real.exp ((7 / 8 : ℝ) * p * Real.log 2) < (A.card : ℝ)) :
    ∃ x ∈ A, ∃ y ∈ A, (p : ℝ) / 4 < (hammingDist x y : ℝ) := by
  classical
  have hcard : 0 < A.card := by
    have hh := (Real.exp_pos ((7 / 8 : ℝ) * p * Real.log 2)).trans hlarge
    exact_mod_cast hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  by_contra hn
  push_neg at hn
  have hsmall := hamming_ball_card_lt hp x A (hn x hx)
  exact (not_lt_of_ge hsmall.le) hlarge

theorem signVector_sub_norm_sq {p : ℕ} (x y : SignCube p) :
    ‖signVector x - signVector y‖ ^ 2 = 4 * (hammingDist x y : ℝ) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖sign (x i) - sign (y i)‖ ^ 2) = _
  simp only [Real.norm_eq_abs, sq_abs]
  have hpoint : ∀ i, (sign (x i) - sign (y i)) ^ 2 = if x i ≠ y i then (4 : ℝ) else 0 := by
    intro i
    cases x i <;> cases y i <;> norm_num [sign]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [hammingDist, mul_comm]


theorem signVector_sub_norm_gt_sqrt {p : ℕ} (x y : SignCube p)
    (hfar : (p : ℝ) / 4 < (hammingDist x y : ℝ)) :
    Real.sqrt p < ‖signVector x - signVector y‖ := by
  have hnorm := signVector_sub_norm_sq x y
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  nlinarith [norm_nonneg (signVector x - signVector y), Real.sqrt_nonneg (p : ℝ)]

end ExactZO.SelectionHamming
