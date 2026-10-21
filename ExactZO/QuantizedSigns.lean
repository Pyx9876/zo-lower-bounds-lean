import ExactZO.SelectionEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.ExponentialBounds

/-! Finite averages and quantized sign sums for S4 direction selection. -/

noncomputable section
open scoped BigOperators
open Finset

namespace ExactZO.QuantizedSigns

def avg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

theorem avg_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

theorem avg_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg (fun x _ => h x)) (Nat.cast_nonneg _)

@[simp] theorem avg_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    avg (fun _ : Ω => c) = c := by
  simp [avg, Fintype.card_ne_zero]

theorem avg_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    avg (fun x => f x + g x) = avg f + avg g := by simp [avg, Finset.sum_add_distrib, add_div]

theorem avg_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    avg (fun x => f x * c) = avg f * c := by
  simp only [avg, ← Finset.sum_mul]
  ring

theorem avg_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [mul_comm c, avg_mul_const]

theorem avg_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (f : ι → Ω → ℝ) :
    avg (fun x => ∑ i, f i x) = ∑ i, avg (f i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]

def prob {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℝ :=
  avg (fun x => if P x then 1 else 0)

theorem prob_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    0 ≤ prob P := avg_nonneg (fun _ => by split_ifs <;> norm_num)

def signSum {p : ℕ} (a : Fin p → ℝ) (x : Fin p → Bool) : ℝ :=
  ∑ j, a j * (if x j then 1 else -1)

theorem sign_mgf {p : ℕ} (a : Fin p → ℝ) (lmb : ℝ)
    (ha : ∑ j, a j ^ 2 ≤ 1) :
    avg (fun x : Fin p → Bool => Real.exp (lmb * signSum a x)) ≤ Real.exp (lmb ^ 2 / 2) := by
  have hfactor : (∑ x : Fin p → Bool, Real.exp (lmb * signSum a x)) =
      ∏ j, (Real.exp (lmb * a j) + Real.exp (-(lmb * a j))) := by
    simp only [signSum, Finset.mul_sum, Real.exp_sum]
    rw [← Fintype.prod_sum (fun (j : Fin p) (b : Bool) =>
      Real.exp (lmb * (a j * (if b then 1 else -1))))]
    apply Finset.prod_congr rfl
    intro j _
    simp [Fintype.sum_bool, mul_assoc]
  have hcosh : ∏ j, (Real.exp (lmb * a j) + Real.exp (-(lmb * a j))) =
      (2 : ℝ) ^ p * ∏ j, Real.cosh (lmb * a j) := by
    calc
      _ = ∏ j, 2 * Real.cosh (lmb * a j) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [Real.cosh_eq]
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have havg : avg (fun x : Fin p → Bool => Real.exp (lmb * signSum a x)) =
      ∏ j, Real.cosh (lmb * a j) := by
    rw [avg, hfactor, hcosh]
    simp [Fintype.card_fun]
  rw [havg]
  calc
    _ ≤ ∏ j, Real.exp ((lmb * a j) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro j _; exact (Real.cosh_pos _).le
      · intro j _; exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (lmb ^ 2 / 2 * ∑ j, a j ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ Real.exp (lmb ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg lmb]

theorem prob_ge_of_mgf {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ)
    (hmgf : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * Y x)) ≤ Real.exp (lmb ^ 2 / 2))
    {b : ℝ} (hb : 0 ≤ b) :
    prob (fun x => b ≤ Y x) ≤ Real.exp (-(b ^ 2 / 2)) := by
  classical
  have hpoint : ∀ x, (if b ≤ Y x then (1 : ℝ) else 0) * Real.exp (b ^ 2) ≤
      Real.exp (b * Y x) := by
    intro x
    split_ifs with hx
    · simp only [one_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hx hb]
    · simpa using (Real.exp_pos (b * Y x)).le
  have hs := (avg_mono hpoint).trans (hmgf b)
  rw [avg_mul_const] at hs
  change prob (fun x => b ≤ Y x) * Real.exp (b ^ 2) ≤ _ at hs
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos (b ^ 2))).mp
  calc
    _ ≤ Real.exp (b ^ 2 / 2) := hs
    _ = Real.exp (-(b ^ 2 / 2)) * Real.exp (b ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem prob_abs_of_mgf {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ)
    (hmgf : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * Y x)) ≤ Real.exp (lmb ^ 2 / 2))
    {b : ℝ} (hb : 0 ≤ b) :
    prob (fun x => b ≤ |Y x|) ≤ 2 * Real.exp (-(b ^ 2 / 2)) := by
  classical
  have hminus : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * (-Y x))) ≤ Real.exp (lmb ^ 2 / 2) := by
    intro lmb
    simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-lmb)
  have hpos := prob_ge_of_mgf Y hmgf hb
  have hneg := prob_ge_of_mgf (fun x => -Y x) hminus hb
  have hpoint : ∀ x, (if b ≤ |Y x| then (1 : ℝ) else 0) ≤
      (if b ≤ Y x then 1 else 0) + (if b ≤ -Y x then 1 else 0) := by
    intro x
    split_ifs <;> simp_all only [le_abs, not_or] <;> norm_num at *
  have h := avg_mono hpoint
  rw [avg_add] at h
  change prob (fun x => b ≤ |Y x|) ≤ prob (fun x => b ≤ Y x) + prob (fun x => b ≤ -Y x) at h
  linarith

def quantize (t y : ℝ) : ℤ := ⌊y / (2 * t) + 1 / 2⌋

theorem quantize_same_bin {t y z : ℝ} (ht : 0 < t)
    (h : quantize t y = quantize t z) : |y - z| < 2 * t := by
  have hylo := Int.floor_le (y / (2 * t) + 1 / 2)
  have hyhi := Int.lt_floor_add_one (y / (2 * t) + 1 / 2)
  have hzlo := Int.floor_le (z / (2 * t) + 1 / 2)
  have hzhi := Int.lt_floor_add_one (z / (2 * t) + 1 / 2)
  change (quantize t y : ℝ) ≤ _ at hylo
  change _ < (quantize t y : ℝ) + 1 at hyhi
  change (quantize t z : ℝ) ≤ _ at hzlo
  change _ < (quantize t z : ℝ) + 1 at hzhi
  rw [h] at hylo hyhi
  apply abs_lt.mpr
  constructor
  · have hdiv : z / (2 * t) - y / (2 * t) < 1 := by linarith
    rw [← sub_div, div_lt_iff₀ (by positivity)] at hdiv
    linarith
  · have hdiv : y / (2 * t) - z / (2 * t) < 1 := by linarith
    rw [← sub_div, div_lt_iff₀ (by positivity)] at hdiv
    linarith

theorem quantize_tail_event {t y : ℝ} (ht : 0 < t) (k : ℕ)
    (hk : k + 1 ≤ (quantize t y).natAbs) : (2 * (k : ℝ) + 1) * t ≤ |y| := by
  have hq : (k : ℝ) + 1 ≤ |(quantize t y : ℝ)| := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ ((quantize t y).natAbs : ℝ) := by exact_mod_cast hk
    simpa only [Nat.cast_add, Nat.cast_one, Int.cast_natAbs, Int.cast_abs] using hh
  have hlo := Int.floor_le (y / (2 * t) + 1 / 2)
  have hhi := Int.lt_floor_add_one (y / (2 * t) + 1 / 2)
  change (quantize t y : ℝ) ≤ _ at hlo
  change _ < (quantize t y : ℝ) + 1 at hhi
  rcases le_abs.mp hq with hq | hq
  · have hdiv : (2 * (k : ℝ) + 1) / 2 ≤ y / (2 * t) := by linarith
    rw [le_div_iff₀ (by positivity)] at hdiv
    have hpos : (2 * (k : ℝ) + 1) * t ≤ y := by nlinarith
    exact hpos.trans (le_abs_self y)
  · have hdiv : y / (2 * t) < -(2 * (k : ℝ) + 1) / 2 := by linarith
    rw [div_lt_iff₀ (by positivity)] at hdiv
    have hneg : (2 * (k : ℝ) + 1) * t ≤ -y := by nlinarith
    exact hneg.trans (neg_le_abs y)

theorem quantize_prob_tail {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ)
    (hmgf : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * Y x)) ≤ Real.exp (lmb ^ 2 / 2))
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    prob (fun x => k + 1 ≤ (quantize t (Y x)).natAbs) ≤
      2 * Real.exp (-(t ^ 2 / 2)) ^ (k + 1) := by
  classical
  have hevent : prob (fun x => k + 1 ≤ (quantize t (Y x)).natAbs) ≤
      prob (fun x => (2 * (k : ℝ) + 1) * t ≤ |Y x|) := by
    apply avg_mono
    intro x
    split_ifs with hk hy
    · norm_num
    · exact False.elim (hy (quantize_tail_event ht k hk))
    · norm_num
    · norm_num
  have htail := prob_abs_of_mgf Y hmgf
    (show 0 ≤ (2 * (k : ℝ) + 1) * t by positivity)
  apply hevent.trans (htail.trans _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcoef : (k : ℝ) + 1 ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
  push_cast
  nlinarith

theorem avg_nat_eq_sum_tails {Ω : Type*} [Fintype Ω] (K : Ω → ℕ)
    (N : ℕ) (hN : ∀ x, K x ≤ N) :
    avg (fun x => (K x : ℝ)) = ∑ k ∈ range N, prob (fun x => k + 1 ≤ K x) := by
  classical
  have hpoint : ∀ x, (K x : ℝ) = ∑ k ∈ range N, if k + 1 ≤ K x then (1 : ℝ) else 0 := by
    intro x
    have hxN := hN x
    have hf : (range N).filter (fun k => k + 1 ≤ K x) = range (K x) := by
      ext k
      simp only [mem_filter, mem_range]
      omega
    rw [← Finset.sum_filter, hf]
    simp
  simp only [prob, avg]
  simp_rw [hpoint]
  rw [Finset.sum_comm, Finset.sum_div]

theorem geometric_succ_sum_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ k ∈ range N, q ^ (k + 1) ≤ q / (1 - q) := by
  have hid := geom_sum_mul_neg q N
  have hrewrite : (∑ k ∈ range N, q ^ (k + 1)) = q * ∑ k ∈ range N, q ^ k := by
    simp_rw [pow_succ, mul_comm _ q]
    rw [Finset.mul_sum]
  rw [hrewrite]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  have hpow := pow_nonneg hq N
  nlinarith [mul_nonneg hq hpow]

theorem quantize_avg_natAbs {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ)
    (hmgf : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * Y x)) ≤ Real.exp (lmb ^ 2 / 2))
    {t : ℝ} (ht : 0 < t) (hq : Real.exp (-(t ^ 2 / 2)) ≤ 1 / 2)
    (N : ℕ) (hN : ∀ x, (quantize t (Y x)).natAbs ≤ N) :
    avg (fun x => ((quantize t (Y x)).natAbs : ℝ)) ≤ 4 * Real.exp (-(t ^ 2 / 2)) := by
  let q := Real.exp (-(t ^ 2 / 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by dsimp [q]; linarith
  calc
    _ = ∑ k ∈ range N, prob (fun x => k + 1 ≤ (quantize t (Y x)).natAbs) :=
      avg_nat_eq_sum_tails _ N hN
    _ ≤ ∑ k ∈ range N, 2 * q ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro k _
      exact quantize_prob_tail Y hmgf ht k
    _ = 2 * ∑ k ∈ range N, q ^ (k + 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (q / (1 - q)) :=
      mul_le_mul_of_nonneg_left (geometric_succ_sum_le hq0.le hq1 N) (by norm_num)
    _ ≤ 4 * q := by
      apply (mul_le_mul_iff_of_pos_right (sub_pos.mpr hq1)).mp
      have hcancel : q / (1 - q) * (1 - q) = q := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hq1))
      dsimp [q] at *
      nlinarith

/-- A finite coding of the integers of absolute value at most `N`. -/
def boundedCode {N : ℕ} (k : ℤ) (hk : k.natAbs ≤ N) : Option (Bool × Fin N) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact none
      | succ n => exact some (true, ⟨n, by simpa using hk⟩)
  | negSucc n => exact some (false, ⟨n, by simpa using hk⟩)

def decodeCode {N : ℕ} : Option (Bool × Fin N) → ℤ
  | none => 0
  | some (b, k) => if b then (k.val : ℤ) + 1 else -((k.val : ℤ) + 1)

theorem decode_boundedCode {N : ℕ} (k : ℤ) (hk : k.natAbs ≤ N) :
    decodeCode (boundedCode k hk) = k := by
  cases k with
  | ofNat n => cases n <;> simp [boundedCode, decodeCode]
  | negSucc n => simp [boundedCode, decodeCode, Int.negSucc_eq]

/-- The geometric Gibbs reference is a finite variant of the paper's
quadratic Gibbs reference. Its first absolute moment gives the same `6δ`
entropy estimate and therefore the identical selection constant 9. -/
def refWeight (a : ℝ) {N : ℕ} : Option (Bool × Fin N) → ℝ
  | none => 1
  | some (_, k) => Real.exp (-(a / 2) * (k.val + 1 : ℕ))

def refMass (a : ℝ) {N : ℕ} (k : Option (Bool × Fin N)) : ℝ :=
  refWeight a k / (1 + 4 * Real.exp (-(a / 2)))

theorem refWeight_pos (a : ℝ) {N : ℕ} (k : Option (Bool × Fin N)) :
    0 < refWeight a k := by
  cases k with
  | none => norm_num [refWeight]
  | some k => exact Real.exp_pos _

theorem refMass_pos (a : ℝ) {N : ℕ} (k : Option (Bool × Fin N)) :
    0 < refMass a k := div_pos (refWeight_pos a k) (by positivity)

theorem refWeight_sum_le {a : ℝ} (hδ : Real.exp (-(a / 2)) ≤ 1 / 2) (N : ℕ) :
    (∑ k : Option (Bool × Fin N), refWeight a k) ≤ 1 + 4 * Real.exp (-(a / 2)) := by
  let δ := Real.exp (-(a / 2))
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hsum : (∑ k : Option (Bool × Fin N), refWeight a k) =
      1 + 2 * ∑ j ∈ range N, δ ^ (j + 1) := by
    simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, refWeight]
    simp_rw [mul_comm (-(a / 2)), Real.exp_nat_mul]
    have hfin : (∑ x : Fin N, Real.exp (-(a / 2)) ^ (x.val + 1)) =
        ∑ j ∈ range N, Real.exp (-(a / 2)) ^ (j + 1) :=
      Fin.sum_univ_eq_sum_range (fun j => Real.exp (-(a / 2)) ^ (j + 1)) N
    rw [hfin]
    dsimp [δ]
    ring
  rw [hsum]
  have hgeom := geometric_succ_sum_le hδ0.le hδ1 N
  have hfrac : δ / (1 - δ) ≤ 2 * δ := by
    apply (div_le_iff₀ (sub_pos.mpr hδ1)).mpr
    dsimp [δ] at *
    nlinarith
  linarith

theorem refMass_sum_le_one {a : ℝ} (hδ : Real.exp (-(a / 2)) ≤ 1 / 2) (N : ℕ) :
    ∑ k : Option (Bool × Fin N), refMass a k ≤ 1 := by
  simp only [refMass, ← Finset.sum_div]
  apply (div_le_one (by positivity : 0 < 1 + 4 * Real.exp (-(a / 2)))).mpr
  exact refWeight_sum_le hδ N

theorem refMass_cost_code {a : ℝ} {N : ℕ} (k : ℤ) (hk : k.natAbs ≤ N) :
    -Real.log (refMass a (boundedCode k hk)) =
      Real.log (1 + 4 * Real.exp (-(a / 2))) + (a / 2) * (k.natAbs : ℝ) := by
  rw [refMass, Real.log_div (ne_of_gt (refWeight_pos _ _)) (by positivity)]
  cases k with
  | ofNat n =>
      have hn : (Int.ofNat n).natAbs = n := rfl
      rw [hn]
      cases n <;> simp [boundedCode, refWeight, Real.log_exp]
  | negSucc n => simp [boundedCode, refWeight, Real.log_exp]

theorem a_mul_exp_neg_half_le_one {a : ℝ} (ha : 0 ≤ a) :
    a * Real.exp (-(a / 2)) ≤ 1 := by
  have ht := Real.quadratic_le_exp_of_nonneg (show 0 ≤ a / 2 by linarith)
  have hle : a ≤ Real.exp (a / 2) := by nlinarith [sq_nonneg (a - 2)]
  rw [Real.exp_neg]
  exact (mul_inv_le_iff₀ (Real.exp_pos (a / 2))).mpr (by simpa using hle)

theorem quantize_reference_cost {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Ω → ℝ)
    (hmgf : ∀ lmb : ℝ, avg (fun x => Real.exp (lmb * Y x)) ≤ Real.exp (lmb ^ 2 / 2))
    {t : ℝ} (ht : 0 < t) (hδ : Real.exp (-(t ^ 2 / 4)) ≤ 1 / 2)
    (N : ℕ) (hN : ∀ x, (quantize t (Y x)).natAbs ≤ N) :
    avg (fun x => -Real.log (refMass (t ^ 2 / 2)
      (boundedCode (quantize t (Y x)) (hN x)))) ≤ 6 * Real.exp (-(t ^ 2 / 4)) := by
  let a := t ^ 2 / 2
  let δ := Real.exp (-(t ^ 2 / 4))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have heq : Real.exp (-(a / 2)) = δ := by dsimp [a, δ]; congr 1; ring
  have hq : Real.exp (-(t ^ 2 / 2)) ≤ 1 / 2 := by
    apply le_trans _ hδ
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg t]
  have hm := quantize_avg_natAbs Y hmgf ht hq N hN
  have hlog : Real.log (1 + 4 * δ) ≤ 4 * δ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 4 * δ by dsimp [δ]; positivity)
    linarith
  have hcost : avg (fun x => -Real.log (refMass (t ^ 2 / 2)
      (boundedCode (quantize t (Y x)) (hN x)))) =
      Real.log (1 + 4 * δ) + (a / 2) * avg (fun x => ((quantize t (Y x)).natAbs : ℝ)) := by
    simp_rw [refMass_cost_code]
    rw [avg_add, avg_const, avg_const_mul]
    rw [heq]
  rw [hcost]
  have hae := a_mul_exp_neg_half_le_one ha
  rw [heq] at hae
  have hexp : Real.exp (-a) = δ * δ := by
    rw [← heq, ← Real.exp_add]
    congr 1
    ring
  change avg (fun x => ((quantize t (Y x)).natAbs : ℝ)) ≤ 4 * Real.exp (-a) at hm
  rw [hexp] at hm
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ a / 2 by linarith)
  have hδ0 : 0 ≤ δ := (Real.exp_pos _).le
  have hmul2 := mul_le_mul_of_nonneg_right hae hδ0
  change _ ≤ 6 * δ
  nlinarith

end ExactZO.QuantizedSigns
