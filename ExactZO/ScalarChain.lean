import ExactZO.Model
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The explicit piecewise scalar functions of Appendix A, with their actual
first derivatives. The finite chain below uses these functions directly. -/

noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

namespace ExactZO.ScalarChain

def phi (t : ℝ) : ℝ :=
  if t ≤ -(5 / 4 : ℝ) then 0 else
  if t < -1 then 2 * (t + 5 / 4) ^ 2 else
  if t ≤ 1 then t + 9 / 8 else
  if t < 5 / 4 then 9 / 4 - 2 * (5 / 4 - t) ^ 2 else 9 / 4

def psi (t : ℝ) : ℝ :=
  if t ≤ (1 / 2 : ℝ) then 0 else
  if t ≤ 3 / 4 then 8 * (t - 1 / 2) ^ 2 else
  if t < 1 then 1 - 8 * (1 - t) ^ 2 else 1

def phiD (t : ℝ) : ℝ :=
  if t ≤ -(5 / 4 : ℝ) then 0 else
  if t < -1 then 4 * (t + 5 / 4) else
  if t ≤ 1 then 1 else
  if t < 5 / 4 then 4 * (5 / 4 - t) else 0

def psiD (t : ℝ) : ℝ :=
  if t ≤ (1 / 2 : ℝ) then 0 else
  if t ≤ 3 / 4 then 16 * (t - 1 / 2) else
  if t < 1 then 16 * (1 - t) else 0

private def hinge (t : ℝ) : ℝ := if t ≤ 0 then 0 else t ^ 2

private theorem hinge_hasDerivAt (t : ℝ) :
    HasDerivAt hinge (2 * max 0 t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [max_eq_left ht.le, mul_zero]
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with x hx
    simp [hinge, le_of_lt (show x < 0 from hx)]
  · have hleft : HasDerivWithinAt hinge 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun x hx => by simp only [hinge, if_pos (show x ≤ 0 from hx)]) (by simp [hinge])
    have hright : HasDerivWithinAt hinge 0 (Ici 0) 0 := by
      have hs : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).pow 2
      apply hs.hasDerivWithinAt.congr
      · intro x hx
        unfold hinge
        split_ifs with h
        · have : x = 0 := le_antisymm h hx
          simp [this]
        · rfl
      · simp [hinge]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, max_self, mul_zero] using
      hleft.union hright
  · rw [max_eq_right ht.le]
    apply ((hasDerivAt_id t).pow 2).congr_deriv (by simp) |>.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    simp [hinge, not_le.mpr (show 0 < x from hx)]

private theorem phi_hinge (t : ℝ) :
    phi t = 2 * (hinge (t + 5 / 4) - hinge (t + 1) -
      hinge (t - 1) + hinge (t - 5 / 4)) := by
  unfold phi hinge
  split_ifs <;> first | (exfalso; linarith) | (ring_nf <;> nlinarith)

private theorem psi_hinge (t : ℝ) :
    psi t = 8 * (hinge (t - 1 / 2) - 2 * hinge (t - 3 / 4) + hinge (t - 1)) := by
  unfold psi hinge
  split_ifs <;> first | (exfalso; linarith) | (ring_nf <;> nlinarith)

private theorem phiD_max (t : ℝ) :
    phiD t = 4 * (max 0 (t + 5 / 4) - max 0 (t + 1) -
      max 0 (t - 1) + max 0 (t - 5 / 4)) := by
  unfold phiD
  simp only [max_def]
  split_ifs <;> linarith

private theorem psiD_max (t : ℝ) :
    psiD t = 16 * (max 0 (t - 1 / 2) - 2 * max 0 (t - 3 / 4) + max 0 (t - 1)) := by
  unfold psiD
  simp only [max_def]
  split_ifs <;> linarith

theorem phi_hasDerivAt (t : ℝ) : HasDerivAt phi (phiD t) t := by
  have hc (a : ℝ) : HasDerivAt (fun x => hinge (x + a)) (2 * max 0 (t + a)) t := by
    simpa using (hinge_hasDerivAt (t + a)).comp t ((hasDerivAt_id t).add_const a)
  have hh := (((hc (5 / 4)).sub (hc 1)).sub (hc (-1))).add (hc (-(5 / 4)))
  convert hh.const_mul 2 using 1
  · ext x
    simpa only [sub_eq_add_neg] using phi_hinge x
  · rw [phiD_max]
    simp only [sub_eq_add_neg]
    ring

theorem psi_hasDerivAt (t : ℝ) : HasDerivAt psi (psiD t) t := by
  have hc (a : ℝ) : HasDerivAt (fun x => hinge (x - a)) (2 * max 0 (t - a)) t := by
    simpa using (hinge_hasDerivAt (t - a)).comp t ((hasDerivAt_id t).sub_const a)
  have hh := ((hc (1 / 2)).sub ((hc (3 / 4)).const_mul 2)).add (hc 1)
  convert hh.const_mul 8 using 1
  · ext x
    exact psi_hinge x
  · rw [psiD_max]
    ring

@[simp] theorem deriv_phi (t : ℝ) : deriv phi t = phiD t := (phi_hasDerivAt t).deriv
@[simp] theorem deriv_psi (t : ℝ) : deriv psi t = psiD t := (psi_hasDerivAt t).deriv

theorem phi_bounds (t : ℝ) : 0 ≤ phi t ∧ phi t ≤ 9 / 4 := by
  unfold phi
  split_ifs <;> constructor <;> nlinarith [sq_nonneg (t + 5 / 4), sq_nonneg (5 / 4 - t)]

theorem psi_bounds (t : ℝ) : 0 ≤ psi t ∧ psi t ≤ 1 := by
  unfold psi
  split_ifs <;> constructor <;> nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (1 - t)]

theorem phiD_bounds (t : ℝ) : 0 ≤ phiD t ∧ phiD t ≤ 1 := by
  unfold phiD
  split_ifs <;> constructor <;> linarith

theorem psiD_bounds (t : ℝ) : 0 ≤ psiD t ∧ psiD t ≤ 4 := by
  unfold psiD
  split_ifs <;> constructor <;> linarith

@[simp] theorem phi_zero : phi 0 = 9 / 8 := by norm_num [phi]
@[simp] theorem psi_zero : psi 0 = 0 := by norm_num [psi]
@[simp] theorem phiD_zero : phiD 0 = 1 := by norm_num [phiD]
@[simp] theorem psiD_zero : psiD 0 = 0 := by norm_num [psiD]

theorem phiD_even (t : ℝ) : phiD (-t) = phiD t := by
  unfold phiD
  split_ifs <;> linarith

theorem phiD_eq_one {t : ℝ} (ht : |t| ≤ 1) : phiD t = 1 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp [phiD, show ¬t ≤ -(5 / 4 : ℝ) by linarith, not_lt.mpr hl, hu]

theorem phiD_support {t : ℝ} (ht : 5 / 4 ≤ |t|) : phiD t = 0 := by
  rw [le_abs] at ht
  unfold phiD
  rcases ht with ht | ht <;> split_ifs <;> linarith

theorem psi_flat {t : ℝ} (ht : t ≤ 1 / 2) : psi t = 0 := by simp only [psi, if_pos ht]
theorem psiD_flat {t : ℝ} (ht : t ≤ 1 / 2) : psiD t = 0 := by simp only [psiD, if_pos ht]
theorem psi_one {t : ℝ} (ht : 1 ≤ t) : psi t = 1 := by
  rw [psi, if_neg (show ¬t ≤ (1 / 2 : ℝ) by linarith),
    if_neg (show ¬t ≤ (3 / 4 : ℝ) by linarith), if_neg (not_lt.mpr ht)]

theorem psiD_support {t : ℝ} (ht : 5 / 4 ≤ |t|) : psiD t = 0 ∧ psiD (-t) = 0 := by
  rw [le_abs] at ht
  unfold psiD
  rcases ht with ht | ht <;> split_ifs <;> constructor <;> linarith

theorem phiD_continuous : Continuous phiD := by
  simp_rw [funext phiD_max]
  fun_prop

theorem psiD_continuous : Continuous psiD := by
  simp_rw [funext psiD_max]
  fun_prop

theorem phi_contDiff : ContDiff ℝ 1 phi := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun t => (phi_hasDerivAt t).differentiableAt,
    by simpa only [show deriv phi = phiD from funext deriv_phi] using phiD_continuous⟩

theorem psi_contDiff : ContDiff ℝ 1 psi := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun t => (psi_hasDerivAt t).differentiableAt,
    by simpa only [show deriv psi = psiD from funext deriv_psi] using psiD_continuous⟩

theorem psi_signed_sum_bounds (t : ℝ) : 0 ≤ psi (-t) + psi t ∧ psi (-t) + psi t ≤ 1 := by
  have hp := psi_bounds t
  have hn := psi_bounds (-t)
  constructor
  · linarith
  · rcases le_total t 0 with ht | ht
    · rw [psi_flat (show t ≤ 1 / 2 by linarith)]
      linarith
    · rw [psi_flat (show -t ≤ 1 / 2 by linarith)]
      linarith

theorem psi_signed_sum_one {t : ℝ} (ht : 1 ≤ |t|) : psi (-t) + psi t = 1 := by
  rw [le_abs] at ht
  rcases ht with ht | ht
  · rw [psi_one ht, psi_flat (show -t ≤ 1 / 2 by linarith)]
    ring
  · rw [psi_one (show 1 ≤ -t by linarith), psi_flat (show t ≤ 1 / 2 by linarith)]
    ring

theorem psiD_signed_sum_bounds (t : ℝ) :
    0 ≤ psiD (-t) + psiD t ∧ psiD (-t) + psiD t ≤ 4 := by
  have hp := psiD_bounds t
  have hn := psiD_bounds (-t)
  constructor
  · linarith
  · rcases le_total t 0 with ht | ht
    · rw [psiD_flat (show t ≤ 1 / 2 by linarith)]
      linarith
    · rw [psiD_flat (show -t ≤ 1 / 2 by linarith)]
      linarith

theorem phiD_weighted (t : ℝ) : |t * phiD t| ≤ 1 := by
  unfold phiD
  split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith

theorem psiD_weighted (t : ℝ) : |t * psiD t| ≤ 3 := by
  unfold psiD
  split_ifs <;> rw [abs_le] <;> constructor <;> nlinarith

def link (a b : ℝ) : ℝ := psi (-a) * phi (-b) - psi a * phi b

def outgoing (a b : ℝ) : ℝ := psiD (-a) * phi (-b) + psiD a * phi b

def incoming (a b : ℝ) : ℝ := (psi (-a) + psi a) * phiD b

theorem link_bounds (a b : ℝ) : -(9 / 4 : ℝ) ≤ link a b ∧ link a b ≤ 9 / 4 := by
  have h₁ := mul_nonneg (psi_bounds (-a)).1 (phi_bounds (-b)).1
  have h₂ := mul_nonneg (psi_bounds a).1 (phi_bounds b).1
  have h₃ := mul_le_mul (psi_bounds (-a)).2 (phi_bounds (-b)).2
    (phi_bounds (-b)).1 (by norm_num : (0 : ℝ) ≤ 1)
  have h₄ := mul_le_mul (psi_bounds a).2 (phi_bounds b).2
    (phi_bounds b).1 (by norm_num : (0 : ℝ) ≤ 1)
  unfold link
  constructor <;> nlinarith

theorem incoming_bounds (a b : ℝ) : 0 ≤ incoming a b ∧ incoming a b ≤ 1 := by
  exact ⟨mul_nonneg (psi_signed_sum_bounds a).1 (phiD_bounds b).1,
    by simpa [incoming] using (mul_le_mul (psi_signed_sum_bounds a).2 (phiD_bounds b).2
      (phiD_bounds b).1 (by norm_num : (0 : ℝ) ≤ 1))⟩

theorem outgoing_bounds (a b : ℝ) : 0 ≤ outgoing a b ∧ outgoing a b ≤ 9 := by
  have h₁ := mul_nonneg (psiD_bounds (-a)).1 (phi_bounds (-b)).1
  have h₂ := mul_nonneg (psiD_bounds a).1 (phi_bounds b).1
  have h₃ := mul_le_mul_of_nonneg_left (phi_bounds (-b)).2 (psiD_bounds (-a)).1
  have h₄ := mul_le_mul_of_nonneg_left (phi_bounds b).2 (psiD_bounds a).1
  have hs := (psiD_signed_sum_bounds a).2
  unfold outgoing
  constructor <;> nlinarith

theorem link_hasDerivAt_left (a b : ℝ) : HasDerivAt (fun x => link x b) (-outgoing a b) a := by
  have hn := ((psi_hasDerivAt (-a)).comp a (hasDerivAt_id a).neg).mul_const (phi (-b))
  have hp := (psi_hasDerivAt a).mul_const (phi b)
  convert hn.sub hp using 1
  simp only [outgoing, mul_neg, mul_one, neg_mul]
  ring

theorem link_hasDerivAt_right (a b : ℝ) : HasDerivAt (link a) (-incoming a b) b := by
  have hn := ((phi_hasDerivAt (-b)).comp b (hasDerivAt_id b).neg).const_mul (psi (-a))
  have hp := (phi_hasDerivAt b).const_mul (psi a)
  convert hn.sub hp using 1
  simp only [incoming, phiD_even, mul_neg, mul_one]
  ring

theorem phiD_lipschitz (x y : ℝ) : |phiD x - phiD y| ≤ 4 * |x - y| := by
  unfold phiD
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem psiD_lipschitz (x y : ℝ) : |psiD x - psiD y| ≤ 16 * |x - y| := by
  unfold psiD
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

@[simp] theorem link_zero_left (b : ℝ) : link 0 b = 0 := by simp [link]
@[simp] theorem link_zero_right (a : ℝ) : link a 0 = 9 / 8 * (psi (-a) - psi a) := by
  simp [link]
  ring

theorem link_flat_left {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) : link a b = 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  simp only [link, psi_flat hu, psi_flat (show -a ≤ 1 / 2 by linarith), zero_mul, sub_zero]

def links (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | b :: tail => link a b + links b tail

def chain : List ℝ → ℝ
  | [] => 0
  | a :: tail => -phi a + links a tail

theorem links_lower (a : ℝ) (ys : List ℝ) : -(9 / 4 : ℝ) * ys.length ≤ links a ys := by
  induction ys generalizing a with
  | nil => simp [links]
  | cons b ys ih =>
    simp only [links, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hb := (link_bounds a b).1
    have hi := ih b
    linarith

theorem links_upper (a : ℝ) (ys : List ℝ) : links a ys ≤ (9 / 4 : ℝ) * ys.length := by
  induction ys generalizing a with
  | nil => simp [links]
  | cons b ys ih =>
    simp only [links, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hb := (link_bounds a b).2
    have hi := ih b
    linarith

theorem chain_lower (ys : List ℝ) : -(9 / 4 : ℝ) * ys.length ≤ chain ys := by
  cases ys with
  | nil => simp [chain]
  | cons a ys =>
    simp only [chain, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hp := (phi_bounds a).2
    have hl := links_lower a ys
    linarith

theorem chain_upper (ys : List ℝ) : chain ys ≤ (9 / 4 : ℝ) * ys.length := by
  cases ys with
  | nil => simp [chain]
  | cons a ys =>
    simp only [chain, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hp := (phi_bounds a).1
    have hl := links_upper a ys
    linarith

@[simp] theorem links_zero_replicate (n : ℕ) : links 0 (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [links]
  | succ n ih => simp [List.replicate_succ, links, ih]

@[simp] theorem chain_zero_replicate (n : ℕ) : chain (List.replicate (n + 1) 0) = -9 / 8 := by
  simp [List.replicate_succ, chain]
  ring

theorem chain_gap (n : ℕ) (ys : List ℝ) (hlen : ys.length = n + 1) :
    chain (List.replicate (n + 1) 0) - chain ys ≤ (9 / 4 : ℝ) * (n + 1 - 1 / 2) := by
  have hl := chain_lower ys
  rw [hlen] at hl
  simp only [chain_zero_replicate, Nat.cast_add, Nat.cast_one] at *
  linarith

theorem links_flat (a : ℝ) (ha : |a| ≤ 1 / 2) (ys : List ℝ)
    (hy : ∀ b ∈ ys, |b| ≤ 1 / 2) : links a ys = 0 := by
  induction ys generalizing a with
  | nil => rfl
  | cons b ys ih =>
    rw [links, link_flat_left ha, ih b (hy b (by simp))]
    · ring
    · intro c hc
      exact hy c (by simp [hc])

theorem links_prefix (a : ℝ) (pref tail : List ℝ)
    (htail : ∀ b ∈ tail, |b| ≤ 1 / 2) :
    links a (pref ++ 0 :: tail) = links a (pref ++ [0]) := by
  induction pref generalizing a with
  | nil => simp only [List.nil_append, links, links_flat 0 (by norm_num) tail htail, add_zero]
  | cons b pref ih => simp only [List.cons_append, links, ih]

theorem chain_prefix (pref tail : List ℝ)
    (htail : ∀ b ∈ tail, |b| ≤ 1 / 2) :
    chain (pref ++ 0 :: tail) = chain (pref ++ [0]) := by
  cases pref with
  | nil => simp only [List.nil_append, chain, links_flat 0 (by norm_num) tail htail, links, add_zero]
  | cons a pref => simp only [List.cons_append, chain, links_prefix a pref tail htail]

section Differential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem outgoing_flat {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) : outgoing a b = 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  simp only [outgoing, psiD_flat hu, psiD_flat (show -a ≤ 1 / 2 by linarith),
    zero_mul, add_zero]

theorem incoming_flat {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) : incoming a b = 0 := by
  obtain ⟨hl, hu⟩ := abs_le.mp ha
  simp only [incoming, psi_flat hu, psi_flat (show -a ≤ 1 / 2 by linarith),
    zero_add, zero_mul]

def linkDifferential (a b : E →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℝ :=
  (-outgoing (a x) (b x)) • a + (-incoming (a x) (b x)) • b

theorem link_comp_hasFDerivAt (a b : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y => link (a y) (b y)) (linkDifferential a b x) x := by
  have pa := (psi_hasDerivAt (a x)).comp_hasFDerivAt x a.hasFDerivAt
  have na := (psi_hasDerivAt (-a x)).comp_hasFDerivAt x a.hasFDerivAt.neg
  have pb := (phi_hasDerivAt (b x)).comp_hasFDerivAt x b.hasFDerivAt
  have nb := (phi_hasDerivAt (-b x)).comp_hasFDerivAt x b.hasFDerivAt.neg
  convert (na.mul nb).sub (pa.mul pb) using 1
  ext v
  simp only [linkDifferential, outgoing, incoming, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      Function.comp_apply, smul_eq_mul, phiD_even]
  ring

def linksDifferential (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x : E) : E →L[ℝ] ℝ :=
  match coords with
  | [] => 0
  | b :: tail => linkDifferential a b x + linksDifferential b tail x

def chainDifferential (coords : List (E →L[ℝ] ℝ)) (x : E) : E →L[ℝ] ℝ :=
  match coords with
  | [] => 0
  | a :: tail => -(phiD (a x) • a) + linksDifferential a tail x

theorem links_comp_hasFDerivAt (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x : E) :
    HasFDerivAt (fun y => links (a y) (coords.map (fun c => c y)))
      (linksDifferential a coords x) x := by
  induction coords generalizing a with
  | nil => exact hasFDerivAt_const 0 x
  | cons b tail ih => exact (link_comp_hasFDerivAt a b x).add (ih b)

theorem chain_comp_hasFDerivAt (coords : List (E →L[ℝ] ℝ)) (x : E) :
    HasFDerivAt (fun y => chain (coords.map (fun c => c y))) (chainDifferential coords x) x := by
  cases coords with
  | nil => exact hasFDerivAt_const 0 x
  | cons a tail =>
    exact ((phi_hasDerivAt (a x)).comp_hasFDerivAt x a.hasFDerivAt).neg.add
      (links_comp_hasFDerivAt a tail x)
theorem linkDifferential_flat (a b : E →L[ℝ] ℝ) (x : E) (ha : |a x| ≤ 1 / 2) :
    linkDifferential a b x = 0 := by
  simp only [linkDifferential, outgoing_flat ha, incoming_flat ha, neg_zero, zero_smul, add_zero]

theorem linksDifferential_flat (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x : E)
    (ha : |a x| ≤ 1 / 2) (hc : ∀ c ∈ coords, |c x| ≤ 1 / 2) :
    linksDifferential a coords x = 0 := by
  induction coords generalizing a with
  | nil => rfl
  | cons b tail ih =>
    rw [linksDifferential, linkDifferential_flat a b x ha,
      ih b (hc b (by simp)) (fun c h => hc c (by simp [h])), zero_add]

theorem linksDifferential_prefix (a u : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x : E) (hu : |u x| ≤ 1 / 2)
    (ht : ∀ c ∈ tail, |c x| ≤ 1 / 2) :
    linksDifferential a (pref ++ u :: tail) x = linksDifferential a (pref ++ [u]) x := by
  induction pref generalizing a with
  | nil => simp only [List.nil_append, linksDifferential,
      linksDifferential_flat u tail x hu ht, add_zero]
  | cons b pref ih => simp only [List.cons_append, linksDifferential, ih]

theorem chainDifferential_prefix (u : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x : E) (hu : |u x| ≤ 1 / 2)
    (ht : ∀ c ∈ tail, |c x| ≤ 1 / 2) :
    chainDifferential (pref ++ u :: tail) x = chainDifferential (pref ++ [u]) x := by
  cases pref with
  | nil => simp only [List.nil_append, chainDifferential,
      linksDifferential_flat u tail x hu ht, linksDifferential, add_zero]
  | cons a pref => simp only [List.cons_append, chainDifferential,
      linksDifferential_prefix a u pref tail x hu ht]

theorem linksDifferential_nonpos (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x v : E)
    (ha : 0 ≤ a v) (hc : ∀ c ∈ coords, 0 ≤ c v) : linksDifferential a coords x v ≤ 0 := by
  induction coords generalizing a with
  | nil => simp [linksDifferential]
  | cons b tail ih =>
    have h₁ := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (outgoing_bounds (a x) (b x)).1) ha
    have h₂ := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (incoming_bounds (a x) (b x)).1)
      (hc b (by simp))
    have hi := ih b (hc b (by simp)) (fun c h => hc c (by simp [h]))
    simp only [linksDifferential, linkDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    linarith

theorem chainDifferential_nonpos (coords : List (E →L[ℝ] ℝ)) (x v : E)
    (hc : ∀ c ∈ coords, 0 ≤ c v) : chainDifferential coords x v ≤ 0 := by
  cases coords with
  | nil => simp [chainDifferential]
  | cons a tail =>
    have h₁ := mul_nonneg (phiD_bounds (a x)).1 (hc a (by simp))
    have h₂ := linksDifferential_nonpos a tail x v (hc a (by simp))
      (fun c h => hc c (by simp [h]))
    simp only [chainDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linarith
theorem linksDifferential_support (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x v : E)
    (ha : a v ≠ 0 → 5 / 4 ≤ |a x|)
    (hc : ∀ c ∈ coords, c v ≠ 0 → 5 / 4 ≤ |c x|) :
    linksDifferential a coords x v = 0 := by
  induction coords generalizing a with
  | nil => rfl
  | cons b tail ih =>
    have hb := hc b (by simp)
    have ho : outgoing (a x) (b x) * a v = 0 := by
      by_cases hz : a v = 0
      · simp [hz]
      · obtain ⟨hp, hn⟩ := psiD_support (ha hz)
        simp [outgoing, hp, hn]
    have hi : incoming (a x) (b x) * b v = 0 := by
      by_cases hz : b v = 0
      · simp [hz]
      · simp [incoming, phiD_support (hb hz)]
    have ht := ih b hb (fun c h => hc c (by simp [h]))
    simp only [linksDifferential, linkDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul, ho, hi, neg_zero, ht, add_zero]

theorem chainDifferential_support (coords : List (E →L[ℝ] ℝ)) (x v : E)
    (hc : ∀ c ∈ coords, c v ≠ 0 → 5 / 4 ≤ |c x|) : chainDifferential coords x v = 0 := by
  cases coords with
  | nil => rfl
  | cons a tail =>
    have ha := hc a (by simp)
    have hh : phiD (a x) * a v = 0 := by
      by_cases hz : a v = 0
      · simp [hz]
      · simp [phiD_support (ha hz)]
    have ht := linksDifferential_support a tail x v ha (fun c h => hc c (by simp [h]))
    simp only [chainDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hh, neg_zero, ht, add_zero]
end Differential

def coordinateMaps (m : ℕ) : List (X m →L[ℝ] ℝ) := List.ofFn EuclideanSpace.proj

def value (m : ℕ) (x : X m) : ℝ := chain ((coordinateMaps m).map (fun c => c x))

def gradient (m : ℕ) (x : X m) : X m :=
  (InnerProductSpace.toDual ℝ (X m)).symm (chainDifferential (coordinateMaps m) x)

theorem value_hasFDerivAt (m : ℕ) (x : X m) :
    HasFDerivAt (value m) (innerSL ℝ (gradient m x)) x := by
  have he : innerSL ℝ (gradient m x) = chainDifferential (coordinateMaps m) x := by
    ext y
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := X m)
  rw [he]
  exact chain_comp_hasFDerivAt (coordinateMaps m) x

def objective (m : ℕ) : Objective m where
  value := value m
  grad := gradient m
  hasDeriv := value_hasFDerivAt m

theorem value_eq_chain (m : ℕ) (x : X m) : value m x = chain (List.ofFn (fun i => x i)) := by
  simp only [value, coordinateMaps, List.map_ofFn]
  rfl

theorem value_lower (m : ℕ) (x : X m) : -(9 / 4 : ℝ) * m ≤ value m x := by
  simpa only [value_eq_chain, List.length_ofFn] using chain_lower (List.ofFn (fun i => x i))

theorem value_zero (n : ℕ) : value (n + 1) 0 = -9 / 8 := by
  rw [value_eq_chain]
  simpa only [PiLp.zero_apply, List.ofFn_const] using chain_zero_replicate n

theorem objective_hasGap (n : ℕ) : HasGap (objective (n + 1))
    ((9 / 4 : ℝ) * (n + 1 - 1 / 2)) := by
  refine ⟨-(9 / 4 : ℝ) * (n + 1), ?_, ?_⟩
  · intro x
    simpa only [objective, Nat.cast_add, Nat.cast_one] using value_lower (n + 1) x
  · change value (n + 1) 0 - _ ≤ _
    rw [value_zero]
    ring_nf
    rfl

theorem gradient_coord (m : ℕ) (x : X m) (i : Fin m) :
    gradient m x i = chainDifferential (coordinateMaps m) x (EuclideanSpace.single i 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := X m)
    (y := chainDifferential (coordinateMaps m) x) (x := EuclideanSpace.single i 1)
  simpa only [gradient, EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using h

theorem gradient_nonpos (m : ℕ) (x : X m) (i : Fin m) : gradient m x i ≤ 0 := by
  rw [gradient_coord]
  apply chainDifferential_nonpos
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  change 0 ≤ (EuclideanSpace.single i (1 : ℝ)) j
  simp only [EuclideanSpace.single_apply]
  split_ifs <;> norm_num

theorem gradient_support (m : ℕ) (x : X m) (i : Fin m) (hi : 5 / 4 ≤ |x i|) :
    gradient m x i = 0 := by
  rw [gradient_coord]
  apply chainDifferential_support
  intro c hc hn
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  change (EuclideanSpace.single i (1 : ℝ)) j ≠ 0 at hn
  have hj : j = i := by
    by_contra h
    exact hn (by simp [EuclideanSpace.single_apply, h])
  subst j
  exact hi

end ExactZO.ScalarChain
