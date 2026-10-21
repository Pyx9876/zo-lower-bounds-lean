import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Field

/-! Finite Gibbs inequality and a large fiber, for the S4 selection argument. -/

noncomputable section
open scoped BigOperators
open Finset

namespace ExactZO.SelectionEntropy

def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ x, p x * Real.log (p x)

theorem entropy_le_crossEntropy {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ x, 0 < q x) (hq1 : ∑ x, q x ≤ 1) :
    entropy p ≤ ∑ x, p x * (-Real.log (q x)) := by
  have hpoint : ∀ x, p x * (Real.log (q x) - Real.log (p x)) ≤ q x - p x := by
    intro x
    by_cases hz : p x = 0
    · simp only [hz, zero_mul, sub_zero]
      exact (hq x).le
    · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hz)
      have h := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (hq x) hpx)) hpx.le
      rw [Real.log_div (ne_of_gt (hq x)) hz] at h
      calc
        _ ≤ p x * (q x / p x - 1) := h
        _ = q x - p x := by field_simp
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) => hpoint x)
  simp only [mul_sub, Finset.sum_sub_distrib, hp1] at hs
  unfold entropy
  simp only [mul_neg, Finset.sum_neg_distrib]
  linarith

theorem exists_atom_ge_exp_neg_entropy {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ x, Real.exp (-entropy p) ≤ p x := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image (univ : Finset α) p univ_nonempty
  have hmax : ∀ y, p y ≤ p x := fun y => hx y (mem_univ y)
  have hxpos : 0 < p x := by
    by_contra hn
    have hz : ∀ y, p y = 0 := fun y => le_antisymm ((hmax y).trans (not_lt.mp hn)) (hp y)
    simp [hz] at hp1
  refine ⟨x, (Real.le_log_iff_exp_le hxpos).mp ?_⟩
  have hs : ∑ y, p y * Real.log (p y) ≤ ∑ y, p y * Real.log (p x) := by
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : p y = 0
    · simp [hy]
    · apply mul_le_mul_of_nonneg_left _ (hp y)
      exact Real.log_le_log (lt_of_le_of_ne (hp y) (Ne.symm hy)) (hmax y)
  simpa [entropy, ← Finset.sum_mul, hp1] using hs

def fiberMass {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) : ℝ :=
  ∑ x, if f x = y then (Fintype.card α : ℝ)⁻¹ else 0

theorem fiberMass_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) : 0 ≤ fiberMass f y := by
  unfold fiberMass
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> positivity)

theorem fiberMass_sum {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [DecidableEq β] (f : α → β) : ∑ y, fiberMass f y = 1 := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem fiberMass_eq_card {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) :
    fiberMass f y = ((univ.filter fun x => f x = y).card : ℝ) / Fintype.card α := by
  simp [fiberMass, ← Finset.sum_filter, div_eq_mul_inv]

theorem fiberMass_expectation {α β : Type*} [Fintype α]
    [Fintype β] [DecidableEq β] (f : α → β) (g : β → ℝ) :
    ∑ y, fiberMass f y * g y = (∑ x, g (f x)) / Fintype.card α := by
  unfold fiberMass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, mem_univ, if_true]
  rw [← Finset.mul_sum]
  ring

theorem exists_large_fiber_of_reference {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [DecidableEq β]
    (f : α → β) (q : β → ℝ) (hq : ∀ y, 0 < q y) (hq1 : ∑ y, q y ≤ 1)
    {B : ℝ} (hB : (∑ x, -Real.log (q (f x))) / Fintype.card α ≤ B) :
    ∃ y, (Fintype.card α : ℝ) * Real.exp (-B) ≤
      ((univ.filter fun x => f x = y).card : ℝ) := by
  have hent : entropy (fiberMass f) ≤ B := by
    have h := entropy_le_crossEntropy (fiberMass f) q
      (fiberMass_nonneg f) (fiberMass_sum f) hq hq1
    rw [fiberMass_expectation] at h
    exact h.trans hB
  obtain ⟨y, hy⟩ := exists_atom_ge_exp_neg_entropy (fiberMass f)
    (fiberMass_nonneg f) (fiberMass_sum f)
  refine ⟨y, ?_⟩
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [fiberMass_eq_card] at hy
  have hh : Real.exp (-B) ≤ Real.exp (-entropy (fiberMass f)) :=
    Real.exp_le_exp.mpr (neg_le_neg hent)
  have := (le_div_iff₀ hcard).mp (hh.trans hy)
  simpa [mul_comm] using this

theorem exists_large_fiber_product_reference {α ι β : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [Fintype β] [Nonempty β]
    [DecidableEq ι] [DecidableEq β]
    (f : α → ι → β) (q : ι → β → ℝ)
    (hq : ∀ i y, 0 < q i y) (hq1 : ∀ i, ∑ y, q i y ≤ 1)
    (B : ι → ℝ)
    (hB : ∀ i, (∑ x, -Real.log (q i (f x i))) / Fintype.card α ≤ B i) :
    ∃ y : ι → β, (Fintype.card α : ℝ) * Real.exp (-(∑ i, B i)) ≤
      ((univ.filter fun x => f x = y).card : ℝ) := by
  classical
  let qjoint : (ι → β) → ℝ := fun y => ∏ i, q i (y i)
  have hpos : ∀ y, 0 < qjoint y := fun y => Finset.prod_pos (fun i _ => hq i (y i))
  have hmass : ∑ y, qjoint y ≤ 1 := by
    dsimp [qjoint]
    rw [← Fintype.prod_sum q]
    calc
      _ ≤ ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg (fun y _ => (hq i y).le)
        · intro i _; exact hq1 i
      _ = 1 := by simp
  have hlog : ∀ x, -Real.log (qjoint (f x)) = ∑ i, -Real.log (q i (f x i)) := by
    intro x
    dsimp [qjoint]
    rw [Real.log_prod _ _ (fun i _ => ne_of_gt (hq i (f x i))), Finset.sum_neg_distrib]
  apply exists_large_fiber_of_reference f qjoint hpos hmass
  simp_rw [hlog]
  rw [Finset.sum_comm, Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => hB i)

end ExactZO.SelectionEntropy
