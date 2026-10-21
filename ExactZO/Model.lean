import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.Trace

noncomputable section

open scoped InnerProductSpace

namespace ExactZO

abbrev X (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The vector field is required to be the actual derivative of the value function. -/
structure Objective (d : ℕ) where
  value : X d → ℝ
  grad : X d → X d
  hasDeriv : ∀ x, HasFDerivAt value (innerSL ℝ (grad x)) x

def HasGap {d : ℕ} (f : Objective d) (Δ : ℝ) : Prop :=
  ∃ lower : ℝ, (∀ x, lower ≤ f.value x) ∧ f.value 0 - lower ≤ Δ

def Smooth {d : ℕ} (f : Objective d) (L : ℝ) : Prop :=
  ∀ x y, ‖f.grad x - f.grad y‖ ≤ L * ‖x - y‖

def SmoothClass {d : ℕ} (L Δ : ℝ) (f : Objective d) : Prop :=
  Smooth f L ∧ HasGap f Δ

def UpperMatrix {d : ℕ} (L E : ℝ) (H : X d →L[ℝ] X d) : Prop :=
  (∀ x y, ⟪H x, y⟫_ℝ = ⟪x, H y⟫_ℝ) ∧
  (∀ x, 0 ≤ ⟪x, H x⟫_ℝ) ∧ ‖H‖ ≤ L ∧
  LinearMap.trace ℝ (X d) H.toLinearMap ≤ L * E

def QuadraticUpper {d : ℕ} (f : Objective d) (H : X d →L[ℝ] X d)
    (x y : X d) : Prop :=
  f.value y ≤ f.value x + ⟪f.grad x, y - x⟫_ℝ +
    (1 / 2 : ℝ) * ⟪y - x, H (y - x)⟫_ℝ

def StrictSublevel {d : ℕ} (f : Objective d) : Set (X d) :=
  {x | f.value x < f.value 0}

/-- A single matrix controls every segment contained in the strict initial sublevel. -/
def SublevelClass {d : ℕ} (L Δ E : ℝ) (f : Objective d) : Prop :=
  SmoothClass L Δ f ∧ ∃ H, UpperMatrix L E H ∧
    ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y

def FixedClass {d : ℕ} (L Δ E : ℝ) (f : Objective d) : Prop :=
  SmoothClass L Δ f ∧ ∃ H, UpperMatrix L E H ∧ ∀ x y, QuadraticUpper f H x y

theorem fixedClass_subset_sublevelClass {d : ℕ} {L Δ E : ℝ} {f : Objective d}
    (hf : FixedClass L Δ E f) : SublevelClass L Δ E f := by
  obtain ⟨hs, H, hH, hq⟩ := hf
  exact ⟨hs, H, hH, fun x y _ => hq x y⟩

theorem sublevelClass_subset_smoothClass {d : ℕ} {L Δ E : ℝ} {f : Objective d}
    (hf : SublevelClass L Δ E f) : SmoothClass L Δ f := hf.1

theorem Objective.continuous {d : ℕ} (f : Objective d) : Continuous f.value :=
  continuous_iff_continuousAt.mpr fun x => (f.hasDeriv x).continuousAt

/-- The lower-bound witness formulation does not require an attained minimum. -/
theorem hasGap_iff_infimum {d : ℕ} (f : Objective d) (Δ : ℝ) :
    HasGap f Δ ↔ BddBelow (Set.range f.value) ∧
      f.value 0 - sInf (Set.range f.value) ≤ Δ := by
  constructor
  · rintro ⟨lower, hlo, hgap⟩
    have hb : BddBelow (Set.range f.value) := by
      refine ⟨lower, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hlo x
    refine ⟨hb, ?_⟩
    have hi : lower ≤ sInf (Set.range f.value) := by
      apply le_csInf (Set.range_nonempty f.value)
      rintro _ ⟨x, rfl⟩
      exact hlo x
    exact (sub_le_sub_left hi (f.value 0)).trans hgap
  · rintro ⟨hb, hgap⟩
    exact ⟨sInf (Set.range f.value),
      fun x => csInf_le hb (Set.mem_range_self x), hgap⟩

theorem HasGap.mono {d : ℕ} {f : Objective d} {Δ Δ' : ℝ}
    (hf : HasGap f Δ) (h : Δ ≤ Δ') : HasGap f Δ' := by
  obtain ⟨lower, hlo, hgap⟩ := hf
  exact ⟨lower, hlo, hgap.trans h⟩

theorem Smooth.mono {d : ℕ} {f : Objective d} {L L' : ℝ}
    (hf : Smooth f L) (h : L ≤ L') : Smooth f L' := by
  intro x y
  exact (hf x y).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem Smooth.continuous_grad {d : ℕ} {f : Objective d} {L : ℝ}
    (hf : Smooth f L) (hL : 0 ≤ L) : Continuous f.grad := by
  have h : LipschitzWith ⟨L, hL⟩ f.grad := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hf x y
  exact h.continuous

end ExactZO
