/- Reused from lean-library Minimax/SmoothGluing.lean at a20965a; source SHA256 39293bc4505d2a1cd02a84c8042c92c04bcf73c87daa17b9365ef7248baa8f7e. Namespace/import adaptation only. -/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! Scalar gluing with actual matching jets. These general lemmas are used
below to prove the manuscript's piecewise functions smooth at their joins. -/
noncomputable section
open Filter
open scoped Topology
namespace ExactZO.ScalarGluing

theorem hasDerivAt_if_of_matching {f g : ℝ → ℝ} {a d : ℝ}
    (p : ℝ → Prop) [DecidablePred p] (hf : HasDerivAt f d a)
    (hg : HasDerivAt g d a) (hfg : f a = g a) :
    HasDerivAt (fun x => if p x then f x else g x) d a := by
  rw [hasDerivAt_iff_tendsto_slope] at hf hg ⊢
  convert hf.if' (p := p) hg using 1
  funext x
  simp only [slope_def_field]
  by_cases ha : p a <;> by_cases hx : p x <;> simp [ha, hx, hfg]

def join (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ c then f x else g x

theorem hasDerivAt_join {f g f' g' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hzero : f c = g c) (hfirst : f' c = g' c) (x : ℝ) :
    HasDerivAt (join c f g) (join c f' g' x) x := by
  rcases lt_trichotomy x c with hx | heq | hx
  · simp only [join, hx.le, if_true]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    exact if_pos hy.le
  · subst x
    simp only [join, le_refl, if_true]
    exact hasDerivAt_if_of_matching (fun x => x ≤ c) (hf c)
      (hfirst ▸ hg c) hzero
  · simp only [join, hx.not_le, if_false]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with y hy
    exact if_neg hy.not_le

theorem continuous_join {f g : ℝ → ℝ} {c : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hzero : f c = g c) :
    Continuous (join c f g) := by
  exact hf.if_le hg continuous_id continuous_const (fun x hx => hx ▸ hzero)

theorem contDiff_one_of_jets {f f' : ℝ → ℝ}
    (h : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f') :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (h x).differentiableAt, ?_⟩
  have he : deriv f = f' := funext (fun x => (h x).deriv)
  rwa [he]

theorem contDiff_two_of_jets {f f' f'' : ℝ → ℝ}
    (h : ∀ x, HasDerivAt f (f' x) x)
    (h' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') :
    ContDiff ℝ 2 f := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (h x).differentiableAt, by simp, ?_⟩
  have he : deriv f = f' := funext (fun x => (h x).deriv)
  rw [he]
  exact contDiff_one_of_jets h' hc

/-- A global C² gluing theorem, including both boundary derivative matches. -/
theorem contDiff_two_join {f g f' g' f'' g'' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hfc : Continuous f'') (hgc : Continuous g'')
    (hzero : f c = g c) (hfirst : f' c = g' c) (hsecond : f'' c = g'' c) :
    ContDiff ℝ 2 (join c f g) :=
  contDiff_two_of_jets (hasDerivAt_join hf hg hzero hfirst)
    (hasDerivAt_join hf' hg' hfirst hsecond) (continuous_join hfc hgc hsecond)

end ExactZO.ScalarGluing
