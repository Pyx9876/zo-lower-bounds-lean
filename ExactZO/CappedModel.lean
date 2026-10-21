import ExactZO.Model
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
open Set Filter
open scoped InnerProductSpace Topology

namespace ExactZO
variable {d : ℕ}

def cappedValue (f : Objective d) (x : X d) : ℝ := min (f.value x) (f.value 0)

theorem cappedValue_continuous (f : Objective d) : Continuous (cappedValue f) :=
  f.continuous.min continuous_const

/-- A scalar first-exit argument. Prefix models are only used while the
entire prefix stays strictly below the cap. -/
theorem capped_line_model {g : ℝ → ℝ} {c A B : ℝ} (hc : Continuous g)
    (hzero : g 0 < c) (hB : 0 ≤ B)
    (hmodel : ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ u ∈ Icc (0 : ℝ) t, g u < c) → g t ≤ g 0 + t * A + (1 / 2 : ℝ) * t ^ 2 * B) :
    min (g 1) c ≤ g 0 + A + (1 / 2 : ℝ) * B := by
  let q : ℝ → ℝ := fun t => g 0 + t * A + (1 / 2 : ℝ) * t ^ 2 * B
  by_cases hq : c ≤ q 1
  · exact (min_le_right _ _).trans (by simpa [q] using hq)
  have hq1 : q 1 < c := lt_of_not_ge hq
  have hqall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : q t < c := by
    have hinter : q t ≤ (1 - t) * g 0 + t * q 1 := by
      have hnonneg := mul_nonneg hB (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
      dsimp only [q] at *
      nlinarith
    have hmax : (1 - t) * g 0 + t * q 1 ≤ max (g 0) (q 1) := by
      have h₀ := mul_le_mul_of_nonneg_left (le_max_left (g 0) (q 1)) (sub_nonneg.mpr ht.2)
      have h₁ := mul_le_mul_of_nonneg_left (le_max_right (g 0) (q 1)) ht.1
      nlinarith
    exact (hinter.trans hmax).trans_lt (max_lt hzero hq1)
  have hall : ∀ t ∈ Icc (0 : ℝ) 1, g t < c := by
    by_contra hn
    push_neg at hn
    obtain ⟨t, ht, htbad⟩ := hn
    let E : Set ℝ := Icc (0 : ℝ) 1 ∩ {u | c ≤ g u}
    have hcompact : IsCompact E := isCompact_Icc.inter_right (isClosed_le continuous_const hc)
    obtain ⟨τ, hleast⟩ := hcompact.exists_isLeast ⟨t, ht, htbad⟩
    have hτ : τ ∈ Icc (0 : ℝ) 1 := hleast.1.1
    have hτbad : c ≤ g τ := hleast.1.2
    have hτpos : 0 < τ := by
      by_contra hh
      have hτzero : τ = 0 := le_antisymm (le_of_not_gt hh) hτ.1
      subst τ
      exact (not_lt_of_ge hτbad) hzero
    have hbefore (u : ℝ) (hu : u ∈ Ico (0 : ℝ) τ) : g u < c := by
      by_contra huBad
      have huE : u ∈ E := ⟨⟨hu.1, hu.2.le.trans hτ.2⟩, le_of_not_gt huBad⟩
      exact (not_lt_of_ge (hleast.2 huE)) hu.2
    have hbefore_model (u : ℝ) (hu : u ∈ Ico (0 : ℝ) τ) : g u ≤ q u := by
      apply hmodel u ⟨hu.1, hu.2.le.trans hτ.2⟩
      intro w hw
      exact hbefore w ⟨hw.1, hw.2.trans_lt hu.2⟩
    have hτclosure : τ ∈ closure (Ico (0 : ℝ) τ) := by
      rw [closure_Ico (ne_of_lt hτpos)]
      exact ⟨hτpos.le, le_rfl⟩
    have hqcont : Continuous q := by fun_prop
    have hτmodel : g τ ≤ q τ := ContinuousWithinAt.closure_le hτclosure
      hc.continuousAt.continuousWithinAt hqcont.continuousAt.continuousWithinAt hbefore_model
    exact (not_lt_of_ge (hτbad.trans hτmodel)) (hqall τ hτ)
  exact (min_le_left _ _).trans (by simpa using hmodel 1 ⟨by norm_num, le_rfl⟩ hall)

/-- The capped upper model at a strictly sublevel starting point. -/
theorem cappedValue_quadraticUpper_strict (f : Objective d) (H : X d →L[ℝ] X d)
    (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    (x v : X d) (hx : f.value x < f.value 0) :
    cappedValue f (x + v) ≤ f.value x + ⟪f.grad x, v⟫_ℝ + (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ := by
  have hline : Continuous (fun t : ℝ => f.value (x + t • v)) := f.continuous.comp (by fun_prop)
  have h := capped_line_model (A := ⟪f.grad x, v⟫_ℝ) (B := ⟪v, H v⟫_ℝ)
    hline (by simpa using hx) (hpos v) ?_
  · simpa [cappedValue] using h
  · intro t ht hprefix
    have hseg : segment ℝ x (x + t • v) ⊆ StrictSublevel f := by
      intro z hz
      rw [segment_eq_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hrt : r * t ∈ Icc (0 : ℝ) t :=
        ⟨mul_nonneg hr.1 ht.1, by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hr.2)]⟩
      have hrepr : (1 - r) • x + r • (x + t • v) = x + (r * t) • v := by module
      dsimp only
      rw [hrepr]
      exact hprefix (r * t) hrt
    have hupper := hmodel x (x + t • v) hseg
    unfold QuadraticUpper at hupper
    simpa only [zero_smul, add_zero, add_sub_cancel_left, real_inner_smul_right, real_inner_smul_left,
      map_smul, smul_smul, pow_two, mul_assoc] using hupper

/-- Continuous extension to the closure of the strict initial sublevel. -/
theorem cappedValue_quadraticUpper_closure (f : Objective d) (H : X d →L[ℝ] X d)
    (hc : Continuous f.grad) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    (x v : X d) (hx : x ∈ closure (StrictSublevel f)) :
    cappedValue f (x + v) ≤ f.value x + ⟪f.grad x, v⟫_ℝ + (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ := by
  have hl : Continuous (fun y : X d => cappedValue f (y + v)) :=
    (cappedValue_continuous f).comp (continuous_id.add continuous_const)
  have hr : Continuous (fun y : X d =>
      f.value y + ⟪f.grad y, v⟫_ℝ + (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ) :=
    (f.continuous.add (hc.inner continuous_const)).add continuous_const
  exact ContinuousWithinAt.closure_le hx hl.continuousAt.continuousWithinAt
    hr.continuousAt.continuousWithinAt
    (fun y hy => cappedValue_quadraticUpper_strict f H hpos hmodel y v hy)

/-- Outside that closure, any point at the initial value is a local minimum,
and its actual derivative therefore vanishes. -/
theorem boundary_inner_gradient_eq_zero (f : Objective d) (x v : X d)
    (hx : f.value x ≤ f.value 0) (hcl : x ∉ closure (StrictSublevel f)) :
    ⟪f.grad x, v⟫_ℝ = 0 := by
  have hxnot : ¬f.value x < f.value 0 := fun h => hcl (subset_closure h)
  have heq : f.value x = f.value 0 := le_antisymm hx (le_of_not_gt hxnot)
  have hmin : IsLocalMin f.value x := by
    change ∀ᶠ y in 𝓝 x, f.value x ≤ f.value y
    have hnhds : (closure (StrictSublevel f))ᶜ ∈ 𝓝 x :=
      isClosed_closure.isOpen_compl.mem_nhds hcl
    filter_upwards [hnhds] with y hy
    rw [heq]
    apply le_of_not_gt
    intro hbad
    exact hy (subset_closure hbad)
  have hder := hmin.hasFDerivAt_eq_zero (f.hasDeriv x)
  have h := congrArg (fun K : X d →L[ℝ] ℝ => K v) hder
  simpa only [innerSL_apply, ContinuousLinearMap.zero_apply] using h

/-- The capped model holds on the whole closed initial sublevel, including
`x = 0`. PSD is used to make a zero-gradient boundary model at least the cap. -/
theorem cappedValue_quadraticUpper (f : Objective d) (H : X d →L[ℝ] X d)
    (hc : Continuous f.grad) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫_ℝ)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    (x v : X d) (hx : f.value x ≤ f.value 0) :
    cappedValue f (x + v) ≤ f.value x + ⟪f.grad x, v⟫_ℝ + (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ := by
  by_cases hcl : x ∈ closure (StrictSublevel f)
  · exact cappedValue_quadraticUpper_closure f H hc hpos hmodel x v hcl
  · have hxnot : ¬f.value x < f.value 0 := fun h => hcl (subset_closure h)
    have heq : f.value x = f.value 0 := le_antisymm hx (le_of_not_gt hxnot)
    rw [boundary_inner_gradient_eq_zero f x v hx hcl, add_zero, heq]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (hpos v)))

/-- A class witness supplies all analytic inputs of the capped model. -/
theorem SublevelClass.exists_capped_model {f : Objective d} {L Δ E : ℝ}
    (hf : SublevelClass L Δ E f) (hL : 0 ≤ L) :
    ∃ H, UpperMatrix L E H ∧ ∀ x v, f.value x ≤ f.value 0 →
      cappedValue f (x + v) ≤ f.value x + ⟪f.grad x, v⟫_ℝ +
        (1 / 2 : ℝ) * ⟪v, H v⟫_ℝ := by
  obtain ⟨hs, H, hH, hmodel⟩ := hf
  exact ⟨H, hH, cappedValue_quadraticUpper f H (hs.1.continuous_grad hL) hH.2.1 hmodel⟩

end ExactZO
