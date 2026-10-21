import ExactZO.SublevelWrapper
import ExactZO.SublevelBarrier
import ExactZO.Stage

/-! The concrete family for the adaptive stage argument. Every field of
`Stage.Family`, including prefix consistency and the zero-coordinate gradient
barrier, is discharged from the explicit sublevel wrapper. -/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.SublevelFamily
open StageGeometry

/-- The actual sublevel-localized chain family, with fixed `m` and `R` in every
full and prefix objective. No analytic family property is an input. -/
def family (d m : ℕ) (R : ℝ) (hm : 1 ≤ m) (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) : Stage.Family d m R (1 / 2) (5 / 8) where
  objective := fun U => SublevelWrapper.objective m R U hR
  z := RadialCompression.compression R
  prefixObjective := fun pre => SublevelWrapper.objective m R (pre ++ [0]) hR
  coefficient := SublevelWrapper.coefficient R
  z_bound := fun x => (RadialCompression.compression_norm_lt hR x).le
  prefix_formula := fun pre u tail x _ _ hu ht =>
    SublevelWrapper.prefix_formula m R pre tail u x hu ht
  barrier := by
    intro U x hU hlen hx
    apply SublevelBarrier.gradient_barrier_of_zero hm hR hscale hU hlen x
    obtain ⟨u, hu, hz⟩ := hx
    exact ⟨u, hu, (RadialCompression.compressed_inner_eq_zero_iff R x u).mp hz⟩

variable {d m : ℕ} {R : ℝ} (hm : 1 ≤ m) (hR : 0 < R)
  (hscale : 1024 * (m : ℝ) ≤ R ^ 2)

@[simp] theorem family_objective (U : List (X d)) :
    (family d m R hm hR hscale).objective U = SublevelWrapper.objective m R U hR := rfl

@[simp] theorem family_prefixObjective (pre : List (X d)) :
    (family d m R hm hR hscale).prefixObjective pre =
      SublevelWrapper.objective m R (pre ++ [0]) hR := rfl

@[simp] theorem family_z (x : X d) :
    (family d m R hm hR hscale).z x = RadialCompression.compression R x := rfl

@[simp] theorem family_coefficient (pre : List (X d)) (x : X d) :
    (family d m R hm hR hscale).coefficient pre x =
      SublevelWrapper.coefficient R pre x := rfl

theorem family_objective_smoothClass (U : List (X d)) (hU : OrthoList U)
    (hlen : U.length = m) :
    SmoothClass 50 ((9 / 4 : ℝ) * ((m : ℝ) - 1 / 2))
      ((family d m R hm hR hscale).objective U) :=
  SublevelWrapper.objective_smoothClass m hR hm hscale hU hlen

end ExactZO.SublevelFamily
