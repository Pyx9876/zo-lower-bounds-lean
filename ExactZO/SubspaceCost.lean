import ExactZO.SubspaceProcedure
import ExactZO.SubspaceBudget

/-! Query accounting along the actual restarted execution. -/
noncomputable section
open scoped InnerProductSpace
namespace ExactZO.SubspaceCost
open StageGeometry FrameGeometry SubspaceEstimate SubspaceResidual SubspaceProcedure

/-- The terminal estimates, every restricted update, every line center and
all failed proposals are charged. Line-search costs telescope on this trajectory. -/
theorem run_ledger {d r : ℕ} {L Δ E ε : ℝ} {f : Objective d}
    {H : X d →L[ℝ] X d} (hL : 0 < L) (hε : 0 < ε)
    (hr : 1 ≤ r) (hrd : r ≤ d) (hf : SmoothClass L Δ f) (hH : UpperMatrix L E H)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel f → QuadraticUpper f H x y)
    (fuel : ℕ) (x : X d) (U : List (X d))
    (hU : OrthoList U) (hlen : U.length < r) (hx : f.value x ≤ f.value 0) :
    let out := run f L ε r (LineSearch.publicFuel L Δ ε) fuel x U
    f.value out.point ≤ f.value x ∧
      (out.cost:ℝ) ≤ 2*((r:ℝ)-1)*out.restrictedCount +
        2*((d:ℝ)+(r:ℝ)-1)*(out.expansionCount+1)+2*out.expansionCount+
        (8*L/ε^2)*(f.value x-f.value out.point) := by
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hr.trans hrd
  have hκ : 0 ≤ 8*L/ε^2 := by positivity
  induction fuel generalizing x U with
  | zero =>
      simp only [run]
      constructor
      · exact le_rfl
      · simp only [Nat.cast_zero,zero_mul,mul_zero,zero_add,sub_self,mul_zero,add_zero]
        nlinarith
  | succ fuel ih =>
      have hlenR : (U.length:ℝ) ≤ (r:ℝ)-1 := by
        have hh : ((U.length+1:ℕ):ℝ) ≤ r := by exact_mod_cast hlen
        push_cast at hh
        linarith
      by_cases hs : ‖estimate f.value U (radius U.length L ε) x‖ ≤ 7*ε/16
      · by_cases hg : ‖fullEstimate f.value L ε x‖ ≤ 15*ε/16
        · simp only [run,step,if_pos hs,if_pos hg,Step.isTerminal,
            if_true,Step.target,Step.frameAfter,Step.queryCost,Step.restrictedCount,Step.expansionCount]
          constructor
          · exact le_rfl
          · push_cast
            nlinarith
        · let u := direction U (fullEstimate f.value L ε x)
          let P := LineSearch.procedure (LineSearch.publicFuel L Δ ε) L ε x u
          let y := P.result f
          let V := nextFrame r U u
          obtain ⟨_,hu,ho,hsl,hUa⟩ := fullEstimate_residual f hf.1 hU hL hε x
            (estimate_stop f hf.1 hU hL hε x hs) (lt_of_not_ge hg)
          obtain ⟨hc,j,hfirst,hres,hcost,hd,hcst,hline⟩ :=
            LineSearch.procedure_spec hL hε hf hH hmodel hx hu hsl
          change 0 < ⟪u,H u⟫_ℝ at hc
          change 7*ε^2/(64*⟪u,H u⟫_ℝ) < f.value x-f.value y at hd
          have hy : f.value y ≤ f.value x := by
            have hp : 0 < 7*ε^2/(64*⟪u,H u⟫_ℝ) := by positivity
            linarith
          have hV : OrthoList V := by
            dsimp only [V,nextFrame]
            split_ifs
            · exact orthoList_nil _
            · exact hUa
          have hVlen : V.length < r := nextFrame_length_lt (by omega) hlen u
          obtain ⟨hm,hl⟩ := ih y V hV hVlen (hy.trans hx)
          have hline' : (P.cost f:ℝ) ≤ (8*L/ε^2)*(f.value x-f.value y)+2 := by
            convert hline using 1 <;> ring
          simp only [run,step,if_pos hs,if_neg hg,Step.isTerminal,Bool.false_eq_true,
            if_false,Step.target,Step.frameAfter,Step.queryCost,Step.restrictedCount,Step.expansionCount]
          change f.value (run f L ε r (LineSearch.publicFuel L Δ ε) fuel y V).point ≤ f.value x ∧ _
          constructor
          · exact hm.trans hy
          · change ((2*U.length+2*d+P.cost f +
                (run f L ε r (LineSearch.publicFuel L Δ ε) fuel y V).cost:ℕ):ℝ) ≤ _
            push_cast
            push_cast at hl
            nlinarith
      · let y := x-L⁻¹•frameMap U (estimate f.value U (radius U.length L ε) x)
        have hd := estimate_descent f hf.1 hU hL hε x (lt_of_not_ge hs)
        change f.value y < f.value x-35*ε^2/(512*L) at hd
        have hy : f.value y ≤ f.value x := by
          have hp : 0 < 35*ε^2/(512*L) := by positivity
          linarith
        obtain ⟨hm,hl⟩ := ih y U hU hlen (hy.trans hx)
        simp only [run,step,if_neg hs,Step.isTerminal,Bool.false_eq_true,if_false,
          Step.target,Step.frameAfter,Step.queryCost,Step.restrictedCount,Step.expansionCount]
        change f.value (run f L ε r (LineSearch.publicFuel L Δ ε) fuel y U).point ≤ f.value x ∧ _
        constructor
        · exact hm.trans hy
        · change ((2*U.length+(run f L ε r (LineSearch.publicFuel L Δ ε) fuel y U).cost:ℕ):ℝ) ≤ _
          push_cast
          push_cast at hl
          nlinarith [mul_nonneg hκ (sub_nonneg.mpr hy)]

end ExactZO.SubspaceCost
