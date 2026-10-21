import ExactZO.Transfer
import ExactZO.Oracle
import ExactZO.Normalization

noncomputable section

namespace ExactZO

variable {d e : ℕ}

/-- The normalized parameters give the exact fixed-class membership in the paper. -/
theorem normalized_fixedClass (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L ε b Lbar D Δ E : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hb : 0 < b) (hbar : 0 < Lbar)
    (hF : FixedClass Lbar D E F)
    (hbudget : Lbar * D / b ^ 2 ≤ L * Δ / ε ^ 2) :
    let s := Lbar * ε / (L * b)
    let a := Lbar * ε ^ 2 / (L * b ^ 2)
    FixedClass L Δ E (embedObjective J a s F) := by
  dsimp
  obtain ⟨hs, ha, hratio, hscale, hgap⟩ :=
    normalization_parameters hL hε hb hbar hbudget
  have h := embedObjective_fixedClass J ha.le hs hbar.le F hF
  rw [hscale, div_mul_cancel₀ L (ne_of_gt hbar)] at h
  exact h.mono le_rfl hgap le_rfl

/-- A direct interface with the source smoothness and upper matrix separated. -/
theorem scaling_lemma_fixedClass (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L ε b Lbar D Δ E lam : ℝ} (H : X e →L[ℝ] X e)
    (hL : 0 < L) (hε : 0 < ε) (hb : 0 < b) (hbar : 0 < Lbar)
    (hsmooth : Smooth F lam) (hlam : lam ≤ Lbar) (hgap : HasGap F D)
    (hH : UpperMatrix Lbar E H) (hmodel : ∀ x y, QuadraticUpper F H x y)
    (hbudget : Lbar * D / b ^ 2 ≤ L * Δ / ε ^ 2) :
    let s := Lbar * ε / (L * b)
    let a := Lbar * ε ^ 2 / (L * b ^ 2)
    FixedClass L Δ E (embedObjective J a s F) := by
  apply normalized_fixedClass J F hL hε hb hbar
  · exact ⟨⟨hsmooth.mono hlam, hgap⟩, H, hH, hmodel⟩
  · exact hbudget

theorem normalized_gradient_barrier (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L ε b Lbar D Δ : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hb : 0 < b) (hbar : 0 < Lbar)
    (hbudget : Lbar * D / b ^ 2 ≤ L * Δ / ε ^ 2) (x : X d) :
    let s := Lbar * ε / (L * b)
    let a := Lbar * ε ^ 2 / (L * b ^ 2)
    ε < ‖(embedObjective J a s F).grad x‖ ↔ b < ‖F.grad (project J s x)‖ := by
  dsimp
  obtain ⟨hs, ha, hratio, hscale, hgap⟩ :=
    normalization_parameters hL hε hb hbar hbudget
  have h := embedObjective_gradient_barrier (b := b) J ha hs F x
  rwa [hratio, div_mul_cancel₀ ε (ne_of_gt hb)] at h

/-- Every reply of the embedded objective is obtained from one projected call. -/
theorem linearReply_embedObjective (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (F : Objective e) (q : LinearQuery d) :
    linearReply (embedObjective J a s F) q =
      (a * (linearReply F (q.project J.toContinuousLinearMap.adjoint s)).1,
        (a / s) • (linearReply F (q.project J.toContinuousLinearMap.adjoint s)).2) := by
  apply linearReply_project
  · intro x
    rfl
  · intro x
    simp [embedObjective_grad, project_apply]

end ExactZO
