import ExactZO.ScalingLemma

/-!
The one-rule scaling statement of `S4_modules/E_lower.tex` with independent
target smoothness `L' ≤ L` and the source matrix trace written explicitly.
The positive source smoothness and barrier constants are essential.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExactZO.S4Scaling

variable {d e : ℕ}

theorem scaling_sublevel (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L L' ε b Λ D Δ E : ℝ} (K : X e →L[ℝ] X e)
    (hL' : 0 < L') (hL : L' ≤ L) (hε : 0 < ε) (hb : 0 < b) (hΛ : 0 < Λ)
    (hsmooth : Smooth F Λ) (hgap : HasGap F D)
    (hsym : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (hnorm : ‖K‖ ≤ Λ)
    (hmodel : ∀ x y, segment ℝ x y ⊆ StrictSublevel F → QuadraticUpper F K x y)
    (hbudget : Λ * D / b ^ 2 ≤ L' * Δ / ε ^ 2)
    (htrace : L' * LinearMap.trace ℝ (X e) K.toLinearMap / Λ ≤ L * E) :
    let σ := Λ * ε / (L' * b)
    let α := Λ * ε ^ 2 / (L' * b ^ 2)
    SublevelClass L Δ E (embedObjective J α σ F) := by
  dsimp
  obtain ⟨hσ, hα, _, hscale, hgap'⟩ :=
    normalization_parameters hL' hε hb hΛ hbudget
  have hK : UpperMatrix Λ (LinearMap.trace ℝ (X e) K.toLinearMap / Λ) K := by
    refine ⟨hsym, hpos, hnorm, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hΛ)]
  have hbase : SublevelClass Λ D (LinearMap.trace ℝ (X e) K.toLinearMap / Λ) F :=
    ⟨⟨hsmooth, hgap⟩, K, hK, hmodel⟩
  have hscaled := embedObjective_sublevelClass J hα hσ hΛ.le F hbase
  rw [hscale, div_mul_cancel₀ L' (ne_of_gt hΛ)] at hscaled
  exact hscaled.mono hL hgap' (by simpa only [mul_div_assoc] using htrace)

theorem scaling_fixed (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L L' ε b Λ D Δ E : ℝ} (K : X e →L[ℝ] X e)
    (hL' : 0 < L') (hL : L' ≤ L) (hε : 0 < ε) (hb : 0 < b) (hΛ : 0 < Λ)
    (hsmooth : Smooth F Λ) (hgap : HasGap F D)
    (hsym : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) (hnorm : ‖K‖ ≤ Λ)
    (hmodel : ∀ x y, QuadraticUpper F K x y)
    (hbudget : Λ * D / b ^ 2 ≤ L' * Δ / ε ^ 2)
    (htrace : L' * LinearMap.trace ℝ (X e) K.toLinearMap / Λ ≤ L * E) :
    let σ := Λ * ε / (L' * b)
    let α := Λ * ε ^ 2 / (L' * b ^ 2)
    FixedClass L Δ E (embedObjective J α σ F) := by
  dsimp
  obtain ⟨hσ, hα, _, hscale, hgap'⟩ :=
    normalization_parameters hL' hε hb hΛ hbudget
  have hK : UpperMatrix Λ (LinearMap.trace ℝ (X e) K.toLinearMap / Λ) K := by
    refine ⟨hsym, hpos, hnorm, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hΛ)]
  have hbase : FixedClass Λ D (LinearMap.trace ℝ (X e) K.toLinearMap / Λ) F :=
    ⟨⟨hsmooth, hgap⟩, K, hK, hmodel⟩
  have hscaled := embedObjective_fixedClass J hα.le hσ hΛ.le F hbase
  rw [hscale, div_mul_cancel₀ L' (ne_of_gt hΛ)] at hscaled
  exact hscaled.mono hL hgap' (by simpa only [mul_div_assoc] using htrace)

theorem scaling_gradient_barrier (J : X e →ₗᵢ[ℝ] X d) (F : Objective e)
    {L' ε b Λ : ℝ} (hL' : 0 < L') (hε : 0 < ε) (hb : 0 < b) (hΛ : 0 < Λ)
    (x : X d) :
    let σ := Λ * ε / (L' * b)
    let α := Λ * ε ^ 2 / (L' * b ^ 2)
    ε < ‖(embedObjective J α σ F).grad x‖ ↔ b < ‖F.grad (project J σ x)‖ := by
  exact normalized_gradient_barrier (D := 0) (Δ := 0) J F hL' hε hb hΛ
    (by simp) x

end ExactZO.S4Scaling
