import ExactZO.Model
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace

namespace ExactZO

variable {e d : ℕ}

/-- The query point pulled back through an arbitrary linear isometric embedding. -/
def project (J : X e →ₗᵢ[ℝ] X d) (s : ℝ) : X d →L[ℝ] X e :=
  s⁻¹ • J.toContinuousLinearMap.adjoint

@[simp] theorem project_apply (J : X e →ₗᵢ[ℝ] X d) (s : ℝ) (x : X d) :
    project J s x = s⁻¹ • J.toContinuousLinearMap.adjoint x := rfl

theorem adjoint_embedding (J : X e →ₗᵢ[ℝ] X d) :
    J.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap = 1 :=
  J.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp J.norm_map

theorem norm_adjoint_embedding_le (J : X e →ₗᵢ[ℝ] X d) (x : X d) :
    ‖J.toContinuousLinearMap.adjoint x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖J.toContinuousLinearMap.adjoint‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖J.toContinuousLinearMap‖ * ‖x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right J.norm_toContinuousLinearMap_le (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_project_le (J : X e →ₗᵢ[ℝ] X d) {s : ℝ} (hs : 0 < s) (x : X d) :
    ‖project J s x‖ ≤ s⁻¹ * ‖x‖ := by
  rw [project_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  exact mul_le_mul_of_nonneg_left (norm_adjoint_embedding_le J x) (inv_nonneg.mpr hs.le)

/-- Scaling and embedding of a differentiable objective, with its actual gradient. -/
def embedObjective (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ) (F : Objective e) : Objective d where
  value x := a * F.value (project J s x)
  grad x := (a / s) • J (F.grad (project J s x))
  hasDeriv x := by
    have h := ((F.hasDeriv (project J s x)).comp x (project J s).hasFDerivAt).const_mul a
    convert h using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply, project_apply, real_inner_smul_left, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right, smul_eq_mul]
    change a / s * ⟪J (F.grad (project J s x)), v⟫_ℝ =
      a * (s⁻¹ * ⟪J (F.grad (project J s x)), v⟫_ℝ)
    ring

@[simp] theorem embedObjective_value (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (F : Objective e) (x : X d) :
    (embedObjective J a s F).value x = a * F.value (project J s x) := rfl

@[simp] theorem embedObjective_grad (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (F : Objective e) (x : X d) :
    (embedObjective J a s F).grad x = (a / s) • J (F.grad (project J s x)) := rfl

theorem embedObjective_grad_norm (J : X e →ₗᵢ[ℝ] X d) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (F : Objective e) (x : X d) :
    ‖(embedObjective J a s F).grad x‖ = (a / s) * ‖F.grad (project J s x)‖ := by
  rw [embedObjective_grad, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ha hs.le), J.norm_map]

theorem embedObjective_hasGap (J : X e →ₗᵢ[ℝ] X d) {a s D : ℝ}
    (ha : 0 ≤ a) (F : Objective e) (hF : HasGap F D) :
    HasGap (embedObjective J a s F) (a * D) := by
  obtain ⟨lower, hlower, hgap⟩ := hF
  refine ⟨a * lower, fun x => mul_le_mul_of_nonneg_left (hlower _) ha, ?_⟩
  simpa [mul_sub] using mul_le_mul_of_nonneg_left hgap ha

theorem embedObjective_smooth (J : X e →ₗᵢ[ℝ] X d) {a s L : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (hL : 0 ≤ L) (F : Objective e)
    (hF : Smooth F L) : Smooth (embedObjective J a s F) ((a / s ^ 2) * L) := by
  intro x y
  calc
    ‖(embedObjective J a s F).grad x - (embedObjective J a s F).grad y‖ =
        (a / s) * ‖F.grad (project J s x) - F.grad (project J s y)‖ := by
      simp only [embedObjective_grad, ← smul_sub, ← map_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hs.le), J.norm_map]
    _ ≤ (a / s) * (L * ‖project J s x - project J s y‖) :=
      mul_le_mul_of_nonneg_left (hF _ _) (div_nonneg ha hs.le)
    _ ≤ (a / s) * (L * (s⁻¹ * ‖x - y‖)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ha hs.le)
      apply mul_le_mul_of_nonneg_left _ hL
      simpa only [← map_sub] using norm_project_le J hs (x - y)
    _ = ((a / s ^ 2) * L) * ‖x - y‖ := by ring

/-- The upper model carries no curvature in the orthogonal complement of the embedding. -/
def embedMatrix (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ) (H : X e →L[ℝ] X e) :
    X d →L[ℝ] X d :=
  (a / s ^ 2) • J.toContinuousLinearMap.comp (H.comp J.toContinuousLinearMap.adjoint)

@[simp] theorem embedMatrix_apply (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (H : X e →L[ℝ] X e) (x : X d) :
    embedMatrix J a s H x = (a / s ^ 2) • J (H (J.toContinuousLinearMap.adjoint x)) := rfl

theorem embedMatrix_inner (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (H : X e →L[ℝ] X e) (x y : X d) :
    ⟪x, embedMatrix J a s H y⟫_ℝ = (a / s ^ 2) *
      ⟪J.toContinuousLinearMap.adjoint x, H (J.toContinuousLinearMap.adjoint y)⟫_ℝ := by
  rw [embedMatrix_apply, real_inner_smul_right]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap _ _).symm

theorem embedMatrix_norm_le (J : X e →ₗᵢ[ℝ] X d) {a s : ℝ}
    (ha : 0 ≤ a) (H : X e →L[ℝ] X e) :
    ‖embedMatrix J a s H‖ ≤ (a / s ^ 2) * ‖H‖ := by
  have hq : 0 ≤ a / s ^ 2 := div_nonneg ha (sq_nonneg s)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hq (norm_nonneg H))
  intro x
  rw [embedMatrix_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq, J.norm_map]
  calc
    _ ≤ (a / s ^ 2) * (‖H‖ * ‖J.toContinuousLinearMap.adjoint x‖) :=
      mul_le_mul_of_nonneg_left (H.le_opNorm _) hq
    _ ≤ (a / s ^ 2) * (‖H‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_adjoint_embedding_le J x) (norm_nonneg H)) hq
    _ = _ := by ring

theorem embedMatrix_trace (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (H : X e →L[ℝ] X e) :
    LinearMap.trace ℝ (X d) (embedMatrix J a s H).toLinearMap =
      (a / s ^ 2) * LinearMap.trace ℝ (X e) H.toLinearMap := by
  change LinearMap.trace ℝ (X d)
    ((a / s ^ 2) • (J.toLinearMap.comp
      (H.toLinearMap.comp J.toContinuousLinearMap.adjoint.toLinearMap))) = _
  rw [map_smul, smul_eq_mul]
  congr 1
  rw [LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro x
  have h := congrArg (fun K : X e →L[ℝ] X e => K x) (adjoint_embedding J)
  change H (J.toContinuousLinearMap.adjoint (J x)) = H x
  rw [show J.toContinuousLinearMap.adjoint (J x) = x from h]

theorem embedMatrix_upperMatrix (J : X e →ₗᵢ[ℝ] X d) {a s L E : ℝ}
    (ha : 0 ≤ a) (H : X e →L[ℝ] X e) (hH : UpperMatrix L E H) :
    UpperMatrix ((a / s ^ 2) * L) E (embedMatrix J a s H) := by
  obtain ⟨hsym, hpos, hnorm, htrace⟩ := hH
  have hq : 0 ≤ a / s ^ 2 := div_nonneg ha (sq_nonneg s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [embedMatrix_apply, real_inner_smul_left, real_inner_smul_right]
    change (a / s ^ 2) * ⟪J.toContinuousLinearMap (H (J.toContinuousLinearMap.adjoint x)), y⟫_ℝ =
      (a / s ^ 2) * ⟪x, J.toContinuousLinearMap (H (J.toContinuousLinearMap.adjoint y))⟫_ℝ
    rw [← J.toContinuousLinearMap.adjoint_inner_right (H (J.toContinuousLinearMap.adjoint x)) y,
      ← J.toContinuousLinearMap.adjoint_inner_left (H (J.toContinuousLinearMap.adjoint y)) x, hsym]
  · intro x
    rw [embedMatrix_inner]
    exact mul_nonneg hq (hpos _)
  · exact (embedMatrix_norm_le J ha H).trans (mul_le_mul_of_nonneg_left hnorm hq)
  · rw [embedMatrix_trace]
    calc
      _ ≤ (a / s ^ 2) * (L * E) := mul_le_mul_of_nonneg_left htrace hq
      _ = _ := by ring

theorem embedObjective_inner_grad (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (F : Objective e) (x v : X d) :
    ⟪(embedObjective J a s F).grad x, v⟫_ℝ =
      a * ⟪F.grad (project J s x), project J s v⟫_ℝ := by
  simp only [embedObjective_grad, real_inner_smul_left, project_apply,
    real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  change (a / s) * ⟪J (F.grad (project J s x)), v⟫_ℝ =
    a * (s⁻¹ * ⟪J (F.grad (project J s x)), v⟫_ℝ)
  ring

theorem embedMatrix_quadratic (J : X e →ₗᵢ[ℝ] X d) (a s : ℝ)
    (H : X e →L[ℝ] X e) (v : X d) :
    ⟪v, embedMatrix J a s H v⟫_ℝ = a * ⟪project J s v, H (project J s v)⟫_ℝ := by
  rw [embedMatrix_inner, project_apply, H.map_smul, real_inner_smul_left,
    real_inner_smul_right]
  ring

theorem embedObjective_quadraticUpper (J : X e →ₗᵢ[ℝ] X d) {a s : ℝ}
    (ha : 0 ≤ a) (F : Objective e) (H : X e →L[ℝ] X e) (x y : X d)
    (hF : QuadraticUpper F H (project J s x) (project J s y)) :
    QuadraticUpper (embedObjective J a s F) (embedMatrix J a s H) x y := by
  unfold QuadraticUpper at *
  rw [embedObjective_value, embedObjective_value, embedObjective_inner_grad,
    embedMatrix_quadratic, map_sub]
  nlinarith [mul_le_mul_of_nonneg_left hF ha]

theorem embedObjective_smoothClass (J : X e →ₗᵢ[ℝ] X d) {a s L D : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (hL : 0 ≤ L) (F : Objective e)
    (hF : SmoothClass L D F) :
    SmoothClass ((a / s ^ 2) * L) (a * D) (embedObjective J a s F) :=
  ⟨embedObjective_smooth J ha hs hL F hF.1, embedObjective_hasGap J ha F hF.2⟩

theorem embedObjective_fixedClass (J : X e →ₗᵢ[ℝ] X d) {a s L D E : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (hL : 0 ≤ L) (F : Objective e)
    (hF : FixedClass L D E F) :
    FixedClass ((a / s ^ 2) * L) (a * D) E (embedObjective J a s F) := by
  obtain ⟨hFD, H, hH, hmodel⟩ := hF
  refine ⟨embedObjective_smoothClass J ha hs hL F hFD,
    embedMatrix J a s H, embedMatrix_upperMatrix J ha H hH, ?_⟩
  intro x y
  exact embedObjective_quadraticUpper J ha F H x y (hmodel _ _)

theorem mem_strictSublevel_embedObjective (J : X e →ₗᵢ[ℝ] X d) {a s : ℝ}
    (ha : 0 < a) (F : Objective e) (x : X d) :
    x ∈ StrictSublevel (embedObjective J a s F) ↔ project J s x ∈ StrictSublevel F := by
  simp only [StrictSublevel, Set.mem_setOf_eq, embedObjective_value, map_zero,
    mul_lt_mul_left ha]

theorem project_segment (J : X e →ₗᵢ[ℝ] X d) (s : ℝ) (x y : X d) :
    project J s '' segment ℝ x y = segment ℝ (project J s x) (project J s y) :=
  image_segment ℝ (project J s).toLinearMap.toAffineMap x y

theorem embedObjective_sublevelClass (J : X e →ₗᵢ[ℝ] X d) {a s L D E : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hL : 0 ≤ L) (F : Objective e)
    (hF : SublevelClass L D E F) :
    SublevelClass ((a / s ^ 2) * L) (a * D) E (embedObjective J a s F) := by
  obtain ⟨hFD, H, hH, hmodel⟩ := hF
  refine ⟨embedObjective_smoothClass J ha.le hs hL F hFD,
    embedMatrix J a s H, embedMatrix_upperMatrix J ha.le H hH, ?_⟩
  intro x y hseg
  apply embedObjective_quadraticUpper J ha.le F H x y
  apply hmodel
  rw [← project_segment]
  rintro z ⟨w, hw, rfl⟩
  exact (mem_strictSublevel_embedObjective J ha F w).mp (hseg hw)

theorem embedObjective_gradient_barrier (J : X e →ₗᵢ[ℝ] X d) {a s b : ℝ}
    (ha : 0 < a) (hs : 0 < s) (F : Objective e) (x : X d) :
    (a / s) * b < ‖(embedObjective J a s F).grad x‖ ↔
      b < ‖F.grad (project J s x)‖ := by
  rw [embedObjective_grad_norm J ha.le hs F x, mul_lt_mul_left (div_pos ha hs)]

theorem UpperMatrix.mono {L₁ L₂ E₁ E₂ : ℝ} {H : X d →L[ℝ] X d}
    (hH : UpperMatrix L₁ E₁ H) (hL : L₁ ≤ L₂) (htrace : L₁ * E₁ ≤ L₂ * E₂) :
    UpperMatrix L₂ E₂ H :=
  ⟨hH.1, hH.2.1, hH.2.2.1.trans hL, hH.2.2.2.trans htrace⟩

theorem SmoothClass.mono {L₁ L₂ D₁ D₂ : ℝ} {F : Objective d}
    (hF : SmoothClass L₁ D₁ F) (hL : L₁ ≤ L₂) (hD : D₁ ≤ D₂) :
    SmoothClass L₂ D₂ F := by
  refine ⟨fun x y => (hF.1 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)), ?_⟩
  obtain ⟨lower, hlower, hgap⟩ := hF.2
  exact ⟨lower, hlower, hgap.trans hD⟩

theorem FixedClass.mono {L₁ L₂ D₁ D₂ E₁ E₂ : ℝ} {F : Objective d}
    (hF : FixedClass L₁ D₁ E₁ F) (hL : L₁ ≤ L₂) (hD : D₁ ≤ D₂)
    (htrace : L₁ * E₁ ≤ L₂ * E₂) : FixedClass L₂ D₂ E₂ F := by
  obtain ⟨hs, H, hH, hmodel⟩ := hF
  exact ⟨hs.mono hL hD, H, hH.mono hL htrace, hmodel⟩

theorem SublevelClass.mono {L₁ L₂ D₁ D₂ E₁ E₂ : ℝ} {F : Objective d}
    (hF : SublevelClass L₁ D₁ E₁ F) (hL : L₁ ≤ L₂) (hD : D₁ ≤ D₂)
    (htrace : L₁ * E₁ ≤ L₂ * E₂) : SublevelClass L₂ D₂ E₂ F := by
  obtain ⟨hs, H, hH, hmodel⟩ := hF
  exact ⟨hs.mono hL hD, H, hH.mono hL htrace, hmodel⟩

end ExactZO
