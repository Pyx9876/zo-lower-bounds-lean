import ExactZO.StageGeometry
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Trace

/-! Total list-frame maps, and their orthogonal geometry under `OrthoList`.
The maps are defined for every list, so objective functions need not carry an
orthogonality proof in their definition. -/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 1000000

namespace ExactZO.FrameGeometry
open StageGeometry

variable {d : ℕ}

/-- Synthesis in the ordered list frame, defined even for nonorthogonal lists. -/
def frameMap (U : List (X d)) : X U.length →L[ℝ] X d :=
  ∑ i : Fin U.length, (EuclideanSpace.proj i).smulRight (U.get i)

/-- Analysis in the ordered list frame, defined even for nonorthogonal lists. -/
def coordinateMap (U : List (X d)) : X d →L[ℝ] X U.length :=
  (frameMap U).adjoint

/-- The frame operator; this is an orthogonal projection for an orthonormal list. -/
def frameProjection (U : List (X d)) : X d →L[ℝ] X d :=
  (frameMap U).comp (coordinateMap U)

@[simp] theorem frameMap_apply (U : List (X d)) (x : X U.length) :
    frameMap U x = ∑ i : Fin U.length, x i • U.get i := by
  simp only [frameMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

@[simp] theorem frameMap_single (U : List (X d)) (i : Fin U.length) :
    frameMap U (EuclideanSpace.single i 1) = U.get i := by
  classical
  simp [frameMap_apply, EuclideanSpace.single_apply, ite_smul]

@[simp] theorem coordinateMap_apply (U : List (X d)) (x : X d) (i : Fin U.length) :
    coordinateMap U x i = ⟪U.get i, x⟫_ℝ := by
  have h := (frameMap U).adjoint_inner_right (EuclideanSpace.single i 1) x
  simpa only [coordinateMap, EuclideanSpace.inner_single_left, one_mul,
    map_one, frameMap_single] using h

theorem coordinateMap_list (U : List (X d)) (x : X d) :
    List.ofFn (fun i => coordinateMap U x i) = U.map (fun u => ⟪u, x⟫_ℝ) := by
  simp only [coordinateMap_apply]
  change List.ofFn ((fun u => ⟪u, x⟫_ℝ) ∘ U.get) = _
  rw [← List.map_ofFn]
  rw [List.ofFn_get]

theorem orthoList_orthonormal {U : List (X d)} (hU : OrthoList U) :
    Orthonormal ℝ U.get := by
  constructor
  · intro i
    exact hU.2 (U.get i) (List.get_mem _ _)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_get.mp hU.1 i j h
    · rw [real_inner_comm]
      exact List.pairwise_iff_get.mp hU.1 j i h

theorem frameMap_inner {U : List (X d)} (hU : OrthoList U) (x y : X U.length) :
    ⟪frameMap U x, frameMap U y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have h := (orthoList_orthonormal hU).inner_sum (fun i => x i) (fun i => y i) Finset.univ
  simpa only [frameMap_apply, RCLike.conj_to_real,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

/-- The actual frame synthesis map as an isometry. -/
def frameIsometry {U : List (X d)} (hU : OrthoList U) : X U.length →ₗᵢ[ℝ] X d :=
  (frameMap U).toLinearMap.isometryOfInner (frameMap_inner hU)

@[simp] theorem frameIsometry_apply {U : List (X d)} (hU : OrthoList U)
    (x : X U.length) : frameIsometry hU x = frameMap U x := rfl

theorem frameMap_norm {U : List (X d)} (hU : OrthoList U) (x : X U.length) :
    ‖frameMap U x‖ = ‖x‖ := (frameIsometry hU).norm_map x

theorem frameMap_opNorm_le {U : List (X d)} (hU : OrthoList U) : ‖frameMap U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [frameMap_norm hU, one_mul, le_refl]

theorem coordinateMap_opNorm_le {U : List (X d)} (hU : OrthoList U) :
    ‖coordinateMap U‖ ≤ 1 := by
  rw [coordinateMap, ContinuousLinearMap.adjoint.norm_map]
  exact frameMap_opNorm_le hU

theorem coordinateMap_norm_le {U : List (X d)} (hU : OrthoList U) (x : X d) :
    ‖coordinateMap U x‖ ≤ ‖x‖ := by
  calc
    ‖coordinateMap U x‖ ≤ ‖coordinateMap U‖ * ‖x‖ := (coordinateMap U).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (coordinateMap_opNorm_le hU) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem coordinateMap_frameMap {U : List (X d)} (hU : OrthoList U) :
    (coordinateMap U).comp (frameMap U) = ContinuousLinearMap.id ℝ (X U.length) := by
  exact (frameMap U).norm_map_iff_adjoint_comp_self.mp (frameMap_norm hU)

@[simp] theorem coordinateMap_frameMap_apply {U : List (X d)} (hU : OrthoList U)
    (x : X U.length) : coordinateMap U (frameMap U x) = x := by
  exact congrArg (fun f : X U.length →L[ℝ] X U.length => f x) (coordinateMap_frameMap hU)

@[simp] theorem coordinateMap_adjoint (U : List (X d)) :
    (coordinateMap U).adjoint = frameMap U := by simp [coordinateMap]

theorem coordinateMap_adjoint_norm {U : List (X d)} (hU : OrthoList U)
    (x : X U.length) : ‖(coordinateMap U).adjoint x‖ = ‖x‖ := by
  rw [coordinateMap_adjoint, frameMap_norm hU]

theorem coordinateMap_lipschitz {U : List (X d)} (hU : OrthoList U) (x y : X d) :
    ‖coordinateMap U x - coordinateMap U y‖ ≤ ‖x - y‖ := by
  rw [← map_sub]
  exact coordinateMap_norm_le hU (x - y)

theorem frameMap_lipschitz {U : List (X d)} (hU : OrthoList U)
    (x y : X U.length) : ‖frameMap U x - frameMap U y‖ = ‖x - y‖ := by
  rw [← map_sub, frameMap_norm hU]

@[simp] theorem frameProjection_apply (U : List (X d)) (x : X d) :
    frameProjection U x = ∑ i : Fin U.length, ⟪U.get i, x⟫_ℝ • U.get i := by
  simp [frameProjection]

theorem frameProjection_inner (U : List (X d)) (x y : X d) :
    ⟪x, frameProjection U y⟫_ℝ = ⟪coordinateMap U x, coordinateMap U y⟫_ℝ := by
  exact ((frameMap U).adjoint_inner_left (coordinateMap U y) x).symm

theorem frameProjection_symmetric (U : List (X d)) (x y : X d) :
    ⟪frameProjection U x, y⟫_ℝ = ⟪x, frameProjection U y⟫_ℝ := by
  rw [real_inner_comm, frameProjection_inner, real_inner_comm, frameProjection_inner]

theorem frameProjection_quadratic (U : List (X d)) (x : X d) :
    ⟪x, frameProjection U x⟫_ℝ = ‖coordinateMap U x‖ ^ 2 := by
  rw [frameProjection_inner, real_inner_self_eq_norm_sq]

theorem frameProjection_nonneg (U : List (X d)) (x : X d) :
    0 ≤ ⟪x, frameProjection U x⟫_ℝ := by
  rw [frameProjection_quadratic]
  exact sq_nonneg _

theorem frameProjection_norm_le {U : List (X d)} (hU : OrthoList U) (x : X d) :
    ‖frameProjection U x‖ ≤ ‖x‖ := by
  change ‖frameMap U (coordinateMap U x)‖ ≤ ‖x‖
  rw [frameMap_norm hU]
  exact coordinateMap_norm_le hU x

theorem frameProjection_opNorm_le {U : List (X d)} (hU : OrthoList U) :
    ‖frameProjection U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  simpa only [one_mul] using frameProjection_norm_le hU

theorem frameProjection_idempotent {U : List (X d)} (hU : OrthoList U) :
    (frameProjection U).comp (frameProjection U) = frameProjection U := by
  apply ContinuousLinearMap.ext
  intro x
  change frameMap U (coordinateMap U (frameMap U (coordinateMap U x))) = _
  rw [coordinateMap_frameMap_apply hU]
  rfl

theorem frameProjection_trace {U : List (X d)} (hU : OrthoList U) :
    LinearMap.trace ℝ (X d) (frameProjection U).toLinearMap = U.length := by
  have h := LinearMap.trace_comp_comm' (coordinateMap U).toLinearMap (frameMap U).toLinearMap
  change LinearMap.trace ℝ (X d)
    ((frameMap U).toLinearMap.comp (coordinateMap U).toLinearMap) = _
  rw [h]
  have hi := congrArg ContinuousLinearMap.toLinearMap (coordinateMap_frameMap hU)
  rw [show (coordinateMap U).toLinearMap.comp (frameMap U).toLinearMap =
      LinearMap.id by exact hi]
  rw [LinearMap.trace_id]
  simp [X]

theorem frameProjection_upperMatrix {U : List (X d)} (hU : OrthoList U) :
    UpperMatrix 1 U.length (frameProjection U) := by
  exact ⟨frameProjection_symmetric U, frameProjection_nonneg U,
    frameProjection_opNorm_le hU, by rw [frameProjection_trace hU, one_mul]⟩


@[simp] theorem coordinateMap_get {U : List (X d)} (hU : OrthoList U)
    (i : Fin U.length) : coordinateMap U (U.get i) = EuclideanSpace.single i 1 := by
  rw [← frameMap_single U i, coordinateMap_frameMap_apply hU]

theorem frameMap_mem_frameSpace (U : List (X d)) (x : X U.length) :
    frameMap U x ∈ frameSpace U := by
  rw [frameMap_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (mem_frameSpace (List.get_mem U i))

theorem frameProjection_mem_frameSpace (U : List (X d)) (x : X d) :
    frameProjection U x ∈ frameSpace U := frameMap_mem_frameSpace U (coordinateMap U x)

private theorem frameSpace_le_of_mem (U : List (X d)) (S : Submodule ℝ (X d))
    (h : ∀ u ∈ U, u ∈ S) : frameSpace U ≤ S := by
  induction U with
  | nil => exact bot_le
  | cons u U ih =>
    apply sup_le
    · apply Submodule.span_le.mpr
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      exact hv ▸ h u (by simp)
    · exact ih (fun v hv => h v (by simp [hv]))

theorem frameSpace_eq_range (U : List (X d)) :
    frameSpace U = LinearMap.range (frameMap U).toLinearMap := by
  apply le_antisymm
  · apply frameSpace_le_of_mem
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hu
    exact ⟨EuclideanSpace.single i 1, frameMap_single U i⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact frameMap_mem_frameSpace U y

theorem coordinateMap_sub_projection {U : List (X d)} (hU : OrthoList U) (x : X d) :
    coordinateMap U (x - frameProjection U x) = 0 := by
  change coordinateMap U (x - frameMap U (coordinateMap U x)) = 0
  rw [map_sub, coordinateMap_frameMap_apply hU, sub_self]

theorem sub_projection_mem_orthogonal {U : List (X d)} (hU : OrthoList U) (x : X d) :
    x - frameProjection U x ∈ (frameSpace U)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  rw [frameSpace_eq_range] at hy
  obtain ⟨z, rfl⟩ := hy
  change ⟪frameMap U z, x - frameProjection U x⟫_ℝ = 0
  rw [← (frameMap U).adjoint_inner_right]
  change ⟪z, coordinateMap U (x - frameProjection U x)⟫_ℝ = 0
  rw [coordinateMap_sub_projection hU]
  exact inner_zero_right _

theorem frameProjection_eq_orthogonalProjection {U : List (X d)} (hU : OrthoList U)
    (x : X d) : frameProjection U x = (frameSpace U).orthogonalProjection x := by
  exact (Submodule.eq_orthogonalProjection_of_mem_orthogonal
    (frameProjection_mem_frameSpace U x) (sub_projection_mem_orthogonal hU x)).symm

end ExactZO.FrameGeometry
