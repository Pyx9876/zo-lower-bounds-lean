import ExactZO.FrameGeometry
import ExactZO.ChainBounds
import ExactZO.ChainPrefix
import ExactZO.RadialSecond
import ExactZO.SublevelPotential

/-! The actual sublevel-localized wrapper. The parameters `m` and `R` are
independent of the frame length, including in prefix objectives. -/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 2000000

namespace ExactZO.SublevelWrapper
open StageGeometry FrameGeometry RadialCompression

variable {d : ℕ}

def mu (m : ℕ) (R : ℝ) : ℝ := 64 * (m : ℝ) / R ^ 2

def chainPoint (R : ℝ) (U : List (X d)) (x : X d) : X U.length :=
  coordinateMap U (compression R x)

def chainGradient (R : ℝ) (U : List (X d)) (x : X d) : X d :=
  frameMap U (ScalarChain.gradient U.length (chainPoint R U x))

def value (m : ℕ) (R : ℝ) (U : List (X d)) (x : X d) : ℝ :=
  ScalarChain.value U.length (chainPoint R U x) +
    SublevelPotential.value (mu m R) (R / 2) x

def gradient (m : ℕ) (R : ℝ) (U : List (X d)) (x : X d) : X d :=
  derivative R x (chainGradient R U x) + SublevelPotential.gradient (mu m R) (R / 2) x

theorem value_hasFDerivAt (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d)) (x : X d) :
    HasFDerivAt (value m R U) (innerSL ℝ (gradient m R U x)) x := by
  have hc := (ScalarChain.value_hasFDerivAt U.length (chainPoint R U x)).comp x
    ((coordinateMap U).hasFDerivAt.comp x (compression_hasFDerivAt hR x))
  have hq := SublevelPotential.value_hasFDerivAt (show 0 < R / 2 by linarith) (mu m R) x
  convert hc.add hq using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [gradient, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply, inner_add_left]
  rw [derivative_symmetric]
  exact congrArg (fun t => t + ⟪SublevelPotential.gradient (mu m R) (R / 2) x, v⟫_ℝ)
    ((frameMap U).adjoint_inner_right
      (ScalarChain.gradient U.length (chainPoint R U x)) (derivative R x v)).symm

def objective (m : ℕ) (R : ℝ) (U : List (X d)) (hR : 0 < R) : Objective d where
  value := value m R U
  grad := gradient m R U
  hasDeriv := value_hasFDerivAt m hR U

theorem mu_nonneg (m : ℕ) (R : ℝ) : 0 ≤ mu m R := by
  unfold mu
  positivity

theorem mu_le_one (m : ℕ) {R : ℝ} (hR : 0 < R) (hscale : 1024 * (m : ℝ) ≤ R ^ 2) :
    mu m R ≤ 1 := by
  rw [mu, div_le_iff₀ (sq_pos_of_pos hR), one_mul]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

@[simp] theorem chainPoint_zero (R : ℝ) (U : List (X d)) : chainPoint R U 0 = 0 := by
  simp [chainPoint, compression]

theorem value_zero (m : ℕ) {R : ℝ} (hR : 0 < R) (U : List (X d))
    (hm : 1 ≤ m) (hlen : U.length = m) : value m R U 0 = -9 / 8 := by
  have hn : m ≠ 0 := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [value, chainPoint_zero, SublevelPotential.value, norm_zero,
    SublevelPotential.scalar_zero (show 0 ≤ R / 2 by linarith), add_zero, hlen]
  rw [hlen]
  exact ScalarChain.value_zero n

theorem value_lower (m : ℕ) {R : ℝ} (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) (U : List (X d)) (hlen : U.length = m) (x : X d) :
    -(9 / 4 : ℝ) * m ≤ value m R U x := by
  have hc := ScalarChain.value_lower U.length (chainPoint R U x)
  have hq := SublevelPotential.value_nonneg (mu_nonneg m R) (mu_le_one m hR hscale)
    (show 0 ≤ R / 2 by linarith) x
  rw (occs := .pos [1]) [hlen] at hc
  unfold value
  linarith

theorem objective_hasGap (m : ℕ) {R : ℝ} (hR : 0 < R) (hm : 1 ≤ m)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) (U : List (X d)) (hlen : U.length = m) :
    HasGap (objective m R U hR) ((9 / 4 : ℝ) * ((m : ℝ) - 1 / 2)) := by
  refine ⟨-(9 / 4 : ℝ) * m, value_lower m hR hscale U hlen, ?_⟩
  change value m R U 0 - _ ≤ _
  rw [value_zero m hR U hm hlen]
  ring_nf
  rfl

theorem potential_outside_inner (m : ℕ) {R : ℝ} (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) (x : X d) (hx : R / 2 ≤ ‖x‖) :
    8 * (m : ℝ) ≤ SublevelPotential.value (mu m R) (R / 2) x := by
  have hr : 0 ≤ R / 2 := by linarith
  have h := SublevelPotential.scalar_mono (mu_nonneg m R) (mu_le_one m hR hscale) hr
    hr (norm_nonneg x) hx
  rw [SublevelPotential.scalar_inner (μ := mu m R) (le_refl (R / 2))] at h
  have he : mu m R * (R / 2) ^ 2 / 2 = 8 * (m : ℝ) := by
    unfold mu
    field_simp
    <;> ring
  rw [he] at h
  exact h

theorem sublevel_inside_inner (m : ℕ) {R : ℝ} (hR : 0 < R) (hm : 1 ≤ m)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) (U : List (X d)) (hlen : U.length = m)
    (x : X d) (hx : value m R U x ≤ value m R U 0) : ‖x‖ < R / 2 := by
  by_contra hh
  have hp := potential_outside_inner m hR hscale x (le_of_not_gt hh)
  have hc := ScalarChain.value_lower U.length (chainPoint R U x)
  rw (occs := .pos [1]) [hlen] at hc
  rw [value_zero m hR U hm hlen] at hx
  change ScalarChain.value U.length (chainPoint R U x) + _ ≤ _ at hx
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith


theorem chainPoint_lipschitz {R : ℝ} (hR : 0 < R) {U : List (X d)}
    (hU : OrthoList U) (x y : X d) : ‖chainPoint R U x - chainPoint R U y‖ ≤ ‖x-y‖ := by
  exact (coordinateMap_lipschitz hU (compression R x) (compression R y)).trans
    (compression_lipschitz hR y x)

theorem chainGradient_norm_le (R : ℝ) {U : List (X d)} (hU : OrthoList U) (x : X d) :
    ‖chainGradient R U x‖ ≤ 10 * Real.sqrt U.length := by
  rw [chainGradient, frameMap_norm hU]
  exact ScalarChain.gradient_norm_le U.length (chainPoint R U x)

theorem chainGradient_lipschitz {R : ℝ} (hR : 0 < R) {U : List (X d)}
    (hU : OrthoList U) (x y : X d) :
    ‖chainGradient R U x - chainGradient R U y‖ ≤ 48 * ‖x-y‖ := by
  rw [chainGradient, chainGradient, frameMap_lipschitz hU]
  exact (ScalarChain.gradient_lipschitz U.length (chainPoint R U x) (chainPoint R U y)).trans
    (mul_le_mul_of_nonneg_left (chainPoint_lipschitz hR hU x y) (by norm_num))

theorem curvature_coefficient_le_one (m : ℕ) {R : ℝ} (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) :
    2 / (Real.sqrt 3 * R) * (10 * Real.sqrt m) ≤ 1 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hroot := Real.sq_sqrt hm
  have h20 : 20 * Real.sqrt m ≤ R := by
    apply (sq_le_sq₀ (by positivity) hR.le).mp
    nlinarith
  have h3 : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have h3pos : 0 < Real.sqrt 3 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos h3pos hR), one_mul]
  have hh := mul_le_mul_of_nonneg_right h3 hR.le
  nlinarith

theorem compressedChainGradient_lipschitz (m : ℕ) {R : ℝ} (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)}
    (hU : OrthoList U) (hlen : U.length = m) (x y : X d) :
    ‖derivative R x (chainGradient R U x) - derivative R y (chainGradient R U y)‖ ≤
      49 * ‖x-y‖ := by
  have hfirst : ‖derivative R x (chainGradient R U x - chainGradient R U y)‖ ≤
      48 * ‖x-y‖ := by
    calc
      _ ≤ ‖derivative R x‖ * ‖chainGradient R U x - chainGradient R U y‖ :=
        (derivative R x).le_opNorm _
      _ ≤ 1 * ‖chainGradient R U x - chainGradient R U y‖ :=
        mul_le_mul_of_nonneg_right (derivative_norm_le_one hR x) (norm_nonneg _)
      _ ≤ 48 * ‖x-y‖ := by simpa only [one_mul] using chainGradient_lipschitz hR hU x y
  have hsecond : ‖(derivative R x - derivative R y) (chainGradient R U y)‖ ≤ ‖x-y‖ := by
    have hK : 0 ≤ 2 / (Real.sqrt 3 * R) := by positivity
    have hg : ‖chainGradient R U y‖ ≤ 10 * Real.sqrt m := by
      simpa only [hlen] using chainGradient_norm_le R hU y
    calc
      _ ≤ ‖derivative R x - derivative R y‖ * ‖chainGradient R U y‖ :=
        (derivative R x - derivative R y).le_opNorm _
      _ ≤ (2 / (Real.sqrt 3 * R) * ‖x-y‖) * (10 * Real.sqrt m) :=
        mul_le_mul (derivative_lipschitz hR y x) hg (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))
      _ = (2 / (Real.sqrt 3 * R) * (10 * Real.sqrt m)) * ‖x-y‖ := by ring
      _ ≤ 1 * ‖x-y‖ := mul_le_mul_of_nonneg_right (curvature_coefficient_le_one m hR hscale)
        (norm_nonneg _)
      _ = ‖x-y‖ := one_mul _
  have he : derivative R x (chainGradient R U x) - derivative R y (chainGradient R U y) =
      derivative R x (chainGradient R U x - chainGradient R U y) +
        (derivative R x - derivative R y) (chainGradient R U y) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem gradient_lipschitz (m : ℕ) {R : ℝ} (hR : 0 < R)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)}
    (hU : OrthoList U) (hlen : U.length = m) (x y : X d) :
    ‖gradient m R U x - gradient m R U y‖ ≤ 50 * ‖x-y‖ := by
  have hc := compressedChainGradient_lipschitz m hR hscale hU hlen x y
  have hq := SublevelPotential.gradient_lipschitz (mu_nonneg m R) (mu_le_one m hR hscale)
    (show 0 ≤ R / 2 by linarith) x y
  have he : gradient m R U x - gradient m R U y =
      (derivative R x (chainGradient R U x) - derivative R y (chainGradient R U y)) +
      (SublevelPotential.gradient (mu m R) (R / 2) x -
        SublevelPotential.gradient (mu m R) (R / 2) y) := by
    unfold gradient
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem objective_smoothClass (m : ℕ) {R : ℝ} (hR : 0 < R) (hm : 1 ≤ m)
    (hscale : 1024 * (m : ℝ) ≤ R ^ 2) {U : List (X d)}
    (hU : OrthoList U) (hlen : U.length = m) :
    SmoothClass 50 ((9 / 4 : ℝ) * ((m : ℝ) - 1 / 2)) (objective m R U hR) := by
  exact ⟨gradient_lipschitz m hR hscale hU hlen, objective_hasGap m hR hm hscale U hlen⟩


/-- The Euclidean frame definition agrees with the scalar chain of actual inner coordinates. -/
theorem frameChain_hasFDerivAt (U : List (X d)) (z : X d) :
    HasFDerivAt (fun y => ScalarChain.chain
      ((U.map (innerSL ℝ)).map (fun c : X d →L[ℝ] ℝ => c y)))
      (innerSL ℝ (frameMap U (ScalarChain.gradient U.length (coordinateMap U z)))) z := by
  have h := (ScalarChain.value_hasFDerivAt U.length (coordinateMap U z)).comp z
    (coordinateMap U).hasFDerivAt
  convert h using 1
  · funext y
    simp only [Function.comp_apply]
    rw [ScalarChain.value_eq_chain, coordinateMap_list]
    simp only [List.map_map, Function.comp_def, innerSL_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply]
    exact ((frameMap U).adjoint_inner_right
      (ScalarChain.gradient U.length (coordinateMap U z)) v).symm

theorem chainGradient_differential (R : ℝ) (U : List (X d)) (x : X d) :
    innerSL ℝ (chainGradient R U x) =
      ScalarChain.chainDifferential (U.map (innerSL ℝ)) (compression R x) := by
  exact (frameChain_hasFDerivAt U (compression R x)).unique
    (ScalarChain.chain_comp_hasFDerivAt (U.map (innerSL ℝ)) (compression R x))

theorem value_prefix (m : ℕ) (R : ℝ) (pre tail : List (X d)) (u x : X d)
    (hu : ⟪u, compression R x⟫_ℝ = 0)
    (ht : ∀ v ∈ tail, |⟪v, compression R x⟫_ℝ| ≤ 1 / 2) :
    value m R (pre ++ u :: tail) x = value m R (pre ++ [0]) x := by
  have htail : ∀ c ∈ tail.map (innerSL ℝ), |c (compression R x)| ≤ 1 / 2 := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact ht v hv
  have h := ScalarChain.chain_comp_prefix_zero (innerSL ℝ u)
    (pre.map (innerSL ℝ)) (tail.map (innerSL ℝ)) (compression R x) hu htail
  unfold value chainPoint
  congr 1
  simp only [ScalarChain.value_eq_chain, coordinateMap_list]
  simpa only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, innerSL_apply, ContinuousLinearMap.zero_apply, inner_zero_left] using h

theorem chainGradient_prefix (R : ℝ) (pre tail : List (X d)) (u x : X d)
    (hu : ⟪u, compression R x⟫_ℝ = 0)
    (ht : ∀ v ∈ tail, |⟪v, compression R x⟫_ℝ| ≤ 1 / 2) :
    chainGradient R (pre ++ u :: tail) x = chainGradient R (pre ++ [0]) x -
      ScalarChain.prefixGate (pre.map (innerSL ℝ)) (compression R x) • u := by
  have htail : ∀ c ∈ tail.map (innerSL ℝ), |c (compression R x)| ≤ 1 / 2 := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact ht v hv
  have h := ScalarChain.chainDifferential_prefix_zero (innerSL ℝ u)
    (pre.map (innerSL ℝ)) (tail.map (innerSL ℝ)) (compression R x) hu htail
  apply ext_inner_right ℝ
  intro v
  have hfull := congrArg (fun f : X d →L[ℝ] ℝ => f v)
    (chainGradient_differential R (pre ++ u :: tail) x)
  have hpre := congrArg (fun f : X d →L[ℝ] ℝ => f v)
    (chainGradient_differential R (pre ++ [0]) x)
  have hv := congrArg (fun f : X d →L[ℝ] ℝ => f v) h
  simp only [List.map_append, List.map_cons, List.map_nil, map_zero] at hfull hpre
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply] at hv hfull hpre
  rw [inner_sub_left, real_inner_smul_left]
  rw [hfull, hpre]
  exact hv

/-- The exact coefficient used by the adaptive stage oracle. It keeps the
compression factor and all wrapper parameters fixed when truncating the frame. -/
def coefficient (R : ℝ) (pre : List (X d)) (x : X d) : ℝ :=
  factor R x * ScalarChain.prefixGate (pre.map (innerSL ℝ)) (compression R x)

theorem coefficient_bounds (R : ℝ) (pre : List (X d)) (x : X d) :
    0 ≤ coefficient R pre x ∧ coefficient R pre x ≤ 1 := by
  have hg := ScalarChain.prefixGate_bounds (pre.map (innerSL ℝ)) (compression R x)
  unfold coefficient
  exact ⟨mul_nonneg (factor_pos R x).le hg.1,
    (mul_le_mul (factor_le_one R x) hg.2 hg.1 (by norm_num)).trans_eq (by ring)⟩

theorem gradient_prefix (m : ℕ) (R : ℝ) (pre tail : List (X d)) (u x : X d)
    (hu : ⟪u, compression R x⟫_ℝ = 0)
    (ht : ∀ v ∈ tail, |⟪v, compression R x⟫_ℝ| ≤ 1 / 2) :
    gradient m R (pre ++ u :: tail) x = gradient m R (pre ++ [0]) x -
      coefficient R pre x • u := by
  have hd := derivative_on_orthogonal R x u hu
  unfold gradient
  rw [chainGradient_prefix R pre tail u x hu ht, map_sub, map_smul, hd]
  simp only [coefficient, smul_smul]
  rw [mul_comm (ScalarChain.prefixGate (pre.map (innerSL ℝ)) (compression R x))]
  abel

theorem prefix_formula (m : ℕ) (R : ℝ) (pre tail : List (X d)) (u x : X d)
    (hu : ⟪u, compression R x⟫_ℝ = 0)
    (ht : ∀ v ∈ tail, |⟪v, compression R x⟫_ℝ| ≤ 1 / 2) :
    value m R (pre ++ u :: tail) x = value m R (pre ++ [0]) x ∧
    gradient m R (pre ++ u :: tail) x = gradient m R (pre ++ [0]) x -
      coefficient R pre x • u :=
  ⟨value_prefix m R pre tail u x hu ht, gradient_prefix m R pre tail u x hu ht⟩

end ExactZO.SublevelWrapper
