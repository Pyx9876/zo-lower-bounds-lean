import ExactZO.RadialSecond
import ExactZO.ScalarChain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Finite scalar junctions along a nonconstant compressed line. Reuses the
polynomial-root method of local-library `Minimax/LineExceptionalSets.lean`,
SHA256 `765b47fb4e5ffa8800f33fb723a088187324b912ea6a5bfc216efa69bd605a83`.
That library theorem concerns uncompressed spheres, so the nonzero polynomial
argument is proved anew here. Hypotheses are exactly positive radius, nonzero
line direction, and nonzero junction value. No generic-line or a.e. premise.
-/
noncomputable section
open scoped InnerProductSpace Topology
open Set Filter
namespace ExactZO.CompressedLinePieces
variable {d : ℕ}

theorem line_norm_sq (x v : X d) (t : ℝ) :
    ‖x + t • v‖ ^ 2 = ‖v‖ ^ 2 * t ^ 2 + 2 * ⟪x, v⟫_ℝ * t + ‖x‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  ring

/-- Every nonzero scalar level has finitely many hits along a nonconstant
compressed line; in particular, no such coordinate can stay at a junction. -/
theorem compressed_level_finite {R b : ℝ} (hR : 0 < R) (hb : b ≠ 0)
    (u x : X d) {v : X d} (hv : v ≠ 0) :
    {t : ℝ | ⟪u, RadialCompression.compression R (x + t • v)⟫_ℝ = b}.Finite := by
  let α := ⟪u, x⟫_ℝ
  let β := ⟪u, v⟫_ℝ
  let p : Polynomial ℝ :=
    Polynomial.C (R ^ 2 * β ^ 2 - b ^ 2 * ‖v‖ ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C (2 * R ^ 2 * α * β - 2 * b ^ 2 * ⟪x, v⟫_ℝ) * Polynomial.X +
    Polynomial.C (R ^ 2 * α ^ 2 - b ^ 2 * (R ^ 2 + ‖x‖ ^ 2))
  have heval (t : ℝ) : p.eval t =
      R ^ 2 * (α + β * t) ^ 2 - b ^ 2 * (R ^ 2 + ‖x + t • v‖ ^ 2) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, line_norm_sq]
    ring
  have hp : p ≠ 0 := by
    intro hp
    by_cases hβ : β = 0
    · have hh := congrArg (fun q : Polynomial ℝ => q.coeff 2) hp
      simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero, hβ] at hh
      norm_num at hh
      exact hh.elim hb hv
    · have hh := congrArg (fun q : Polynomial ℝ => q.eval (-α / β)) hp
      dsimp only at hh
      rw [heval, Polynomial.eval_zero] at hh
      have hz : α + β * (-α / β) = 0 := by field_simp; ring
      rw [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_sub] at hh
      have hpos : 0 < b ^ 2 * (R ^ 2 + ‖x + (-α / β) • v‖ ^ 2) := by
        exact mul_pos (sq_pos_of_ne_zero hb) (add_pos_of_pos_of_nonneg
          (sq_pos_of_pos hR) (sq_nonneg _))
      linarith
  apply (Polynomial.finite_setOf_isRoot hp).subset
  intro t ht
  change p.eval t = 0
  rw [heval]
  have hi := RadialCompression.factor_identity hR (x + t • v)
  have hi' : RadialCompression.factor R (x + t • v) ^ 2 *
      (R ^ 2 + ‖x + t • v‖ ^ 2) = R ^ 2 := by
    field_simp at hi
    nlinarith only [hi]
  have hcoord : RadialCompression.factor R (x + t • v) * (α + β * t) = b := by
    simpa only [RadialCompression.compression, real_inner_smul_right, inner_add_right,
      real_inner_smul_right, α, β, Set.mem_setOf_eq, mul_comm t] using ht
  have hs := congrArg (fun z : ℝ => z ^ 2) hcoord
  dsimp only at hs
  have he : b ^ 2 * (R ^ 2 + ‖x + t • v‖ ^ 2) = R ^ 2 * (α + β * t) ^ 2 := by
    calc
      _ = (RadialCompression.factor R (x + t • v) ^ 2 * (α + β * t) ^ 2) *
          (R ^ 2 + ‖x + t • v‖ ^ 2) := by rw [← hs]; ring
      _ = (RadialCompression.factor R (x + t • v) ^ 2 *
          (R ^ 2 + ‖x + t • v‖ ^ 2)) * (α + β * t) ^ 2 := by ring
      _ = _ := by rw [hi']
  linarith

/-- Finite frames and finite nonzero junction lists give one finite exceptional
set that works simultaneously for every compressed coordinate. -/
theorem compressed_junctions_finite {R : ℝ} (hR : 0 < R)
    (U : List (X d)) (J : Finset ℝ) (hJ : ∀ b ∈ J, b ≠ 0)
    (x : X d) {v : X d} (hv : v ≠ 0) :
    {t : ℝ | ∃ u ∈ U, ∃ b ∈ J,
      ⟪u, RadialCompression.compression R (x + t • v)⟫_ℝ = b}.Finite := by
  classical
  induction U with
  | nil => simp
  | cons u U ih =>
    have hu : {t : ℝ | ∃ b ∈ J,
        ⟪u, RadialCompression.compression R (x + t • v)⟫_ℝ = b}.Finite := by
      have hh := Set.Finite.biUnion J.finite_toSet
        (fun b hb => compressed_level_finite hR (hJ b hb) u x hv)
      convert hh using 1
      ext t
      simp
    convert hu.union ih using 1
    ext t
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
    aesop

private theorem contDiffAt_ite_le {n : WithTop ℕ∞} {f g : ℝ → ℝ} {a t : ℝ}
    (ht : t ≠ a) (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) :
    ContDiffAt ℝ n (fun z => if z ≤ a then f z else g z) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with z hz
    simp only [if_pos (le_of_lt (show z < a from hz))]
  · apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with z hz
    simp only [if_neg (not_le.mpr (show a < z from hz))]

private theorem contDiffAt_ite_lt {n : WithTop ℕ∞} {f g : ℝ → ℝ} {a t : ℝ}
    (ht : t ≠ a) (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) :
    ContDiffAt ℝ n (fun z => if z < a then f z else g z) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with z hz
    simp only [if_pos (show z < a from hz)]
  · apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with z hz
    simp only [if_neg (not_lt.mpr (le_of_lt (show a < z from hz)))]

/-- The scalar chain factors are smooth away from their actual piece junctions. -/
theorem phi_contDiffAt {n : WithTop ℕ∞} {t : ℝ}
    (h₁ : t ≠ -(5 / 4 : ℝ)) (h₂ : t ≠ -1) (h₃ : t ≠ 1) (h₄ : t ≠ 5 / 4) :
    ContDiffAt ℝ n ScalarChain.phi t := by
  unfold ScalarChain.phi
  apply contDiffAt_ite_le h₁ contDiffAt_const
  apply contDiffAt_ite_lt h₂ (by fun_prop)
  apply contDiffAt_ite_le h₃ (by fun_prop)
  exact contDiffAt_ite_lt h₄ (by fun_prop) contDiffAt_const

theorem phiD_contDiffAt {n : WithTop ℕ∞} {t : ℝ}
    (h₁ : t ≠ -(5 / 4 : ℝ)) (h₂ : t ≠ -1) (h₃ : t ≠ 1) (h₄ : t ≠ 5 / 4) :
    ContDiffAt ℝ n ScalarChain.phiD t := by
  unfold ScalarChain.phiD
  apply contDiffAt_ite_le h₁ contDiffAt_const
  apply contDiffAt_ite_lt h₂ (by fun_prop)
  apply contDiffAt_ite_le h₃ contDiffAt_const
  exact contDiffAt_ite_lt h₄ (by fun_prop) contDiffAt_const

theorem psi_contDiffAt {n : WithTop ℕ∞} {t : ℝ}
    (h₁ : t ≠ (1 / 2 : ℝ)) (h₂ : t ≠ 3 / 4) (h₃ : t ≠ 1) :
    ContDiffAt ℝ n ScalarChain.psi t := by
  unfold ScalarChain.psi
  apply contDiffAt_ite_le h₁ contDiffAt_const
  apply contDiffAt_ite_le h₂ (by fun_prop)
  exact contDiffAt_ite_lt h₃ (by fun_prop) contDiffAt_const

theorem psiD_contDiffAt {n : WithTop ℕ∞} {t : ℝ}
    (h₁ : t ≠ (1 / 2 : ℝ)) (h₂ : t ≠ 3 / 4) (h₃ : t ≠ 1) :
    ContDiffAt ℝ n ScalarChain.psiD t := by
  unfold ScalarChain.psiD
  apply contDiffAt_ite_le h₁ contDiffAt_const
  apply contDiffAt_ite_le h₂ (by fun_prop)
  exact contDiffAt_ite_lt h₃ (by fun_prop) contDiffAt_const

/-- All scalar junctions needed by `phi`, `psi`, and their reflected arguments. -/
def scalarJunctions : Finset ℝ := {-(5/4), -1, -(3/4), -(1/2), 1/2, 3/4, 1, 5/4}

theorem scalarJunctions_nonzero (b : ℝ) (hb : b ∈ scalarJunctions) : b ≠ 0 := by
  norm_num [scalarJunctions] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem exists_finite_scalar_junctions {R : ℝ} (hR : 0 < R) (U : List (X d))
    (x : X d) {v : X d} (hv : v ≠ 0) :
    ∃ S : Finset ℝ, ∀ t ∉ S, ∀ u ∈ U,
      ⟪u, RadialCompression.compression R (x + t • v)⟫_ℝ ∉ scalarJunctions := by
  classical
  have hfin := compressed_junctions_finite hR U scalarJunctions scalarJunctions_nonzero x hv
  refine ⟨hfin.toFinset, ?_⟩
  intro t ht u hu hj
  exact ht (hfin.mem_toFinset.mpr ⟨u, hu, _, hj, rfl⟩)

theorem neg_mem_scalarJunctions_iff (t : ℝ) : -t ∈ scalarJunctions ↔ t ∈ scalarJunctions := by
  norm_num [scalarJunctions, neg_eq_iff_eq_neg]
  tauto

theorem scalar_contDiffAt_of_not_mem {n : WithTop ℕ∞} {t : ℝ} (ht : t ∉ scalarJunctions) :
    ContDiffAt ℝ n ScalarChain.phi t ∧ ContDiffAt ℝ n ScalarChain.phiD t ∧
    ContDiffAt ℝ n ScalarChain.psi t ∧ ContDiffAt ℝ n ScalarChain.psiD t := by
  simp only [scalarJunctions, Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  rcases ht with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  exact ⟨phi_contDiffAt h₁ h₂ h₇ h₈, phiD_contDiffAt h₁ h₂ h₇ h₈,
    psi_contDiffAt h₅ h₆ h₇, psiD_contDiffAt h₅ h₆ h₇⟩

theorem scalar_neg_contDiffAt_of_not_mem {n : WithTop ℕ∞} {t : ℝ} (ht : t ∉ scalarJunctions) :
    ContDiffAt ℝ n ScalarChain.phi (-t) ∧ ContDiffAt ℝ n ScalarChain.phiD (-t) ∧
    ContDiffAt ℝ n ScalarChain.psi (-t) ∧ ContDiffAt ℝ n ScalarChain.psiD (-t) :=
  scalar_contDiffAt_of_not_mem (fun h => ht ((neg_mem_scalarJunctions_iff t).mp h))

section ChainSmooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : WithTop ℕ∞}

/-- Local smoothness of a link follows from its actual scalar factors. -/
theorem link_comp_contDiffAt (a b : E →L[ℝ] ℝ) (x : E)
    (ha : a x ∉ scalarJunctions) (hb : b x ∉ scalarJunctions) :
    ContDiffAt ℝ n (fun y => ScalarChain.link (a y) (b y)) x := by
  have pa := (scalar_contDiffAt_of_not_mem (n := n) ha).2.2.1.comp x a.contDiff.contDiffAt
  have na := (scalar_neg_contDiffAt_of_not_mem (n := n) ha).2.2.1.comp x a.contDiff.contDiffAt.neg
  have pb := (scalar_contDiffAt_of_not_mem (n := n) hb).1.comp x b.contDiff.contDiffAt
  have nb := (scalar_neg_contDiffAt_of_not_mem (n := n) hb).1.comp x b.contDiff.contDiffAt.neg
  exact (na.mul nb).sub (pa.mul pb)

theorem links_comp_contDiffAt (a : E →L[ℝ] ℝ) (coords : List (E →L[ℝ] ℝ)) (x : E)
    (ha : a x ∉ scalarJunctions) (hc : ∀ c ∈ coords, c x ∉ scalarJunctions) :
    ContDiffAt ℝ n (fun y => ScalarChain.links (a y) (coords.map (fun c => c y))) x := by
  induction coords generalizing a with
  | nil => exact contDiffAt_const
  | cons b tail ih =>
    exact (link_comp_contDiffAt a b x ha (hc b (by simp))).add
      (ih b (hc b (by simp)) (fun c h => hc c (by simp [h])))

theorem chain_comp_contDiffAt (coords : List (E →L[ℝ] ℝ)) (x : E)
    (hc : ∀ c ∈ coords, c x ∉ scalarJunctions) :
    ContDiffAt ℝ n (fun y => ScalarChain.chain (coords.map (fun c => c y))) x := by
  cases coords with
  | nil => exact contDiffAt_const
  | cons a tail =>
    exact ((scalar_contDiffAt_of_not_mem (hc a (by simp))).1.comp x a.contDiff.contDiffAt).neg.add
      (links_comp_contDiffAt a tail x (hc a (by simp)) (fun c h => hc c (by simp [h])))

end ChainSmooth

/-- The actual chain is locally smooth at every point whose coordinates avoid
the finite junction set. -/
theorem value_contDiffAt {n : WithTop ℕ∞} (m : ℕ) (x : X m)
    (hx : ∀ i : Fin m, x i ∉ scalarJunctions) : ContDiffAt ℝ n (ScalarChain.value m) x := by
  apply chain_comp_contDiffAt
  intro c hc
  simp only [ScalarChain.coordinateMaps, List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  exact hx i

/-- The actual gradient is locally smooth, so its Hessian really exists at
all regular points; this is not an assumed Hessian certificate. -/
theorem gradient_contDiffAt {n : WithTop ℕ∞} (m : ℕ) (x : X m)
    (hx : ∀ i : Fin m, x i ∉ scalarJunctions) : ContDiffAt ℝ n (ScalarChain.gradient m) x := by
  have hd := (value_contDiffAt (n := n + 1) m x hx).fderiv_right (m := n) le_rfl
  have h := (InnerProductSpace.toDual ℝ (X m)).symm.contDiff.contDiffAt.comp x hd
  have he : (fun y => (InnerProductSpace.toDual ℝ (X m)).symm
      (fderiv ℝ (ScalarChain.value m) y)) = ScalarChain.gradient m := by
    funext y
    rw [(ScalarChain.value_hasFDerivAt m y).fderiv]
    exact (InnerProductSpace.toDual ℝ (X m)).symm_apply_apply _
  simpa only [Function.comp_def, he] using h

theorem hessian_exists (m : ℕ) (x : X m)
    (hx : ∀ i : Fin m, x i ∉ scalarJunctions) :
    HasFDerivAt (ScalarChain.gradient m) (fderiv ℝ (ScalarChain.gradient m) x) x :=
  ((gradient_contDiffAt (n := 1) m x hx).differentiableAt le_rfl).hasFDerivAt

/-- Symmetry is derived from the locally smooth actual chain value. -/
theorem hessian_symmetric (m : ℕ) (x : X m)
    (hx : ∀ i : Fin m, x i ∉ scalarJunctions) (u v : X m) :
    ⟪fderiv ℝ (ScalarChain.gradient m) x u, v⟫_ℝ =
      ⟪u, fderiv ℝ (ScalarChain.gradient m) x v⟫_ℝ := by
  have he : fderiv ℝ (ScalarChain.value m) = fun y => innerSL ℝ (ScalarChain.gradient m y) :=
    funext (fun y => (ScalarChain.value_hasFDerivAt m y).fderiv)
  have hd : HasFDerivAt (fderiv ℝ (ScalarChain.value m))
      ((innerSL ℝ).comp (fderiv ℝ (ScalarChain.gradient m) x)) x := by
    rw [he]
    exact (innerSL ℝ).hasFDerivAt.comp x (hessian_exists m x hx)
  have hs := (value_contDiffAt (n := 2) m x hx).isSymmSndFDerivAt (by norm_num)
  have hh := hs u v
  rw [hd.fderiv] at hh
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply, real_inner_comm u] using hh

end ExactZO.CompressedLinePieces
