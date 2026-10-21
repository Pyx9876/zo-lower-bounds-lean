import ExactZO.FrameGeometry
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Trace charges are taken separately on each orthonormal restart block. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace ExactZO.SubspaceBudget
open StageGeometry FrameGeometry

theorem trace_eq_sum_quadratic {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (X d)) (H : X d →L[ℝ] X d) :
    LinearMap.trace ℝ (X d) H.toLinearMap = ∑ i, ⟪b i, H (b i)⟫_ℝ := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]

theorem frame_curvature_sum_le_trace {d : ℕ} {U : List (X d)}
    (hU : OrthoList U) (H : X d →L[ℝ] X d)
    (hpos : ∀ x, 0 ≤ ⟪x, H x⟫_ℝ) :
    (∑ i : Fin U.length, ⟪U.get i, H (U.get i)⟫_ℝ) ≤
      LinearMap.trace ℝ (X d) H.toLinearMap := by
  classical
  have hu := orthoList_orthonormal hU
  obtain ⟨W,b,hW,hb⟩ := hu.toSubtypeRange.exists_orthonormalBasis_extension
  rw [trace_eq_sum_quadratic b H]
  have hs : (Finset.univ.image U.get) ⊆ W := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hW (Set.mem_range_self i)
  calc
    _ = ∑ x ∈ Finset.univ.image U.get, ⟪x, H x⟫_ℝ := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => hu.linearIndependent.injective hij
    _ ≤ ∑ x ∈ W, ⟪x,H x⟫_ℝ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ => hpos x)
    _ = ∑ i : W, ⟪b i,H (b i)⟫_ℝ := by
      simp only [hb]
      exact (Finset.sum_attach W (fun x => ⟪x,H x⟫_ℝ)).symm

/-- A positive block's inverse curvatures consume a quadratic gap budget. -/
theorem block_decrease {k : ℕ} {L E ε : ℝ} (hk : 0 < k)
    (hL : 0 < L) (hE : 0 < E) (hε : 0 < ε)
    (curv dec : Fin k → ℝ) (hc : ∀ i, 0 < curv i)
    (hs : ∑ i, curv i ≤ L*E)
    (hd : ∀ i, ε^2/(10*curv i) < dec i) :
    ε^2*(k:ℝ)^2/(10*L*E) < ∑ i, dec i := by
  have hn : (0:ℝ) < k := by exact_mod_cast hk
  have hsumpos : 0 < ∑ i, curv i := by
    apply Finset.sum_pos
    · intro i _; exact hc i
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hk⟩⟩
  have ht := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ : Fin k => (1:ℝ))
    (fun i _ => hc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_pow, one_div] at ht
  have hb : (k:ℝ)^2/(L*E) ≤ ∑ i, (curv i)⁻¹ :=
    (div_le_div_of_nonneg_left (sq_nonneg _) hsumpos hs).trans ht
  have hstrict : (∑ i, ε^2/(10*curv i)) < ∑ i, dec i := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hk⟩⟩
    · intro i _; exact hd i
  have heq : (∑ i, ε^2/(10*curv i)) = (ε^2/10)*∑ i, (curv i)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [heq] at hstrict
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ε^2/10)
  calc
    _ = (ε^2/10)*((k:ℝ)^2/(L*E)) := by ring
    _ ≤ _ := hm
    _ < _ := hstrict

/-- Cauchy--Schwarz for the true curvatures of one actual orthonormal frame. -/
theorem frame_inverse_charge {d : ℕ} {U : List (X d)} (hU : OrthoList U)
    {L E : ℝ} (hL : 0 < L) (hE : 0 < E)
    (H : X d →L[ℝ] X d) (hH : UpperMatrix L E H)
    (hcurv : ∀ u ∈ U, 0 < ⟪u,H u⟫_ℝ) :
    (U.length:ℝ)^2/(L*E) ≤ ∑ i : Fin U.length, (⟪U.get i,H (U.get i)⟫_ℝ)⁻¹ := by
  by_cases hn : U.length = 0
  · have hnil : U = [] := List.length_eq_zero_iff.mp hn
    subst U
    simp
  have hk : 0 < U.length := Nat.pos_of_ne_zero hn
  have hc : ∀ i : Fin U.length, 0 < ⟪U.get i,H (U.get i)⟫_ℝ :=
    fun i => hcurv _ (List.get_mem U i)
  have hsumpos : 0 < ∑ i : Fin U.length, ⟪U.get i,H (U.get i)⟫_ℝ := by
    apply Finset.sum_pos
    · intro i _; exact hc i
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hk⟩⟩
  have hs := (frame_curvature_sum_le_trace hU H hH.2.1).trans hH.2.2.2
  have ht := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun _ : Fin U.length => (1:ℝ)) (fun i _ => hc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_pow, one_div] at ht
  exact (div_le_div_of_nonneg_left (sq_nonneg _) hsumpos hs).trans ht

/-- A partial restart block costs at most r/4 after division by r. -/
theorem count_le_of_square_budget {q s r B : ℝ} (hr : 0 < r)
    (hbudget : q*r^2+s^2 ≤ B) : q*r+s ≤ B/r+r/4 := by
  apply (mul_le_mul_iff_of_pos_right hr).mp
  calc
    (q*r+s)*r ≤ B+r^2/4 := by nlinarith [sq_nonneg (s-r/2)]
    _ = (B/r+r/4)*r := by field_simp; ring

/-- The real cost ledger includes terminal estimates, centers and failed proposals. -/
theorem capacity_ledger_bound {d r E T n J Q : ℝ}
    (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) (hT : 1 ≤ T)
    (hn0 : 0 ≤ n) (hJ : J ≤ 512*T/35)
    (hn : n ≤ 10*E*T/r+r/4)
    (hQ : Q ≤ 2*(d+r-1)*(n+1)+2*(r-1)*J+8*T+2*n) :
    Q < 40*d*E*T/r+30*(d+T)*r := by
  have hJcoef := mul_le_mul_of_nonneg_left hJ (by nlinarith : 0 ≤ 2*(r-1))
  have hncoef := mul_le_mul_of_nonneg_left hrd hn0
  have hbase : Q ≤ 4*d*n+4*d+(1024/35:ℝ)*(r-1)*T+8*T := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hn (by nlinarith : 0 ≤ 4*d)
  have hmiddle : 4*d*n ≤ 40*d*E*T/r+d*r := by
    convert hprod using 1 <;> ring
  have hdr : d ≤ d*r := by nlinarith
  have htr : 0 < T*r := by positivity
  nlinarith

end ExactZO.SubspaceBudget
