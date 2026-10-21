import ExactZO.ScalarChain

/-! First unfinished-coordinate and weighted first-derivative estimates for
Appendix A's explicit scalar chain. All estimates use its actual differential. -/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 2000000

namespace ExactZO.ScalarChain

theorem incoming_eq_one {a b : ℝ} (ha : 1 ≤ |a|) (hb : |b| ≤ 1) :
    incoming a b = 1 := by
  simp only [incoming, psi_signed_sum_one ha, phiD_eq_one hb, mul_one]

theorem incoming_weighted (a b : ℝ) : |incoming a b * b| ≤ 1 := by
  have hs := psi_signed_sum_bounds a
  have hw := phiD_weighted b
  calc
    |incoming a b * b| = (psi (-a) + psi a) * |b * phiD b| := by
      rw [incoming, mul_assoc, abs_mul, abs_of_nonneg hs.1]
      congr 1
      ring_nf
    _ ≤ 1 * 1 := mul_le_mul hs.2 hw (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem psiD_signed_weighted (a : ℝ) :
    |a| * (psiD (-a) + psiD a) ≤ 3 := by
  rcases le_total a 0 with ha | ha
  · rw [psiD_flat (show a ≤ 1 / 2 by linarith), add_zero]
    have h := psiD_weighted (-a)
    simpa only [abs_mul, abs_neg, abs_of_nonneg (psiD_bounds (-a)).1] using h
  · rw [psiD_flat (show -a ≤ 1 / 2 by linarith), zero_add]
    have h := psiD_weighted a
    simpa only [abs_mul, abs_of_nonneg (psiD_bounds a).1] using h

theorem outgoing_weighted (a b : ℝ) : |outgoing a b * a| ≤ 27 / 4 := by
  have hp := mul_le_mul_of_nonneg_left (phi_bounds b).2 (psiD_bounds a).1
  have hn := mul_le_mul_of_nonneg_left (phi_bounds (-b)).2 (psiD_bounds (-a)).1
  have hsum : outgoing a b ≤ (psiD (-a) + psiD a) * (9 / 4) := by
    unfold outgoing
    linarith
  have h := mul_le_mul_of_nonneg_right hsum (abs_nonneg a)
  have hw := psiD_signed_weighted a
  rw [abs_mul, abs_of_nonneg (outgoing_bounds a b).1]
  nlinarith

section Differential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linkDifferential_self_bound (a b : E →L[ℝ] ℝ) (x : E) :
    |linkDifferential a b x x| ≤ 31 / 4 := by
  have ho := outgoing_weighted (a x) (b x)
  have hi := incoming_weighted (a x) (b x)
  calc
    |linkDifferential a b x x| ≤ |outgoing (a x) (b x) * a x| +
        |incoming (a x) (b x) * b x| := by
      simpa only [linkDifferential, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul, abs_neg] using
        (abs_add_le (-(outgoing (a x) (b x) * a x))
          (-(incoming (a x) (b x) * b x)))
    _ ≤ 31 / 4 := by linarith

theorem linksDifferential_self_bound (a : E →L[ℝ] ℝ)
    (coords : List (E →L[ℝ] ℝ)) (x : E) :
    |linksDifferential a coords x x| ≤ (31 / 4 : ℝ) * coords.length := by
  induction coords generalizing a with
  | nil => simp [linksDifferential]
  | cons b tail ih =>
    have hh := linkDifferential_self_bound a b x
    have ht := ih b
    simp only [linksDifferential, ContinuousLinearMap.add_apply,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (by linarith)

theorem chainDifferential_self_bound (coords : List (E →L[ℝ] ℝ)) (x : E) :
    |chainDifferential coords x x| ≤ (31 / 4 : ℝ) * coords.length := by
  cases coords with
  | nil => simp [chainDifferential]
  | cons a tail =>
    have hh := phiD_weighted (a x)
    have ht := linksDifferential_self_bound a tail x
    simp only [chainDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    have htriangle := abs_add_le (-(phiD (a x) * a x)) (linksDifferential a tail x x)
    rw [abs_neg] at htriangle
    rw [mul_comm (phiD (a x))] at *
    linarith

theorem linksDifferential_first_barrier (a b : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x v : E)
    (ha : 1 ≤ |a x|) (hp : ∀ c ∈ pref, 1 ≤ |c x|)
    (hb : |b x| ≤ 1) (hv : b v = 1) (hav : 0 ≤ a v)
    (hn : ∀ c ∈ pref ++ b :: tail, 0 ≤ c v) :
    linksDifferential a (pref ++ b :: tail) x v ≤ -1 := by
  induction pref generalizing a with
  | nil =>
    have hout := mul_nonneg (outgoing_bounds (a x) (b x)).1 hav
    have htail := linksDifferential_nonpos b tail x v (by rw [hv]; norm_num)
      (fun c hc => hn c (by simp [hc]))
    simp only [List.nil_append, linksDifferential, linkDifferential,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      incoming_eq_one ha hb, hv, neg_mul, one_mul]
    linarith
  | cons c pref ih =>
    have hcv : 0 ≤ c v := hn c (by simp)
    have hrest := ih c (hp c (by simp)) (fun d hd => hp d (by simp [hd])) hcv
      (fun d hd => hn d (by simp [hd]))
    have hout := mul_nonneg (outgoing_bounds (a x) (c x)).1 hav
    have hin := mul_nonneg (incoming_bounds (a x) (c x)).1 hcv
    simp only [List.cons_append, linksDifferential, linkDifferential,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul]
    linarith

theorem chainDifferential_first_barrier (b : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x v : E)
    (hp : ∀ c ∈ pref, 1 ≤ |c x|) (hb : |b x| ≤ 1) (hv : b v = 1)
    (hn : ∀ c ∈ pref ++ b :: tail, 0 ≤ c v) :
    chainDifferential (pref ++ b :: tail) x v ≤ -1 := by
  cases pref with
  | nil =>
    have htail := linksDifferential_nonpos b tail x v (by rw [hv]; norm_num)
      (fun c hc => hn c (by simp [hc]))
    simp only [List.nil_append, chainDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      phiD_eq_one hb, hv, mul_one, neg_mul]
    linarith
  | cons a pref =>
    have hav : 0 ≤ a v := hn a (by simp)
    have hrest := linksDifferential_first_barrier a b pref tail x v
      (hp a (by simp)) (fun c hc => hp c (by simp [hc])) hb hv hav
      (fun c hc => hn c (by simp [hc]))
    have hh := mul_nonneg (phiD_bounds (a x)).1 hav
    simp only [List.cons_append, chainDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linarith

theorem exists_first_incomplete (coords : List (E →L[ℝ] ℝ)) (x : E)
    (h : ∃ c ∈ coords, |c x| < 1) :
    ∃ pref b tail, coords = pref ++ b :: tail ∧ |b x| < 1 ∧
      ∀ c ∈ pref, 1 ≤ |c x| := by
  induction coords with
  | nil => simp at h
  | cons a coords ih =>
    by_cases ha : |a x| < 1
    · exact ⟨[], a, coords, rfl, ha, by simp⟩
    · have ht : ∃ c ∈ coords, |c x| < 1 := by
        obtain ⟨c, hc, hcsmall⟩ := h
        rcases List.mem_cons.mp hc with hc | hc
        · exact (ha (hc ▸ hcsmall)).elim
        · exact ⟨c, hc, hcsmall⟩
      obtain ⟨pref, b, tail, heq, hb, hp⟩ := ih ht
      refine ⟨a :: pref, b, tail, by simp [heq], hb, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_of_not_gt ha
      · exact hp c hc

theorem chainDifferential_exists_barrier (coords : List (E →L[ℝ] ℝ)) (x : E)
    (h : ∃ c ∈ coords, |c x| < 1) :
    ∃ b ∈ coords, |b x| < 1 ∧ ∀ v : E, b v = 1 →
      (∀ c ∈ coords, 0 ≤ c v) → chainDifferential coords x v ≤ -1 := by
  obtain ⟨pref, b, tail, rfl, hb, hp⟩ := exists_first_incomplete coords x h
  refine ⟨b, by simp, hb, ?_⟩
  intro v hv hn
  exact chainDifferential_first_barrier b pref tail x v hp hb.le hv hn

end Differential

theorem gradient_weighted (m : ℕ) (x : X m) :
    |⟪x, gradient m x⟫_ℝ| ≤ (31 / 4 : ℝ) * m := by
  have he := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := X m)
    (y := chainDifferential (coordinateMaps m) x) (x := x)
  rw [real_inner_comm]
  change |⟪(InnerProductSpace.toDual ℝ (X m)).symm
    (chainDifferential (coordinateMaps m) x), x⟫_ℝ| ≤ _
  rw [he]
  simpa only [coordinateMaps, List.length_ofFn] using
    chainDifferential_self_bound (coordinateMaps m) x

theorem gradient_weighted_coarse (m : ℕ) (x : X m) :
    |⟪x, gradient m x⟫_ℝ| ≤ (25 / 2 : ℝ) * m := by
  have h := gradient_weighted m x
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gradient_exists_barrier (m : ℕ) (x : X m) (h : ∃ i : Fin m, |x i| < 1) :
    ∃ i : Fin m, |x i| < 1 ∧ gradient m x i ≤ -1 := by
  have hc : ∃ c ∈ coordinateMaps m, |c x| < 1 := by
    obtain ⟨i, hi⟩ := h
    exact ⟨EuclideanSpace.proj i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  obtain ⟨c, hc, hsmall, hbar⟩ := chainDifferential_exists_barrier (coordinateMaps m) x hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  refine ⟨i, hsmall, ?_⟩
  rw [gradient_coord]
  apply hbar
  · change (EuclideanSpace.single i (1 : ℝ)) i = 1
    simp [EuclideanSpace.single_apply]
  · intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    change 0 ≤ (EuclideanSpace.single i (1 : ℝ)) j
    simp only [EuclideanSpace.single_apply]
    split_ifs <;> norm_num


/-- The actual coordinate at any first unfinished position is at most minus one. -/
theorem gradient_first_barrier (m : ℕ) (x : X m) (j : Fin m)
    (hj : |x j| ≤ 1) (hfirst : ∀ i : Fin m, i < j → 1 ≤ |x i|) :
    gradient m x j ≤ -1 := by
  let coords := coordinateMaps m
  have hlen : j.val < coords.length := by simpa [coords, coordinateMaps] using j.isLt
  have hget : coords[j.val] = EuclideanSpace.proj j := by simp [coords, coordinateMaps]
  have heq : coords.take j.val ++ EuclideanSpace.proj j :: coords.drop (j.val + 1) = coords := by
    rw [← hget, List.cons_getElem_drop_succ, List.take_append_drop]
  rw [gradient_coord]
  change chainDifferential coords x (EuclideanSpace.single j 1) ≤ -1
  rw [← heq]
  apply chainDifferential_first_barrier
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp hc
    have him : i < m := by
      simpa [coords, coordinateMaps] using (lt_min_iff.mp hi).2
    simpa [coords, coordinateMaps] using hfirst ⟨i, him⟩ (lt_min_iff.mp hi).1
  · exact hj
  · change (EuclideanSpace.single j (1 : ℝ)) j = 1
    simp [EuclideanSpace.single_apply]
  · intro c hc
    rw [heq] at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    change 0 ≤ (EuclideanSpace.single j (1 : ℝ)) i
    simp only [EuclideanSpace.single_apply]
    split_ifs <;> norm_num

end ExactZO.ScalarChain
