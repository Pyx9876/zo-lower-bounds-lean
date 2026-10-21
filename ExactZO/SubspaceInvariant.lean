import ExactZO.SubspaceBudget

/-! A single potential for restricted moves and complete/partial restart blocks.
It retains the actual objective value, actual frame and the same matrix H. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace ExactZO.SubspaceInvariant
open StageGeometry FrameGeometry SubspaceBudget

def charge {d : ℕ} (H : X d →L[ℝ] X d) (U : List (X d)) : ℝ :=
  (U.map fun u => (⟪u,H u⟫_ℝ)⁻¹).sum

@[simp] theorem charge_nil {d : ℕ} (H : X d →L[ℝ] X d) : charge H [] = 0 := rfl

@[simp] theorem charge_append {d : ℕ} (H : X d →L[ℝ] X d)
    (U : List (X d)) (u : X d) :
    charge H (U++[u]) = charge H U + (⟪u,H u⟫_ℝ)⁻¹ := by
  simp [charge]

theorem charge_eq_sum {d : ℕ} (H : X d →L[ℝ] X d) (U : List (X d)) :
    charge H U = ∑ i : Fin U.length, (⟪U.get i,H (U.get i)⟫_ℝ)⁻¹ := by
  have heq : List.ofFn (fun i : Fin U.length => (⟪U.get i,H (U.get i)⟫_ℝ)⁻¹) =
      U.map (fun u => (⟪u,H u⟫_ℝ)⁻¹) := by
    change List.ofFn ((fun u : X d => (⟪u,H u⟫_ℝ)⁻¹) ∘ U.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [← List.sum_ofFn,heq]
  rfl

theorem charge_nonneg {d : ℕ} (H : X d →L[ℝ] X d) (U : List (X d))
    (hc : ∀ u ∈ U, 0 < ⟪u,H u⟫_ℝ) : 0 ≤ charge H U := by
  rw [charge_eq_sum]
  exact Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hc _ (List.get_mem U i))).le)

def potential {d : ℕ} (H : X d →L[ℝ] X d) (L E : ℝ) (r q : ℕ)
    (U : List (X d)) : ℝ := (q:ℝ)*(r:ℝ)^2/(L*E)+charge H U

def stepDecrease (L ε : ℝ) : ℝ := 35*ε^2/(512*L)
def timeParameter (L Δ ε : ℝ) : ℝ := L*Δ/ε^2
def restrictedLimit (L Δ ε : ℝ) : ℕ := ⌊512*timeParameter L Δ ε/35⌋₊
def expansionLimit (L Δ E ε : ℝ) (r : ℕ) : ℕ :=
  ⌊10*E*timeParameter L Δ ε/r+(r:ℝ)/4⌋₊
def totalFuel (L Δ E ε : ℝ) (r : ℕ) : ℕ :=
  restrictedLimit L Δ ε + expansionLimit L Δ E ε r + 1

structure StateBudget {d : ℕ} (f : Objective d) (H : X d →L[ℝ] X d)
    (L E ε : ℝ) (r : ℕ) (x : X d) (U : List (X d)) (j q : ℕ) : Prop where
  ortho : OrthoList U
  curv : ∀ u ∈ U, 0 < ⟪u,H u⟫_ℝ
  size : U.length < r
  budget : (j:ℝ)*stepDecrease L ε+(ε^2/10)*potential H L E r q U ≤ f.value 0-f.value x

theorem initial {d : ℕ} (f : Objective d) (H : X d →L[ℝ] X d)
    (L E ε : ℝ) {r : ℕ} (hr : 0 < r) :
    StateBudget f H L E ε r 0 [] 0 0 := by
  constructor
  · exact orthoList_nil d
  · simp
  · simpa using hr
  · simp [potential]

theorem StateBudget.sublevel {d : ℕ} {f : Objective d} {H : X d →L[ℝ] X d}
    {L E ε : ℝ} {r : ℕ} {x : X d} {U : List (X d)} {j q : ℕ}
    (h : StateBudget f H L E ε r x U j q) (hL : 0 < L) (hE : 0 < E) :
    f.value x ≤ f.value 0 := by
  have hp : 0 ≤ potential H L E r q U := by
    unfold potential
    exact add_nonneg (by positivity) (charge_nonneg H U h.curv)
  have hs : 0 ≤ (j:ℝ)*stepDecrease L ε := by unfold stepDecrease; positivity
  have hb := h.budget
  nlinarith [mul_nonneg (by positivity : 0 ≤ ε^2/10) hp]

theorem StateBudget.restricted_move {d : ℕ} {f : Objective d} {H : X d →L[ℝ] X d}
    {L E ε : ℝ} {r : ℕ} {x y : X d} {U : List (X d)} {j q : ℕ}
    (h : StateBudget f H L E ε r x U j q)
    (hd : f.value y ≤ f.value x-stepDecrease L ε) :
    StateBudget f H L E ε r y U (j+1) q := by
  refine ⟨h.ortho,h.curv,h.size,?_⟩
  have hb := h.budget
  push_cast
  nlinarith

/-- Appending an expansion is charged before any reset; trace is never summed across blocks. -/
theorem StateBudget.expansion_move {d : ℕ} {f : Objective d} {H : X d →L[ℝ] X d}
    {L E ε : ℝ} {r : ℕ} {x y u : X d} {U : List (X d)} {j q : ℕ}
    (h : StateBudget f H L E ε r x U j q) (hL : 0 < L) (hE : 0 < E)
    (hH : UpperMatrix L E H) (hu : ‖u‖=1)
    (ho : ∀ v ∈ U, ⟪u,v⟫_ℝ=0) (hc : 0 < ⟪u,H u⟫_ℝ)
    (hd : ε^2/(10*⟪u,H u⟫_ℝ) ≤ f.value x-f.value y) :
    StateBudget f H L E ε r y
      (if U.length+1=r then [] else U++[u]) j
      (if U.length+1=r then q+1 else q) := by
  have hUa := h.ortho.append_unit hu ho
  have hca : ∀ v ∈ U++[u], 0 < ⟪v,H v⟫_ℝ := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h.curv v hv
    · have hvu := List.mem_singleton.mp hv
      simpa only [hvu] using hc
  have hpot : potential H L E r q (U++[u]) =
      potential H L E r q U+(⟪u,H u⟫_ℝ)⁻¹ := by simp [potential]; ring
  have hbud : (j:ℝ)*stepDecrease L ε+(ε^2/10)*potential H L E r q (U++[u]) ≤
      f.value 0-f.value y := by
    have heq : ε^2/(10*⟪u,H u⟫_ℝ) = (ε^2/10)*(⟪u,H u⟫_ℝ)⁻¹ := by ring
    rw [heq] at hd
    rw [hpot]
    have hb := h.budget
    nlinarith
  by_cases hs : U.length+1=r
  · simp only [hs,if_pos]
    refine ⟨orthoList_nil _,by simp,by simpa using (Nat.zero_le U.length).trans_lt h.size,?_⟩
    have hh := frame_inverse_charge hUa hL hE H hH hca
    rw [← charge_eq_sum] at hh
    have hl : (U++[u]).length=r := by simpa using hs
    rw [hl] at hh
    have hp : potential H L E r (q+1) [] ≤ potential H L E r q (U++[u]) := by
      simp only [potential,charge_nil,Nat.cast_add,Nat.cast_one,add_zero]
      convert add_le_add_left hh ((q:ℝ)*(r:ℝ)^2/(L*E)) using 1 <;> ring
    exact (add_le_add_left (mul_le_mul_of_nonneg_left hp (by positivity)) _).trans hbud
  · simp only [hs,if_neg]
    exact ⟨hUa,hca,by simp; have:=h.size; omega,hbud⟩

theorem StateBudget.counts_real {d : ℕ} {f : Objective d} {H : X d →L[ℝ] X d}
    {L Δ E ε : ℝ} {r : ℕ} {x : X d} {U : List (X d)} {j q : ℕ}
    (h : StateBudget f H L E ε r x U j q) (hL : 0 < L) (hE : 0 < E)
    (hε : 0 < ε) (hH : UpperMatrix L E H) (hgap : HasGap f Δ) :
    (j:ℝ) ≤ 512*timeParameter L Δ ε/35 ∧
      ((q*r+U.length:ℕ):ℝ) ≤ 10*E*timeParameter L Δ ε/r+(r:ℝ)/4 := by
  have hLE : 0 < L*E := mul_pos hL hE
  have hc : 0 < stepDecrease L ε := by unfold stepDecrease; positivity
  have heps : 0 < ε^2/10 := by positivity
  have hp0 : 0 ≤ potential H L E r q U := by
    unfold potential
    exact add_nonneg (by positivity) (charge_nonneg H U h.curv)
  obtain ⟨lower,hlo,hgap0⟩ := hgap
  have hg : f.value 0-f.value x ≤ Δ := by linarith [hlo x]
  have hb := h.budget.trans hg
  have hj0 : 0 ≤ (j:ℝ)*stepDecrease L ε := by positivity
  constructor
  · have h1 : (j:ℝ)*stepDecrease L ε ≤ Δ := by
      nlinarith [mul_nonneg heps.le hp0]
    have h2 := (le_div_iff₀ hc).mpr h1
    have hid : Δ/stepDecrease L ε = 512*timeParameter L Δ ε/35 := by
      unfold stepDecrease timeParameter
      field_simp
      ring
    rwa [hid] at h2
  · have hcs := frame_inverse_charge h.ortho hL hE H hH h.curv
    rw [← charge_eq_sum] at hcs
    have hlower : ((q:ℝ)*(r:ℝ)^2+(U.length:ℝ)^2)/(L*E) ≤
        potential H L E r q U := by
      rw [add_div]
      exact add_le_add_left hcs _
    have hpmax : potential H L E r q U ≤ Δ/(ε^2/10) := by
      apply (le_div_iff₀ heps).mpr
      nlinarith
    have hsq := (div_le_iff₀ hLE).mp (hlower.trans hpmax)
    have hid : Δ/(ε^2/10)*(L*E) = 10*E*timeParameter L Δ ε := by
      unfold timeParameter
      field_simp
      ring
    rw [hid] at hsq
    have hr : (0:ℝ) < r := by exact_mod_cast (Nat.zero_le U.length).trans_lt h.size
    have hh := count_le_of_square_budget hr hsq
    simpa only [Nat.cast_add,Nat.cast_mul] using hh

theorem StateBudget.counts_bound {d : ℕ} {f : Objective d} {H : X d →L[ℝ] X d}
    {L Δ E ε : ℝ} {r : ℕ} {x : X d} {U : List (X d)} {j q : ℕ}
    (h : StateBudget f H L E ε r x U j q) (hL : 0 < L) (hE : 0 < E)
    (hε : 0 < ε) (hH : UpperMatrix L E H) (hgap : HasGap f Δ) :
    j ≤ restrictedLimit L Δ ε ∧ q*r+U.length ≤ expansionLimit L Δ E ε r := by
  have hb := h.counts_real hL hE hε hH hgap
  exact ⟨Nat.le_floor hb.1,Nat.le_floor hb.2⟩

end ExactZO.SubspaceInvariant
