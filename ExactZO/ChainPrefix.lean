import ExactZO.ScalarChain

/-! Exact value and differential identities for hiding an unfinished chain
coordinate at zero. These are identities of the explicit chain, not additional
premises on a wrapper. -/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace ExactZO.ScalarChain

section Differential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gate at the end of a nonempty list, with its first entry supplied separately. -/
def terminalGate (a : E →L[ℝ] ℝ) : List (E →L[ℝ] ℝ) → E → ℝ
  | [], x => psi (-(a x)) + psi (a x)
  | b :: tail, x => terminalGate b tail x

/-- The incoming coefficient at the coordinate following `pref`.
The empty prefix has the chain's initial coefficient one. -/
def prefixGate : List (E →L[ℝ] ℝ) → E → ℝ
  | [], _ => 1
  | a :: tail, x => terminalGate a tail x

theorem terminalGate_bounds (a : E →L[ℝ] ℝ) (pref : List (E →L[ℝ] ℝ)) (x : E) :
    0 ≤ terminalGate a pref x ∧ terminalGate a pref x ≤ 1 := by
  induction pref generalizing a with
  | nil => exact psi_signed_sum_bounds (a x)
  | cons b pref ih => exact ih b

theorem prefixGate_bounds (pref : List (E →L[ℝ] ℝ)) (x : E) :
    0 ≤ prefixGate pref x ∧ prefixGate pref x ≤ 1 := by
  cases pref with
  | nil => norm_num [prefixGate]
  | cons a pref => exact terminalGate_bounds a pref x

theorem terminalGate_append (a b : E →L[ℝ] ℝ)
    (pref : List (E →L[ℝ] ℝ)) (x : E) :
    terminalGate a (pref ++ [b]) x = psi (-(b x)) + psi (b x) := by
  induction pref generalizing a with
  | nil => rfl
  | cons c pref ih => exact ih c

theorem prefixGate_append (b : E →L[ℝ] ℝ) (pref : List (E →L[ℝ] ℝ)) (x : E) :
    prefixGate (pref ++ [b]) x = psi (-(b x)) + psi (b x) := by
  cases pref with
  | nil => rfl
  | cons a pref => exact terminalGate_append a b pref x

theorem linkDifferential_zero_last (a u : E →L[ℝ] ℝ) (x : E) (hu : u x = 0) :
    linkDifferential a u x = linkDifferential a 0 x -
      (psi (-(a x)) + psi (a x)) • u := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [linkDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, hu,
    incoming, phiD_zero, mul_one, smul_eq_mul, mul_zero, add_zero]
  ring

theorem linksDifferential_zero_last (a u : E →L[ℝ] ℝ)
    (pref : List (E →L[ℝ] ℝ)) (x : E) (hu : u x = 0) :
    linksDifferential a (pref ++ [u]) x = linksDifferential a (pref ++ [0]) x -
      terminalGate a pref x • u := by
  induction pref generalizing a with
  | nil =>
    simpa only [List.nil_append, linksDifferential, add_zero, terminalGate] using
      linkDifferential_zero_last a u x hu
  | cons b pref ih =>
    simp only [List.cons_append, linksDifferential, terminalGate, ih b]
    abel

theorem chainDifferential_zero_last (u : E →L[ℝ] ℝ)
    (pref : List (E →L[ℝ] ℝ)) (x : E) (hu : u x = 0) :
    chainDifferential (pref ++ [u]) x = chainDifferential (pref ++ [0]) x -
      prefixGate pref x • u := by
  cases pref with
  | nil =>
    simp [chainDifferential, linksDifferential, prefixGate, hu]
  | cons a pref =>
    simp only [List.cons_append, chainDifferential, prefixGate,
      linksDifferential_zero_last a u pref x hu]
    abel

/-- The unseen tail contributes no values when the separating coordinate is zero. -/
theorem chain_comp_prefix_zero (u : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x : E) (hu : u x = 0)
    (ht : ∀ c ∈ tail, |c x| ≤ 1 / 2) :
    chain ((pref ++ u :: tail).map (fun c : E →L[ℝ] ℝ => c x)) =
      chain ((pref ++ [0]).map (fun c : E →L[ℝ] ℝ => c x)) := by
  have htail : ∀ b ∈ tail.map (fun c : E →L[ℝ] ℝ => c x), |b| ≤ 1 / 2 := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact ht c hc
  simpa only [List.map_append, List.map_cons, List.map_nil, hu,
    ContinuousLinearMap.zero_apply] using
    chain_prefix (pref.map (fun c : E →L[ℝ] ℝ => c x)) (tail.map (fun c : E →L[ℝ] ℝ => c x)) htail

/-- The exact derivative correction at a zero separating coordinate.
The scalar coefficient is independently proved to lie in `[0,1]`. -/
theorem chainDifferential_prefix_zero (u : E →L[ℝ] ℝ)
    (pref tail : List (E →L[ℝ] ℝ)) (x : E) (hu : u x = 0)
    (ht : ∀ c ∈ tail, |c x| ≤ 1 / 2) :
    chainDifferential (pref ++ u :: tail) x =
      chainDifferential (pref ++ [0]) x - prefixGate pref x • u := by
  rw [chainDifferential_prefix u pref tail x (by rw [hu]; norm_num) ht]
  exact chainDifferential_zero_last u pref x hu

end Differential
end ExactZO.ScalarChain
