import ExactZO.ValueProcedure
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace
namespace ExactZO.STP
variable {d : ℕ}

/-- Three true scalar replies choose a point; the center wins every tie
with its proposals. The two proposals may tie with each other. -/
def choose (x p q : X d) (vx vp vq : ℝ) : X d :=
  if min vp vq < vx then if vp ≤ vq then p else q else x

def step (f : Objective d) (h : ℝ) (x a : X d) : X d :=
  choose x (x + h • a) (x - h • a) (f.value x)
    (f.value (x + h • a)) (f.value (x - h • a))

theorem choose_value (f : Objective d) (x p q : X d) :
    f.value (choose x p q (f.value x) (f.value p) (f.value q)) =
      min (f.value x) (min (f.value p) (f.value q)) := by
  unfold choose
  split_ifs with hm hp
  · rw [min_eq_right hm.le, min_eq_left hp]
  · rw [min_eq_right hm.le, min_eq_right (le_of_not_ge hp)]
  · exact (min_eq_left (le_of_not_gt hm)).symm

theorem step_value (f : Objective d) (h : ℝ) (x a : X d) :
    f.value (step f h x a) =
      min (f.value x) (min (f.value (x + h • a)) (f.value (x - h • a))) :=
  choose_value f x _ _

theorem step_monotone (f : Objective d) (h : ℝ) (x a : X d) :
    f.value (step f h x a) ≤ f.value x := by
  rw [step_value]
  exact min_le_left _ _

theorem step_le_plus (f : Objective d) (h : ℝ) (x a : X d) :
    f.value (step f h x a) ≤ f.value (x + h • a) := by
  rw [step_value]
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem step_le_minus (f : Objective d) (h : ℝ) (x a : X d) :
    f.value (step f h x a) ≤ f.value (x - h • a) := by
  rw [step_value]
  exact (min_le_right _ _).trans (min_le_right _ _)

def iterates (f : Objective d) (h : ℝ) (a : ℕ → X d) : ℕ → X d
  | 0 => 0
  | n + 1 => step f h (iterates f h a n) (a n)

theorem iterates_sublevel (f : Objective d) (h : ℝ) (a : ℕ → X d) (n : ℕ) :
    f.value (iterates f h a n) ≤ f.value 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (step_monotone f h _ _).trans ih

end ExactZO.STP
