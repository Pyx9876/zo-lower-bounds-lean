import ExactZO.Oracle

noncomputable section
open MeasureTheory
namespace ExactZO

/-- Erasing derivative replies is measurable on the full transcript space. -/
theorem measurable_valueHistory {d : ℕ} : Measurable (@valueHistory d) := by
  exact Transcript.measurable_map
    (measurable_valueEntry_mk.comp
      (measurable_linearEntry_point.prodMk measurable_linearEntry_value))

/-- The rank-zero embedding maps both action branches measurably. -/
theorem measurable_embedValueAction {d : ℕ} :
    Measurable (fun act : (valueModel d).Action =>
      match act with
      | .query x => (OracleModel.Action.query (valueQuery x) : (linearModel d).Action)
      | .output x => OracleModel.Action.output x) := by
  have h := OracleModel.measurable_action_elim (valueModel d)
    ((OracleModel.measurable_action_query (linearModel d)).comp measurable_valueQuery)
    (OracleModel.measurable_action_output (linearModel d))
  convert h using 1
  funext act
  cases act <;> rfl

/-- The exact oracle embedding preserves joint seed/transcript measurability. -/
theorem jointlyMeasurable_embedValue {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (policy : Ω → (valueModel d).Algorithm)
    (hpolicy : (valueModel d).JointlyMeasurable policy) :
    (linearModel d).JointlyMeasurable (fun ω => embedValueAlgorithm (policy ω)) := by
  exact measurable_embedValueAction.comp
    (hpolicy.comp (measurable_fst.prodMk (measurable_valueHistory.comp measurable_snd)))

end ExactZO
