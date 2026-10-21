import Mathlib.Data.List.OfFn
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
Finite transcripts carry the measurable structure of the countable disjoint
union of their finite Cartesian powers. The sigma lemmas below are used only
with countable indices when distributing a product over the disjoint union.
-/

noncomputable section

open Set MeasurableSpace

namespace ExactZO.Transcript

variable {α β γ Ω : Type*}

/-- Transport a measurable space across an explicit equivalence. -/
def equivComap (e : α ≃ β) [MeasurableSpace β] :
    @MeasurableEquiv α β (MeasurableSpace.comap e inferInstance) inferInstance := by
  letI : MeasurableSpace α := MeasurableSpace.comap e inferInstance
  exact
    { toEquiv := e
      measurable_toFun := comap_measurable e
      measurable_invFun := by
        intro s hs
        rcases hs with ⟨t, ht, rfl⟩
        convert ht using 1
        ext x
        simp }

section Sigma

variable {ι : Type*} {B : ι → Type*} [∀ i, MeasurableSpace (B i)]

theorem measurable_sigma_mk (i : ι) :
    Measurable (Sigma.mk i : B i → Sigma B) := by
  intro s hs
  exact (measurableSet_iInf.mp hs) i

theorem measurable_sigma_iff [MeasurableSpace γ] {f : Sigma B → γ} :
    Measurable f ↔ ∀ i, Measurable (fun b : B i => f ⟨i, b⟩) := by
  constructor
  · intro hf i
    exact hf.comp (measurable_sigma_mk i)
  · intro hf s hs
    exact measurableSet_iInf.mpr (fun i => hf i hs)

theorem measurableEmbedding_sigma_mk (i : ι) :
    MeasurableEmbedding (Sigma.mk i : B i → Sigma B) where
  injective := sigma_mk_injective
  measurable := measurable_sigma_mk i
  measurableSet_image' := by
    classical
    intro s hs
    apply measurableSet_iInf.mpr
    intro j
    change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
    by_cases hji : j = i
    · subst j
      simpa only [sigma_mk_injective.preimage_image] using hs
    · have hempty : (Sigma.mk j) ⁻¹' (Sigma.mk i '' s) = ∅ := by
        ext x
        constructor
        · rintro ⟨y, hy, he⟩
          exact (hji (congrArg Sigma.fst he).symm).elim
        · intro hx
          exact hx.elim
      rw [hempty]
      exact MeasurableSet.empty

/-- A joint map on a product with a countable coproduct is measurable exactly
when every full seed-times-fiber restriction is measurable. -/
theorem measurable_prod_sigma_iff [Countable ι] [MeasurableSpace Ω]
    [MeasurableSpace γ] {f : Ω × Sigma B → γ} :
    Measurable f ↔ ∀ i, Measurable (fun p : Ω × B i => f (p.1, ⟨i, p.2⟩)) := by
  let inc (i : ι) : Ω × B i → Ω × Sigma B := fun p => (p.1, ⟨i, p.2⟩)
  have hinc (i : ι) : MeasurableEmbedding (inc i) := by
    exact (show MeasurableEmbedding (id : Ω → Ω) from .id).prodMap
      (measurableEmbedding_sigma_mk i)
  constructor
  · intro hf i
    exact hf.comp (hinc i).measurable
  · intro hf s hs
    have heq : f ⁻¹' s = ⋃ i, inc i '' ((fun p => f (inc i p)) ⁻¹' s) := by
      ext p
      rcases p with ⟨ω, ⟨i, b⟩⟩
      constructor
      · intro hp
        exact mem_iUnion.mpr ⟨i, ⟨(ω, b), hp, rfl⟩⟩
      · intro hp
        rcases mem_iUnion.mp hp with ⟨j, q, hq, hqp⟩
        exact hqp ▸ hq
    rw [heq]
    exact MeasurableSet.iUnion (fun i => (hinc i).measurableSet_image' (hf i hs))

end Sigma

/-- The standard measurable space of finite lists, transported from the
countable disjoint union of finite Cartesian powers. -/
instance listMeasurableSpace [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

/-- This equivalence witnesses both directions of the transcript encoding. -/
def listEquiv [MeasurableSpace α] : List α ≃ᵐ (Σ n : ℕ, Fin n → α) :=
  equivComap List.equivSigmaTuple

theorem measurable_ofFn [MeasurableSpace α] (n : ℕ) :
    Measurable (List.ofFn : (Fin n → α) → List α) :=
  (listEquiv (α := α)).symm.measurable.comp (measurable_sigma_mk n)

theorem measurable_list_iff [MeasurableSpace α] [MeasurableSpace β]
    {f : List α → β} :
    Measurable f ↔ ∀ n, Measurable (fun a : Fin n → α => f (List.ofFn a)) := by
  constructor
  · intro hf n
    exact hf.comp (measurable_ofFn n)
  · intro hf
    have hg : Measurable (fun s : Σ n : ℕ, Fin n → α => f (List.ofFn s.2)) :=
      measurable_sigma_iff.mpr hf
    have h := hg.comp (listEquiv (α := α)).measurable
    change Measurable (fun l : List α => f (List.ofFn l.get)) at h
    simpa only [List.ofFn_get] using h

theorem measurable_prod_list_iff [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {f : Ω × List α → β} :
    Measurable f ↔
      ∀ n, Measurable (fun p : Ω × (Fin n → α) => f (p.1, List.ofFn p.2)) := by
  constructor
  · intro hf n
    exact hf.comp (measurable_fst.prodMk ((measurable_ofFn n).comp measurable_snd))
  · intro hf
    have hg : Measurable (fun p : Ω × (Σ n : ℕ, Fin n → α) =>
        f (p.1, List.ofFn p.2.2)) := measurable_prod_sigma_iff.mpr hf
    have h := hg.comp
      (measurable_fst.prodMk ((listEquiv (α := α)).measurable.comp measurable_snd))
    change Measurable (fun p : Ω × List α => f (p.1, List.ofFn p.2.get)) at h
    simpa only [List.ofFn_get] using h

theorem measurable_map [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) : Measurable (List.map f) := by
  apply measurable_list_iff.mpr
  intro n
  have h : Measurable (fun a : Fin n → α => fun i => f (a i)) :=
    measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  simpa only [List.map_ofFn, Function.comp_def] using (measurable_ofFn n).comp h

end ExactZO.Transcript
