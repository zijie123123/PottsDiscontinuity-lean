/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimitV1
public import PottsDiscontinuity.FK.BoxTranslation

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

/-- The unique source-defined free-box weak limit is invariant under every
integer translation of the original lattice configuration. -/
theorem freeBoxLimit_translation_invariant (q : Parameters) (a : LatticeVertex) :
    ProbabilityMeasure.map
        (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q))
        (latticeConfigurationTranslate a) =
      Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hproperty := (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
  have horigin : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n) atTop (𝓝 μ) :=
    hproperty (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hshift : Tendsto (fun n => boxProbabilityMeasure q a n) atTop (𝓝 μ) := by
    apply hproperty (fun _ => a) (fun n => n)
    · intro n
      exact latticeBox_mono a (Nat.le_succ n)
    · intro v
      obtain ⟨n, hn⟩ := origin_latticeBox_exhaustive (latticeTranslate (-a) v)
      refine ⟨n, ?_⟩
      simpa [latticeTranslate] using
        (mem_latticeBox_translate_iff a (0, 0) (latticeTranslate (-a) v) n).mpr hn
  have hmap : Tendsto
      (fun n => ProbabilityMeasure.map (boxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) atTop
      (𝓝 (ProbabilityMeasure.map μ (latticeConfigurationTranslate a))) :=
    ((ProbabilityMeasure.continuous_map
      (latticeConfigurationTranslationHomeomorph a).continuous_toFun).continuousAt.tendsto).comp
      horigin
  have hterms :
      (fun n => ProbabilityMeasure.map (boxProbabilityMeasure q (0, 0) n)
        (latticeConfigurationTranslate a)) =
      (fun n => boxProbabilityMeasure q a n) := by
    funext n
    simpa [latticeTranslate] using boxProbabilityMeasure_translation_map q a (0, 0) n
  rw [hterms] at hmap
  have hEq := tendsto_nhds_unique hmap hshift
  simpa [μ] using hEq

end
end PottsDiscontinuity.FK.Internal
