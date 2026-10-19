module

public import PottsDiscontinuity.Potts.ObservedPartitionLimits

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

variable {A : Type*} [Fintype A]

theorem infiniteFreePartition_measurableSet (v : A → ℤ × ℤ) (R : Setoid A) :
    MeasurableSet {ω | infiniteFreePartition v ω = R} := by
  apply partition_event_measurable
  intro a b
  have he : {ω | infiniteFreePartition v ω a b} = infiniteFreeDataEvent {(v a, v b)} := by
    ext ω; simp [infiniteFreeDataEvent]; rfl
  rw [he, ← iUnion_freeDataEvent]
  exact MeasurableSet.iUnion (fun n => (freeDataEvent_isClopen n _).isOpen.measurableSet)

theorem infiniteWiredPartition_measurableSet (v : A → Option (ℤ × ℤ)) (R : Setoid A) :
    MeasurableSet {ω | infiniteWiredPartition v ω = R} := by
  apply partition_event_measurable
  intro a b
  have he : {ω | infiniteWiredPartition v ω a b} = infiniteMergedDataEvent {(v a, v b)} := by
    ext ω; simp [infiniteMergedDataEvent]; rfl
  rw [he, ← iInter_wiredDataEvent]
  exact MeasurableSet.iInter (fun n => (wiredDataEvent_isClopen n _).isOpen.measurableSet)

end
end PottsDiscontinuity.Potts
