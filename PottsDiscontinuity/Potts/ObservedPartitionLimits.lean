module

public import PottsDiscontinuity.Potts.ConditionedConnectionLimit
public import PottsDiscontinuity.Potts.FinitePartitionLimits
public import PottsDiscontinuity.Potts.FreeConnectionLimit

/-! Distributions and expectations of finite observed connection partitions. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

variable {A : Type*} [Fintype A]

def observedFreePartition (v : A → ℤ × ℤ) (n : ℕ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (localFreeGraph (rcInfiniteOpenGraph ω) n).reachableSetoid.comap v

def infiniteFreePartition (v : A → ℤ × ℤ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (rcInfiniteOpenGraph ω).reachableSetoid.comap v

def observedWiredPartition (v : A → Option (ℤ × ℤ)) (n : ℕ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (localWiredSetoid (rcInfiniteOpenGraph ω) (n + 1)).comap v

def infiniteWiredPartition (v : A → Option (ℤ × ℤ)) (ω : FK.LatticeConfiguration) : Setoid A :=
  (infiniteMergedSetoid (rcInfiniteOpenGraph ω)).comap v

omit [Fintype A] in
private theorem observedFree_moment_event (v : A → ℤ × ℤ) (n : ℕ) (F : Finset (A × A)) :
    {ω | ∀ z ∈ F, observedFreePartition v n ω z.1 z.2} =
      freeDataEvent n (F.image (fun z => (v z.1, v z.2))) := by
  ext ω
  change (∀ z ∈ F, (localFreeGraph (rcInfiniteOpenGraph ω) n).Reachable (v z.1) (v z.2)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact h a ha
  · intro h z hz
    exact h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

omit [Fintype A] in
private theorem infiniteFree_moment_event (v : A → ℤ × ℤ) (F : Finset (A × A)) :
    {ω | ∀ z ∈ F, infiniteFreePartition v ω z.1 z.2} =
      infiniteFreeDataEvent (F.image (fun z => (v z.1, v z.2))) := by
  ext ω
  change (∀ z ∈ F, (rcInfiniteOpenGraph ω).Reachable (v z.1) (v z.2)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact h a ha
  · intro h z hz
    exact h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

omit [Fintype A] in
private theorem observedWired_moment_event (v : A → Option (ℤ × ℤ)) (n : ℕ) (F : Finset (A × A)) :
    {ω | ∀ z ∈ F, observedWiredPartition v n ω z.1 z.2} =
      wiredDataEvent (n + 1) (F.image (fun z => (v z.1, v z.2))) := by
  ext ω
  change (∀ z ∈ F, localWiredSetoid (rcInfiniteOpenGraph ω) (n + 1) (v z.1) (v z.2)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact h a ha
  · intro h z hz
    exact h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

omit [Fintype A] in
private theorem infiniteWired_moment_event (v : A → Option (ℤ × ℤ)) (F : Finset (A × A)) :
    {ω | ∀ z ∈ F, infiniteWiredPartition v ω z.1 z.2} =
      infiniteMergedDataEvent (F.image (fun z => (v z.1, v z.2))) := by
  ext ω
  change (∀ z ∈ F, infiniteMergedSetoid (rcInfiniteOpenGraph ω) (v z.1) (v z.2)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact h a ha
  · intro h z hz
    exact h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem free_observed_partition_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (v : A → ℤ × ℤ) (R : Setoid A) :
    Tendsto (fun n => (closedBoxProbabilityMeasure θ n).toMeasure.real
      {ω | observedFreePartition v n ω = R}) atTop
      (𝓝 (μ.toMeasure.real {ω | infiniteFreePartition v ω = R})) := by
  apply partition_probability_tendsto
  · intro n a b
    have he : {ω | observedFreePartition v n ω a b} = freeDataEvent n {(v a, v b)} := by
      ext ω; simp [freeDataEvent]; rfl
    rw [he]
    exact (freeDataEvent_isClopen _ _).isOpen.measurableSet
  · intro a b
    have he : {ω | infiniteFreePartition v ω a b} = infiniteFreeDataEvent {(v a, v b)} := by
      ext ω; simp [infiniteFreeDataEvent]; rfl
    rw [he, ← iUnion_freeDataEvent]
    exact MeasurableSet.iUnion (fun n => (freeDataEvent_isClopen n _).isOpen.measurableSet)
  · intro F
    simp_rw [observedFree_moment_event, infiniteFree_moment_event]
    exact free_connection_moments_tendsto θ μ hμ _

theorem wired_observed_partition_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (v : A → Option (ℤ × ℤ)) (R : Setoid A) :
    Tendsto (fun n => (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure.real
      {ω | observedWiredPartition v n ω = R}) atTop
      (𝓝 (μ.toMeasure.real {ω | infiniteWiredPartition v ω = R})) := by
  apply partition_probability_tendsto
  · intro n a b
    have he : {ω | observedWiredPartition v n ω a b} = wiredDataEvent (n + 1) {(v a, v b)} := by
      ext ω; simp [wiredDataEvent]; rfl
    rw [he]
    exact (wiredDataEvent_isClopen _ _).isOpen.measurableSet
  · intro a b
    have he : {ω | infiniteWiredPartition v ω a b} = infiniteMergedDataEvent {(v a, v b)} := by
      ext ω; simp [infiniteMergedDataEvent]; rfl
    rw [he, ← iInter_wiredDataEvent]
    exact MeasurableSet.iInter (fun n => (wiredDataEvent_isClopen n _).isOpen.measurableSet)
  · intro F
    simp_rw [observedWired_moment_event, infiniteWired_moment_event]
    exact conditioned_connection_moments_tendsto q hq β hβ μ hμ _

/-- Every function of the free observed partition, including its colouring
kernel, has convergent expectation. -/
theorem free_partitionExpectation_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (v : A → ℤ × ℤ) (K : Setoid A → ℝ) :
    Tendsto (fun n => partitionExpectation (closedBoxProbabilityMeasure θ n).toMeasure
      (observedFreePartition v n) K) atTop
      (𝓝 (partitionExpectation μ.toMeasure (infiniteFreePartition v) K)) :=
  partitionExpectation_tendsto _ μ _ _ K (free_observed_partition_tendsto θ μ hμ v)

/-- Every function of the merged wired observed partition has convergent expectation. -/
theorem wired_partitionExpectation_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (v : A → Option (ℤ × ℤ)) (K : Setoid A → ℝ) :
    Tendsto (fun n => partitionExpectation
      (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure
      (observedWiredPartition v n) K) atTop
      (𝓝 (partitionExpectation μ.toMeasure (infiniteWiredPartition v) K)) :=
  partitionExpectation_tendsto _ μ _ _ K (wired_observed_partition_tendsto q hq β hβ μ hμ v)

end
end PottsDiscontinuity.Potts
