module

public import PottsDiscontinuity.Potts.BooleanDataLimits
public import PottsDiscontinuity.Potts.BoolMeasureBridge

/-! Finite connection partitions and expectations of their colouring kernels. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

variable {A X : Type*}

/-- Equivalence relations on a finite observation set form a finite type. -/
instance finiteObservedSetoid [Finite A] : Finite (Setoid A) := by
  let f : Setoid A → (A × A → Bool) := fun R z => decide (R z.1 z.2)
  apply Finite.of_injective f
  intro R S h
  apply Setoid.ext
  intro a b
  have hh := congrArg (fun c : Bool => c = true) (congrFun h (a, b))
  simpa only [f, decide_eq_true_eq] using hh.to_iff

local instance observedSetoidFintype [Finite A] : Fintype (Setoid A) := Fintype.ofFinite _

/-- The literal expectation of any function of a finite connection partition. -/
def partitionExpectation [Finite A] [MeasurableSpace X] (μ : Measure X)
    (r : X → Setoid A) (K : Setoid A → ℝ) : ℝ :=
  ∑ R : Setoid A, μ.real {x | r x = R} * K R

theorem partition_eq_event [Fintype A] (r : X → Setoid A) (R : Setoid A) :
    {x | r x = R} = booleanEventPattern (fun z : A × A => {x | r x z.1 z.2})
      (Finset.univ.filter (fun z : A × A => R z.1 z.2))
      (Finset.univ.filter (fun z : A × A => ¬ R z.1 z.2)) := by
  ext x
  constructor
  · intro h
    change r x = R at h
    subst h
    simp [booleanEventPattern]
  · rintro ⟨hp, hn⟩
    apply Setoid.ext
    intro a b
    by_cases h : R a b
    · exact ⟨fun _ => h, fun _ => hp (a, b) (by simp [h])⟩
    · exact ⟨fun hr => (hn (a, b) (by simp [h]) hr).elim, fun hr => (h hr).elim⟩

/-- Convergence of all positive relation moments gives the entire partition law. -/
theorem partition_probability_tendsto [Fintype A] [MeasurableSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (r : ℕ → X → Setoid A) (rinf : X → Setoid A)
    (hr : ∀ n a b, MeasurableSet {x | r n x a b})
    (hri : ∀ a b, MeasurableSet {x | rinf x a b})
    (hmom : ∀ F : Finset (A × A), Tendsto
      (fun n => (μs n).toMeasure.real {x | ∀ z ∈ F, r n x z.1 z.2}) atTop
      (𝓝 (μ.toMeasure.real {x | ∀ z ∈ F, rinf x z.1 z.2}))) (R : Setoid A) :
    Tendsto (fun n => (μs n).toMeasure.real {x | r n x = R}) atTop
      (𝓝 (μ.toMeasure.real {x | rinf x = R})) := by
  simp_rw [partition_eq_event]
  exact boolean_pattern_probability_tendsto μs μ (fun n (z : A × A) => {x | r n x z.1 z.2})
    (fun (z : A × A) => {x | rinf x z.1 z.2}) (fun n (z : A × A) => hr n z.1 z.2)
    (fun (z : A × A) => hri z.1 z.2) hmom _ _

theorem partitionExpectation_tendsto [Fintype A] [MeasurableSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (r : ℕ → X → Setoid A) (rinf : X → Setoid A) (K : Setoid A → ℝ)
    (h : ∀ R : Setoid A, Tendsto (fun n => (μs n).toMeasure.real {x | r n x = R}) atTop
      (𝓝 (μ.toMeasure.real {x | rinf x = R}))) :
    Tendsto (fun n => partitionExpectation (μs n).toMeasure (r n) K) atTop
      (𝓝 (partitionExpectation μ.toMeasure rinf K)) := by
  exact tendsto_finsetSum _ (fun R _ => (h R).mul_const (K R))

/-- On a finite sample space, partition expectation is the ordinary weighted sum. -/
theorem partitionExpectation_pmf [Finite A] [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (p : PMF X) (r : X → Setoid A) (K : Setoid A → ℝ) :
    partitionExpectation p.toMeasure r K = ∑ x : X, (p x).toReal * K (r x) := by
  unfold partitionExpectation
  simp_rw [finite_pmf_measureReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (r x)]
  · simp
  · intro R _ hR
    simp [Ne.symm hR]
  · simp

theorem partition_event_measurable [Fintype A] [MeasurableSpace X]
    (r : X → Setoid A) (hr : ∀ a b, MeasurableSet {x | r x a b}) (R : Setoid A) :
    MeasurableSet {x | r x = R} := by
  rw [partition_eq_event]
  exact booleanEventPattern_measurable _ (fun (z : A × A) => hr z.1 z.2) _ _

/-- Partition expectation commutes with the actual pushforward law. -/
theorem partitionExpectation_map {Y : Type*} [Fintype A] [MeasurableSpace X] [MeasurableSpace Y]
    (p : PMF X) (f : X → Y) (hf : Measurable f) (r : Y → Setoid A) (K : Setoid A → ℝ)
    (hr : ∀ a b, MeasurableSet {y | r y a b}) :
    partitionExpectation (p.map f).toMeasure r K = partitionExpectation p.toMeasure (r ∘ f) K := by
  unfold partitionExpectation
  apply Finset.sum_congr rfl
  intro R _
  congr 1
  simp only [Measure.real]
  rw [PMF.toMeasure_map_apply _ _ _ hf (partition_event_measurable r hr R)]
  rfl

end
end PottsDiscontinuity.Potts
