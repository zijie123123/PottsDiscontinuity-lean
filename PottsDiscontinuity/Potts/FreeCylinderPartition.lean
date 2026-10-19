module

public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.Potts.ColourKernelPartitions
public import PottsDiscontinuity.Potts.FreeBoundary

/-! The exact finite free Potts cylinder is a function of the observed FK partition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance cylinderVertexDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq ↥(V : Set (ℤ × ℤ)) := fun _ _ => Classical.propDecidable _
local instance cylinderVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype ↥(V : Set (ℤ × ℤ)) := Fintype.ofFinite _
local instance cylinderEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := fun _ _ => Classical.propDecidable _
local instance cylinderEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance freeCylinderDiscrete {V : Type*} (G : SimpleGraph V) :
    DiscreteMeasurableSpace (FK.Configuration G) := ⟨fun _ => trivial⟩

variable {A : Type*} [Fintype A]

theorem potts_free_cylinder_eq_partitionExpectation
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (n : ℕ)
    (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q (box n),
      if ∀ a, σ ⟨v a, hv a⟩ = ξ a then pottsProb q (box n) β 0 σ else 0) =
    partitionExpectation (closedBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure
      (observedFreePartition v n) (fun R => clusterCylinderProbability R id ξ) := by
  trans ∑ ω : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet → Bool,
    rcProb (box n) (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 0 ω *
      clusterCylinderProbability (rcOpenGraph (box n) ω).reachableSetoid (fun a => ⟨v a, hv a⟩) ξ
  · apply Eq.trans _ (pottsProb_free_cylinder q hq (box n) β hβ (fun a => ⟨v a, hv a⟩) ξ)
    apply Finset.sum_congr
    · ext σ; simp
    · intro σ _
      split_ifs <;> rfl
  symm
  change partitionExpectation (((FK.law _ (fkParameters q hq β hβ)
    (FK.frozenBoundaryCondition (box n) 0)).map (closedExtension (box n))).toMeasure)
    (observedFreePartition v n) _ = _
  rw [partitionExpectation_map _ _ measurable_from_top _ _ (by
    intro a b
    have he : {ω | observedFreePartition v n ω a b} = freeDataEvent n {(v a, v b)} := by
      ext ω; simp [freeDataEvent]; rfl
    rw [he]
    exact (freeDataEvent_isClopen _ _).isOpen.measurableSet), partitionExpectation_pmf]
  rw [← (FK.boolConfigurationEquiv (squareLattice.induce (box n : Set (ℤ × ℤ)))).sum_comp]
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω _
    rw [FK.law_apply, ENNReal.toReal_ofReal (FK.configurationProbability_pos _ _ _ _).le,
      FK.configurationProbability_eq_rcProb]
    have hR : observedFreePartition v n
        (closedExtension (box n) (FK.boolConfigurationEquiv _ ω)) =
        (rcOpenGraph (box n) ω).reachableSetoid.comap (fun a => ⟨v a, hv a⟩) := by
      apply Setoid.ext
      intro a b
      change (localFreeGraph (rcInfiniteOpenGraph (closedExtension (box n) (FK.boolConfigurationEquiv _ ω))) n).Reachable
        (v a) (v b) ↔ _
      rw [localFreeGraph_reachable_inside n _ ⟨v a, hv a⟩ ⟨v b, hv b⟩,
        boxObservation_closedExtension_self, FK.rcOpenGraph_eq]
      rfl
    simp only [Function.comp_def, hR]
    rw [← clusterCylinderProbability_factor]

end
end PottsDiscontinuity.Potts
