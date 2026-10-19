module

public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.Potts.ColourKernelPartitions
public import PottsDiscontinuity.Potts.GhostPartitionExpectation
public import PottsDiscontinuity.Potts.GhostCylinder

/-! Exact literal Potts cylinders as expectations of marked connection partitions. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace
local instance ghostCylinderPartitionLiteralDecidable (n : ℕ) : DecidableEq (LiteralBond (box n)) :=
  fun _ _ => Classical.propDecidable _
local instance ghostCylinderPartitionBoundary (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _
local instance ghostCylinderPartitionShell (n : ℕ) : Fintype (OuterShellEdge n) := Fintype.ofFinite _
local instance ghostCylinderPartitionDiscrete {V : Type*} (G : SimpleGraph V) :
    DiscreteMeasurableSpace (FK.Configuration G) := ⟨fun _ => trivial⟩

variable {A : Type*} [Fintype A]

omit [Fintype A] in
private theorem restored_observedWiredPartition (n : ℕ) (hn : 0 < n)
    (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    observedWiredPartition (Option.map v) n
      (openExtension (box (n + 1)) (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η))) =
    (ghostOpenGraph (box n) ω).reachableSetoid.comap
      (markedMap (fun a => some (⟨v a, hv a⟩ : ↥(box n : Set (ℤ × ℤ)))) none) := by
  apply Setoid.ext
  intro a b
  change (finiteWiredConnectionGraph (rcInfiniteOpenGraph
    (openExtension (box (n + 1)) (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η))))
      (n + 1)).reachableSetoid (boxGhostProjection (n + 1) (Option.map v a))
      (boxGhostProjection (n + 1) (Option.map v b)) ↔ _
  rw [← wiredObservationGraph_eq, boxObservation_openExtension_self,
    restored_wiredObservation_reachableSetoid]
  change (ghostOpenGraph (box n) ω).reachableSetoid
    (collapseOuterGhost n (boxGhostProjection (n + 1) (Option.map v a)))
    (collapseOuterGhost n (boxGhostProjection (n + 1) (Option.map v b))) ↔ _
  rw [collapseOuterGhost_projection, collapseOuterGhost_projection]
  have hp (a : Option A) : boxGhostProjection n (Option.map v a) =
      markedMap (fun a => some (⟨v a, hv a⟩ : ↥(box n : Set (ℤ × ℤ)))) none a := by
    cases a with
    | none => rfl
    | some a => simp [boxGhostProjection, hv a, markedMap]
  rw [hp a, hp b]
  rfl

theorem potts_ghost_cylinder_eq_partitionExpectation
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (n : ℕ) (hn : 0 < n) (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q (box n),
      if ∀ a, σ ⟨v a, hv a⟩ = ξ a then pottsProb q (box n) β i σ else 0) =
    partitionExpectation (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure
      (observedWiredPartition (Option.map v) n)
      (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) := by
  let vf : A → ↥(box n : Set (ℤ × ℤ)) := fun a => ⟨v a, hv a⟩
  refine Eq.trans ?_ ((pottsProb_ghost_cylinder q hq (box n) β i hi vf ξ).trans ?_)
  · apply Finset.sum_congr
    · ext σ; simp
    · intro σ _
      split_ifs <;> rfl
  symm
  change partitionExpectation (((conditionedOuterLaw (fkParameters q hq β hβ) n).map
    (openExtension (box (n + 1)))).toMeasure) (observedWiredPartition (Option.map v) n) _ = _
  rw [partitionExpectation_map _ _ measurable_from_top _ _ (by
    intro a b
    have he : {ω | observedWiredPartition (Option.map v) n ω a b} =
        wiredDataEvent (n + 1) {(Option.map v a, Option.map v b)} := by
      ext ω; simp [wiredDataEvent]; rfl
    rw [he]
    exact (wiredDataEvent_isClopen _ _).isOpen.measurableSet)]
  rw [conditionedOuterLaw_partitionExpectation q hq β hβ n hn _
    (fun ω => (ghostOpenGraph (box n) ω).reachableSetoid.comap (markedMap (some ∘ vf) none)) _
    (restored_observedWiredPartition n hn v hv)]
  apply Finset.sum_congr
  · ext ω; simp
  · intro ω _
    exact congrArg (fun c : ℝ => ghostRCProbability q (box n) β ω * c)
      (pinnedClusterCylinderProbability_factor (ghostOpenGraph (box n) ω).reachableSetoid
        (some ∘ vf) ξ none (boundaryColor q i hi)).symm

end
end PottsDiscontinuity.Potts
