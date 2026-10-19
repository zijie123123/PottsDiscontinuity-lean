/- Original assembly of the ported finite-box limits and the exact frozen cylinder bridge. -/
module

public import PottsDiscontinuity.FK.FrozenLimitBridge
public import PottsDiscontinuity.FK.FreeBoxLimit
public import PottsDiscontinuity.FK.WiredBoxLimits
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK

noncomputable section

/-- The origin-centered ported box is exactly the frozen box. -/
theorem latticeBox_origin_eq_box (n : ℕ) : latticeBox (0, 0) n = box n := by
  simp only [latticeBox, box, zero_sub, zero_add]

/-- The generic frozen-law extension agrees with the ported free finite-box law. -/
theorem frozenExtendedProbabilityMeasure_free (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    frozenExtendedProbabilityMeasure θ (latticeBox c r) 0 (boxConfiguration c r) =
      boxProbabilityMeasure θ c r := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law (boxGraph c r) θ (frozenBoundaryCondition (latticeBox c r) 0)).map
    (boxConfiguration c r)).toMeasure =
    ((law (boxGraph c r) θ (BoundaryCondition.free ∅)).map (boxConfiguration c r)).toMeasure
  have hlaw : law (boxGraph c r) θ (frozenBoundaryCondition (latticeBox c r) 0) =
      law (boxGraph c r) θ (BoundaryCondition.free ∅) := by
    apply law_eq_of_boundary_partition_eq
    simp [frozenBoundaryCondition, BoundaryCondition.free]
  rw [hlaw]

/-- The generic frozen-law extension agrees with the ported wired finite-box law. -/
theorem frozenExtendedProbabilityMeasure_wired (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    frozenExtendedProbabilityMeasure θ (latticeBox c r) 1 (wiredBoxConfiguration c r) =
      wiredBoxProbabilityMeasure θ c r := by
  rfl

/-- Every weak limit of the ported free origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_freeBox_tendsto (θ : Parameters)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 0
    (fun n => latticeBox (0, 0) n) latticeBox_origin_eq_box
    (fun n => boxConfiguration (0, 0) n) ?_ μ ?_
  · intro n C f
    exact boxConfiguration_at (0, 0) n C f
  · simpa only [frozenExtendedProbabilityMeasure_free] using hμ

/-- Every weak limit of the ported wired origin-box laws has the exact frozen characterization. -/
theorem isRCInfiniteVolumeLimit_of_wiredBox_tendsto (θ : Parameters)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ)) :
    IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ.toMeasure := by
  refine isRCInfiniteVolumeLimit_of_extended_tendsto θ 1
    (fun n => latticeBox (0, 0) n) latticeBox_origin_eq_box
    (fun n => wiredBoxConfiguration (0, 0) n) ?_ μ ?_
  · intro n C f
    exact wiredBoxConfiguration_at (0, 0) n C f
  · simpa only [frozenExtendedProbabilityMeasure_wired] using hμ

/-- For independent interior edge probabilities and cluster weights at least one,
both frozen boundary conditions have infinite-volume limits. -/
theorem exists_isRCInfiniteVolumeLimit_interior (θ : Parameters) (i : Fin 2) :
    ∃ μ, IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ := by
  fin_cases i
  · obtain ⟨μ, hμ, _⟩ := Internal.freeBoxLimit_existsUnique (q := θ)
    exact ⟨μ.toMeasure, isRCInfiniteVolumeLimit_of_freeBox_tendsto θ μ
      (hμ (fun _ => (0, 0)) (fun n => n)
        origin_latticeBox_nested origin_latticeBox_exhaustive)⟩
  · obtain ⟨μ, hμ⟩ := wiredBoxProbabilityMeasure_exists_limit θ
    exact ⟨μ.toMeasure, isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ μ hμ⟩

/-- The frozen random-cluster box limits exist for every `p ∈ [0,1]`, `q ≥ 1`,
and either free or wired boundary condition. -/
theorem exists_isRCInfiniteVolumeLimit
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (i : Fin 2) :
    ∃ μ, PottsDiscontinuity.IsRCInfiniteVolumeLimit p q i μ := by
  by_cases hp0 : (p : ℝ) = 0
  · have hp : p = ⟨0, by norm_num⟩ := Subtype.ext hp0
    rw [hp]
    exact exists_isRCInfiniteVolumeLimit_zero q i
  by_cases hp1 : (p : ℝ) = 1
  · have hp : p = ⟨1, by norm_num⟩ := Subtype.ext hp1
    rw [hp]
    exact exists_isRCInfiniteVolumeLimit_one q i
  let θ : Parameters :=
    { val := q
      property := hq
      edgeProbability := ⟨p, lt_of_le_of_ne p.property.1 (Ne.symm hp0),
        lt_of_le_of_ne p.property.2 hp1⟩ }
  exact exists_isRCInfiniteVolumeLimit_interior θ i

end
end PottsDiscontinuity.FK
