module

public import PottsDiscontinuity.Potts.GhostCylinderPartition
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.SpinObservation
public import PottsDiscontinuity.Potts.PottsLimitConstruction

/-! Literal positive-boundary Potts limits and merged Edwards–Sokal colouring. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
local instance wiredLimitLiteralDecidable (n : ℕ) : DecidableEq (LiteralBond (box n)) :=
  fun _ _ => Classical.propDecidable _
local instance wiredLimitBoundary (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _

theorem wired_potts_cylinder_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinCylinder q A ξ))
      atTop (𝓝 (wiredESCylinder q φ.toMeasure i hi A ξ)) := by
  have ht := wired_partitionExpectation_tendsto q hq β hβ φ hφ
    (Option.map (fun a : ↥A => a.val))
    (fun R => pinnedClusterCylinderProbability R some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi))
  change Tendsto _ atTop (𝓝 (wiredESCylinder q φ.toMeasure i hi A ξ)) at ht
  apply ht.congr'
  have hs : ∀ᶠ n : ℕ in atTop, A ⊆ box n :=
    (eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x)
  filter_upwards [hs, eventually_gt_atTop 0] with n hn hn0
  rw [← spinObservationEvent_subtype q A ξ]
  exact ((pottsBoxProbabilityMeasure_observed q hq β hβ i n (fun a : ↥A => a.val)
    (fun a => hn a.property) (fun a : ↥A => ξ a.val)).trans
    (potts_ghost_cylinder_eq_partitionExpectation q hq β hβ i hi n hn0 (fun a : ↥A => a.val)
      (fun a => hn a.property) (fun a : ↥A => ξ a.val))).symm

/-- The paper's literal boundary Hamiltonian has a full Potts box limit; its
cylinders are given by colouring finite wired clusters uniformly and every
infinite cluster with the prescribed boundary colour. -/
theorem exists_wired_potts_limit_with_colouring (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    ∃ (φ : ProbabilityMeasure FK.LatticeConfiguration) (μ : ProbabilityMeasure (SpinSpace q)),
      IsRCInfiniteVolumeLimit (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 1 φ.toMeasure ∧
      IsPottsInfiniteVolumeLimit q β i μ.toMeasure ∧
      IsWiredEdwardsSokalColouring q φ.toMeasure i hi μ.toMeasure := by
  obtain ⟨φ, hφ⟩ := FK.wiredBoxProbabilityMeasure_exists_limit (fkParameters q hq β hβ)
  obtain ⟨μ, hμ, hcyl⟩ := potts_limit_of_cylinder_limits q hq β hβ i
    (wiredESCylinder q φ.toMeasure i hi) (wired_potts_cylinder_tendsto q hq β hβ i hi φ hφ)
  exact ⟨φ, μ, FK.isRCInfiniteVolumeLimit_of_wiredBox_tendsto _ φ hφ, hμ, μ.prop, hcyl⟩

end
end PottsDiscontinuity.Potts
