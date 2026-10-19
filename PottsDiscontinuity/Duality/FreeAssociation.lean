module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionEvents
public import PottsDiscontinuity.Duality.FreeBoxDihedral
public import PottsDiscontinuity.FK.BoxLimits
public import PottsDiscontinuity.FK.FreeBoxPositiveAssociation
public import PottsDiscontinuity.Infra.CylinderUniqueness

/-! Positive association for actual, unbounded free connectivity events. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Duality

open FK

/-- Any frozen free box limit is the existing unique free weak limit. -/
lemma free_limit_eq_selected (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    μ = (Classical.choose (freeBoxLimit_existsUnique θ)).toMeasure := by
  let ν := Classical.choose (freeBoxLimit_existsUnique θ)
  have hν := (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
    (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  exact rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ
    (isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hν)

lemma free_clopen_positive_association (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    μ s * μ t ≤ μ (s ∩ t) := by
  have := hμ.1
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top μ s) (measure_ne_top μ t))
    (measure_ne_top μ (s ∩ t))).1
  rw [ENNReal.toReal_mul, free_limit_eq_selected θ μ hμ]
  simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def] using
    Internal.freeBoxLimit_clopen_positive_association θ s t hs ht hsu htu

/-- FKG for whole-plane actual connection events, obtained by finite-path
approximation from the proved clopen FKG inequality. -/
theorem free_connection_positive_association
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (u v x y : LatticeVertex) :
    μ (connectionEvent u v) * μ (connectionEvent x y) ≤
      μ (connectionEvent u v ∩ connectionEvent x y) := by
  rw [measure_connectionEvent_eq_iSup μ u v, measure_connectionEvent_eq_iSup μ x y,
    ENNReal.iSup_mul]
  apply iSup_le
  intro S
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro T
  have hS : finiteConnectionUnion u v S ⊆ connectionEvent u v := by
    rw [connectionEvent_eq_iUnion]
    exact Set.subset_iUnion _ S
  have hT : finiteConnectionUnion x y T ⊆ connectionEvent x y := by
    rw [connectionEvent_eq_iUnion]
    exact Set.subset_iUnion _ T
  exact (free_clopen_positive_association θ μ hμ _ _
    (finiteConnectionUnion_isClopen u v S) (finiteConnectionUnion_isClopen x y T)
    (finiteConnectionUnion_isUpperSet u v S) (finiteConnectionUnion_isUpperSet x y T)).trans
    (measure_mono (Set.inter_subset_inter hS hT))

/-- Positive association and actual path concatenation give the two-point
supermultiplicativity inequality. -/
theorem free_connection_mul_le (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (u v w : LatticeVertex) :
    μ (connectionEvent u v) * μ (connectionEvent v w) ≤ μ (connectionEvent u w) := by
  refine (free_connection_positive_association θ μ hμ u v v w).trans (measure_mono ?_)
  intro ω hω
  exact hω.1.trans hω.2

/-- Every lattice graph symmetry preserving all centered boxes preserves the
actual free infinite-volume measure. -/
theorem free_limit_map_latticeIso
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (e : squareLattice ≃g squareLattice)
    (hbox : ∀ c v r, e v ∈ latticeBox (e c) r ↔ v ∈ latticeBox c r) :
    μ.map (latticeConfigurationIsoHomeomorph e) = μ := by
  rw [free_limit_eq_selected θ μ hμ]
  exact congrArg ProbabilityMeasure.toMeasure
    (Internal.freeBoxLimit_latticeIso_invariant θ e hbox)

end PottsDiscontinuity.Duality
