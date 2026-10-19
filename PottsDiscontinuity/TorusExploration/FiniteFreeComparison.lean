module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.FiniteBoxComparison
public import PottsDiscontinuity.TorusExploration.ReflectionComparison

/-! Comparison of a genuinely embedded finite free FK law with the free
infinite-volume law on the square lattice. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK MeasureTheory Filter Topology
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance finiteFreeComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- The free law on any finite embedded graph is dominated by the actual free
limit on the increasing cylinder events of its original edges. -/
theorem finiteFree_event_le_freeLimit (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure G θ (BoundaryCondition.free ∅) E).toReal ≤
      μ.real (embeddedCylinderEvent G f hG E) := by
  let : Fintype V := Fintype.ofFinite _
  have hcontained : ∃ R : ℕ, ∀ v, f v ∈ latticeBox (0,0) R := by
    choose R hR using fun v : V => origin_latticeBox_exhaustive (f v)
    refine ⟨Finset.univ.sup R,?_⟩
    intro v
    exact latticeBox_mono (0,0) (Finset.le_sup (f := R) (Finset.mem_univ v)) (hR v)
  obtain ⟨R,hR⟩ := hcontained
  let ν := Classical.choose (freeBoxLimit_existsUnique θ)
  have hν := (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
    (fun _ => (0,0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
    (embeddedCylinderEvent_isClopen G f hG E)
  have htr := (NNReal.continuous_coe.continuousAt.tendsto).comp ht
  rw [Duality.free_limit_eq_selected θ μ hμ]
  change (measure G θ (BoundaryCondition.free ∅) E).toReal ≤
    ((ν (embeddedCylinderEvent G f hG E) : NNReal) : ℝ)
  apply ge_of_tendsto htr
  filter_upwards [eventually_ge_atTop R] with n hn
  have hc := finiteFree_event_le_box G θ f hG n
    (fun v => latticeBox_mono (0,0) hn (hR v)) E hE
  simpa only [Function.comp_apply,ProbabilityMeasure.measureReal_eq_coe_coeFn] using hc

/-- Actual connectivity in an arbitrary finite planar subgraph under free FK
is bounded by the actual infinite-volume free two-point probability. -/
theorem finiteFree_connectivity_le_freeLimit (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice) (u v : V) :
    (measure G θ (BoundaryCondition.free ∅) (connectivityEvent G u v)).toReal ≤
      μ.real (CorrLength.connectionEvent (f u) (f v)) := by
  have := hμ.1
  have hc := finiteFree_event_le_freeLimit G θ μ hμ f hG (connectivityEvent G u v)
    (fun _ _ hAB hA => actualConnected_mono hAB hA)
  refine hc.trans ?_
  rw [corrLength_connectionEvent_eq]
  exact measureReal_mono (embeddedConnectivityEvent_subset G f hG u v)

end
end PottsDiscontinuity.TorusExploration
