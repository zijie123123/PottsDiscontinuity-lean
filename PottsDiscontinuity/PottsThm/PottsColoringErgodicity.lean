module

public import Mathlib.Probability.UniformOn
public import PottsDiscontinuity.PottsThm.ColoringErgodicity
public import PottsDiscontinuity.RCInfinite.Mixing

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite
open scoped ENNReal

noncomputable section

/-- The canonical iid cluster-colouring factor of an RC infinite-volume limit
is translation ergodic. -/
theorem clusterColoring_map_ergodic_of_RCmixing {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] [Nonempty C]
    (θ : FK.Parameters) (i : Fin 2) (φ : Measure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i φ) (c₀ : C) :
    IsTranslationErgodic
      ((φ.prod (iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set C)))).map
        (clusterColoring c₀)) := by
  let ν : Measure C := ProbabilityTheory.uniformOn (Set.univ : Set C)
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : Vertex => ν))
    infer_instance
  have hcolorPres (a : Vertex) :
      MeasurePreserving (iidFieldShift (latticeShiftEquiv a))
        (iidFieldMeasure ν) (iidFieldMeasure ν) :=
    iidFieldShift_measurePreserving ν (latticeShiftEquiv a)
  have hcolorMix (A B : Set (Vertex → C)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      Tendsto (fun a : Vertex => (iidFieldMeasure ν).real
        (A ∩ iidFieldShift (latticeShiftEquiv a) ⁻¹' B)) cofinite
        (𝓝 ((iidFieldMeasure ν).real A * (iidFieldMeasure ν).real B)) := by
    exact iidField_mixing_of_finite_separation ν c₀ latticeShiftEquiv
      eventually_latticeShift_disjoint hA hB
  have hRCmix := isRCInfiniteVolumeLimit_interior_edge_mixing θ i φ hφ
  let : IsProbabilityMeasure φ := hφ.1
  exact mixingProduct_factor_translationErgodic
    (fun a ω => edgeTranslate a ω)
    (fun a u => iidFieldShift (latticeShiftEquiv a) u)
    (fun a => ⟨edgeTranslate_measurable a, hRCmix.1 a⟩) hcolorPres
    (fun A B hA hB => hRCmix.2 A B hA hB) hcolorMix
    (clusterColoring c₀) (measurable_clusterColoring c₀)
    (fun a z x => clusterColoring_equivariant c₀ a z x)

end
end PottsDiscontinuity.PottsThm
