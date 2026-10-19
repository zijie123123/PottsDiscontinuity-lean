module

public import FixedPointTheorems.brouwer
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.PottsThm.ColoringCylinderLaw

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open PottsDiscontinuity.Duality
open scoped ENNReal

noncomputable section

/-- The canonical free cluster coloring has the Edwards--Sokal cylinder law
whenever the bond measure almost surely has only finite clusters. -/
theorem freeColoringMap_isFreeESC (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hno : φ.toMeasure Duality.existsInfiniteCluster = 0) :
    IsFreeEdwardsSokalColouring q φ.toMeasure
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q))) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := ⟨1, le_rfl, by omega⟩
  have : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : Vertex => ν))
    infer_instance
  have : IsProbabilityMeasure φ.toMeasure := φ.property
  let F : LatticeConfiguration × (Vertex → Set.Icc 1 q) → SpinSpace q :=
    clusterColoring c₀
  have hF : Measurable F := measurable_clusterColoring c₀
  refine ⟨inferInstance, ?_⟩
  intro A ξ
  let E : Set (LatticeConfiguration × (Vertex → Set.Icc 1 q)) :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = F ⁻¹' spinCylinder q A ξ := by
    ext z
    simp [E, F, spinCylinder]
  have hCyl : MeasurableSet (spinCylinder q A ξ) :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  have hE : MeasurableSet E := by
    rw [hEq]
    exact hF hCyl
  have hfinite_ae : ∀ᵐ ω ∂φ.toMeasure, ∀ x, (RCInfinite.cluster ω x).Finite := by
    have hnot : ∀ᵐ ω ∂φ.toMeasure, ω ∉ Duality.existsInfiniteCluster := by
      exact ae_iff.mpr (by simpa using hno)
    filter_upwards [hnot] with ω hω x
    simp only [Duality.existsInfiniteCluster, Set.mem_ofPred_eq, not_exists] at hω
    by_contra hfinite
    exact hω x (by simpa [RCInfinite.cluster, Duality.cluster] using hfinite)
  let r : LatticeConfiguration → Setoid (↥A) :=
    fun ω => infiniteFreePartition (fun a : ↥A => a.val) ω
  let K : Setoid (↥A) → ℝ :=
    fun R => clusterCylinderProbability R id (fun a : ↥A => ξ a.val)
  have hRmeas (R : Setoid (↥A)) : MeasurableSet {ω | r ω = R} := by
    exact infiniteFreePartition_measurableSet (fun a : ↥A => a.val) R
  have hKnonneg (R : Setoid (↥A)) : 0 ≤ K R := by
    dsimp [K, clusterCylinderProbability]
    split_ifs <;> positivity
  have hfiber_ae : ∀ᵐ ω ∂φ.toMeasure,
      iidFieldMeasure ν (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) := by
    filter_upwards [hfinite_ae] with ω hfinite
    let : Fintype (Quotient (r ω)) := Fintype.ofFinite _
    change iidFieldMeasure ν
        {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
          clusterColoring c₀ (ω, u) a.val = ξ a.val} = _
    exact freeClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ hfinite
  calc
    ((φ.toMeasure.prod (iidFieldMeasure ν)).map F).real (spinCylinder q A ξ) =
        (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂φ.toMeasure).toReal := by
      rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply hE]
      rw [lintegral_congr_ae hfiber_ae]
    _ = freeESCylinder q φ.toMeasure A ξ := by
      rw [toReal_lintegral_finitePartitionKernel φ.toMeasure r K hKnonneg hRmeas]
      rfl

/-- The canonical wired cluster coloring has the wired Edwards--Sokal cylinder
law for every bond measure. Infinite clusters are assigned the fixed boundary
color. -/
theorem wiredColoringMap_isWiredESC (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration) (i : Fin (q + 1))
    (hi : 1 ≤ (i : ℕ)) :
    IsWiredEdwardsSokalColouring q φ.toMeasure i hi
      ((φ.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))))).map
          (clusterColoring (boundaryColor q i hi))) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := boundaryColor q i hi
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have : IsProbabilityMeasure (iidFieldMeasure (I := Vertex) ν) := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : Vertex => ν))
    infer_instance
  have : IsProbabilityMeasure φ.toMeasure := φ.property
  let F : LatticeConfiguration × (Vertex → Set.Icc 1 q) → SpinSpace q :=
    clusterColoring c₀
  have hF : Measurable F := measurable_clusterColoring c₀
  refine ⟨inferInstance, ?_⟩
  intro A ξ
  let E : Set (LatticeConfiguration × (Vertex → Set.Icc 1 q)) :=
    {z | ∀ a : ↥A, clusterColoring c₀ z a.val = ξ a.val}
  have hEq : E = F ⁻¹' spinCylinder q A ξ := by
    ext z
    simp [E, F, spinCylinder]
  have hCyl : MeasurableSet (spinCylinder q A ξ) :=
    (spinCylinder_isClopen q A ξ).isOpen.measurableSet
  have hE : MeasurableSet E := by
    rw [hEq]
    exact hF hCyl
  let r : LatticeConfiguration → Setoid (Option ↥A) :=
    fun ω => infiniteWiredPartition (Option.map (fun a : ↥A => a.val)) ω
  let K : Setoid (Option ↥A) → ℝ := fun R =>
    pinnedClusterCylinderProbability R some (fun a : ↥A => ξ a.val) none c₀
  have hRmeas (R : Setoid (Option ↥A)) : MeasurableSet {ω | r ω = R} := by
    exact infiniteWiredPartition_measurableSet
      (Option.map (fun a : ↥A => a.val)) R
  have hKnonneg (R : Setoid (Option ↥A)) : 0 ≤ K R := by
    dsimp [K, pinnedClusterCylinderProbability]
    split_ifs <;> positivity
  have hfiber (ω : LatticeConfiguration) :
      iidFieldMeasure ν (Prod.mk ω ⁻¹' E) = ENNReal.ofReal (K (r ω)) := by
    change iidFieldMeasure ν
        {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
          clusterColoring c₀ (ω, u) a.val = ξ a.val} = _
    exact wiredClusterColoring_fiber_cylinder_uniform q (by omega) ω A ξ i hi
  calc
    ((φ.toMeasure.prod (iidFieldMeasure ν)).map F).real (spinCylinder q A ξ) =
        (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂φ.toMeasure).toReal := by
      rw [Measure.real_def, Measure.map_apply hF hCyl, ← hEq, Measure.prod_apply hE]
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hfiber)]
    _ = wiredESCylinder q φ.toMeasure i hi A ξ := by
      rw [toReal_lintegral_finitePartitionKernel φ.toMeasure r K hKnonneg hRmeas]
      rfl

end
end PottsDiscontinuity.PottsThm
