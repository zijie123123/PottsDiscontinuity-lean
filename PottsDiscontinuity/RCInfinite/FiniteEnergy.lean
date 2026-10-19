module

public import PottsDiscontinuity.RCInfinite.Cylinders
public import PottsDiscontinuity.FK.FiniteEnergy

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section

attribute [local instance] configurationMeasurableSpace
local instance edgeDecidableEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet :=
  Classical.decEq _

/-- The exact lower conditional probability for an open edge. -/
def openEnergy (θ : Parameters) : ℝ :=
  edgeParameter θ / (edgeParameter θ + (1 - edgeParameter θ) * θ.val)

theorem openEnergy_pos (θ : Parameters) : 0 < openEnergy θ :=
  div_pos (edgeParameter_pos θ)
    (add_pos (edgeParameter_pos θ)
      (mul_pos (one_sub_edgeParameter_pos θ) (clusterWeight_pos θ)))

/-- A common positive bound for both edge states. -/
def energyBound (θ : Parameters) : ℝ := min (openEnergy θ) (1 - edgeParameter θ)

theorem energyBound_pos (θ : Parameters) : 0 < energyBound θ :=
  lt_min (openEnergy_pos θ) (one_sub_edgeParameter_pos θ)

def boxExtension (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r)) : LatticeConfiguration :=
  if i = 0 then boxConfiguration c r C else wiredBoxConfiguration c r C

def boxBoundary (i : Fin 2) (c : LatticeVertex) (r : ℕ) : BoundaryCondition (BoxVertex c r) :=
  if i = 0 then BoundaryCondition.free ∅ else BoundaryCondition.wired (boxVertexBoundary c r)

@[simp] theorem boxExtension_at (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) :
    boxExtension i c r C (boxEdgeEmbedding c r e) = decide (e ∈ C) := by
  classical
  fin_cases i <;> simp [boxExtension]

theorem boxExtension_erase_other (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (C : Configuration (boxGraph c r)) (e : (boxGraph c r).edgeSet) (f : Edge)
    (hef : boxEdgeEmbedding c r e ≠ f) :
    boxExtension i c r (C.erase e) f = boxExtension i c r C f := by
  classical
  by_cases hf : f ∈ Set.range (boxEdgeEmbedding c r)
  · obtain ⟨g, rfl⟩ := hf
    have hge : g ≠ e := fun h => hef (congrArg (boxEdgeEmbedding c r) h.symm)
    simp [hge]
  · fin_cases i
    · simp [boxExtension, boxConfiguration_outside c r _ f hf]
    · simp [boxExtension, wiredBoxConfiguration_outside c r _ f hf]

theorem boxMeasure_apply (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    (boxMeasure θ i c r : Measure LatticeConfiguration) A =
      measure (boxGraph c r) θ (boxBoundary i c r) ((boxExtension i c r) ⁻¹' A) := by
  classical
  unfold boxMeasure boxBoundary boxExtension
  split_ifs
  · change ((law (boxGraph c r) θ (BoundaryCondition.free ∅)).map
      (boxConfiguration c r)).toMeasure A =
        (law (boxGraph c r) θ (BoundaryCondition.free ∅)).toMeasure
          ((boxConfiguration c r) ⁻¹' A)
    exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA
  · change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
      (wiredBoxConfiguration c r)).toMeasure A =
        (law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).toMeasure
          ((wiredBoxConfiguration c r) ⁻¹' A)
    exact PMF.toMeasure_map_apply _ _ _ measurable_from_top hA

theorem finite_edge_energy {V : Type*} [Finite V] {G : SimpleGraph V}
    (θ : Parameters) (ξ : BoundaryCondition V) (e : G.edgeSet)
    (B : Set (Configuration G)) (hB : ∀ C, C ∈ B ↔ C.erase e ∈ B) :
    openEnergy θ * (measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {C | e ∈ C})).toReal ∧
    (1 - edgeParameter θ) * (measure G θ ξ B).toReal ≤
      (measure G θ ξ (B ∩ {C | e ∉ C})).toReal := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : G.Adj u v := G.mem_edgeSet.mp he
    exact ⟨(configurationProbability_edge_finite_energy θ ξ B huv hB).1,
      (configurationProbability_edge_finite_energy_closed θ ξ B huv hB).1⟩

theorem box_edge_energy (θ : Parameters) (i : Fin 2) (c : LatticeVertex) (r : ℕ)
    (e : (boxGraph c r).edgeSet) {B : Set LatticeConfiguration}
    (hB : MeasurableSet B) (hind : DependsOn ({boxEdgeEmbedding c r e}ᶜ) B) :
    openEnergy θ * (boxMeasure θ i c r : Measure LatticeConfiguration).real B ≤
      (boxMeasure θ i c r : Measure LatticeConfiguration).real
        (B ∩ {ω | ω (boxEdgeEmbedding c r e) = true}) ∧
    (1 - edgeParameter θ) * (boxMeasure θ i c r : Measure LatticeConfiguration).real B ≤
      (boxMeasure θ i c r : Measure LatticeConfiguration).real
        (B ∩ {ω | ω (boxEdgeEmbedding c r e) = false}) := by
  classical
  have hstable : ∀ C, boxExtension i c r C ∈ B ↔
      boxExtension i c r (C.erase e) ∈ B := by
    intro C
    apply hind
    intro f hf
    exact (boxExtension_erase_other i c r C e f (by simpa using Ne.symm hf)).symm
  have h := finite_edge_energy θ (boxBoundary i c r) e
    ((boxExtension i c r) ⁻¹' B) hstable
  have ht (b : Bool) : MeasurableSet {ω : LatticeConfiguration | ω (boxEdgeEmbedding c r e) = b} :=
    (isCylinder_coordinate _ b).measurableSet
  simp only [Measure.real, boxMeasure_apply θ i c r hB,
    boxMeasure_apply θ i c r (hB.inter (ht true)),
    boxMeasure_apply θ i c r (hB.inter (ht false))]
  have hopen : (boxExtension i c r) ⁻¹'
      (B ∩ {ω | ω (boxEdgeEmbedding c r e) = true}) =
      ((boxExtension i c r) ⁻¹' B) ∩ {C | e ∈ C} := by
    ext C
    simp
  have hclosed : (boxExtension i c r) ⁻¹'
      (B ∩ {ω | ω (boxEdgeEmbedding c r e) = false}) =
      ((boxExtension i c r) ⁻¹' B) ∩ {C | e ∉ C} := by
    ext C
    simp
  rwa [hopen, hclosed]

theorem eventually_edge_in_box (e : Edge) :
    ∀ᶠ n : ℕ in atTop, ∃ f : (boxGraph (0, 0) n).edgeSet,
      boxEdgeEmbedding (0, 0) n f = e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    filter_upwards [eventually_mem_box x, eventually_mem_box y] with n hx hy
    have hx' : x ∈ latticeBox (0, 0) n := by rwa [latticeBox_origin_eq_box]
    have hy' : y ∈ latticeBox (0, 0) n := by rwa [latticeBox_origin_eq_box]
    exact ⟨⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), he⟩, rfl⟩

/-- The finite-energy lower bounds pass to every frozen box limit on every
cylinder event which does not read the sampled edge. -/
theorem cylinder_finite_energy (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (e : Edge) {B : Set LatticeConfiguration} (hB : IsCylinder B)
    (hind : DependsOn ({e}ᶜ) B) :
    openEnergy θ * μ.real B ≤ μ.real (B ∩ {ω | ω e = true}) ∧
    (1 - edgeParameter θ) * μ.real B ≤ μ.real (B ∩ {ω | ω e = false}) := by
  have hlim := tendsto_cylinder_probability θ i μ hμ hB
  have hevent := eventually_edge_in_box e
  constructor
  · apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hlim)
      (tendsto_cylinder_probability θ i μ hμ (hB.inter (isCylinder_coordinate e true)))
    filter_upwards [hevent] with n hn
    obtain ⟨f, hf⟩ := hn
    simpa [hf] using (box_edge_energy θ i (0, 0) n f hB.measurableSet
      (by simpa [hf] using hind)).1
  · apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hlim)
      (tendsto_cylinder_probability θ i μ hμ (hB.inter (isCylinder_coordinate e false)))
    filter_upwards [hevent] with n hn
    obtain ⟨f, hf⟩ := hn
    simpa [hf] using (box_edge_energy θ i (0, 0) n f hB.measurableSet
      (by simpa [hf] using hind)).2

end
end PottsDiscontinuity.RCInfinite
