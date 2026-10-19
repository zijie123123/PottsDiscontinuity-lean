module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.TorusExploration.EmbeddedCylinderEvent

/-! Free comparison for arbitrary finite graphs embedded in a lattice box. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK FK.FiniteProbability MeasureTheory
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance finiteBoxComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

lemma fk_measureReal_eq_expectation (θ : Parameters) (ξ : BoundaryCondition V)
    (E : Set (Configuration G)) :
    (measure G θ ξ E).toReal = expectation (law G θ ξ) (E.indicator fun _ => (1 : ℝ)) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro A _
  rw [law_apply,ENNReal.toReal_ofReal (configurationProbability_pos G θ ξ A).le]

/-- The vertex inclusion induced by a genuine containing box. -/
def embeddedBoxVertex (f : V ↪ LatticeVertex) (n : ℕ)
    (h : ∀ v, f v ∈ latticeBox (0,0) n) : V ↪ BoxVertex (0,0) n where
  toFun v := ⟨f v,h v⟩
  inj' := fun _ _ hv => f.injective (congrArg Subtype.val hv)

omit [Finite V] in
lemma embeddedBox_graph_le (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (n : ℕ) (h : ∀ v, f v ∈ latticeBox (0,0) n) :
    G.map (embeddedBoxVertex f n h) ≤ boxGraph (0,0) n := by
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
  exact hG ((SimpleGraph.map_adj _ _ _ _).2 ⟨u,v,huv,rfl,rfl⟩)

omit [Finite V] in
lemma embeddedBox_edge_commute (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (n : ℕ) (h : ∀ v, f v ∈ latticeBox (0,0) n) (e : G.edgeSet) :
    boxEdgeEmbedding (0,0) n
      (embeddedEdgeEmbedding G (boxGraph (0,0) n) (embeddedBoxVertex f n h)
        (embeddedBox_graph_le G f hG n h) e) = embeddedEdgeEmbedding G squareLattice f hG e := by
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map (embeddedBoxVertex f n h) e.val) = Sym2.map f e.val
  rw [Sym2.map_map]
  rfl

/-- Reading a configuration from a containing box supplies a witness of the
actual increasing cylinder event in its literal closed lattice extension. -/
lemma embeddedBox_mem_cylinder (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (n : ℕ) (h : ∀ v, f v ∈ latticeBox (0,0) n) (E : Set (Configuration G))
    (A : Configuration (boxGraph (0,0) n))
    (hA : embeddedConfigurationRestriction G (boxGraph (0,0) n) (embeddedBoxVertex f n h)
      (embeddedBox_graph_le G f hG n h) A ∈ E) :
    boxConfiguration (0,0) n A ∈ embeddedCylinderEvent G f hG E := by
  apply (mem_embeddedCylinderEvent G f hG E _).2
  refine ⟨_,hA,?_⟩
  intro e he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_map.1 he
  rw [← embeddedBox_edge_commute G f hG n h d,boxConfiguration_at]
  exact decide_eq_true ((mem_embeddedConfigurationRestriction _ _ _ _ _ _).1 hd)

/-- A finite embedded free law is dominated by the free containing box on its
original increasing events. -/
theorem finiteFree_event_le_box (θ : Parameters) (f : V ↪ LatticeVertex)
    (hG : G.map f ≤ squareLattice) (n : ℕ) (h : ∀ v, f v ∈ latticeBox (0,0) n)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure G θ (BoundaryCondition.free ∅) E).toReal ≤
      (boxProbabilityMeasure θ (0,0) n : Measure LatticeConfiguration).real
        (embeddedCylinderEvent G f hG E) := by
  let I := E.indicator (fun _ => (1 : ℝ))
  have hI0 (A) : 0 ≤ I A := by by_cases ha : A ∈ E <;> simp [I,ha]
  have hI : Monotone I := by
    intro A B hAB
    by_cases ha : A ∈ E
    · have hb := hE hAB ha
      simp [I,ha,hb]
    · simpa [I,ha] using hI0 B
  have hc := embedded_free_expectation_le G (boxGraph (0,0) n) (embeddedBoxVertex f n h)
    (embeddedBox_graph_le G f hG n h) θ ∅ ∅ I hI0 hI
  rw [fk_measureReal_eq_expectation] 
  refine hc.trans ?_
  have hm := expectation_mono (law (boxGraph (0,0) n) θ (BoundaryCondition.free ∅))
    (fun A => I (embeddedConfigurationRestriction G (boxGraph (0,0) n) (embeddedBoxVertex f n h)
      (embeddedBox_graph_le G f hG n h) A))
    (fun A => (embeddedCylinderEvent G f hG E).indicator (fun _ => (1 : ℝ))
      (boxConfiguration (0,0) n A)) (by
        intro A
        by_cases ha : embeddedConfigurationRestriction G (boxGraph (0,0) n) (embeddedBoxVertex f n h)
          (embeddedBox_graph_le G f hG n h) A ∈ E
        · have hb := embeddedBox_mem_cylinder G f hG n h E A ha
          simp [I,ha,hb]
        · simp only [I,Set.indicator_of_notMem ha]
          by_cases hb : boxConfiguration (0,0) n A ∈ embeddedCylinderEvent G f hG E <;>
            simp [hb])
  refine hm.trans_eq ?_
  have hb : (boxProbabilityMeasure θ (0,0) n : Measure LatticeConfiguration)
      (embeddedCylinderEvent G f hG E) =
      measure (boxGraph (0,0) n) θ (BoundaryCondition.free ∅)
        ((boxConfiguration (0,0) n) ⁻¹' embeddedCylinderEvent G f hG E) := by
    change ((law (boxGraph (0,0) n) θ (BoundaryCondition.free ∅)).map _).toMeasure _ = _
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
      (embeddedCylinderEvent_isClopen G f hG E).isOpen.measurableSet]
    rfl
  rw [Measure.real_def,hb,fk_measureReal_eq_expectation]
  rfl

end
end PottsDiscontinuity.TorusExploration
