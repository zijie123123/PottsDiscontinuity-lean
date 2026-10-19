/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCylinders
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.SubgraphComparison

/-!
# Monotonicity of free box all-open cylinder probabilities

The comparison is on the actual induced graphs. A smaller box configuration is
read from the larger sample along the vertex embedding, preserving the original
lattice edges and their states.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory FiniteProbability
noncomputable section

local instance boxComparisonSmallEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _
local instance boxComparisonLargeEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _
local instance boxComparisonSmallEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (boxGraph c r).edgeSet := Classical.decEq _

/-- The actual inclusion of vertex carriers induced by containment of boxes. -/
def boxVertexEmbedding {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s) : BoxVertex c r ↪ BoxVertex d s where
  toFun v := ⟨v.val, hbox v.property⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    change u.val = v.val
    exact congrArg (fun w : BoxVertex d s => w.val) h

/-- The induced small graph maps into the actual induced large graph. -/
theorem boxGraph_map_boxVertexEmbedding {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s) :
    (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  exact (boxGraph_adj_iff d s _ _).2 ((boxGraph_adj_iff c r _ _).1 huv)

def boxCylinderEvent (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) : Set (Configuration (boxGraph c r)) :=
  {A | F ⊆ A.map (boxEdgeEmbedding c r)}

private theorem boxCylinderEvent_upper (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (boxCylinderEvent c r F) := by
  intro A B hAB hA
  exact hA.trans (Finset.map_subset_map.mpr hAB)

private theorem boxCylinderEvent_indicator_nonneg (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) :
    ∀ A, 0 ≤ (boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ)) A := by
  classical
  intro A
  by_cases h : A ∈ boxCylinderEvent c r F <;> simp [Set.indicator, h]

private theorem boxCylinderEvent_indicator_mono (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) :
    Monotone ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ boxCylinderEvent c r F
  · have hB := boxCylinderEvent_upper c r F hAB hA
    simp [Set.indicator, hA, hB]
  · simp only [Set.indicator_of_notMem hA]
    exact boxCylinderEvent_indicator_nonneg c r F B

private theorem boxEdgeEmbedding_compatible {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH e) = boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v : BoxVertex c r => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem boxCylinderEvent_restrict_iff {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r))
    (A : Configuration (boxGraph d s)) :
    A ∈ boxCylinderEvent d s F ↔
      embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A ∈ boxCylinderEvent c r F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈ A.map (boxEdgeEmbedding d s) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp heOpen
    have hcompat := boxEdgeEmbedding_compatible hbox hGH x
    have hyx : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH x = y := by
      apply (boxEdgeEmbedding d s).injective
      calc
        boxEdgeEmbedding d s
            (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
              (boxVertexEmbedding hbox) hGH x) = boxEdgeEmbedding c r x := hcompat
        _ = e := hx
        _ = boxEdgeEmbedding d s y := hye.symm
    have hy' : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH x ∈ A := by rw [hyx]; exact hy
    have hrestrict := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr hy'
    apply Finset.mem_map.mpr
    exact ⟨x, hrestrict, hx⟩
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈ (embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A).map (boxEdgeEmbedding c r) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp heOpen
    have hyx : y = x := (boxEdgeEmbedding c r).injective (hye.trans hx.symm)
    have hrestrict : x ∈ embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        (boxVertexEmbedding hbox) hGH A := by rw [← hyx]; exact hy
    have hy' := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hrestrict
    have hcompat := boxEdgeEmbedding_compatible hbox hGH x
    apply Finset.mem_map.mpr
    exact ⟨embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH x, hy', hcompat.trans hx⟩

private theorem boxCylinder_toReal_eq_expectation (q : Parameters)
    (c : LatticeVertex) (r : ℕ) (F : Finset squareLattice.edgeSet) :
    (((boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal) =
      expectation (law (boxGraph c r) q (BoundaryCondition.free ∅))
        ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))) := by
  rw [boxProbabilityMeasure_allOpen]
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro A hA
  have hp := configurationProbability_pos (boxGraph c r) q (BoundaryCondition.free ∅) A
  simp only [law_apply, ENNReal.toReal_ofReal hp.le]
  rfl

/-- Free FK all-open cylinder probabilities increase under containment of the
actual induced square boxes. The finite edge set may extend outside the smaller
box, in which case its smaller-box probability is zero. -/
theorem boxProbabilityMeasure_allOpen_mono (q : Parameters)
    (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset squareLattice.edgeSet) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
      (boxProbabilityMeasure q d s : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  classical
  let f := boxVertexEmbedding hbox
  have hGH : (boxGraph c r).map f ≤ boxGraph d s := boxGraph_map_boxVertexEmbedding hbox
  by_cases hF : ∀ e ∈ F, e ∈ Set.range (boxEdgeEmbedding c r)
  · have hcmp := embedded_free_expectation_le (boxGraph c r) (boxGraph d s) f hGH q
      ∅ ∅ ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ)))
      (boxCylinderEvent_indicator_nonneg c r F) (boxCylinderEvent_indicator_mono c r F)
    have hleft := boxCylinder_toReal_eq_expectation q c r F
    have hright := boxCylinder_toReal_eq_expectation q d s F
    have hlarge :
        expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
          (fun A => (boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))
            (embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s) f hGH A)) =
          expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
            ((boxCylinderEvent d s F).indicator (fun _ => (1 : ℝ))) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro A hA
      have heq := boxCylinderEvent_restrict_iff hbox hGH F hF A
      by_cases h : A ∈ boxCylinderEvent d s F
      · have hr : embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
            f hGH A ∈ boxCylinderEvent c r F := heq.mp h
        simp [Set.indicator, h, hr]
      · have hr : embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
            f hGH A ∉ boxCylinderEvent c r F := by
          intro hs
          exact h (heq.mpr hs)
        simp [Set.indicator, h, hr]
    have hcmp' := hcmp.trans_eq hlarge
    have hreal :
        (((boxProbabilityMeasure q c r : Measure LatticeConfiguration)
          (LatticeConfiguration.allOpen F)).toReal) ≤
        (((boxProbabilityMeasure q d s : Measure LatticeConfiguration)
          (LatticeConfiguration.allOpen F)).toReal) := by
      calc
        _ = expectation (law (boxGraph c r) q (BoundaryCondition.free ∅))
            ((boxCylinderEvent c r F).indicator (fun _ => (1 : ℝ))) := hleft
        _ ≤ expectation (law (boxGraph d s) q (BoundaryCondition.free ∅))
            ((boxCylinderEvent d s F).indicator (fun _ => (1 : ℝ))) := hcmp'
        _ = _ := hright.symm
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

  · push Not at hF
    obtain ⟨e, heF, heRange⟩ := hF
    have hempty : boxCylinderEvent c r F = ∅ := by
      ext A
      constructor
      · intro hA
        have heMap : e ∈ A.map (boxEdgeEmbedding c r) := hA heF
        obtain ⟨a, ha, hEq⟩ := Finset.mem_map.mp heMap
        exact heRange ⟨a, hEq⟩
      · simp
    rw [boxProbabilityMeasure_allOpen q c r F]
    change measure (boxGraph c r) q (BoundaryCondition.free ∅)
      (boxCylinderEvent c r F) ≤ _
    rw [hempty, measure_empty]
    exact bot_le

end
end PottsDiscontinuity.FK
