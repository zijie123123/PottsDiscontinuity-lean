module

public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterComparison
public import PottsDiscontinuity.Potts.ConditionedComparison
public import PottsDiscontinuity.Potts.GhostBoxContraction
public import PottsDiscontinuity.Potts.OutsideComparison

/-! The domain comparison for the actual frozen boxes and corner correction. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

 theorem box_mono {m n : ℕ} (h : m ≤ n) : box m ⊆ box n := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  omega

def nestedBoxEmbedding {m n : ℕ} (h : m ≤ n) :
    ↥(box m : Set (ℤ × ℤ)) ↪ ↥(box n : Set (ℤ × ℤ)) :=
  (squareLattice.induceHomOfLE (fun _ hx => box_mono h hx)).toEmbedding

theorem nestedBox_map_le {m n : ℕ} (h : m ≤ n) :
    (squareLattice.induce (box m : Set (ℤ × ℤ))).map (nestedBoxEmbedding h) ≤
      squareLattice.induce (box n : Set (ℤ × ℤ)) := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
  exact hab

theorem nestedBox_interior_closed {m n : ℕ} (h : m ≤ n)
    {x : ↥(box m : Set (ℤ × ℤ))} (hx : x.val ∉ vertexBoundary (box m))
    {y : ↥(box n : Set (ℤ × ℤ))}
    (hxy : (squareLattice.induce _).Adj (nestedBoxEmbedding h x) y) :
    ∃ z : ↥(box m : Set (ℤ × ℤ)), nestedBoxEmbedding h z = y ∧
      (squareLattice.induce _).Adj x z := by
  have hy : y.val ∈ box m := by
    by_contra hn
    exact hx ⟨x.property, y.val, hxy, hn⟩
  exact ⟨⟨y.val, hy⟩, Subtype.ext rfl, hxy⟩

theorem nestedBox_avoids_boundary {m n : ℕ} (h : m ≤ n)
    {x : ↥(box m : Set (ℤ × ℤ))} (hx : x.val ∉ vertexBoundary (box m)) :
    (nestedBoxEmbedding h x).val ∉ vertexBoundary (box n) := by
  rintro ⟨_, y, hxy, hy⟩
  exact hx ⟨x.property, y, hxy, fun hym => hy (box_mono h hym)⟩

theorem cornerPoint_not_mem_smaller {m n : ℕ} (h : m < n) (b : Bool × Bool) :
    cornerPoint n b ∉ box m := by
  rw [mem_box_iff]
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> dsimp [cornerPoint] <;> omega

/-- The four correction edges are exterior to every strictly smaller box. -/
theorem cornerCutEdges_subset_removed {m n : ℕ} (h : m < n) :
    cornerCutEdges n ⊆ FK.subgraphRemovedEdges
      ((squareLattice.induce (box m : Set (ℤ × ℤ))).map
        (nestedBoxEmbedding (show m ≤ n + 1 by omega)))
      (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) := by
  intro e he
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
  rw [FK.mem_subgraphRemovedEdges]
  intro he
  have he' := ((squareLattice.induce (box m : Set (ℤ × ℤ))).map
    (nestedBoxEmbedding (show m ≤ n + 1 by omega))).mem_edgeSet.mp he
  rw [SimpleGraph.map_adj] at he'
  obtain ⟨x, y, _, hxb, _⟩ := he'
  have hx : x.val = cornerPoint n b := congrArg Subtype.val hxb
  exact cornerPoint_not_mem_smaller h b (hx ▸ x.property)

/-- Reading an event on a smaller frozen box from a larger configuration. -/
def nestedBoxEvent {m n : ℕ} (h : m ≤ n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ))))) :
    Set (FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :=
  {C | FK.embeddedConfigurationRestriction _ _ (nestedBoxEmbedding h) (nestedBox_map_le h) C ∈ S}

theorem nestedBoxEvent_upper {m n : ℕ} (h : m ≤ n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) : IsUpperSet (nestedBoxEvent h S) := by
  intro C D hCD hC
  exact hS (FK.embeddedConfigurationRestriction_monotone _ _ _ _ hCD) hC

/-- The lower-comparison input with all geometry discharged: the corner
correction lies outside the smaller box. -/
theorem corner_corrected_box_joint_comparison (θ : FK.Parameters) {m n : ℕ} (h : m < n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    (FK.measure _ θ (outerBoxWiring n)
      (nestedBoxEvent (show m ≤ n + 1 by omega) S ∩ (cornerClosureEvent n)ᶜ)).toReal ≤
    (FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box m)}) S).toReal *
      (1 - (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal) := by
  exact embedded_joint_not_allClosed_le _ _
    (nestedBoxEmbedding (show m ≤ n + 1 by omega)) (nestedBox_map_le _)
    θ (outerBoxWiring n) {x | x.val ∈ vertexBoundary (box m)}
    (fun _ hx _ hxy => nestedBox_interior_closed _ hx hxy)
    (fun _ hx => nestedBox_avoids_boundary _ hx)
    (cornerCutEdges n) (cornerCutEdges_subset_removed h) S hS

/-- The upper-comparison input for the actual four-corner correction. -/
theorem corner_corrected_box_conditional_le (θ : FK.Parameters) {m n : ℕ} (h : m < n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    (FK.measure _ θ (outerBoxWiring n)
      (nestedBoxEvent (show m ≤ n + 1 by omega) S ∩ cornerClosureEvent n)).toReal /
        (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal ≤
    (FK.measure _ θ (outerBoxWiring n)
      (nestedBoxEvent (show m ≤ n + 1 by omega) S)).toReal := by
  apply conditioned_decreasing_event_le θ (outerBoxWiring n) _ _
    (nestedBoxEvent_upper _ S hS) (isLowerSet_allClosedEdges _)
  exact (pow_pos (FK.one_sub_edgeParameter_pos θ) 4).trans_le
    (cornerClosureEvent_probability_lower_bound θ n (by omega))

/-- Total probability and domain Markov give the other half of the squeeze. -/
theorem corner_corrected_box_total_comparison (θ : FK.Parameters) {m n : ℕ} (h : m < n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    (FK.measure _ θ (outerBoxWiring n)
      (nestedBoxEvent (show m ≤ n + 1 by omega) S)).toReal ≤
    (FK.measure _ θ (outerBoxWiring n)
      (nestedBoxEvent (show m ≤ n + 1 by omega) S ∩ cornerClosureEvent n)).toReal +
    (FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box m)}) S).toReal *
      (1 - (FK.measure _ θ (outerBoxWiring n) (cornerClosureEvent n)).toReal) := by
  have hc := corner_corrected_box_joint_comparison θ h S hS
  have hs := measureReal_inter_add_sdiff (μ := FK.measure _ θ (outerBoxWiring n))
    (s := nestedBoxEvent (show m ≤ n + 1 by omega) S)
    (MeasurableSpace.measurableSet_top (s := cornerClosureEvent n))
  have hd : nestedBoxEvent (show m ≤ n + 1 by omega) S \ cornerClosureEvent n =
      nestedBoxEvent (show m ≤ n + 1 by omega) S ∩ (cornerClosureEvent n)ᶜ := rfl
  rw [hd] at hs
  change _ + (FK.measure _ θ (outerBoxWiring n)
    (nestedBoxEvent (show m ≤ n + 1 by omega) S ∩ (cornerClosureEvent n)ᶜ)).toReal = _ at hs
  simp only [Measure.real] at hs
  linarith

/-- Quantitative corner-conditioning squeeze on every increasing inner event. -/
theorem corner_corrected_box_squeeze (θ : FK.Parameters) {m n : ℕ} (h : m < n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    let E := nestedBoxEvent (show m ≤ n + 1 by omega) S
    let μ := FK.measure (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) θ (outerBoxWiring n)
    let u := (μ E).toReal
    let c := (FK.measure _ θ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box m)}) S).toReal
    let g := (μ (E ∩ cornerClosureEvent n)).toReal / (μ (cornerClosureEvent n)).toReal
    u - (c - u) / (1 - FK.edgeParameter θ) ^ 4 ≤ g ∧ g ≤ u := by
  dsimp only
  have huc := FK.embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (nestedBoxEmbedding (show m ≤ n + 1 by omega)) (nestedBox_map_le _)
    θ (outerBoxWiring n) {x | x.val ∈ vertexBoundary (box m)}
    (fun _ hx _ hxy => nestedBox_interior_closed _ hx hxy)
    (fun _ hx => nestedBox_avoids_boundary _ hx) S hS
  exact conditioned_ratio_squeeze_bounds (pow_pos (FK.one_sub_edgeParameter_pos θ) 4)
    (cornerClosureEvent_probability_lower_bound θ n (by omega))
    (corner_corrected_box_conditional_le θ h S hS) huc
    (corner_corrected_box_total_comparison θ h S hS)

end
end PottsDiscontinuity.Potts
