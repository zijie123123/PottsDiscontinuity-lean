module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionEvents
public import PottsDiscontinuity.Duality.CrossingDuality
public import PottsDiscontinuity.Duality.DualConfigurationBridge

/-! The rectangle crossing alternative on the actual whole-plane configuration
carrier, stated as a covering by long primal or dual connection events. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial
noncomputable section

/-- Literal restriction to sampled original rectangle edges. -/
def rectangleRestriction (a : LatticeVertex) (w h : ℕ) (ω : LatticeConfiguration) :
    Configuration (rectangleGraph a w h) := by
  classical
  exact Finset.univ.filter fun e => ω (rectanglePrimalEdgeToSquareEdge a w h e) = true

@[simp] lemma mem_rectangleRestriction (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (e : (rectangleGraph a w h).edgeSet) :
    e ∈ rectangleRestriction a w h ω ↔
      ω (rectanglePrimalEdgeToSquareEdge a w h e) = true := by
  simp [rectangleRestriction]

lemma dual_rectangleRestriction_at (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) (g : (rectangleDualGraph a w h).edgeSet) :
    wholePlaneDualConfigurationHomeomorph ω (rectangleDualEdgeToSquareEdge a w h g) =
      decide (g ∈ rectanglePrimalDualConfigurationEquiv a w h (rectangleRestriction a w h ω)) := by
  classical
  obtain ⟨e, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
  rw [rectangleDualEdgeToSquareEdge_carrier]
  change latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω) e.crossingBond = _
  rw [wholePlaneDualConfigurationHomeomorph_bondState]
  change Bool.not (ω (latticeBondEdge (primalBondOfDual e.crossingBond))) = _
  rw [rectangleDualEdge_crossing_originalEdge]
  simp only [mem_rectanglePrimalDualConfigurationEquiv]
  have hm := mem_rectangleRestriction a w h ω e.primalEdge
  by_cases he : e.primalEdge ∈ rectangleRestriction a w h ω
  · have hop := hm.1 he
    simp only [hop, Bool.not_true]
    exact (decide_eq_false (by exact not_not.2 he)).symm
  · have hop : ω (rectanglePrimalEdgeToSquareEdge a w h e.primalEdge) = false := by
      cases hs : ω (rectanglePrimalEdgeToSquareEdge a w h e.primalEdge)
      · rfl
      · exact (he (hm.2 hs)).elim
    simp only [hop, Bool.not_false]
    exact (decide_eq_true (by exact he)).symm

/-- Open finite graph paths remain open paths on the original lattice when
every original sampled edge has the same state. -/
def sampledOpenGraphHom {S : Finset LatticeVertex}
    (G : SimpleGraph (S : Set LatticeVertex)) (j : G.edgeSet ↪ squareLattice.edgeSet)
    (hj : ∀ e, (j e).val = Sym2.map Subtype.val e.val)
    (A : Configuration G) (ω : LatticeConfiguration)
    (hω : ∀ e ∈ A, ω (j e) = true) : openGraph G A →g rcInfiniteOpenGraph ω where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    obtain ⟨e, he, heuv⟩ := (openGraph_adj G A u v).1 huv
    have hjv : (j e).val = s(u.val, v.val) := by rw [hj, heuv]; rfl
    have hadj : squareLattice.Adj u.val v.val := by
      apply squareLattice.mem_edgeSet.1
      rw [← hjv]
      exact (j e).property
    rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph]
    change ∃ hadj : squareLattice.Adj u.val v.val,
      ω ⟨s(u.val, v.val), squareLattice.mem_edgeSet.2 hadj⟩ = true
    refine ⟨hadj, ?_⟩
    have heq : (⟨s(u.val, v.val), squareLattice.mem_edgeSet.2 hadj⟩ : squareLattice.edgeSet) =
        j e := Subtype.ext hjv.symm
    rw [heq]
    exact hω e he

/-- Long connections with endpoints in a specified finite vertex set. -/
def longConnectionEvent (S : Finset LatticeVertex) (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u ∈ S, ∃ v ∈ S,
    (n : ℤ) ≤ |v.1 - u.1| + |v.2 - u.2| ∧ ω ∈ connectionEvent u v}

lemma longConnectionEvent_measurableSet (S : Finset LatticeVertex) (n : ℕ) :
    MeasurableSet (longConnectionEvent S n) := by
  have heq : longConnectionEvent S n = ⋃ u ∈ S, ⋃ v ∈ S,
      if (n : ℤ) ≤ |v.1 - u.1| + |v.2 - u.2| then connectionEvent u v else ∅ := by
    ext ω
    simp [longConnectionEvent, and_left_comm]
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro v
  apply MeasurableSet.iUnion
  intro _
  split_ifs
  · exact connectionEvent_measurableSet u v
  · exact MeasurableSet.empty

/-- In a square, either an actual primal connection spans its width or an
actual complementary dual connection spans at least that distance. -/
theorem planar_long_connection_alternative (ω : LatticeConfiguration)
    (a : LatticeVertex) (n : ℕ) :
    ω ∈ longConnectionEvent (latticeRectangle a n n) n ∨
      wholePlaneDualConfigurationHomeomorph ω ∈
        longConnectionEvent (rectangleDualExpanded a n n) n := by
  classical
  let A := rectangleRestriction a n n ω
  by_cases hc : A ∈ rectangleHorizontalCrossingEvent a n n
  · left
    obtain ⟨u, v, hu, hv, hconn⟩ := hc
    refine ⟨u.val, u.property, v.val, v.property, ?_, ?_⟩
    · have hux := (Finset.mem_filter.1 hu).2
      have hvx := (Finset.mem_filter.1 hv).2
      change u.val.1 = a.1 at hux
      change v.val.1 = a.1 + (n : ℤ) at hvx
      rw [hux, hvx, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · let j : (rectangleGraph a n n).edgeSet ↪ squareLattice.edgeSet :=
        frozenEdgeEmbedding (latticeRectangle a n n)
      let f := sampledOpenGraphHom (rectangleGraph a n n) j (fun _ => rfl) A ω
        (fun e he => (mem_rectangleRestriction a n n ω e).1 he)
      exact hconn.map f
  · right
    obtain ⟨b, hb, t, ht, hconn⟩ := (rectangle_crossing_duality a n n A).1 hc
    refine ⟨b.val, b.property, t.val, t.property, ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
      change (n : ℤ) ≤ |(a.1 + ((min j n : ℕ) : ℤ)) -
        (a.1 + ((min i n : ℕ) : ℤ))| + |(a.2 + (n : ℤ)) - (a.2 - 1)|
      have heq : (a.2 + (n : ℤ)) - (a.2 - 1) = (n : ℤ) + 1 := by ring
      rw [heq, abs_of_nonneg (by omega : 0 ≤ (n : ℤ) + 1)]
      have := abs_nonneg ((a.1 + ((min j n : ℕ) : ℤ)) -
        (a.1 + ((min i n : ℕ) : ℤ)))
      omega
    · let B := rectanglePrimalDualConfigurationEquiv a n n A
      let f := sampledOpenGraphHom (rectangleDualGraph a n n)
        (rectangleDualEdgeToSquareEdge a n n) (fun _ => rfl) B
        (wholePlaneDualConfigurationHomeomorph ω) (by
          intro e he
          rw [dual_rectangleRestriction_at a n n ω e, decide_eq_true_eq]
          exact he)
      exact hconn.map f

end
end PottsDiscontinuity.Duality
