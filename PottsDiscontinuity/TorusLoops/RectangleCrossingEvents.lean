module

public import PottsDiscontinuity.TorusLoops.RectangleCrossings

/-!
# Crossing components of the cut rectangle

These components are defined from the cut graph itself, so their count is
unchanged by changing any edge state on either deleted seam. This is the event
needed for the finite-energy comparison.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Distinct components of the cut rectangle that connect its left and right
vertex boundaries. -/
noncomputable def rectangleCrossingComponents (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Finset (rectangleOpenGraph hN hM A).ConnectedComponent := by
  classical
  letI : Fintype (rectangleOpenGraph hN hM A).ConnectedComponent := Fintype.ofFinite _
  exact Finset.univ.filter fun c =>
    ∃ u v, u.val.1.val = 0 ∧ v.val.1.val + 1 = N ∧
      (rectangleOpenGraph hN hM A).connectedComponentMk u = c ∧
      (rectangleOpenGraph hN hM A).Reachable u v

/-- Closing or opening one indexed seam edge does not change the cut graph. -/
theorem rectangleOpenGraph_toggleEdge_seam (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleOpenGraph hN hM (toggleEdge A v) = rectangleOpenGraph hN hM A := by
  ext u w
  rw [rectangleOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he, hx, hy, hp⟩, hne⟩
    have hev : e ≠ v := by
      intro heq
      subst e
      rcases hseam with hzero | hzero
      · exact hx hzero
      · exact hy hzero
    have hA : A e = true := by
      rw [toggleEdge_away A hev] at he
      exact he
    exact ⟨⟨e, hA, hx, hy, hp⟩, hne⟩
  · rintro ⟨⟨e, he, hx, hy, hp⟩, hne⟩
    have hev : e ≠ v := by
      intro heq
      subst e
      rcases hseam with hzero | hzero
      · exact hx hzero
      · exact hy hzero
    have htoggle : toggleEdge A v e = A e := by
      rw [toggleEdge_away A hev]
    exact ⟨⟨e, by simpa [htoggle] using he, hx, hy, hp⟩, hne⟩

/-- The cut graphs before and after a seam toggle are canonically isomorphic. -/
def rectangleOpenGraph_toggleEdge_iso (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    rectangleOpenGraph hN hM (toggleEdge A v) ≃g rectangleOpenGraph hN hM A where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    rw [rectangleOpenGraph_toggleEdge_seam hN hM A v hseam]
    simp

/-- The number of cut-rectangle crossing components is seam-invariant. -/
theorem rectangleCrossingComponents_card_toggleEdge_seam
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    (rectangleCrossingComponents hN hM (toggleEdge A v)).card =
      (rectangleCrossingComponents hN hM A).card := by
  classical
  let φ := rectangleOpenGraph_toggleEdge_iso hN hM A v hseam
  let e := φ.connectedComponentEquiv
  let : Fintype (rectangleOpenGraph hN hM (toggleEdge A v)).ConnectedComponent :=
    Fintype.ofFinite _
  let : Fintype (rectangleOpenGraph hN hM A).ConnectedComponent := Fintype.ofFinite _
  have hmap :
      (rectangleCrossingComponents hN hM (toggleEdge A v)).map e.toEmbedding =
        rectangleCrossingComponents hN hM A := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_map.mp hc with ⟨d, hd, hdc⟩
      rcases Finset.mem_filter.mp hd with ⟨_, u, w, hu, hw, hdu, hreach⟩
      subst c
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, w, hu, hw, ?_, ?_⟩
      · calc
          (rectangleOpenGraph hN hM A).connectedComponentMk u =
              (rectangleOpenGraph hN hM A).connectedComponentMk (φ u) :=
                congrArg _ (by rfl)
          _ = e ((rectangleOpenGraph hN hM (toggleEdge A v)).connectedComponentMk u) := by
                symm
                simp [e]
          _ = e d := congrArg e hdu
      · have hreachA : (rectangleOpenGraph hN hM A).Reachable u w := by
          rw [← rectangleOpenGraph_toggleEdge_seam hN hM A v hseam]
          exact hreach
        exact hreachA
    · intro hc
      rcases Finset.mem_filter.mp hc with ⟨_, u, w, hu, hw, hcu, hreach⟩
      let d := e.symm c
      have hreach' :
          (rectangleOpenGraph hN hM (toggleEdge A v)).Reachable u w :=
        by
          rw [rectangleOpenGraph_toggleEdge_seam hN hM A v hseam]
          exact hreach
      have hdu :
          (rectangleOpenGraph hN hM (toggleEdge A v)).connectedComponentMk u = d := by
        calc
          (rectangleOpenGraph hN hM (toggleEdge A v)).connectedComponentMk u =
              (rectangleOpenGraph hN hM (toggleEdge A v)).connectedComponentMk (φ.symm u) :=
                congrArg _ (by rfl)
          _ = e.symm ((rectangleOpenGraph hN hM A).connectedComponentMk u) := by
                symm
                simp [e]
          _ = e.symm c := congrArg e.symm hcu
      refine Finset.mem_map.mpr ⟨d,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, w, hu, hw, hdu, hreach'⟩, ?_⟩
      simp [d]
  have hcard := congrArg Finset.card hmap
  simpa [Finset.card_map] using hcard

/-- The event that at least `k` distinct cut-rectangle components cross
horizontally. -/
def hasAtLeastRectangleCrossings (hN : Even N) (hM : Even M) (k : ℕ) :
    Set (RCConfig N M) :=
  {A | k ≤ (rectangleCrossingComponents hN hM A).card}

/-- The crossing-count event is invariant under toggling any seam edge. -/
theorem hasAtLeastRectangleCrossings_toggleEdge_seam
    (hN : Even N) (hM : Even M) (k : ℕ) (A : RCConfig N M)
    (v : Fin N × Fin M)
    (hseam : v.1.val = 0 ∨ v.2.val = 0) :
    A ∈ hasAtLeastRectangleCrossings hN hM k ↔
      toggleEdge A v ∈ hasAtLeastRectangleCrossings hN hM k := by
  simp only [hasAtLeastRectangleCrossings, Set.mem_ofPred_eq]
  rw [rectangleCrossingComponents_card_toggleEdge_seam hN hM A v hseam]

end PottsDiscontinuity.TorusLoops
