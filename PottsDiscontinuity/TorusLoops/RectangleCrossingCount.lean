module

public import PottsDiscontinuity.TorusLoops.RectangleCrossingEvents

/-!
# Winding loops produce distinct cut-rectangle crossing components

Every full-torus primal cluster represented by a clean horizontal winding
loop contains a cut-rectangle crossing. Distinct full-torus clusters give
distinct cut-rectangle components, since the cut graph is a subgraph of the
torus primal graph.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

private theorem rectangleReachable_sub_diamond (hN : Even N) (hM : Even M)
    (A : RCConfig N M) {u v : FaceVertex N M true}
    (h : (rectangleOpenGraph hN hM A).Reachable u v) :
    (diamondOpenGraph hN hM true A).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => rfl
  | @tail w z hreach hadj ih =>
      apply ih.trans
      rw [rectangleOpenGraph, SimpleGraph.fromEdgeSet_adj] at hadj
      rcases hadj with ⟨⟨e, he, hx, hy, hp⟩, hne⟩
      have hadj' : (diamondOpenGraph hN hM true A).Adj w z := by
        rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨e, he, hp⟩, hne⟩
      exact (SimpleGraph.reachable_iff_reflTransGen w z).mp hadj'.reachable

private theorem horizontalCrossingPrimalClusters_hasCrossing
    (hN : Even N) (hM : Even M) (hNp : 0 < N)
    (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (hc : c ∈ horizontalCrossingPrimalClusters hN hM A) :
    hasRectangleCrossingX hN hM A c := by
  classical
  rcases Finset.mem_image.mp hc with ⟨q, hq, rfl⟩
  exact cleanHorizontalLoop_cluster_crosses hN hM hNp A q hq

/-- The clean-loop crossing clusters inject into the distinct components of
the cut graph that cross horizontally. -/
theorem horizontalCrossingPrimalClusters_card_le_rectangleCrossingComponents
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) :
    (horizontalCrossingPrimalClusters hN hM A).card ≤
      (rectangleCrossingComponents hN hM A).card := by
  classical
  let H := horizontalCrossingPrimalClusters hN hM A
  let K := rectangleCrossingComponents hN hM A
  let G := diamondOpenGraph hN hM true A
  let R := rectangleOpenGraph hN hM A
  let crossData : ∀ c : G.ConnectedComponent, c ∈ H →
      ∃ u v : FaceVertex N M true,
        u.val.1.val = 0 ∧ v.val.1.val + 1 = N ∧
          G.connectedComponentMk u = c ∧ R.Reachable u v := by
    intro c hc
    exact horizontalCrossingPrimalClusters_hasCrossing hN hM hNp A c hc
  let u₀ : FaceVertex N M true := faceEndpoint hN hM true
    (⟨⟨0, hNp⟩, ⟨0, hMp⟩⟩) false
  let d₀ : R.ConnectedComponent := R.connectedComponentMk u₀
  let f : G.ConnectedComponent → R.ConnectedComponent := fun c =>
    if hc : c ∈ H then R.connectedComponentMk (Classical.choose (crossData c hc)) else d₀
  have hmaps : Set.MapsTo f H K := by
    intro c hc
    have hdata := Classical.choose_spec (Classical.choose_spec (crossData c hc))
    let u := Classical.choose (crossData c hc)
    let w := Classical.choose (Classical.choose_spec (crossData c hc))
    have hu : u.val.1.val = 0 := hdata.1
    have hw : w.val.1.val + 1 = N := hdata.2.1
    have hreach : R.Reachable u w := hdata.2.2.2
    dsimp [f]
    split_ifs with h
    · change R.connectedComponentMk u ∈ rectangleCrossingComponents hN hM A
      unfold rectangleCrossingComponents
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, w, hu, hw, rfl, hreach⟩
    · exact (h hc).elim
  have hinj : Set.InjOn f H := by
    intro c hc d hd hcd
    have hcData := Classical.choose_spec (Classical.choose_spec (crossData c hc))
    have hdData := Classical.choose_spec (Classical.choose_spec (crossData d hd))
    let u := Classical.choose (crossData c hc)
    let u' := Classical.choose (crossData d hd)
    have hfc : f c = R.connectedComponentMk u := by
      dsimp [f]
      split_ifs with h
      · rfl
      · exact (h hc).elim
    have hfd : f d = R.connectedComponentMk u' := by
      dsimp [f]
      split_ifs with h
      · rfl
      · exact (h hd).elim
    have hrect : R.connectedComponentMk u = R.connectedComponentMk u' :=
      hfc.symm.trans (hcd.trans hfd)
    have hreach : R.Reachable u u' := SimpleGraph.ConnectedComponent.exact hrect
    have hdiamond : G.Reachable u u' := rectangleReachable_sub_diamond hN hM A hreach
    have hcomp : G.connectedComponentMk u = G.connectedComponentMk u' :=
      SimpleGraph.ConnectedComponent.sound hdiamond
    have hcu : G.connectedComponentMk u = c := hcData.2.2.1
    have hdu : G.connectedComponentMk u' = d := hdData.2.2.1
    calc
      c = G.connectedComponentMk u := hcu.symm
      _ = G.connectedComponentMk u' := hcomp
      _ = d := hdu
  simpa [H, K] using Finset.card_le_card_of_injOn f hmaps hinj

/-- Corrected loop-to-crossing count using the number of distinct components
of the cut rectangle. The factor two is retained. -/
theorem windingLoopCount_le_threeN_add_two_mul_rectangleCrossingComponents
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) :
    windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A ≤
      3 * N + 2 * (rectangleCrossingComponents hN hM A).card := by
  calc
    windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A ≤
        3 * N + 2 * (horizontalCrossingPrimalClusters hN hM A).card :=
      windingLoopCount_le_threeN_add_two_mul_rectangleCrossings hN hM hNp hMp A
    _ ≤ 3 * N + 2 * (rectangleCrossingComponents hN hM A).card :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_left 2
          (horizontalCrossingPrimalClusters_card_le_rectangleCrossingComponents
            hN hM hNp hMp A)) _

/-- A large winding-loop count forces many distinct horizontal crossings in
the cut graph, with the factor-two threshold rounded upward. -/
theorem windingLoopCount_ge_implies_rectangleCrossings
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (k : ℕ) (A : RCConfig N M)
    (hk : k ≤ windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A) :
    (k - 3 * N + 1) / 2 ≤ (rectangleCrossingComponents hN hM A).card := by
  have hcount := windingLoopCount_le_threeN_add_two_mul_rectangleCrossingComponents
    hN hM hNp hMp A
  omega

end PottsDiscontinuity.TorusLoops
