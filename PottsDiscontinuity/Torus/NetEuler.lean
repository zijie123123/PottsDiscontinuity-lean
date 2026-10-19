module

public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.Torus.RibbonHandleIntersection

/-!
# Winding nets and the torus Euler relation

A net is a single actual open cluster carrying two conserved rational one-cycles
with independent lifted winding classes. The full cellular homology calculation
identifies those classes with the two displacement coordinates. The cellular
intersection criterion and cluster localization prove the net/handle equivalence.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The determinant of the two lifted displacement classes. -/
def diamondWindingDeterminant (A : RCConfig N M) (f g : OpenDiamondEdge A → ℚ) : ℚ :=
  diamondHorizontalDisplacement A f * diamondVerticalDisplacement A g -
    diamondVerticalDisplacement A f * diamondHorizontalDisplacement A g

/-- One actual cluster carries two independent torus winding classes.
Rational conserved one-cycles are the cellular homology model; the support premise
requires both classes to be carried by the same connected cluster. -/
def HasWindingNet (hN : Even N) (hM : Even M) (A : RCConfig N M) : Prop :=
  ∃ c : (diamondOpenGraph hN hM true A).ConnectedComponent,
    ∃ f g : diamondCycleSpace hN hM A,
      SupportedOnDiamondCluster hN hM A c f ∧ SupportedOnDiamondCluster hN hM A c g ∧
        diamondWindingDeterminant A f.val g.val ≠ 0

theorem ribbonIntersection_eq_zero_iff_windingDeterminant_zero (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f g = 0 ↔ diamondWindingDeterminant A f.val g.val = 0 := by
  have he := ribbonIntersection_mul_area_subgraph hN hM hNp hMp A f g
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  change ribbonIntersection hN hM A f g = 0 ↔ _
  rw [diamondWindingDeterminant, ← he, mul_eq_zero]
  simp only [hn, false_or]

theorem ribbonHandleCount_one_iff_net_of_pos (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    ribbonHandleCount hN hM A = 1 ↔ HasWindingNet hN hM A := by
  classical
  constructor
  · intro hh
    obtain ⟨f, g, hfg⟩ := (ribbonHandleCount_one_iff_intersection_nonzero hN hM A).mp hh
    obtain ⟨c, hc⟩ := exists_cluster_intersection_nonzero hN hM A f g hfg
    refine ⟨c, diamondClusterCycle hN hM A c f, diamondClusterCycle hN hM A c g,
      diamondClusterCycle_supported hN hM A c f, diamondClusterCycle_supported hN hM A c g, ?_⟩
    exact fun he => hc ((ribbonIntersection_eq_zero_iff_windingDeterminant_zero
      hN hM hNp hMp A _ _).mpr he)
  · rintro ⟨c, f, g, _, _, hfg⟩
    apply (ribbonHandleCount_one_iff_intersection_nonzero hN hM A).mpr
    exact ⟨f, g, fun he => hfg ((ribbonIntersection_eq_zero_iff_windingDeterminant_zero
      hN hM hNp hMp A f g).mp he)⟩

/-- The genus-one component criterion is exactly the winding-defined net condition. -/
theorem ribbonHandleCount_one_iff_net (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    ribbonHandleCount hN hM A = 1 ↔ HasWindingNet hN hM A := by
  by_cases hn : N = 0
  · subst N
    have ha : A = closedRCConfig 0 M := by funext v; exact Fin.elim0 v.1
    have hh : ribbonHandleCount hN hM A = 0 := by rw [ha, ribbonHandleCount_closed]
    have he : ¬HasWindingNet hN hM A := by rintro ⟨c, _⟩; exact isEmptyElim c
    simp only [hh, Nat.zero_ne_one, he]
  · by_cases hm : M = 0
    · subst M
      have ha : A = closedRCConfig N 0 := by funext v; exact Fin.elim0 v.2
      have hh : ribbonHandleCount hN hM A = 0 := by rw [ha, ribbonHandleCount_closed]
      have he : ¬HasWindingNet hN hM A := by rintro ⟨c, _⟩; exact isEmptyElim c
      simp only [hh, Nat.zero_ne_one, he]
    · exact ribbonHandleCount_one_iff_net_of_pos hN hM (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm) A

/-- The paper's net indicator, defined through the actual cluster winding condition. -/
noncomputable def rcNetIndicator (hN : Even N) (hM : Even M) (A : RCConfig N M) : ℕ := by
  classical
  exact if HasWindingNet hN hM A then 1 else 0

theorem ribbonHandleCount_eq_netIndicator (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    ribbonHandleCount hN hM A = rcNetIndicator hN hM A := by
  classical
  by_cases hn : HasWindingNet hN hM A
  · rw [(ribbonHandleCount_one_iff_net hN hM A).mpr hn]
    simp only [rcNetIndicator, hn, ite_true]
  · have hh : ribbonHandleCount hN hM A ≠ 1 := fun h => hn ((ribbonHandleCount_one_iff_net hN hM A).mp h)
    have hb := ribbonHandleCount_le_one hN hM A
    have hz : ribbonHandleCount hN hM A = 0 := by omega
    rw [hz]
    simp only [rcNetIndicator, hn, ite_false]

/-- The torus Euler/net identity, using actual cluster, boundary-loop and open-edge counts. -/
theorem euler_netIndicator (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    2 * clusterCount hN hM true A + openCount A =
      rcLoopCount hN hM A + N * M / 2 + 2 * rcNetIndicator hN hM A := by
  rw [← ribbonHandleCount_eq_netIndicator]
  exact euler_ribbonHandleCount hN hM A

end PottsDiscontinuity.Torus
