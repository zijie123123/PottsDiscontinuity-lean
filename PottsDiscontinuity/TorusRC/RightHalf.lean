module

public import PottsDiscontinuity.FK.WiredRemoval
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge

/-! # The right-half interior and the exterior measurability of B -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Indexed edges in the right half of the lifted strip, excluding the
horizontal seam. Index zero is the right boundary column N in the cover. -/
def rightHalfInteriorSite (e : Fin N × Fin M) : Prop :=
  (e.1.val = 0 ∨ N / 2 < e.1.val) ∧ e.2.val ≠ 0

/-- Every edge used by a left-strip path has a strictly positive horizontal
index no larger than the strip width. -/
theorem leftStrip_edge_index_range (hN : 0 < N) (hM : 0 < M)
    (A : RCConfig N M) (K : ℕ) (hK : K < N) {u v : RotatedVertex}
    (huv : (liftedStripGraph hN hM A 0 (K : ℤ)).Adj u v) :
    1 ≤ (liftedEdgeIndex hN hM u v).1.val ∧
      (liftedEdgeIndex hN hM u v).1.val ≤ K := by
  have hdist : |u.val.1 - v.val.1| = 1 := huv.1.1
  have hne : u.val.1 ≠ v.val.1 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hdist
    norm_num at hdist
  have hmax1 : 1 ≤ max u.val.1 v.val.1 := by
    have hu := huv.2.2.1.1
    have hv := huv.2.2.2.1
    omega
  have hmaxK : max u.val.1 v.val.1 ≤ (K : ℤ) :=
    max_le huv.2.2.1.2 huv.2.2.2.2
  have hval : ((liftedEdgeIndex hN hM u v).1.val : ℤ) = max u.val.1 v.val.1 := by
    change ((periodicCoordinate hN (max u.val.1 v.val.1)).val : ℤ) = _
    rw [periodicCoordinate_val, Int.emod_eq_of_lt (by omega) (by omega)]
  constructor <;> omega

theorem leftStripGraph_le_of_agree (hN : 0 < N) (hM : 0 < M)
    (A B : RCConfig N M) (K : ℕ) (hK : K < N)
    (hAB : ∀ e : Fin N × Fin M, 1 ≤ e.1.val → e.1.val ≤ K → A e = B e) :
    liftedStripGraph hN hM A 0 (K : ℤ) ≤ liftedStripGraph hN hM B 0 (K : ℤ) := by
  intro u v huv
  have hi := leftStrip_edge_index_range hN hM A K hK huv
  refine ⟨huv.1, ?_, huv.2.2⟩
  rw [← hAB (liftedEdgeIndex hN hM u v) hi.1 hi.2]
  exact huv.2.1

/-- The left annular crossing depends only on indices `1,...,3n` and does
not inspect the right-half interior edges. -/
theorem leftStripCrossing_congr (hN : 0 < N) (hM : 0 < M)
    (A B : RCConfig N M) (n : ℕ) (hn : 3 * n < N)
    (hAB : ∀ e : Fin N × Fin M, 1 ≤ e.1.val → e.1.val ≤ 3 * n → A e = B e) :
    torusRCLeftStripCrossing hN hM A n ↔ torusRCLeftStripCrossing hN hM B n := by
  have hg : liftedStripGraph hN hM A 0 ((3 * n : ℕ) : ℤ) =
      liftedStripGraph hN hM B 0 ((3 * n : ℕ) : ℤ) :=
    le_antisymm (leftStripGraph_le_of_agree hN hM A B (3 * n) hn hAB)
      (leftStripGraph_le_of_agree hN hM B A (3 * n) hn
        (fun e hi1 hin => (hAB e hi1 hin).symm))
  unfold torusRCLeftStripCrossing
  rw [hg]

/-- The source barrier event is determined by the configuration outside the
right-half interior (including all seam-edge states). -/
theorem barrier_congr_outside_rightHalf (hN : 0 < N) (hM : 0 < M)
    (A B : RCConfig N M) (n : ℕ) (hn : 3 * n ≤ N / 2)
    (hAB : ∀ e : Fin N × Fin M, ¬ rightHalfInteriorSite e → A e = B e) :
    A ∈ torusRCBarrier hN hM n ↔ B ∈ torusRCBarrier hN hM n := by
  have hcross := leftStripCrossing_congr hN hM A B n (by omega)
    (fun e hi1 hin => hAB e (by
      intro he
      rcases he.1 with he | he <;> omega))
  have hseam : torusRCSeamAllButOneOpen hM A ↔ torusRCSeamAllButOneOpen hM B := by
    have heq (i : Fin N) : A (i, ⟨0, hM⟩) = B (i, ⟨0, hM⟩) :=
      hAB (i, ⟨0, hM⟩) (by simp [rightHalfInteriorSite])
    unfold torusRCSeamAllButOneOpen
    simp_rw [heq]
  change (¬ torusRCLeftStripCrossing hN hM A n ∧ torusRCSeamAllButOneOpen hM A) ↔
    (¬ torusRCLeftStripCrossing hN hM B n ∧ torusRCSeamAllButOneOpen hM B)
  rw [hcross, hseam]

noncomputable section

local instance rightHalfGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

local instance rightHalfGraphDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

/-- Exactly the edges outside the right-half interior, including row zero. -/
def rightHalfFrozenEdges (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) :
    FK.Configuration (fullDiamondGraph hN hM) := by
  classical
  exact Finset.univ.filter fun e =>
    ¬ rightHalfInteriorSite ((torusIndexedEdgeEquiv hN hM hN4 hM4).symm e)

@[simp] theorem mem_rightHalfFrozenEdges (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (v : Fin N × Fin M) :
    torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ rightHalfFrozenEdges hN hM hN4 hM4 ↔
      ¬ rightHalfInteriorSite v := by
  classical
  simp [rightHalfFrozenEdges]

/-- Restore an exterior state and a remaining state to the original indexed
configuration; every frozen open and closed edge keeps its exact state. -/
def rightHalfRestore (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) : RCConfig N M :=
  (torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val)

private theorem configurationEquiv_symm_true (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (C : FK.Configuration (fullDiamondGraph hN hM)) (v : Fin N × Fin M) :
    (torusRCConfigurationEquiv hN hM hN4 hM4).symm C v = true ↔
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ C := by
  have h := mem_torusRCConfigurationEquiv hN hM hN4 hM4
    ((torusRCConfigurationEquiv hN hM hN4 hM4).symm C) v
  change _ ↔ torusIndexedEdgeEmbedding hN hM hN4 hM4 v ∈ C
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem rightHalfRestore_true_iff (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) (v : Fin N × Fin M) :
    rightHalfRestore hN hM hN4 hM4 H A v = true ↔
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ A.val ∨
      torusIndexedEdgeEquiv hN hM hN4 hM4 v ∈ H.val := by
  unfold rightHalfRestore
  rw [configurationEquiv_symm_true, Finset.mem_union]

theorem rightHalfRestore_mono (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    {A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)} (hAB : A ≤ B) :
    rightHalfRestore hN hM hN4 hM4 H A ≤ rightHalfRestore hN hM hN4 hM4 H B := by
  intro v
  cases ha : rightHalfRestore hN hM hN4 hM4 H A v
  · exact Bool.false_le _
  · have hmem := (rightHalfRestore_true_iff hN hM hN4 hM4 H A v).mp ha
    have hb := (rightHalfRestore_true_iff hN hM hN4 hM4 H B v).mpr
      (hmem.imp (fun h => hAB h) id)
    rw [hb]

theorem rightHalfRestore_agree_outside (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) (v : Fin N × Fin M)
    (hv : ¬ rightHalfInteriorSite v) :
    rightHalfRestore hN hM hN4 hM4 H A v = rightHalfRestore hN hM hN4 hM4 H B v := by
  classical
  have hvR := (mem_rightHalfFrozenEdges hN hM hN4 hM4 v).mpr hv
  have hnotA : torusIndexedEdgeEquiv hN hM hN4 hM4 v ∉ A.val :=
    fun h => Finset.disjoint_left.mp A.property h hvR
  have hnotB : torusIndexedEdgeEquiv hN hM hN4 hM4 v ∉ B.val :=
    fun h => Finset.disjoint_left.mp B.property h hvR
  have htrue : rightHalfRestore hN hM hN4 hM4 H A v = true ↔
      rightHalfRestore hN hM hN4 hM4 H B v = true := by
    unfold rightHalfRestore
    rw [configurationEquiv_symm_true, configurationEquiv_symm_true]
    simp only [Finset.mem_union, hnotA, hnotB, false_or]
  cases ha : rightHalfRestore hN hM hN4 hM4 H A v <;>
    cases hb : rightHalfRestore hN hM hN4 hM4 H B v <;> simp_all

/-- Membership in B is constant on every right-half conditional fiber. -/
theorem barrier_rightHalfRestore_iff (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (hn : 3 * n ≤ N / 2)
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (A B : FK.RemainingConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :
    rightHalfRestore hN hM hN4 hM4 H A ∈ torusRCBarrier hNp hMp n ↔
      rightHalfRestore hN hM hN4 hM4 H B ∈ torusRCBarrier hNp hMp n :=
  barrier_congr_outside_rightHalf hNp hMp _ _ n hn
    (rightHalfRestore_agree_outside hN hM hN4 hM4 H A B)

/-- The actual exterior event corresponding to B, evaluated by restoring the
empty interior state. Fiber constancy proves this choice immaterial. -/
def rightHalfBarrierExterior (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M) (n : ℕ) :
    Set (FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :=
  {H | rightHalfRestore hN hM hN4 hM4 H ⟨∅, Finset.disjoint_empty_left _⟩ ∈
    torusRCBarrier hNp hMp n}

/-- Exact exterior-measurability identity for use with the joint fiber law. -/
theorem barrier_iff_rightHalfExterior (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (n : ℕ) (hn : 3 * n ≤ N / 2) (A : RCConfig N M) :
    A ∈ torusRCBarrier hNp hMp n ↔
      (FK.configurationSplitEquiv (fullDiamondGraph hN hM)
        (rightHalfFrozenEdges hN hM hN4 hM4)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A)).2 ∈
          rightHalfBarrierExterior hN hM hN4 hM4 hNp hMp n := by
  let P := FK.configurationSplitEquiv (fullDiamondGraph hN hM)
    (rightHalfFrozenEdges hN hM hN4 hM4)
    (torusRCConfigurationEquiv hN hM hN4 hM4 A)
  have hrestore : rightHalfRestore hN hM hN4 hM4 P.2 P.1 = A := by
    unfold rightHalfRestore
    have hsplit := (FK.configurationSplitEquiv (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)).symm_apply_apply
      (torusRCConfigurationEquiv hN hM hN4 hM4 A)
    change P.1.val ∪ P.2.val = torusRCConfigurationEquiv hN hM hN4 hM4 A at hsplit
    rw [hsplit, Equiv.symm_apply_apply]
  change A ∈ torusRCBarrier hNp hMp n ↔
    rightHalfRestore hN hM hN4 hM4 P.2 ⟨∅, Finset.disjoint_empty_left _⟩ ∈
      torusRCBarrier hNp hMp n
  rw [← hrestore]
  exact barrier_rightHalfRestore_iff hN hM hN4 hM4 hNp hMp n hn P.2 P.1 _

end

end PottsDiscontinuity.TorusRC
