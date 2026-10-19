module

public import PottsDiscontinuity.TorusRC.BoxInterior

/-! # Products of local free-box bounds on an exact right-half fiber -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

noncomputable local instance boxProductNativeEdgeFintype (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

noncomputable local instance boxProductEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

noncomputable local instance boxProductEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

noncomputable local instance boxProductRemainingFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _

noncomputable section

/-- FKG combines all boxes whose lifts avoid the seam. No disjointness of the
boxes is required, and the frozen exterior state is arbitrary. -/
theorem liftedBoxFreeConnectionProbability_prod_le_fiber
    {ι : Type*} [DecidableEq ι] (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (s : Finset ι) (c v : ι → RotatedVertex) (R : ℕ)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : ∀ i ∈ s, (N / 2 : ℤ) ≤ (c i).val.1 - R)
    (hright : ∀ i ∈ s, (c i).val.1 + R ≤ (N : ℤ))
    (hbottom : ∀ i ∈ s, 0 < (c i).val.2 - R)
    (htop : ∀ i ∈ s, (c i).val.2 + R < (M : ℤ))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4)) :
    (∏ i ∈ s, liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
      (c i) R (c i) (v i)) ≤
      torusRCFiberEventProbability
        (torusRCFiberLaw hN hM hN4 hM4 q (rightHalfFrozenEdges hN hM hN4 hM4) H)
        {A | ∀ i ∈ s, liftedBoxConnection hNp hMp
          (rightHalfRestore hN hM hN4 hM4 H A) (N / 2 : ℤ) (N : ℤ) R (c i) (v i)} := by
  classical
  apply torusRCFiberEventProbability_finset_inter_ge_prod
    hN hM hN4 hM4 q (rightHalfFrozenEdges hN hM hN4 hM4) H s
  · intro i A B hAB hA
    exact liftedBoxConnection_mono hNp hMp _ _ R (c i) (v i)
      (rightHalfRestore_mono hN hM hN4 hM4 H hAB) hA
  · intro i _
    apply FK.FiniteProbability.expectation_nonneg
    intro A
    by_cases hA : A ∈ liftedBoxFreeConnectionEvent (c i) R (c i) (v i) <;>
      simp [Set.indicator, hA]
  · intro i hi
    exact liftedBoxFreeConnectionProbability_le_free_remaining hN hM hN4 hM4 hNp hMp
      q (c i) R (v i) hRN hRM (hleft i hi) (hright i hi)
      (hbottom i hi) (htop i hi) H

end

end PottsDiscontinuity.TorusRC
