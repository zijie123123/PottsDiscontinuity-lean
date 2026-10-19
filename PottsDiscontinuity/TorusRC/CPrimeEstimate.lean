module

public import PottsDiscontinuity.TorusRC.BoxTranslation
public import PottsDiscontinuity.TorusRC.CPrimeFiber
public import PottsDiscontinuity.TorusRC.FiberDisintegration

/-! # The corrected conditional chain bound, with a height-independent cost -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

noncomputable local instance cPrimeEstimateEdges (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _
noncomputable local instance cPrimeEstimateEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _
noncomputable local instance cPrimeEstimateRemaining (hN : Even N) (hM : Even M)
    (F : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) F) := Fintype.ofFinite _
noncomputable local instance cPrimeEstimateBoxEdges (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

noncomputable section

theorem liftedBoxFreeConnectionProbability_nonneg (θ : FK.Parameters)
    (c : RotatedVertex) (R : ℕ) (u v : RotatedVertex) :
    0 ≤ liftedBoxFreeConnectionProbability θ c R u v :=
  torusRCFiberEventProbability_nonneg _ _

theorem liftedBoxFreeConnectionProbability_le_one (θ : FK.Parameters)
    (c : RotatedVertex) (R : ℕ) (u v : RotatedVertex) :
    liftedBoxFreeConnectionProbability θ c R u v ≤ 1 := by
  have h := FK.FiniteProbability.expectation_mono
    (p := FK.law (liftedBoxGraph c R) θ (FK.BoundaryCondition.free ∅))
    (f := (liftedBoxFreeConnectionEvent c R u v).indicator (fun _ => (1 : ℝ)))
    (g := fun _ => (1 : ℝ)) (by
      intro A
      by_cases hA : A ∈ liftedBoxFreeConnectionEvent c R u v <;> simp [Set.indicator, hA])
  simpa [liftedBoxFreeConnectionProbability, torusRCFiberEventProbability,
    FK.FiniteProbability.expectation_const] using h

/-- Common-factor form of the full fixed-fiber C-prime estimate. Missing
interior factors may be inserted because each free-box probability is at most one. -/
theorem liftedCPrime_fiber_lower_bound_power (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (x : ℤ) (hx : Even x) (n R : ℕ)
    (hn : 0 < n) (hnleft : 3 * n ≤ N / 2) (hnR : 2 * n ≤ R)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ x - R) (hright : x + R ≤ (N : ℤ))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM)
      (rightHalfFrozenEdges hN hM hN4 hM4))
    (hH : H ∈ rightHalfBarrierExterior hN hM hN4 hM4 hNp hMp n) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (R + 2 * n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin R
        rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n)) ≤
      torusRCFiberEventProbability
        (torusRCFiberLaw hN hM hN4 hM4 q (rightHalfFrozenEdges hN hM hN4 hM4) H)
        {A | rightHalfRestore hN hM hN4 hM4 H A ∈
          liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R} := by
  have h := liftedCPrime_fiber_lower_bound hN hM hN4 hM4 hNp hMp q x hx n R
    hn hnleft hnR hRN hRM hleft hright H hH
  simp_rw [liftedBoxFreeConnectionProbability_chain] at h
  rw [Finset.prod_const] at h
  have hcard : (interiorChainIndices M n R).card ≤ M / (2 * n) :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (liftedBoxFreeConnectionProbability_nonneg _ _ _ _ _)
      (liftedBoxFreeConnectionProbability_le_one _ _ _ _ _) hcard)
    (pow_nonneg (fkOpenEnergy_pos _).le _)).trans h

/-- Averaging the fixed-fiber estimate over B gives its exact conditional
bound in multiplication form, without assuming that B has positive mass. -/
theorem liftedCPrime_mul_barrier_lower_bound (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (x : ℤ) (hx : Even x) (n R : ℕ)
    (hn : 0 < n) (hnleft : 3 * n ≤ N / 2) (hnR : 2 * n ≤ R)
    (hRN : 2 * R < N) (hRM : 2 * R < M)
    (hleft : (N / 2 : ℤ) ≤ x - R) (hright : x + R ≤ (N : ℤ)) :
    (fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (R + 2 * n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin R
        rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n))) *
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n) ≤
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n ∩
        liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R) := by
  classical
  let G := fullDiamondGraph hN hM
  let F := rightHalfFrozenEdges hN hM hN4 hM4
  let S := rightHalfBarrierExterior hN hM hN4 hM4 hNp hMp n
  let E := fun H : FK.RemovedConfiguration G F =>
    {A | rightHalfRestore hN hM hN4 hM4 H A ∈
      liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R}
  let P := fun A : RCConfig N M => FK.configurationSplitEquiv G F
    (torusRCConfigurationEquiv hN hM hN4 hM4 A)
  have hrestore (A : RCConfig N M) :
      rightHalfRestore hN hM hN4 hM4 (P A).2 (P A).1 = A := by
    unfold rightHalfRestore
    have hs := (FK.configurationSplitEquiv G F).symm_apply_apply
      (torusRCConfigurationEquiv hN hM hN4 hM4 A)
    change (P A).1.val ∪ (P A).2.val = torusRCConfigurationEquiv hN hM hN4 hM4 A at hs
    rw [hs, Equiv.symm_apply_apply]
  have hS : {A | (P A).2 ∈ S} = torusRCBarrier hNp hMp n := by
    ext A
    exact (barrier_iff_rightHalfExterior hN hM hN4 hM4 hNp hMp n hnleft A).symm
  have hT : {A | (P A).2 ∈ S ∧ (P A).1 ∈ E (P A).2} =
      torusRCBarrier hNp hMp n ∩
        liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R := by
    ext A
    have hb := barrier_iff_rightHalfExterior hN hM hN4 hM4 hNp hMp n hnleft A
    change ((P A).2 ∈ S ∧ rightHalfRestore hN hM hN4 hM4 (P A).2 (P A).1 ∈
      liftedCPrime hNp hMp (N / 2 : ℤ) (N : ℤ) x hx hM n R) ↔ _
    rw [hrestore]
    exact and_congr_left fun _ => hb.symm
  have h := torusRCProbability_fiber_lower_bound hN hM hN4 hM4 q F S E _
    (fun H hH => liftedCPrime_fiber_lower_bound_power hN hM hN4 hM4 hNp hMp
      q x hx n R hn hnleft hnR hRN hRM hleft hright H hH)
  change _ * torusRCProbability hN hM q {A | (P A).2 ∈ S} ≤
    torusRCProbability hN hM q {A | (P A).2 ∈ S ∧ (P A).1 ∈ E (P A).2} at h
  rwa [hS,hT] at h

/-- Source-positioned C-prime estimate for N divisible by eight. The exponent
K(N,n)=2(N/4+2n) is independent of M, and M need not be divisible by 2n. -/
theorem torusCPrime_mul_barrier_lower_bound (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (hNdiv : 8 ∣ N) (q : Set.Ici (1 : ℝ)) (n : ℕ)
    (hn : 0 < n) (h8n : 8 * n ≤ N) (hNM : N / 2 < M) :
    (fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (N / 4 + 2 * n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin
        (N / 4) rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n))) *
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n) ≤
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n ∩
        torusCPrime hNp hMp hNdiv hM n) := by
  have hmod : N % 8 = 0 := Nat.mod_eq_zero_of_dvd hNdiv
  have hleft : (N / 2 : ℤ) ≤ sourceRightColumn N - N / 4 := by
    dsimp [sourceRightColumn]
    omega
  have hright : sourceRightColumn N + N / 4 ≤ (N : ℤ) := by
    dsimp [sourceRightColumn]
    omega
  exact liftedCPrime_mul_barrier_lower_bound hN hM hN4 hM4 hNp hMp q
    (sourceRightColumn N) (sourceRightColumn_even hNdiv) n (N / 4)
    hn (by omega) (by omega) (by omega) (by omega) hleft hright

end

end PottsDiscontinuity.TorusRC
