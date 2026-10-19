module

public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.TorusTopology.BarrierEvent

/-! A finite configuration witnessing the exact-one vertical-winding event on
large widths divisible by eight. -/

@[expose] public section

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus TorusRC CorrLength

def exactOneWitnessConfig (N M : ℕ) :
    RCConfig N M := fun e => decide (e.1.val ≠ 1)

private theorem exactOneWitnessConfig_isolatedSeamIndex {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) :
    ∀ j : Fin M,
      exactOneWitnessConfig N M (⟨1, by omega⟩, j) = false := by
  intro j
  obtain ⟨k, hk⟩ := hNdiv
  have hkpos : 1 ≤ k := by omega
  have hcol : 1 ≠ 3 * (N / 4) + 1 := by
    rw [hk]
    omega
  change decide (1 ≠ 1) = false
  simp

private theorem exactOneWitnessConfig_seam_all_but_one {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hM : 0 < M) :
    TorusRC.torusRCSeamAllButOneOpen hM (exactOneWitnessConfig N M) := by
  refine ⟨⟨1, by omega⟩, ?_, ?_⟩
  · change decide (1 ≠ 1) = false
    simp
  · intro i hi
    have hi' : i.val ≠ 1 := fun h => hi (Fin.ext h)
    change decide (i.val ≠ 1) = true
    simp [hi']

private theorem exactOneWitnessConfig_noLeftCrossing {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M) :
    ¬ TorusRC.torusRCLeftStripCrossing (by omega) hMpos
      (exactOneWitnessConfig N M) 1 := by
  intro hcross
  rcases hcross with ⟨u, v, hu, hv, hreach⟩
  have hNpos : 0 < N := by omega
  let G := TorusRC.liftedStripGraph hNpos hMpos
    (exactOneWitnessConfig N M) 0 3
  have hisolated (z : RotatedVertex) (hz : G.Adj u z) : False := by
    have hzxnonneg : 0 ≤ z.val.1 := hz.2.2.2.1
    have hzxabs : |z.val.1| = 1 := by
      simpa [hu] using hz.1.1
    have hzx : z.val.1 = 1 := by
      have hpos : 0 ≤ z.val.1 := hzxnonneg
      rw [abs_of_nonneg hpos] at hzxabs
      omega
    have hfirst : (TorusRC.liftedEdgeIndex hNpos hMpos u z).1 =
        (⟨1, by omega⟩ : Fin N) := by
      apply Fin.ext
      change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = 1
      rw [hu, hzx, max_eq_right (by norm_num : (0 : ℤ) ≤ 1)]
      exact congrArg Fin.val
        (TorusTopology.periodicCoordinate_nat hNpos (⟨1, by omega⟩ : Fin N))
    have hclosed := exactOneWitnessConfig_isolatedSeamIndex hNdiv hNlarge
      (TorusRC.liftedEdgeIndex hNpos hMpos u z).2
    have hopen := hz.2.1
    have hpair : ((⟨1, by omega⟩ : Fin N),
        (TorusRC.liftedEdgeIndex hNpos hMpos u z).2) =
        TorusRC.liftedEdgeIndex hNpos hMpos u z := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    have hclosed' : exactOneWitnessConfig N M
        (TorusRC.liftedEdgeIndex hNpos hMpos u z) = false := by
      rw [← hpair]
      exact hclosed
    exact Bool.noConfusion (hclosed'.symm.trans hopen)
  rcases hreach with ⟨w⟩
  cases w with
  | nil => omega
  | cons hadj _ => exact hisolated _ hadj

private theorem exactOneWitnessConfig_in_CPrime {N M : ℕ}
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMeven : Even M) (hMpos : 0 < M) :
    (exactOneWitnessConfig N M) ∈
      TorusRC.torusCPrime (by omega) hMpos hNdiv hMeven 1 := by
  have hNdivCopy := hNdiv
  obtain ⟨kN, hkN⟩ := hNdivCopy
  have hkNpos : 1 ≤ kN := by omega
  have hNformula : N = 8 * kN := hkN
  have hcol : 3 * (N / 4) = 6 * kN := by omega
  have hcolLt : 3 * (N / 4) + 1 < N := by omega
  have hx : TorusRC.sourceRightColumn N = (3 * (N / 4) : ℕ) := rfl
  have hxEven : Even (TorusRC.sourceRightColumn N) :=
    TorusRC.sourceRightColumn_even hNdiv
  have hstripLo : (N / 2 : ℤ) ≤ TorusRC.sourceRightColumn N := by
    rw [hx]
    exact_mod_cast (show N / 2 ≤ 3 * (N / 4) by omega)
  have hstripHi : TorusRC.sourceRightColumn N + 1 ≤ (N : ℤ) := by
    rw [hx]
    exact_mod_cast (show 3 * (N / 4) + 1 ≤ N by omega)
  have hcolumnOpen (j : Fin M) :
      exactOneWitnessConfig N M
        (⟨3 * (N / 4) + 1, hcolLt⟩, j) = true := by
    change decide (3 * (N / 4) + 1 ≠ 1) = true
    exact decide_eq_true_eq.mpr (by omega)
  have hlocal (j : ℕ) (hj : j < M / 2) :
      TorusRC.liftedBoxConnection (by omega) hMpos (exactOneWitnessConfig N M)
        (N / 2 : ℤ) (N : ℤ) (N / 4)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 j)
        (TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)) := by
    let t : ℤ := 2 * (j : ℤ)
    let u : RotatedVertex := TorusRC.liftedChainSite
      (TorusRC.sourceRightColumn N) hxEven 1 j
    let v : RotatedVertex := TorusRC.liftedChainSite
      (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)
    let z : RotatedVertex := ⟨(TorusRC.sourceRightColumn N + 1, t + 1), by
      rcases hxEven with ⟨x, hx⟩
      refine ⟨x + j + 1, ?_⟩
      dsimp [t]
      omega⟩
    have hNpos : 0 < N := by omega
    have hcolIndex : TorusRC.periodicCoordinate hNpos
        (TorusRC.sourceRightColumn N + 1) =
          (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N) := by
      have hp := TorusTopology.periodicCoordinate_nat hNpos
        (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N)
      simpa [TorusRC.sourceRightColumn] using hp
    have hux : u.val.1 = TorusRC.sourceRightColumn N := by rfl
    have hzx : z.val.1 = TorusRC.sourceRightColumn N + 1 := by rfl
    have hvx : v.val.1 = TorusRC.sourceRightColumn N := by rfl
    have huy : u.val.2 = t := by
      change 2 * (1 : ℤ) * (j : ℤ) = t
      simp [t]
    have hzy : z.val.2 = t + 1 := by rfl
    have hvy : v.val.2 = t + 2 := by
      change 2 * (1 : ℤ) * ((j + 1 : ℕ) : ℤ) = t + 2
      simp [t]
      ring
    have hindex1 : TorusRC.liftedEdgeIndex hNpos hMpos u z =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 1)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = _
        rw [hux, hzx, max_eq_right (by omega : TorusRC.sourceRightColumn N ≤
          TorusRC.sourceRightColumn N + 1)]
        exact congrArg Fin.val hcolIndex
      · change TorusRC.periodicCoordinate hMpos (max u.val.2 z.val.2) = _
        rw [huy, hzy, max_eq_right (by omega : t ≤ t + 1)]
    have hindex2 : TorusRC.liftedEdgeIndex hNpos hMpos z v =
        (⟨3 * (N / 4) + 1, hcolLt⟩,
          TorusRC.periodicCoordinate hMpos (t + 2)) := by
      apply Prod.ext
      · apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max z.val.1 v.val.1)).val = _
        rw [hzx, hvx, max_eq_left (by omega : TorusRC.sourceRightColumn N ≤
          TorusRC.sourceRightColumn N + 1)]
        exact congrArg Fin.val hcolIndex
      · change TorusRC.periodicCoordinate hMpos (max z.val.2 v.val.2) = _
        rw [hzy, hvy, max_eq_right (by omega : t + 1 ≤ t + 2)]
    have hAdj1 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj u z := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |u.val.1 - z.val.1| = 1 ∧ |u.val.2 - z.val.2| = 1
        rw [hux, hzx, huy, hzy]
        norm_num
      · rw [hindex1]
        exact hcolumnOpen ⟨TorusRC.periodicCoordinate hMpos (t + 1), by omega⟩
      · constructor
        · rw [hux]
          exact hstripLo
        · rw [hux]
          omega
      · constructor
        · rw [hzx]
          exact hstripLo.trans (by omega)
        · rw [hzx]
          exact hstripHi
    have hAdj2 :
        (TorusRC.liftedStripGraph hNpos hMpos (exactOneWitnessConfig N M)
          (N / 2 : ℤ) (N : ℤ)).Adj z v := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · change |z.val.1 - v.val.1| = 1 ∧ |z.val.2 - v.val.2| = 1
        rw [hzx, hvx, hzy, hvy]
        norm_num
      · rw [hindex2]
        exact hcolumnOpen ⟨TorusRC.periodicCoordinate hMpos (t + 2), by omega⟩
      · constructor
        · rw [hzx]
          exact hstripLo.trans (by omega)
        · rw [hzx]
          exact hstripHi
      · constructor
        · rw [hvx]
          exact hstripLo
        · rw [hvx]
          omega
    refine ⟨SimpleGraph.Walk.cons hAdj1 (SimpleGraph.Walk.cons hAdj2 .nil), ?_⟩
    have hR : 2 ≤ (N / 4 : ℤ) := by
      exact_mod_cast (show 2 ≤ N / 4 by omega)
    have hboxU : TorusRC.inLiftedBox (N / 4) u u := by
      simp [TorusRC.inLiftedBox]
      positivity
    have hboxZ : TorusRC.inLiftedBox (N / 4) u z := by
      change |z.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧
        |z.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      rw [hux, hzx, huy, hzy]
      constructor <;> norm_num <;> omega
    have hboxV : TorusRC.inLiftedBox (N / 4) u v := by
      change |v.val.1 - u.val.1| ≤ (N / 4 : ℤ) ∧
        |v.val.2 - u.val.2| ≤ (N / 4 : ℤ)
      rw [hux, hvx, huy, hvy]
      constructor <;> norm_num <;> omega
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hw
    simp at hw
    rcases hw with rfl | rfl | rfl
    · exact hboxU
    · exact hboxZ
    · exact hboxV
  change (exactOneWitnessConfig N M) ∈
    TorusRC.liftedCPrime (by omega) hMpos (N / 2 : ℤ) (N : ℤ)
      (TorusRC.sourceRightColumn N) hxEven hMeven 1 (N / 4)
  simp only [TorusRC.liftedCPrime, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · intro j hj
    have hj' : j < M / 2 := by simpa using hj
    exact hlocal j hj'
  · have hk : M / (2 * 1) = M / 2 := by omega
    have hy : TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (M / 2) =
        TorusRC.liftedColumnSite (TorusRC.sourceRightColumn N) M hxEven
          (by exact_mod_cast hMeven) := by
      apply Subtype.ext
      change (TorusRC.sourceRightColumn N, 2 * (1 : ℤ) * ((M / 2 : ℕ) : ℤ)) =
        (TorusRC.sourceRightColumn N, (M : ℤ))
      apply Prod.ext
      · rfl
      · have hMevenCopy := hMeven
        rcases hMevenCopy with ⟨m, hm⟩
        norm_num
        omega
    rw [hk, hy]
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    simp [TorusRC.inLiftedBox]
    positivity

theorem exactOneProbability_pos_of_large_eight_width
    {N M : ℕ} (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M)
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M)
    (hMlarge : N / 2 < M) :
    0 < TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1} := by
  have hNpos : 0 < N := by omega
  have hB : exactOneWitnessConfig N M ∈ TorusRC.torusRCBarrier hNpos hMpos 1 := by
    refine ⟨exactOneWitnessConfig_noLeftCrossing hNdiv hNlarge hMpos, ?_⟩
    exact exactOneWitnessConfig_seam_all_but_one hNdiv hNlarge hMpos
  have hC := exactOneWitnessConfig_in_CPrime hNdiv hNlarge hM hMpos
  have hU := TorusTopology.hBCU_proved hN hM hNpos hMpos hNdiv 1
    (by omega) hMlarge _ hB hC
  apply (TorusRC.torusRCProbability_pos_iff hN hM q _).2
  exact ⟨exactOneWitnessConfig N M, hU⟩

end PottsDiscontinuity.RCMProof
