/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceCornerCompass
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCorners

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem selectedCornerCoeff_positiveDartCount_le_one {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := by
  classical
  unfold parafermionicCoverFacePositiveDartCount
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hdi : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
    (Finset.mem_filter.mp hi).2
  have hdj : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts j.1 :=
    (Finset.mem_filter.mp hj).2
  have hfaces := parafermionicCoverFiniteFaceDart_unique n i.2 j.2 hdi hdj
  exact Subtype.ext hfaces

private theorem selectedCornerCoeff_forward_count_one_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d) :
    parafermionicCoverFacePositiveDartCount S v w = 1 ↔
      d ∈ parafermionicCoverFiniteFaceSelectedCorners S v := by
  classical
  constructor
  · intro hcount
    have hcard : (S.filter fun i => (v.1,w.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card = 1 := by
      simpa [parafermionicCoverFacePositiveDartCount] using hcount
    have hpos : 0 < (S.filter fun i => (v.1,w.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card := by rw [hcard]; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rcases Finset.mem_filter.mp hi with ⟨hiS, hdart⟩
    obtain ⟨c, hvc, hwc⟩ :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i v.1 w.1).mp hdart
    have hdir : c = d := by
      apply parafermionicCoverCompassNeighbor_injective v.1
      calc
        parafermionicCoverCompassNeighbor v.1 c = w.1 := by
          exact hwc.symm
        _ = parafermionicCoverCompassNeighbor v.1 d := hd
    subst c
    exact (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v d).2
      ⟨i, hiS, hvc.symm⟩
  · intro hcorner
    rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v d).mp hcorner with
      ⟨i, hiS, hvc⟩
    have hnext := parafermionicCoverFiniteFaceCorner_next_compass i d
    have hdart : (v.1,w.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i v.1 w.1).2
        ⟨d, hvc.symm, hd⟩
    have hmem : i ∈ S.filter fun j => (v.1,w.1) ∈
        parafermionicCoverFiniteFaceDarts j.1 := Finset.mem_filter.mpr ⟨hiS, hdart⟩
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S v w := by
      unfold parafermionicCoverFacePositiveDartCount
      exact Finset.card_pos.mpr ⟨i, hmem⟩
    have hle := selectedCornerCoeff_positiveDartCount_le_one S v w
    omega

private theorem selectedCornerCoeff_reverse_count_one_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d) :
    parafermionicCoverFacePositiveDartCount S w v = 1 ↔
      d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v := by
  classical
  constructor
  · intro hcount
    have hcard : (S.filter fun i => (w.1,v.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card = 1 := by
      simpa [parafermionicCoverFacePositiveDartCount] using hcount
    have hpos : 0 < (S.filter fun i => (w.1,v.1) ∈
        parafermionicCoverFiniteFaceDarts i.1).card := by rw [hcard]; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rcases Finset.mem_filter.mp hi with ⟨hiS, hdart⟩
    obtain ⟨c, hwc, hvc⟩ :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i w.1 v.1).mp hdart
    have hc : d + 2 = c := by
      apply parafermionicCoverCompassNeighbor_injective w.1
      calc
        parafermionicCoverCompassNeighbor w.1 (d + 2) = v.1 := by
          rw [hd]
          exact parafermionicCoverCompassNeighbor_reverse v.1 d
        _ = parafermionicCoverCompassNeighbor w.1 c := hvc
    have hdir : c + 1 = d - 1 := by
      rw [← hc]
      fin_cases d <;> decide
    have hcorner : parafermionicCoverFaceCorner i.1 (d - 1) = v.1 := by
      rw [← hdir]
      have hnext := parafermionicCoverFiniteFaceCorner_next_compass i c
      rw [← hwc] at hnext
      exact hnext.trans hvc.symm
    exact (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v (d - 1)).2
      ⟨i, hiS, hcorner⟩
  · intro hcorner
    rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v (d - 1)).mp hcorner with
      ⟨i, hiS, hvc⟩
    have hprev := parafermionicCoverFiniteFaceCorner_prev_compass i (d - 1)
    have hidx : (d - 1) + 1 = d := by fin_cases d <;> decide
    have hcorneridx : (d - 1) - 1 = d + 2 := by fin_cases d <;> decide
    have hfirst : parafermionicCoverFaceCorner i.1 (d + 2) = w.1 := by
      rw [← hcorneridx, hprev, hidx, hvc, hd]
    have hback : parafermionicCoverCompassNeighbor w.1 (d + 2) = v.1 := by
      rw [hd]
      exact parafermionicCoverCompassNeighbor_reverse v.1 d
    have hdart : (w.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
      (parafermionicCoverFiniteFaceDart_iff_corner_compass i w.1 v.1).2
        ⟨d + 2, hfirst.symm, hback.symm⟩
    have hmem : i ∈ S.filter fun j => (w.1,v.1) ∈
        parafermionicCoverFiniteFaceDarts j.1 := Finset.mem_filter.mpr ⟨hiS, hdart⟩
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S w v := by
      unfold parafermionicCoverFacePositiveDartCount
      exact Finset.card_pos.mpr ⟨i, hmem⟩
    have hle := selectedCornerCoeff_positiveDartCount_le_one S w v
    omega

/-- A directed positive-dart count along compass direction `d` is the
indicator that `d` is a selected corner at its source. -/
theorem parafermionicCoverFacePositiveDartCount_eq_selectedCornerIndicator
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d) :
    parafermionicCoverFacePositiveDartCount S v w =
      if d ∈ parafermionicCoverFiniteFaceSelectedCorners S v then 1 else 0 := by
  by_cases hcorner : d ∈ parafermionicCoverFiniteFaceSelectedCorners S v
  · have hone := (selectedCornerCoeff_forward_count_one_iff S v w d hd).2 hcorner
    simp [hcorner, hone]
  · have hne : parafermionicCoverFacePositiveDartCount S v w ≠ 1 := by
      intro hone
      exact hcorner ((selectedCornerCoeff_forward_count_one_iff S v w d hd).1 hone)
    have hle := selectedCornerCoeff_positiveDartCount_le_one S v w
    simp [hcorner]
    omega

/-- The reversed edge count is the indicator at the preceding corner. -/
theorem parafermionicCoverFacePositiveDartCount_reverse_eq_selectedCornerIndicator
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d) :
    parafermionicCoverFacePositiveDartCount S w v =
      if d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v then 1 else 0 := by
  by_cases hcorner : d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v
  · have hone := (selectedCornerCoeff_reverse_count_one_iff S v w d hd).2 hcorner
    simp [hcorner, hone]
  · have hne : parafermionicCoverFacePositiveDartCount S w v ≠ 1 := by
      intro hone
      exact hcorner ((selectedCornerCoeff_reverse_count_one_iff S v w d hd).1 hone)
    have hle := selectedCornerCoeff_positiveDartCount_le_one S w v
    simp [hcorner]
    omega

/-- The oriented coefficient is the integer difference of the two adjacent
corner indicators. -/
theorem parafermionicCoverFaceBoundaryCoefficient_eq_selectedCornerIndicators
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n) (d : Fin 4)
    (hd : w.1 = parafermionicCoverCompassNeighbor v.1 d) :
    parafermionicCoverFaceBoundaryCoefficient S v w =
      (if d ∈ parafermionicCoverFiniteFaceSelectedCorners S v then (1 : ℤ) else 0) -
      (if d - 1 ∈ parafermionicCoverFiniteFaceSelectedCorners S v then (1 : ℤ) else 0) := by
  rw [parafermionicCoverFaceBoundaryCoefficient,
    parafermionicCoverFacePositiveDartCount_eq_selectedCornerIndicator S v w d hd,
    parafermionicCoverFacePositiveDartCount_reverse_eq_selectedCornerIndicator S v w d hd]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end PottsDiscontinuity.TorusTopology.Planar.Medial
