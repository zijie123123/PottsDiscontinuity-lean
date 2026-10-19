module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.Duality.ConnectionSymmetry

/-! A reflection bound uniform in the horizontal coordinate of an unrolled
crossing. Its diagonal rate has exactly the normalization required by (3.16). -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK MeasureTheory

lemma corrLength_connectionEvent_eq (u v : LatticeVertex) :
    CorrLength.connectionEvent u v = Duality.connectionEvent u v := by
  ext ω
  exact CorrLength.connectionEvent_iff_rcInfiniteReachable u v ω

lemma twoPoint_swap (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    Duality.twoPoint μ (x.2,x.1) = Duality.twoPoint μ x := by
  have h := Duality.twoPoint_quarterTurn θ μ hμ (x.1,-x.2)
  simp only [neg_neg] at h
  exact h.trans (Duality.twoPoint_flipY θ μ hμ x)

/-- Reflection across the rotated vertical axis and FKG glue two equal
connections into a connection along the vertical diagonal. -/
theorem connection_sq_le_diagonal_sum (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    μ.real (CorrLength.connectionEvent (0,0) x) ^ 2 ≤
      μ.real (CorrLength.connectionEvent (0,0) (x.1+x.2,x.1+x.2)) := by
  have h := Duality.twoPoint_mul_le θ μ hμ x (x.2,x.1)
  rw [twoPoint_swap θ μ hμ x,← pow_two] at h
  have heq : x+(x.2,x.1) = (x.1+x.2,x.1+x.2) := by ext <;> simp [add_comm]
  rw [heq] at h
  simp only [corrLength_connectionEvent_eq]
  exact h

/-- Uniform in the horizontal lifted displacement: height k costs at most
one half of the logarithmic probability at diagonalSite(2k). -/
theorem connection_sq_le_diagonalSite_of_sum (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) (k : ℕ)
    (hk : x.1+x.2=(k : ℤ)) :
    μ.real (CorrLength.connectionEvent (0,0) x) ^ 2 ≤
      μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*k))) := by
  rw [CorrLength.diagonalSite_even]
  simpa only [hk] using connection_sq_le_diagonal_sum θ μ hμ x

end PottsDiscontinuity.TorusExploration
