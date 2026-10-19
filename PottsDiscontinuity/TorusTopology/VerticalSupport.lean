module

public import PottsDiscontinuity.Torus.LoopStatistics

/-! The weak form of the vertical loop structure for U = 1 (at most two loops with nonzero
vertical winding), required by the sector estimate, uses only the
absolute winding mass, not classification of essential torus curves. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus
variable {N M : ℕ}
noncomputable section

/-- Loops with nonzero algebraic vertical winding at a reference row. -/
def verticalWindingLoops (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M) : Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact univ.filter fun q =>
    loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0

/-- Each vertically winding loop contributes at least one to absolute mass. -/
theorem verticalWindingLoops_card_le_mass (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M) :
    (verticalWindingLoops hN hM j A).card ≤
      verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j := by
  classical
  calc
    _ = ∑ _q ∈ verticalWindingLoops hN hM j A, 1 := by simp
    _ ≤ ∑ q ∈ verticalWindingLoops hN hM j A,
        (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).natAbs := by
      apply Finset.sum_le_sum
      intro q hq
      have hn := (Finset.mem_filter.1 hq).2
      have hp := Int.natAbs_pos.2 hn
      omega
    _ ≤ verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The vertical loop structure for U = 1, in the weaker form required by the sector
estimate of Corollary 3.13(ii): U=1 allows at most
two loops with nonzero vertical winding. No claim of zero horizontal winding. -/
theorem verticalWindingLoops_card_le_two_of_U_eq_one
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
    (hU : rcVerticalWinding hN hM j A = 1) :
    (verticalWindingLoops hN hM j A).card ≤ 2 := by
  have he := two_mul_verticalWindingCount hN (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  change 2 * rcVerticalWinding hN hM j A = _ at he
  rw [hU] at he
  exact (verticalWindingLoops_card_le_mass hN hM j A).trans (by omega)

end
end PottsDiscontinuity.TorusTopology
