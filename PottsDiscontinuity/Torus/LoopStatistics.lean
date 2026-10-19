module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Vertical winding counts and the sector bound

Parity of the signed flux proves the evenness of the total absolute vertical winding
without a classification of essential loops. The canonical checkerboard orientation
then defines the unoriented RC statistic U using the actual smoothed loop cycles.
Its independence of other choices of loop orientation is a separate proof obligation.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Parity, rather than parallelism of essential loops, already proves that the total
absolute vertical winding is even. -/
theorem verticalMass_even (hN : Even N) (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) : Even (verticalMass ω s h j) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
    (verticalMass ω s h j : ZMod 2) =
        ((∑ q : DirectedLoop ω s h, loopVertical ω s h j q : ℤ) : ZMod 2) := by
      simp only [verticalMass, Nat.cast_sum, Int.cast_sum, ZMod.natAbs_mod_two]
    _ = ((2 * (ω.absUp : ℤ) - N : ℤ) : ZMod 2) := by rw [sum_loopVertical]
    _ = 0 := by
      have hn : (N : ZMod 2) = 0 := hN.natCast_zmod_two
      have htwo : (2 : ZMod 2) = 0 := by decide
      push_cast
      rw [htwo, zero_mul, hn, sub_self]

/-- Half the actual absolute vertical displacement winding, for a directed loop partition. -/
noncomputable def verticalWindingCount (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) : ℕ := verticalMass ω s h j / 2

theorem two_mul_verticalWindingCount (hN : Even N) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : CompatibleConfig ω s) (j : Fin M) :
    2 * verticalWindingCount ω s h j = verticalMass ω s h j := by
  exact Nat.mul_div_cancel' (verticalMass_even hN ω s h j).two_dvd

/-- The up-arrow sector forces at least r pairs of absolute vertical windings. -/
theorem sector_le_verticalWindingCount (hN : Even N) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : CompatibleConfig ω s) (j : Fin M) {r : ℕ}
    (hr : ω.absUp + r = N / 2) : r ≤ verticalWindingCount ω s h j := by
  have hb := two_mul_sector_le_verticalMass hN ω s h j hr
  have he := two_mul_verticalWindingCount hN ω s h j
  omega

/-- The RC loop-count statistic ell, using the canonical orientation of its smoothing. -/
noncomputable def rcLoopCount (hN : Even N) (hM : Even M) (A : RCConfig N M) : ℕ :=
  loopCount hN hM (rcSmoothing A)

/-- The RC vertical statistic U: half the sum of absolute vertical windings of its loops.
The row is an explicit nonempty reference-line index; there is no empty-torus fallback. -/
noncomputable def rcVerticalWinding (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M) : ℕ :=
  verticalWindingCount (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j

end PottsDiscontinuity.Torus
