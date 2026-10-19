module

public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Summing the signed turns over the actual loop partition

The local turn at an outgoing dart is determined by its paired incoming dart.
The loop sums therefore add to the previously defined vertex turn sum. This proves
the bookkeeping and local-table step of Lemma 3.11, but does not assert the discrete
Umlaufsatz or classify the total turn of an individual loop by contractibility.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The signed quarter turn from the paired incoming strand to this outgoing dart. -/
def strandTurn (s : Bool) : Port → ℤ
  | .west | .east => if s then 1 else -1
  | .south | .north => if s then -1 else 1

/-- The two actual strand turns reproduce the local signed table. -/
theorem sum_outgoing_strandTurn (s l r d u : Bool) (h : Compatible s l r d u) :
    ∑ p : Port, (if localOut l r d u p then strandTurn s p else 0) = quarterTurn s l r := by
  revert s l r d u
  decide

/-- Integer turn sum of a single directed loop, measured in quarter turns. -/
noncomputable def loopTurn (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (q : DirectedLoop ω s h) : ℤ :=
  loopSum ω s h (fun d => strandTurn (s d.1) d.2) q

/-- Total turning of the actual loop cycles equals the sum of the local vertex contributions. -/
theorem sum_loopTurn (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) :
    ∑ q : DirectedLoop ω s h, loopTurn ω s h q = totalQuarterTurn ω s := by
  classical
  change (∑ q : DirectedLoop ω s h,
    loopSum ω s h (fun d => strandTurn (s d.1) d.2) q) = _
  rw [sum_loopSum]
  rw [← Finset.sum_subtype (univ.filter fun d => dartOut ω d = true)
    (by intro d; simp) (fun d => strandTurn (s d.1) d.2), Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun v _ => sum_outgoing_strandTurn _ _ _ _ _ (h v)

end PottsDiscontinuity.Torus
