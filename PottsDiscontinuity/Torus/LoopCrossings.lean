module

public import PottsDiscontinuity.Torus.EdgeIndex
public import PottsDiscontinuity.SixVertex.TraceFormula

/-!
# Algebraic crossings of actual directed loop orbits

Crossings are signed intersections with a fixed row of vertical edges. Grouping the
edge sum by the genuine permutation cycles proves the row-flux formula and the lower
bound on total absolute vertical crossings in a prescribed six-vertex sector.
No turning-number, simplicity, parallelism, or genus assumption is used.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Signed crossing of row `j` by a directed edge. -/
def verticalCross (j : Fin M) : Dart N M → ℤ
  | ((_, k), .north) => if k = j then 1 else 0
  | ((_, k), .south) => if prv k = j then -1 else 0
  | (_, .west) => 0
  | (_, .east) => 0

theorem verticalCross_edgeReverse (j : Fin M) (d : Dart N M) :
    verticalCross j (edgeReverse d) = -verticalCross j d := by
  rcases d with ⟨⟨i, k⟩, p⟩
  cases p <;> simp only [verticalCross, edgeReverse, prv, nxt,
    Equiv.symm_apply_apply, neg_zero, neg_ite, neg_neg]

/-- A genuine finite sum over the directed edges in one cyclic orbit. -/
noncomputable def loopSum (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f : Dart N M → ℤ) (q : DirectedLoop ω s h) : ℤ := by
  classical
  exact ∑ d : DirectedDart ω with directedLoopOf ω s h d = q, f d.val

/-- The directed loop classes partition the indexed edge set. -/
theorem sum_loopSum (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f : Dart N M → ℤ) :
    ∑ q : DirectedLoop ω s h, loopSum ω s h f q = ∑ d : DirectedDart ω, f d.val := by
  classical
  exact Finset.sum_fiberwise univ (directedLoopOf ω s h) (fun d => f d.val)

/-- The algebraic vertical intersection number of one loop with a fixed reference row. -/
noncomputable def loopVertical (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) (q : DirectedLoop ω s h) : ℤ :=
  loopSum ω s h (verticalCross j) q

theorem verticalCross_arrowDart (ω : ArrowConfig N M) (j : Fin M)
    (v : Fin N × Fin M) (b : Bool) :
    verticalCross j (arrowDart ω (v, b)) =
      if b then (if v.2 = j then (if ω.vert v then 1 else -1) else 0) else 0 := by
  rcases v with ⟨i, k⟩
  cases b <;> simp only [arrowDart] <;> split_ifs <;>
    simp_all only [verticalCross, prv, nxt, Equiv.symm_apply_apply, ite_true, ite_false]

/-- The signed crossing sum over all directed edges is twice the number of up arrows minus N. -/
theorem sum_verticalCross (ω : ArrowConfig N M) (j : Fin M) :
    ∑ d : DirectedDart ω, verticalCross j d.val = 2 * (ω.rowUp j : ℤ) - N := by
  rw [← (edgeDirectedEquiv ω).sum_comp]
  change (∑ e : MedialEdge N M, verticalCross j (arrowDart ω e)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [verticalCross_arrowDart]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false, add_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', mem_univ, ite_true]
  have hs : ∀ b : Bool, (if b then (1 : ℤ) else -1) =
      2 * (if b = true then 1 else 0) - 1 := by decide
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 2
  simp only [ArrowConfig.rowUp, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- The source's signed row-flux identity, for the actual cyclic loop carrier. -/
theorem sum_loopVertical (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) :
    ∑ q : DirectedLoop ω s h, loopVertical ω s h j q = 2 * (ω.absUp : ℤ) - N := by
  change (∑ q : DirectedLoop ω s h, loopSum ω s h (verticalCross j) q) = _
  rw [sum_loopSum, sum_verticalCross, rowUp_eq_absUp h.iceRule]

/-- Total absolute intersection count, prior to division by two in the definition of U. -/
noncomputable def verticalMass (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) : ℕ :=
  ∑ q : DirectedLoop ω s h, (loopVertical ω s h j q).natAbs

/-- A configuration with `N/2-r` up arrows has at least `2r` absolute vertical loop crossings.
This is the counting part of the up-arrow counting argument in the proof of Corollary 3.13
(Section 3.3.1); it does not use parallelism of loops. -/
theorem two_mul_sector_le_verticalMass (hN : Even N) (ω : ArrowConfig N M)
    (s : Smoothing N M) (h : CompatibleConfig ω s) (j : Fin M) {r : ℕ}
    (hr : ω.absUp + r = N / 2) : 2 * r ≤ verticalMass ω s h j := by
  have he : N % 2 = 0 := by rcases hN with ⟨k, hk⟩; omega
  have hflux := sum_loopVertical ω s h j
  have hs : (∑ q : DirectedLoop ω s h, loopVertical ω s h j q) = -(2 * (r : ℤ)) := by
    omega
  have hb := Finset.abs_sum_le_sum_abs
    (fun q : DirectedLoop ω s h => loopVertical ω s h j q) univ
  rw [hs, abs_neg, abs_of_nonneg (by positivity)] at hb
  have hm : (verticalMass ω s h j : ℤ) =
      ∑ q : DirectedLoop ω s h, |loopVertical ω s h j q| := by
    simp only [verticalMass, Nat.cast_sum, Int.natCast_natAbs]
  rw [← hm] at hb
  exact_mod_cast hb

end PottsDiscontinuity.Torus
