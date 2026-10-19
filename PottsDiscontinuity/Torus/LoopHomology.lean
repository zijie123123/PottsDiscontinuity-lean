module

public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Discrete vertical homology of the smoothed loop cycles

An elementary coboundary calculation shows that a closed orbit has the same signed
intersection with every horizontal reference row. Summing those intersections gives
its lifted vertical displacement. Thus the crossing statistic has its actual winding
meaning, independently of any turning-number classification.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem loopSum_sub (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f g : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f d - g d) q = loopSum ω s h f q - loopSum ω s h g q := by
  classical
  unfold loopSum
  rw [Finset.sum_sub_distrib]

/-- Reindexing a cyclic orbit by its path step does not change its sum. -/
theorem loopSum_step (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f (stepPerm s d)) q = loopSum ω s h f q := by
  classical
  unfold loopSum
  simp only [Finset.sum_filter]
  refine Fintype.sum_equiv (directedStep ω s h) _ _ ?_
  intro d
  rw [directedLoopOf_step]
  rfl

/-- A row-indicator potential on the initial vertex of a dart. -/
def rowPotential (j : Fin M) (d : Dart N M) : ℤ := if d.1.2 = j then 1 else 0

/-- Adjacent reference-row cocycles differ by a vertex coboundary. -/
theorem verticalCross_sub_prv (s : Smoothing N M) (j : Fin M) (d : Dart N M) :
    verticalCross j d - verticalCross (prv j) d =
      rowPotential j d - rowPotential j (stepPerm s d) := by
  rcases d with ⟨⟨i, k⟩, p⟩
  have hn : nxt k = j ↔ k = prv j := by
    constructor
    · intro h
      rw [← h]
      simp only [nxt, prv, Equiv.symm_apply_apply]
    · intro h
      rw [h]
      simp only [nxt, prv, Equiv.apply_symm_apply]
  have hp : prv k = prv j ↔ k = j := (finRotate M).symm.injective.eq_iff
  have hh (a b : Prop) [Decidable a] [Decidable b] :
      ((if a then (-1 : ℤ) else 0) - if b then -1 else 0) =
        (if b then 1 else 0) - if a then 1 else 0 := by
    by_cases ha : a <;> by_cases hb : b <;>
      simp only [ha, hb, ite_true, ite_false] <;> norm_num
  cases p <;>
    simp only [verticalCross, rowPotential, stepPerm_apply, strandReverse,
      edgeReverse, hn, hp, sub_self]
  all_goals
    first
    | exact (sub_self (if k = j then (1 : ℤ) else 0)).symm
    | exact hh (prv k = j) (k = j)

/-- A closed loop has equal intersection with two adjacent horizontal reference rows. -/
theorem loopVertical_prv (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) (q : DirectedLoop ω s h) :
    loopVertical ω s h j q = loopVertical ω s h (prv j) q := by
  have hb : loopSum ω s h (fun d => verticalCross j d - verticalCross (prv j) d) q = 0 := by
    simp_rw [verticalCross_sub_prv s j]
    rw [loopSum_sub, loopSum_step, sub_self]
  rw [loopSum_sub] at hb
  exact sub_eq_zero.mp hb

/-- The intersection number is independent of the chosen horizontal reference row. -/
theorem loopVertical_eq (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j k : Fin M) (q : DirectedLoop ω s h) :
    loopVertical ω s h j q = loopVertical ω s h k q := by
  have hM : 0 < M := Fin.pos j
  have hz : ∀ l : Fin M, loopVertical ω s h l q = loopVertical ω s h ⟨0, hM⟩ q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
    intro l
    induction l using Fin.induction with
    | zero => rfl
    | succ l ih =>
      rw [loopVertical_prv, prv_succ]
      exact ih
  exact (hz j).trans (hz k).symm

/-- Vertical displacement in the integer lift of one directed torus edge. -/
def verticalIncrement : Dart N M → ℤ
  | (_, .north) => 1
  | (_, .south) => -1
  | (_, .west) => 0
  | (_, .east) => 0

theorem sum_verticalCross_rows (d : Dart N M) :
    ∑ j : Fin M, verticalCross j d = verticalIncrement d := by
  rcases d with ⟨⟨i, k⟩, p⟩
  cases p <;> simp [verticalCross, verticalIncrement]

/-- The winding is exactly the lifted vertical displacement divided by the vertical period:
this integral identity avoids division and has no zero-period fallback. -/
theorem loop_vertical_displacement (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) (q : DirectedLoop ω s h) :
    loopSum ω s h verticalIncrement q = (M : ℤ) * loopVertical ω s h j q := by
  classical
  calc
    loopSum ω s h verticalIncrement q =
        ∑ k : Fin M, loopVertical ω s h k q := by
      unfold loopVertical loopSum
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => (sum_verticalCross_rows d.val).symm
    _ = ∑ _k : Fin M, loopVertical ω s h j q :=
      Finset.sum_congr rfl fun k _ => loopVertical_eq ω s h k j q
    _ = (M : ℤ) * loopVertical ω s h j q := by simp

end PottsDiscontinuity.Torus
