module

public import PottsDiscontinuity.TorusTopology.LoopMidpoints

/-! The actual midpoint lift is periodic up to its geometric deck displacement.
Nonzero winding gives a nonzero deck displacement. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}

lemma loopOrbit_add_period (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    (directedStep ω s h)^[n + loopPeriod ω s h d] d =
      (directedStep ω s h)^[n] d :=
  Function.iterate_add_minimalPeriod_eq

/-- The two integer seam displacements of the chosen loop. -/
noncomputable def loopDeckDisplacement (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (i : Fin N) (j : Fin M) : ℤ × ℤ :=
  ((N : ℤ) * loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d),
   (M : ℤ) * loopVertical ω s h j (directedLoopOf ω s h d))

/-- The original-coordinate lift repeats with exactly its homological translation. -/
theorem loopLiftPosition_add_period (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (i : Fin N) (j : Fin M) (n : ℕ) :
    loopLiftPosition ω s h d (n + loopPeriod ω s h d) =
      loopLiftPosition ω s h d n + loopDeckDisplacement ω s h d i j := by
  have hsum (f : Dart N M → ℤ) :
      (∑ k ∈ range (n + loopPeriod ω s h d), f ((directedStep ω s h)^[k] d).val) =
      (∑ k ∈ range (loopPeriod ω s h d), f ((directedStep ω s h)^[k] d).val) +
      ∑ k ∈ range n, f ((directedStep ω s h)^[k] d).val := by
    rw [Nat.add_comm n,Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm,loopOrbit_add_period]
  have hx := loop_horizontal_displacement ω s h i (directedLoopOf ω s h d)
  have hy := loop_vertical_displacement ω s h j (directedLoopOf ω s h d)
  rw [loopSum_eq_sum_period] at hx hy
  ext <;> simp only [loopLiftPosition,hsum,loopDeckDisplacement,Prod.fst_add,Prod.snd_add]
  · omega
  · omega

lemma rotatedMidpoint_translate (z v : ℤ × ℤ) (p : Port) :
    rotatedMidpoint (z+v) p = rotatedMidpoint z p + (v.1+v.2,v.2-v.1) := by
  cases p <;> ext <;> simp [rotatedMidpoint] <;> ring

/-- The square-lattice midpoint polygon is periodic with the corresponding
rotated deck displacement, on the same actual ordered orbit. -/
theorem loopMidpointPosition_add_period (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (i : Fin N) (j : Fin M) (n : ℕ) :
    loopMidpointPosition ω s h d (n + loopPeriod ω s h d) =
      loopMidpointPosition ω s h d n +
        ((loopDeckDisplacement ω s h d i j).1 + (loopDeckDisplacement ω s h d i j).2,
         (loopDeckDisplacement ω s h d i j).2 - (loopDeckDisplacement ω s h d i j).1) := by
  simp only [loopMidpointPosition,loopOrbit_add_period,
    loopLiftPosition_add_period ω s h d i j,rotatedMidpoint_translate]

/-- Nonzero winding is precisely nonzero translation of the midpoint lift. -/
theorem rotated_loopDeckDisplacement_ne_zero_iff
    (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s)
    (d : DirectedDart ω) (i : Fin N) (j : Fin M) :
    ((loopDeckDisplacement ω s h d i j).1 + (loopDeckDisplacement ω s h d i j).2,
     (loopDeckDisplacement ω s h d i j).2 - (loopDeckDisplacement ω s h d i j).1) ≠ (0,0) ↔
      loopVertical ω s h j (directedLoopOf ω s h d) ≠ 0 ∨
      loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d) ≠ 0 := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast (Fin.pos j).ne'
  have hrot (a b : ℤ) : (a+b,b-a) = (0,0) ↔ a=0 ∧ b=0 := by
    simp only [Prod.mk.injEq]
    omega
  simp only [ne_eq,hrot]
  simp only [loopDeckDisplacement,mul_eq_zero,hN0,hM0,false_or,not_and_or]
  exact or_comm

end PottsDiscontinuity.TorusTopology
