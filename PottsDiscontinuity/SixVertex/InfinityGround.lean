module

public import PottsDiscontinuity.SixVertex.InfinitySupport

/-!
# The positive sine-product candidate on the original defect carrier

The shifted coordinates are `X_j + j` and their circumference is
`N + card(defects x)`. Positivity holds directly for this actual finite candidate.
Its eigenvector equation is not asserted in this file.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Canonically ordered defect positions, shifted by their zero-based labels. -/
noncomputable def defectCoordinate (x : Finset (Fin N))
    (j : Fin (defects x).card) : ℕ :=
  ((defects x).orderEmbOfFin rfl j).val + j.val

/-- The Vandermonde sine product evaluated on the shifted defect coordinates. -/
noncomputable def defectGroundWeight (x : Finset (Fin N)) : ℝ :=
  ∏ a : Fin (defects x).card, ∏ b ∈ Ioi a,
    Real.sin (Real.pi * ((defectCoordinate x b : ℝ) - defectCoordinate x a) /
      ((N : ℝ) + (defects x).card))

theorem defectCoordinate_strictMono (x : Finset (Fin N)) : StrictMono (defectCoordinate x) := by
  intro a b hab
  have hp := (defects x).orderEmbOfFin rfl |>.strictMono hab
  have ha : a.val < b.val := hab
  change ((defects x).orderEmbOfFin rfl a).val <
    ((defects x).orderEmbOfFin rfl b).val at hp
  unfold defectCoordinate
  omega

theorem defectCoordinate_lt (x : Finset (Fin N)) (j : Fin (defects x).card) :
    defectCoordinate x j < N + (defects x).card := by
  have h1 := ((defects x).orderEmbOfFin rfl j).isLt
  have h2 := j.isLt
  unfold defectCoordinate
  omega

/-- The candidate is strictly positive, with the empty product included. -/
theorem defectGroundWeight_pos (hN : 0 < N) (x : Finset (Fin N)) :
    0 < defectGroundWeight x := by
  apply prod_pos
  intro a _
  apply prod_pos
  intro b hb
  have hab : a < b := mem_Ioi.mp hb
  have hp := defectCoordinate_strictMono x hab
  have hl := defectCoordinate_lt x b
  have ha := Nat.zero_le (defectCoordinate x a)
  have hden : (0 : ℝ) < N + (defects x).card := by positivity
  have hdiff : (0 : ℝ) < (defectCoordinate x b : ℝ) - defectCoordinate x a := by
    exact sub_pos.mpr (Nat.cast_lt.mpr hp)
  have hbound : (defectCoordinate x b : ℝ) - defectCoordinate x a <
      (N : ℝ) + (defects x).card := by
    have hcast : (defectCoordinate x b : ℝ) < (N : ℝ) + (defects x).card := by
      exact_mod_cast hl
    have hnonneg : (0 : ℝ) ≤ defectCoordinate x a := Nat.cast_nonneg _
    linarith only [hcast, hnonneg]
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hdiff) hden
  · rw [div_lt_iff₀ hden]
    exact mul_lt_mul_of_pos_left hbound Real.pi_pos

end PottsDiscontinuity.SixVertex
