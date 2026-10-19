module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# The corrected scalar boundary limit in Lemma 3.7 of the companion paper

In the proof of Lemma 3.7 (the limit of `T₀(ε)`) of the companion paper [8], arXiv:1611.09909
(The Bethe ansatz for the six-vertex and XXZ models: an exposition), the boundary bracket must be
`z^(-N) - 1`.
The printed bracket `1 - z^(-N)` has the negative of the claimed limit.
We prove the limits on the punctured complex neighborhood of `1`, using an exact
finite-geometric-sum identity. This is only the scalar boundary calculation, not Lemma 3.7
for the entire permutation sum.
-/

@[expose] public section

open Finset Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- The corrected decomposition of the two constant-word scalar factors. -/
theorem constant_words_boundary_decomposition (c : ℝ) (w : ℂ) (N : ℕ) :
    M c w + L c w * (w ^ N)⁻¹ =
      (M c w + L c w) + L c w * ((w ^ N)⁻¹ - 1) := by ring

/-- Remove the apparent pole by a finite geometric sum. -/
theorem L_mul_inv_pow_sub_one (c : ℝ) (N : ℕ) {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    L c w * ((w ^ N)⁻¹ - 1) =
      (1 - w + (c : ℂ) ^ 2 * w) * (∑ k ∈ range N, w ^ k) / w ^ N := by
  rw [geom_sum_eq hw1]
  have hd : 1 - w ≠ 0 := sub_ne_zero.mpr hw1.symm
  have hd' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hp : w ^ N ≠ 0 := pow_ne_zero N hw0
  unfold L
  field_simp
  ring

end PottsDiscontinuity.BetheAnsatz
