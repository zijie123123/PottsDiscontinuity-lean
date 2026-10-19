module

public import PottsDiscontinuity.Bethe.AsymptoticOffset

/-! # Quantitative truncation at the logarithmic singularity

Root-spacing and root-offset estimates are kept separate from the spectral
profile: this finite estimate applies to every derivative with `|x l'(x)|`
bounded. The zero root is explicitly excluded.
-/

@[expose] public section

open Set Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The geometric pair estimate and reflection symmetry imply exact linear
control at root locations, without a mesh-error term. -/
theorem ratio_offset_root_linear {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r)) {C : ℝ}
    (hpair : ∀ i j,
      |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤
        C * |q i - q j|) (j : Fin (N / 2 - r)) :
    |offsetDisplacement N r h4 hr p q j| ≤ C * |q j| := by
  have h := hpair j (Fin.rev j)
  rw [offsetDisplacement_rev h4 hr hp hq, show q (Fin.rev j) = -q j from hq.2.2 j] at h
  have he (x : ℝ) : |x - -x| = 2 * |x| := by
    rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he, he] at h
  linarith

end PottsDiscontinuity.Bethe
