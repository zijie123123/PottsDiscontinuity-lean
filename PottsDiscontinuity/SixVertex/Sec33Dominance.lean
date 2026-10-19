module

public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.SixVertex.Sec33Symmetry

/-!
# Abstract assembly of the six-vertex dominance gap

The repaired large-width argument in the dependency graph has external Potts-model inputs.  This
module proves its finite spectral assembly conditionally on the stated exponential gap for all
`r ≥ 2` and the strict `r = 1` comparison; it does not prove those analytic hypotheses.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c η : ℝ}

/-- Every particle-number block is the sector at its distance from half filling, after using the
global arrow-flip symmetry on the upper half. -/
theorem exists_Lambda_offset_eq_pfRoot (hEven : Even N) {n : ℕ} (hn : n ≤ N) :
    ∃ r ≤ N / 2, pfRoot (transferBlock N c n) = Lambda c N r := by
  by_cases hmid : n ≤ N / 2
  · refine ⟨N / 2 - n, Nat.sub_le _ _, ?_⟩
    unfold Lambda
    have hsub : N / 2 - (N / 2 - n) = n := by omega
    rw [hsub]
  · let r : ℕ := n - N / 2
    rcases hEven with ⟨k, hk⟩
    have hN : N = 2 * (N / 2) := by omega
    have hr : r ≤ N / 2 := by
      dsimp [r]
      rw [hN]
      omega
    refine ⟨r, hr, ?_⟩
    have hcomp : N - n = N / 2 - r := by
      dsimp [r]
      rw [hN]
      omega
    rw [pfRoot_transferBlock_compl (N := N) c hn]
    unfold Lambda
    rw [hcomp]

/-- If every sector at distance at least two has a uniform exponential gap below `LambdaMax`,
and the first sector is strictly below the center, then the center is the maximizing block. -/
theorem LambdaMax_eq_Lambda0_of_dominance (hc : 0 < c) (hEven : Even N) (hN : 0 < N)
    (heta : 0 < η)
    (hbulk : ∀ r : ℕ, 2 ≤ r → r ≤ N / 2 →
      Lambda c N r ≤ Real.exp (-η) * LambdaMax c N)
    (hfirst : Lambda c N 1 < Lambda c N 0) :
    LambdaMax c N = Lambda c N 0 := by
  obtain ⟨n, hn, hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := N)
  obtain ⟨r, hr, hroot⟩ := exists_Lambda_offset_eq_pfRoot (N := N) (c := c) hEven hn
  have hmaxroot : LambdaMax c N = Lambda c N r := hmax.symm.trans hroot
  by_cases hr0 : r = 0
  · simpa [hr0] using hmaxroot
  · by_cases hr1 : r = 1
    · have hcenter : Lambda c N 0 ≤ LambdaMax c N := by
        unfold Lambda
        exact pfRoot_transferBlock_le_LambdaMax (N := N) (c := c) (by omega)
      rw [hmaxroot, hr1] at hcenter
      linarith
    · have hrge : 2 ≤ r := by omega
      have hgap := hbulk r hrge hr
      have hexp : Real.exp (-η) < 1 :=
        (Real.exp_lt_one_iff).2 (by linarith)
      have hlt : Real.exp (-η) * LambdaMax c N < LambdaMax c N :=
        by simpa only [one_mul] using
          mul_lt_mul_of_pos_right hexp (LambdaMax_pos (c := c) (N := N) hc)
      rw [← hmaxroot] at hgap
      linarith

/-- With the center block known to maximize the full transfer matrix, the fixed-width ratio has
the paper's stated growth rate. -/
theorem tendsto_log_Z6V_ratio_eq_Lambda_ratio (hc : 0 < c) (hN : 0 < N)
    {r : ℕ} (hr : r ≤ N / 2) (hmax : LambdaMax c N = Lambda c N 0) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop
      (𝓝 (Real.log (Lambda c N r / Lambda c N 0))) := by
  have hrate := tendsto_log_Z6V_ratio (N := N) hc hN hr
  have hcenter := Lambda_pos (N := N) hc (Nat.zero_le _)
  have hrpos := Lambda_pos (N := N) hc hr
  have hlog : Real.log (Lambda c N r) - Real.log (Lambda c N 0) =
      Real.log (Lambda c N r / Lambda c N 0) := by
    rw [Real.log_div (ne_of_gt hrpos) (ne_of_gt hcenter)]
  rw [hmax, hlog] at hrate
  exact hrate

end PottsDiscontinuity.SixVertex
