module

public import PottsDiscontinuity.SixVertex.Sec33Partition

/-!
# Growth rates of six-vertex sector ratios

The full partition function grows at the largest block Perron root.  This gives the ratio rate
with that root in the denominator; the centered-block comparison follows because its Perron root
is at most the largest block root.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ} {c : ℝ}

/-- A fixed winding sector is strictly positive at every positive height. -/
theorem Z6Vr_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) {r : ℕ}
    (hr : r ≤ N / 2) : 0 < Z6Vr c N M r := by
  rw [Z6Vr_eq_trace_block hN hM c hr]
  let : Nonempty (State N (N / 2 - r)) := ⟨packed (by omega)⟩
  exact trace_pow_pos_of_nonneg_pos_diag (transferBlock_nonneg hc.le _)
    (fun x => by rw [transferBlock_apply_self]; norm_num) M

/-- The full six-vertex partition function is positive at every positive height. -/
theorem Z6V_pos (hc : 0 < c) (hN : 0 < N) (hM : 0 < M) : 0 < Z6V c N M := by
  have hsector := Z6Vn_pos (N := N) hc hN hM (n := N / 2) (by omega)
  exact lt_of_lt_of_le hsector (Z6Vn_le_Z6V (N := N) hc.le hM (by omega))

/-- For every fixed `N` and admissible `r`, the logarithmic ratio has a limit. -/
theorem tendsto_log_Z6V_ratio (hc : 0 < c) (hN : 0 < N) {r : ℕ} (hr : r ≤ N / 2) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop
      (𝓝 (Real.log (Lambda c N r) - Real.log (LambdaMax c N))) := by
  have hnum := tendsto_log_Z6Vr (N := N) hc hN hr
  have hden := tendsto_log_Z6V (N := N) hc hN
  have hdiff := hnum.sub hden
  have hEq : (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) =ᶠ[atTop]
      (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vr c N M r) -
        (1 / (M : ℝ)) * Real.log (Z6V c N M)) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hnumpos := Z6Vr_pos (N := N) hc hN hM hr
    have hdenpos := Z6V_pos (N := N) hc hN hM
    rw [Real.log_div (ne_of_gt hnumpos) (ne_of_gt hdenpos)]
    ring
  exact hdiff.congr' hEq.symm

/-- The centered-block limsup comparison follows from the exact ratio rate and
`Lambda c N 0 ≤ LambdaMax c N`. -/
theorem limsup_log_Z6V_ratio_le_center (hc : 0 < c) (hN : 0 < N) {r : ℕ}
    (hr : r ≤ N / 2) :
    Filter.limsup (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (Z6Vr c N M r / Z6V c N M)) atTop ≤
      Real.log (Lambda c N r) - Real.log (Lambda c N 0) := by
  rw [(tendsto_log_Z6V_ratio (N := N) hc hN hr).limsup_eq]
  have hcenter : Lambda c N 0 ≤ LambdaMax c N := by
    unfold Lambda
    exact pfRoot_transferBlock_le_LambdaMax (N := N) (c := c) (by omega)
  have hcenterpos := Lambda_pos (N := N) hc (Nat.zero_le _)
  have hlog := Real.log_le_log hcenterpos hcenter
  linarith

end PottsDiscontinuity.SixVertex
