module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobenius
public import PottsDiscontinuity.SixVertex.Irreducible
public import PottsDiscontinuity.SixVertex.TraceFormula

/-!
# Perron–Frobenius eigenvalue of the blocks `V^{[n]}` and the rate of `Z^{(r)}_{6V}`

For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is symmetric, primitive and has a simple positive
Perron–Frobenius eigenvalue with a strictly positive eigenvector.  With
`Λ_r(N) = pfRoot (V^{[N/2 - r]})` we obtain
`lim_{M → ∞} (1/M) log Z^{(r)}_{6V}(N, M) = log Λ_r(N)` for `N ≥ 1`, `0 ≤ r ≤ N/2`.
-/

@[expose] public section

open Finset Matrix Filter Topology PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

/-- `Λ_r(N)`: the Perron–Frobenius eigenvalue (largest eigenvalue) of the block `V^{[N/2 - r]}`. -/
noncomputable def Lambda (c : ℝ) (N r : ℕ) : ℝ := pfRoot (transferBlock N c (N / 2 - r))

/-- Every block `V^{[n]}`, `0 ≤ n ≤ N`, has the Perron–Frobenius property: its largest eigenvalue
is positive and simple, has a strictly positive eigenvector, and every other eigenvalue has
strictly smaller absolute value. -/
theorem transferBlock_perronFrobenius (hc : 0 < c) {n : ℕ} (hn : n ≤ N) :
    0 < pfRoot (transferBlock N c n) ∧
    IsGreatest (spectrum ℝ (transferBlock N c n)) (pfRoot (transferBlock N c n)) ∧
    (∃ v : State N n → ℝ, (∀ x, 0 < v x) ∧
      transferBlock N c n *ᵥ v = pfRoot (transferBlock N c n) • v) ∧
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (transferBlock N c n))
      (pfRoot (transferBlock N c n))) = 1 ∧
    (transferBlock N c n).charpoly.rootMultiplicity (pfRoot (transferBlock N c n)) = 1 ∧
    ∀ μ ∈ spectrum ℝ (transferBlock N c n), μ ≠ pfRoot (transferBlock N c n) →
      |μ| < pfRoot (transferBlock N c n) := by
  have : Nonempty (State N n) := ⟨packed hn⟩
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, -⟩ :=
    perronFrobenius_primitive (transferBlock_isHermitian (c := c) n) (transferBlock_isPrimitive hc hn)
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `Λ_r(N) > 0` for `0 ≤ r ≤ N/2` and `c > 0`. -/
theorem Lambda_pos (hc : 0 < c) {r : ℕ} (hr : r ≤ N / 2) : 0 < Lambda c N r :=
  (transferBlock_perronFrobenius hc (n := N / 2 - r) (by omega)).1

/-- **Rate of `Z^{(r)}_{6V}`** (`sec:RCM#PF-block-rate`): for `c > 0`, `N ≥ 1` and `0 ≤ r ≤ N/2`,
`lim_{M→∞} (1/M) log Z^{(r)}_{6V}(N, M) = log Λ_r(N)`. -/
theorem tendsto_log_Z6Vr (hc : 0 < c) (hN : 0 < N) {r : ℕ} (hr : r ≤ N / 2) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vr c N M r)) atTop
      (𝓝 (Real.log (Lambda c N r))) := by
  have : Nonempty (State N (N / 2 - r)) := ⟨packed (by omega)⟩
  have key := tendsto_log_trace_pow (transferBlock_isHermitian (c := c) (N := N) (N / 2 - r))
    (transferBlock_isPrimitive hc (by omega))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  rw [Z6Vr_eq_trace_block hN hM c hr]

/-- Same statement for the blocks indexed by the number `n` of up arrows per row. -/
theorem tendsto_log_Z6Vn (hc : 0 < c) (hN : 0 < N) {n : ℕ} (hn : n ≤ N) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (Z6Vn c N M n)) atTop
      (𝓝 (Real.log (pfRoot (transferBlock N c n)))) := by
  have : Nonempty (State N n) := ⟨packed hn⟩
  have key := tendsto_log_trace_pow (transferBlock_isHermitian (c := c) (N := N) n)
    (transferBlock_isPrimitive hc hn)
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  rw [Z6Vn_eq_trace_block hN hM c n]

/-! ### The one-dimensional blocks `n = 0` and `n = N` -/

end PottsDiscontinuity.SixVertex
