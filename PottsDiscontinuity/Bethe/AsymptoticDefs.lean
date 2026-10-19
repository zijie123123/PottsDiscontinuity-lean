module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.KMap

/-!
# Definitions for the asymptotics of discrete Bethe roots

This module records the objects in (2.3), (2.5), and (2.13) of
arXiv:1611.09877v2.  The step density is extended by zero off its cyclic root
partition.  The offset function uses the first and last offsets on the two
boundary half-cells; this makes it a total function on `[-π, π]` while agreeing
with the source's interior step values.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The weighted supremum norm (2.3), written in the `α` coordinate where
`k'(α) = Xi (lamOf Δ) α`. -/
noncomputable def densityNorm (Δ : ℝ) (_hΔ : Δ < -1) (f : ℝ → ℝ)
    (_hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|)) : ℝ :=
  sSup (Set.range fun α : Icc (-Real.pi) Real.pi =>
    |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|)

/-- The empirical measure `μ_N = (1/N) Σ δ_{p_i}`. -/
noncomputable def empiricalMeasure (N : ℕ) (_hN : 0 < N) (n : ℕ)
    (p : Fin n → ℝ) : Measure ℝ :=
  (↑N : ENNReal)⁻¹ • ∑ j : Fin n, Measure.dirac (p j)

/-- Cyclic extension of an ordered root vector, with the two extra endpoints
`p₀ = pₙ - 2π` and `pₙ₊₁ = p₁ + 2π`. -/
noncomputable def rootPartitionPoint (n : ℕ) (p : Fin n → ℝ) (hn : 0 < n)
    (j : Fin (n + 2)) : ℝ :=
  if h0 : j.val = 0 then
    p ⟨n - 1, by omega⟩ - 2 * Real.pi
  else if hn₁ : j.val = n + 1 then
    p ⟨0, by omega⟩ + 2 * Real.pi
  else
    p ⟨j.val - 1, by omega⟩

/-- Multiplicity of the `j`th root gap in (2.5): interior gaps have weight 1,
and the two cyclic boundary gaps have weight `N + 1 - 2n` (equal to `2r+1`
when `n=N/2-r`). -/
def rootGapMultiplicity (N n : ℕ) (_hsize : 2 * n ≤ N) (j : Fin (n + 1)) : ℝ :=
  if j.val = 0 ∨ j.val = n then ((N + 1 - 2 * n : ℕ) : ℝ) else 1

/-- The step density `ρ_p` of (2.5), on the cyclic root partition.  The
configuration and size hypotheses ensure positive gaps and a nonnegative
boundary multiplicity. -/
noncomputable def rootStepDensity (N n : ℕ) (p : Fin n → ℝ)
    (_hp : p ∈ S_n n) (hn : 0 < n) (_hsize : 2 * n ≤ N) (x : ℝ) : ℝ :=
  ∑ j : Fin (n + 1),
    if rootPartitionPoint n p hn j.castSucc ≤ x ∧ x < rootPartitionPoint n p hn j.succ then
      rootGapMultiplicity N n _hsize j /
        ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
    else 0

/-- The offset displacement (2.13).  For odd `r`, the two `p` indices are
`j+(r-1)/2` and `j+(r+1)/2`, as required by the corrected source indices. -/
noncomputable def offsetDisplacement (N r : ℕ) (hN : 4 ∣ N) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (ptilde : Fin (N / 2 - r) → ℝ)
    (j : Fin (N / 2 - r)) : ℝ :=
  if heven : r % 2 = 0 then
    (N : ℝ) * (ptilde j - p ⟨j.val + r / 2, by omega⟩)
  else
    (N : ℝ) * (ptilde j -
      (p ⟨j.val + (r - 1) / 2, by omega⟩ +
        p ⟨j.val + (r + 1) / 2, by omega⟩) / 2)

/-- The offset function associated with (2.13).  On interior root cells it
equals the displacement at the left endpoint.  The two boundary half-cells
use the nearest displacement, giving the continuous-interval representative
needed for a uniform statement on the closed interval. -/
noncomputable def offsetFunction (N r : ℕ) (hN : 4 ∣ N) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (ptilde : Fin (N / 2 - r) → ℝ)
    (hn : 0 < N / 2 - r) (x : ℝ) : ℝ := by
  let n := N / 2 - r
  let eps := offsetDisplacement N r hN hr p ptilde
  let first : Fin n := ⟨0, by dsimp [n]; exact hn⟩
  let last : Fin n := ⟨n - 1, by dsimp [n]; omega⟩
  exact if x < ptilde first then eps first else if ptilde last ≤ x then eps last else
    ∑ j : Fin n, if hnext : j.val + 1 < n then
      if ptilde j ≤ x ∧ x < ptilde ⟨j.val + 1, hnext⟩ then eps j else 0 else 0

/-- Size side condition `0 < N i / 2` for the root step densities of Theorem 2.9. Statements
use this named lemma instead of an inline tactic proof, so that no module-private auxiliary
proof appears in an exported statement. -/
theorem half_pos_of_half_sub_pos {ι : Type*} (N : ι → ℕ) (r : ℕ) (hn : ∀ i, 0 < N i / 2 - r)
    (i : ι) :
    0 < N i / 2 := by
  have := hn i
  omega

/-- Size side condition `2 * (N i / 2) ≤ N i` for the root step densities of Theorem 2.9. -/
theorem two_mul_half_le {ι : Type*} (N : ι → ℕ) (i : ι) : 2 * (N i / 2) ≤ N i := by
  omega

/-- Size side condition `2 * (N i / 2 - r) ≤ N i` for the root step densities of Theorem 2.9. -/
theorem two_mul_half_sub_le {ι : Type*} (N : ι → ℕ) (r : ℕ) (i : ι) :
    2 * (N i / 2 - r) ≤ N i := by
  omega

end PottsDiscontinuity.Bethe
