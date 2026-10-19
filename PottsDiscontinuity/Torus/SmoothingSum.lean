module

public import PottsDiscontinuity.Torus.LocalSmoothing

/-!
# Independent local smoothings and the six-vertex weight

This module proves the finite product/sum step of Lemma 3.12 for the actual two
turning pairings, on the same indexed torus as `SixVertex.ArrowConfig`.
It does not identify the product of local turn factors with the paper's weight
defined by counting clockwise/counterclockwise contractible loops. That identification
requires the global turning-number theorem and is not assumed here.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

/-- A choice of one of the two turning pairings at every medial vertex. -/
abbrev Smoothing (N M : ℕ) := Fin N × Fin M → Bool

variable {N M : ℕ}

/-- Each strand of the smoothing follows the prescribed arrows. -/
def CompatibleConfig (ω : ArrowConfig N M) (s : Smoothing N M) : Prop :=
  ∀ v, Compatible (s v) (ω.left v) (ω.right v) (ω.below v) (ω.above v)

instance (ω : ArrowConfig N M) (s : Smoothing N M) : Decidable (CompatibleConfig ω s) := by
  unfold CompatibleConfig
  infer_instance

/-- Total signed quarter turns, summed over both strands at every medial vertex. -/
def totalQuarterTurn (ω : ArrowConfig N M) (s : Smoothing N M) : ℤ :=
  ∑ v, quarterTurn (s v) (ω.left v) (ω.right v)

/-- Product of the local exponential turn factors. Incompatible arrow/smoothing pairs have
weight zero. This is not the paper's loop-count definition of oriented loop weight. -/
noncomputable def smoothingWeight (lam : ℝ) (ω : ArrowConfig N M)
    (s : Smoothing N M) : ℝ :=
  ∏ v, turnWeight lam (s v) (ω.left v) (ω.right v) (ω.below v) (ω.above v)

theorem CompatibleConfig.iceRule {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) : ω.IceRule :=
  fun v => (h v).iceRule

/-- The compatible global smoothing data exist precisely for ice-rule configurations.
The explicit choice is the left/above pairing whenever it is compatible. -/
theorem exists_compatibleConfig_iff (ω : ArrowConfig N M) :
    (∃ s, CompatibleConfig ω s) ↔ ω.IceRule := by
  constructor
  · rintro ⟨s, hs⟩
    exact hs.iceRule
  · intro h
    refine ⟨fun v => !decide (Compatible false (ω.left v) (ω.right v)
      (ω.below v) (ω.above v)), fun v => ?_⟩
    obtain ⟨b, hb⟩ := (exists_compatible_iff _ _ _ _).2 (h v)
    by_cases hf : Compatible false (ω.left v) (ω.right v) (ω.below v) (ω.above v)
    · simp only [hf, decide_true, Bool.not_true]
    · cases b
      · exact (hf hb).elim
      · simp only [hf, decide_false, Bool.not_false]
        exact hb

theorem smoothingWeight_nonneg (lam : ℝ) (ω : ArrowConfig N M) (s : Smoothing N M) :
    0 ≤ smoothingWeight lam ω s :=
  Finset.prod_nonneg fun _ _ => turnWeight_nonneg lam _ _ _ _ _

/-- The total local turn factor is the exponential of the total signed turning angle
in units of quarter turns. This is bookkeeping, not a turning-number classification. -/
theorem smoothingWeight_eq_exp {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (lam : ℝ) :
    smoothingWeight lam ω s = Real.exp (lam / 4 * (totalQuarterTurn ω s : ℝ)) := by
  unfold smoothingWeight totalQuarterTurn
  unfold CompatibleConfig at h
  simp only [turnWeight, h, ↓reduceIte]
  rw [← Real.exp_sum]
  congr 1
  simp only [Int.cast_sum, Finset.mul_sum]

/-- The product of the local sums equals the sum over all independent smoothings.
The result uses the existing six-vertex weight, including zero off the ice rule. -/
theorem sum_smoothingWeight (lam : ℝ) (ω : ArrowConfig N M) :
    ∑ s : Smoothing N M, smoothingWeight lam ω s =
      w6V1 (Real.exp (lam / 2) + Real.exp (-lam / 2)) ω := by
  unfold smoothingWeight
  have hp := Finset.sum_prod_piFinset (univ : Finset Bool)
    (fun v : Fin N × Fin M => fun b =>
      turnWeight lam b (ω.left v) (ω.right v) (ω.below v) (ω.above v))
  rw [Fintype.piFinset_univ] at hp
  rw [hp, w6V1_eq_prod]
  exact Finset.prod_congr rfl fun v _ => sum_turnWeight lam _ _ _ _

/-- Summing the local smoothing expansion gives exactly `SixVertex.Z6V`.
No FK partition function or global loop statistic occurs in this intermediate identity. -/
theorem sum_smoothingWeight_eq_Z6V (lam : ℝ) :
    (∑ ω : ArrowConfig N M, ∑ s : Smoothing N M, smoothingWeight lam ω s) =
      Z6V (Real.exp (lam / 2) + Real.exp (-lam / 2)) N M := by
  simp only [sum_smoothingWeight, Z6V]

/-- The same expansion preserves the existing row sector, with no truncated subtraction. -/
theorem sum_smoothingWeight_eq_Z6Vr (lam : ℝ) (r : ℕ) :
    (∑ ω : ArrowConfig N M with ω.absUp + r = N / 2,
      ∑ s : Smoothing N M, smoothingWeight lam ω s) =
      Z6Vr (Real.exp (lam / 2) + Real.exp (-lam / 2)) N M r := by
  simp only [sum_smoothingWeight, Z6Vr]

end PottsDiscontinuity.Torus
