module

public import PottsDiscontinuity.SixVertex.LocalWeight

/-!
# The two turning smoothings at a medial vertex

Source: §3.3.1, Fig. 8 and the local table in the proof of Lemma 3.11.
`false` pairs left/above and right/below; `true` pairs left/below and right/above.
Compatibility says that each paired strand is oriented from an incoming to an outgoing edge.
Turns are measured in quarter turns, positive counterclockwise.

These are local data, not a definition of the paper's global loop weight. In particular,
no assertion about the turning number or homotopy class of a closed loop is made here.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

/-- Orientation compatibility of a turning smoothing with the four incident arrows. -/
def Compatible (s l r d u : Bool) : Prop :=
  if s then l ≠ d ∧ r ≠ u else l = u ∧ r = d

instance (s l r d u : Bool) : Decidable (Compatible s l r d u) := by
  unfold Compatible
  infer_instance

/-- Total signed quarter turns of the two strands. For compatible arrows these are
the actual turns, with the incoming directions determined by `l` and `r`. -/
def quarterTurn (s l r : Bool) : ℤ :=
  if s then (if l then -1 else 1) + (if r then 1 else -1)
  else (if l then 1 else -1) + (if r then -1 else 1)

/-- A compatible smoothing exists exactly for the six ice-rule patterns. -/
theorem exists_compatible_iff (l r d u : Bool) :
    (∃ s, Compatible s l r d u) ↔ inDegree l r d u = 2 := by
  revert l r d u
  decide

/-- Every compatible local smoothing obeys the ice rule. -/
theorem Compatible.iceRule {s l r d u : Bool} (h : Compatible s l r d u) :
    inDegree l r d u = 2 :=
  (exists_compatible_iff l r d u).1 ⟨s, h⟩

/-- The local exponential turn factor, with zero weight for incompatible smoothings. -/
noncomputable def turnWeight (lam : ℝ) (s l r d u : Bool) : ℝ :=
  if Compatible s l r d u then Real.exp (lam / 4 * (quarterTurn s l r : ℝ)) else 0

theorem turnWeight_nonneg (lam : ℝ) (s l r d u : Bool) :
    0 ≤ turnWeight lam s l r d u := by
  unfold turnWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The sum of the two local turn factors is exactly the existing six-vertex local weight.
This is the local algebra behind Lemma 3.12, without any global turning-number input. -/
theorem sum_turnWeight (lam : ℝ) (l r d u : Bool) :
    ∑ s : Bool, turnWeight lam s l r d u =
      localWeight 1 1 (Real.exp (lam / 2) + Real.exp (-lam / 2)) l r d u := by
  have hp : lam / 4 * (2 : ℝ) = lam / 2 := by ring
  have hn : lam / 4 * (-2 : ℝ) = -lam / 2 := by ring
  cases l <;> cases r <;> cases d <;> cases u <;>
    simp [turnWeight, Compatible, quarterTurn,
      localWeight, vertexType?, vertexWeight, hp, hn, add_comm]

end PottsDiscontinuity.Torus
