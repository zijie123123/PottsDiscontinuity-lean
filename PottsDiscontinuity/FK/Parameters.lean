/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

/-! Independent finite random-cluster parameters. The cluster weight is at least
one, with no upper bound, and the edge probability lies strictly between zero
and one. Endpoint edge probabilities are handled separately. -/

@[expose] public section

namespace PottsDiscontinuity.FK

/-- Independent cluster weight and interior edge probability. -/
structure Parameters where
  val : ℝ
  property : 1 ≤ val
  edgeProbability : Set.Ioo (0 : ℝ) 1

/-- The edge probability stored independently of the cluster weight. -/
def edgeParameter (q : Parameters) : ℝ := q.edgeProbability.val

lemma clusterWeight_pos (q : Parameters) : 0 < q.val :=
  lt_of_lt_of_le zero_lt_one q.property

lemma clusterWeight_nonneg (q : Parameters) : 0 ≤ q.val :=
  (clusterWeight_pos q).le

lemma edgeParameter_pos (q : Parameters) : 0 < edgeParameter q :=
  q.edgeProbability.property.1

lemma edgeParameter_lt_one (q : Parameters) : edgeParameter q < 1 :=
  q.edgeProbability.property.2

lemma one_sub_edgeParameter_pos (q : Parameters) : 0 < 1 - edgeParameter q :=
  sub_pos.mpr (edgeParameter_lt_one q)

end PottsDiscontinuity.FK
