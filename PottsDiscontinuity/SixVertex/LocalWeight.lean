module

public import PottsDiscontinuity.SixVertex.Defs

/-!
# The weight `w(ω)` as a product of local vertex weights

For an arrow configuration `ω`, `w(ω) = ∏_v localWeight(v)` where the local weight of a vertex is
`a`, `b`, `c` according to its type and `0` if the vertex violates the ice rule.
-/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- Local weight of a vertex with left/right/lower/upper arrows `l, r, d, u`:
`a`, `b`, `c` for the types `1,2`, `3,4`, `5,6` and `0` if the ice rule fails. -/
def localWeight (a b c : ℝ) (l r d u : Bool) : ℝ :=
  match vertexType? l r d u with
  | none => 0
  | some t => vertexWeight a b c t

theorem inDegree_eq_two_iff_isSome (l r d u : Bool) :
    inDegree l r d u = 2 ↔ vertexType? l r d u ≠ none := by
  revert l r d u
  decide

/-- Number of vertices of type `t` as a sum of indicators. -/
private theorem numType_eq_sum (ω : ArrowConfig N M) (t : VertexType) :
    ω.numType t = ∑ v : Fin N × Fin M,
      (if vertexType? (ω.left v) (ω.right v) (ω.below v) (ω.above v) = some t then 1 else 0) := by
  unfold ArrowConfig.numType
  rw [Finset.card_filter]

private theorem localWeight_eq_pow (a b c : ℝ) (l r d u : Bool)
    (h : vertexType? l r d u ≠ none) :
    localWeight a b c l r d u =
      a ^ ((if vertexType? l r d u = some .t1 then 1 else 0) +
            (if vertexType? l r d u = some .t2 then 1 else 0)) *
      b ^ ((if vertexType? l r d u = some .t3 then 1 else 0) +
            (if vertexType? l r d u = some .t4 then 1 else 0)) *
      c ^ ((if vertexType? l r d u = some .t5 then 1 else 0) +
            (if vertexType? l r d u = some .t6 then 1 else 0)) := by
  revert h
  cases l <;> cases r <;> cases d <;> cases u <;>
    simp [localWeight, vertexType?, vertexWeight]

/-- `w(ω)` is the product over the vertices of the local weights. -/
theorem w6V_eq_prod (a b c : ℝ) (ω : ArrowConfig N M) :
    w6V a b c ω =
      ∏ v : Fin N × Fin M, localWeight a b c (ω.left v) (ω.right v) (ω.below v) (ω.above v) := by
  unfold w6V
  split_ifs with hice
  · have hne : ∀ v : Fin N × Fin M,
        vertexType? (ω.left v) (ω.right v) (ω.below v) (ω.above v) ≠ none :=
      fun v => (inDegree_eq_two_iff_isSome _ _ _ _).1 (hice v)
    rw [Finset.prod_congr rfl (fun v _ => localWeight_eq_pow a b c _ _ _ _ (hne v))]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← numType_eq_sum, ← numType_eq_sum,
      ← numType_eq_sum, ← numType_eq_sum, ← numType_eq_sum, ← numType_eq_sum]
  · unfold ArrowConfig.IceRule at hice
    push Not at hice
    obtain ⟨v, hv⟩ := hice
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    have : vertexType? (ω.left v) (ω.right v) (ω.below v) (ω.above v) = none := by
      by_contra hne
      exact hv ((inDegree_eq_two_iff_isSome _ _ _ _).2 hne)
    simp [localWeight, this]

/-- Specialisation to `a = b = 1`: the local weight is `0` off the ice rule, and `c` or `1` according
to whether the two vertical arrows differ (types 5, 6) or not. -/
theorem localWeight_one_one (c : ℝ) (l r d u : Bool) :
    localWeight 1 1 c l r d u = if inDegree l r d u = 2 then (if d = u then 1 else c) else 0 := by
  cases l <;> cases r <;> cases d <;> cases u <;>
    simp [localWeight, vertexType?, vertexWeight, inDegree]

theorem w6V1_eq_prod (c : ℝ) (ω : ArrowConfig N M) :
    w6V1 c ω =
      ∏ v : Fin N × Fin M, localWeight 1 1 c (ω.left v) (ω.right v) (ω.below v) (ω.above v) :=
  w6V_eq_prod 1 1 c ω

end PottsDiscontinuity.SixVertex
