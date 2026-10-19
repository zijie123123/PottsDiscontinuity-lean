module

public import PottsDiscontinuity.SixVertex.Interlace

/-!
# The entrywise infinite-anisotropy limit

Lemma 3.2 of arXiv:1611.09877v2 and its proof (the normalized limit `V^{[n]}_∞`). The
definition includes `n = 0`, where the limit is `(2)`, rather than the adjacency formula valid
for `n > 0`.
No path-counting or spectral assertion is used here.
-/

@[expose] public section

open Finset Matrix Filter Topology

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- Number of vertical arrows which change between the two row states. -/
def arrowDistance (x y : Finset (Fin N)) : ℕ :=
  (univ.filter fun i => Psi x i ≠ Psi y i).card

/-- The infinite-anisotropy block: distinct disjoint interlaced states have entry one.
The zero-particle block retains its diagonal entry two. -/
noncomputable def infinityBlock (N n : ℕ) : Matrix (State N n) (State N n) ℝ :=
  fun x y => if x = y then (if n = 0 then 2 else 0)
    else if Interlaced x.1 y.1 ∧ Disjoint x.1 y.1 then 1 else 0

theorem arrowDistance_eq (x y : Finset (Fin N)) :
    arrowDistance x y = (x \ y).card + (y \ x).card := by
  have he : (univ.filter fun i => Psi x i ≠ Psi y i) = (x \ y) ∪ (y \ x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp [Psi, hx, hy]
  rw [arrowDistance, he, card_union_of_disjoint]
  exact disjoint_left.mpr (by simp only [Finset.mem_sdiff]; tauto)

theorem arrowDistance_state (x y : State N n) :
    arrowDistance x.1 y.1 = 2 * (x.1 \ y.1).card := by
  rw [arrowDistance_eq, card_sdiff_comm (y.2.trans x.2.symm)]
  omega

theorem arrowDistance_eq_two_mul_iff (x y : State N n) :
    arrowDistance x.1 y.1 = 2 * n ↔ Disjoint x.1 y.1 := by
  rw [arrowDistance_state]
  have hc := card_sdiff_add_card_inter x.1 y.1
  rw [x.2] at hc
  rw [disjoint_iff_inter_eq_empty, ← card_eq_zero]
  omega

@[simp] theorem infinityBlock_apply_self (x : State N n) :
    infinityBlock N n x x = if n = 0 then 2 else 0 := by
  simp [infinityBlock]

theorem infinityBlock_eq_one_iff (hn : 0 < n) (x y : State N n) :
    infinityBlock N n x y = 1 ↔ Interlaced x.1 y.1 ∧ Disjoint x.1 y.1 := by
  by_cases hxy : x = y
  · subst y
    have hx : ¬ Disjoint x.1 x.1 := by
      simp only [disjoint_self, Finset.bot_eq_empty, ← card_eq_zero, x.2]
      omega
    simp only [infinityBlock_apply_self, Nat.ne_of_gt hn, ↓reduceIte, hx, and_false]
    norm_num
  · simp only [infinityBlock, hxy, ↓reduceIte]
    split_ifs <;> simp_all

theorem infinityBlock_symm (x y : State N n) :
    infinityBlock N n x y = infinityBlock N n y x := by
  simp only [infinityBlock, eq_comm, interlaced_comm x.1 y.1, disjoint_comm]

theorem infinityBlock_isHermitian : (infinityBlock N n).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext x y
  exact infinityBlock_symm y x

theorem infinityBlock_nonneg (x y : State N n) : 0 ≤ infinityBlock N n x y := by
  unfold infinityBlock
  split_ifs <;> norm_num

end PottsDiscontinuity.SixVertex
