module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusIrreducible

/-!
# Positive eigenvectors and finite matrix covers

The row-fiber identity is the precise weighted version of the covering condition.
The statements are generic linear algebra. They do not assert that the two
specific defect and walker matrices already satisfy that identity.
-/

@[expose] public section

open Finset Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

section PositiveEigenvector

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- A strictly positive eigenvector identifies the top eigenvalue of a symmetric
nonnegative matrix, even when the matrix is reducible. -/
theorem pfRoot_eq_of_strictly_positive_eigenvector {A : Matrix S S ℝ}
    (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j) {ρ : ℝ} {v : S → ℝ}
    (hv : ∀ i, 0 < v i) (he : A *ᵥ v = ρ • v) : pfRoot A = ρ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  have hb : A *ᵥ eigvec hA i = pfRoot A • eigvec hA i := by rw [mulVec_eigvec, hi]
  let w : S → ℝ := fun j => |eigvec hA i j|
  have hw : A *ᵥ w = pfRoot A • w :=
    abs_mulVec_eq hA hpos hb (by rw [abs_of_nonneg (pfRoot_nonneg hA hpos)])
  have hne : eigvec hA i ≠ 0 := by
    intro hz
    have hn := eigvec_dot hA i i
    rw [hz] at hn
    simp at hn
  have hcoord : ∃ j, eigvec hA i j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (funext hh)
  obtain ⟨j, hj⟩ := hcoord
  have hdot : 0 < v ⬝ᵥ w := by
    apply sum_pos' (fun j _ => mul_nonneg (hv j).le (abs_nonneg _))
    exact ⟨j, mem_univ _, mul_pos (hv j) (abs_pos.mpr hj)⟩
  have hs := Matrix.dotProduct_transpose_mulVec A v w
  rw [Matrix.isHermitian_iff_isSymm.mp hA, hw, he, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm w v] at hs
  exact mul_right_cancel₀ hdot.ne' hs

end PositiveEigenvector

section Covers

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- The sum of edge weights into every fiber equals the corresponding quotient edge weight.
This formulation includes multiple edges and non-free quotient actions. -/
def IsRowCover (A : Matrix S S ℝ) (B : Matrix T T ℝ) (f : S → T) : Prop :=
  ∀ x t, (∑ y ∈ univ.filter (fun y => f y = t), A x y) = B (f x) t

omit [DecidableEq S] in
/-- Pullback along a row cover intertwines the two adjacency operators. -/
theorem IsRowCover.mulVec {A : Matrix S S ℝ} {B : Matrix T T ℝ} {f : S → T}
    (hc : IsRowCover A B f) (v : T → ℝ) : A *ᵥ (v ∘ f) = (B *ᵥ v) ∘ f := by
  funext x
  change (∑ y, A x y * v (f y)) = ∑ t, B (f x) t * v t
  calc
    (∑ y, A x y * v (f y)) = ∑ y, ∑ t, if f y = t then A x y * v t else 0 := by
      apply sum_congr rfl
      intro y _
      simp
    _ = ∑ t, ∑ y, if f y = t then A x y * v t else 0 := sum_comm
    _ = ∑ t, (∑ y ∈ univ.filter (fun y => f y = t), A x y) * v t := by
      apply sum_congr rfl
      intro t _
      rw [sum_mul, sum_filter]
    _ = ∑ t, B (f x) t * v t := by
      apply sum_congr rfl
      intro t _
      rw [hc x t]

end Covers

end PottsDiscontinuity.SixVertex
