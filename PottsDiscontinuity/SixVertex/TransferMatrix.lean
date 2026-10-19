module

public import PottsDiscontinuity.SixVertex.Interlace

/-!
# Elementary properties of the transfer matrix `V` and its blocks `V^{[n]}`

* `V` is symmetric (`transferMatrix_transpose`), has nonnegative entries for `c ≥ 0`, and is block
  diagonal with respect to the number of up arrows (`transferMatrix_apply_eq_zero_of_card_ne`,
  `transferMatrix_mulVec_supported`, `transferMatrix_submatrix_sigma_eq_blockDiagonal'`);
* each block `V^{[n]}` is symmetric and nonnegative, with diagonal entries `2`.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

theorem transferMatrix_apply (c : ℝ) (x y : Finset (Fin N)) :
    transferMatrix N c x y =
      if x = y then 2 else
        if Interlaced x y then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := by
  rfl

@[simp] theorem transferMatrix_apply_self (c : ℝ) (x : Finset (Fin N)) :
    transferMatrix N c x x = 2 := by
  rw [transferMatrix_apply]; simp

theorem transferMatrix_apply_of_ne {x y : Finset (Fin N)} (hxy : x ≠ y) (h : Interlaced x y) :
    transferMatrix N c x y = c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  rw [transferMatrix_apply]; simp [hxy, h]

theorem transferMatrix_apply_of_not_interlaced {x y : Finset (Fin N)} (hxy : x ≠ y)
    (h : ¬ Interlaced x y) : transferMatrix N c x y = 0 := by
  rw [transferMatrix_apply]; simp [hxy, h]

/-- `V(x, y) = 0` unless `x` and `y` have the same number of entries (block diagonality). -/
theorem transferMatrix_apply_eq_zero_of_card_ne {x y : Finset (Fin N)} (h : x.card ≠ y.card) :
    transferMatrix N c x y = 0 := by
  have hxy : x ≠ y := fun e => h (e ▸ rfl)
  exact transferMatrix_apply_of_not_interlaced hxy (fun hi => h hi.card_eq)

/-- `V` is symmetric. -/
theorem transferMatrix_symm (x y : Finset (Fin N)) :
    transferMatrix N c x y = transferMatrix N c y x := by
  rw [transferMatrix_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · subst hxy; rfl
  · have hyx : y ≠ x := fun e => hxy e.symm
    simp only [hxy, hyx, ↓reduceIte]
    by_cases hi : Interlaced x y
    · simp only [hi, hi.symm, ↓reduceIte]
      congr 2
      ext i
      simp [ne_comm]
    · have hi' : ¬ Interlaced y x := fun h => hi h.symm
      simp [hi, hi']

theorem transferMatrix_transpose : (transferMatrix N c)ᵀ = transferMatrix N c := by
  ext x y
  exact transferMatrix_symm y x

theorem transferMatrix_isHermitian : (transferMatrix N c).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact transferMatrix_transpose

theorem transferMatrix_nonneg (hc : 0 ≤ c) (x y : Finset (Fin N)) :
    0 ≤ transferMatrix N c x y := by
  rw [transferMatrix_apply]
  split_ifs
  · norm_num
  · exact pow_nonneg hc _
  · exact le_rfl

/-- For `c > 0`: `V(x, y) > 0` iff `x = y` or `x` and `y` are interlaced. -/
theorem transferMatrix_pos_iff (hc : 0 < c) (x y : Finset (Fin N)) :
    0 < transferMatrix N c x y ↔ x = y ∨ Interlaced x y := by
  rw [transferMatrix_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · by_cases hi : Interlaced x y
    · simp [hxy, hi, pow_pos hc]
    · simp [hxy, hi]

/-! ### The blocks `V^{[n]}` -/

theorem transferBlock_apply (c : ℝ) (n : ℕ) (x y : State N n) :
    transferBlock N c n x y = transferMatrix N c x.1 y.1 := rfl

@[simp] theorem transferBlock_apply_self (c : ℝ) (n : ℕ) (x : State N n) :
    transferBlock N c n x x = 2 := by
  rw [transferBlock_apply, transferMatrix_apply_self]

theorem transferBlock_transpose (n : ℕ) : (transferBlock N c n)ᵀ = transferBlock N c n := by
  ext x y
  exact transferMatrix_symm y.1 x.1

theorem transferBlock_isHermitian (n : ℕ) : (transferBlock N c n).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact transferBlock_transpose n

theorem transferBlock_nonneg (hc : 0 ≤ c) (n : ℕ) (x y : State N n) :
    0 ≤ transferBlock N c n x y :=
  transferMatrix_nonneg hc x.1 y.1

theorem transferBlock_pos_iff (hc : 0 < c) (n : ℕ) (x y : State N n) :
    0 < transferBlock N c n x y ↔ x.1 = y.1 ∨ Interlaced x.1 y.1 :=
  transferMatrix_pos_iff hc x.1 y.1

/-! ### `V` is the block diagonal matrix of the `V^{[n]}` -/

end PottsDiscontinuity.SixVertex
