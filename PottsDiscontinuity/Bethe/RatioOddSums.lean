module

public import PottsDiscontinuity.Bethe.AsymptoticSumSplit
public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Finite reflection and telescoping identities for the odd quotient -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_ell_neg (c x : ℝ) : ratioEll c (-x) = ratioEll c x := by
  unfold ratioEll
  rw [ratio_M_neg, Complex.norm_conj]

theorem ratio_ell_zero (c : ℝ) : ratioEll c 0 = 0 := by
  simp [ratioEll, BetheAnsatz.M]

theorem ratio_sum_even_reflection {m h : ℕ} (hcount : 2 * h = m)
    (f : Fin m → ℝ) (hsym : ∀ j, f (Fin.rev j) = f j) :
    (∑ j, f j) = 2 * ∑ j : Fin h, f ⟨h + j.val, by omega⟩ := by
  have hleft : (∑ j : Fin h, f ⟨j.val, by omega⟩) =
      ∑ j : Fin h, f ⟨h + j.val, by omega⟩ := by
    calc
      _ = ∑ j : Fin h, f ⟨h + (Fin.rev j).val, by omega⟩ := by
        apply sum_congr rfl
        intro j hj
        rw [← hsym ⟨h + (Fin.rev j).val, by omega⟩]
        congr 1
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin h)) (fun j => f ⟨h + j.val, by omega⟩)
  have hmid : (∑ j : Fin h, f ⟨j.val + h, by omega⟩) =
      ∑ j : Fin h, f ⟨h + j.val, by omega⟩ := by
    apply sum_congr rfl
    intro j hj
    congr 1
    exact Fin.ext (Nat.add_comm _ _)
  have hs := sum_fin_split_block (m := m) (a := h) (n := h) (b := 0) (by omega) f
  simp only [Fin.sum_univ_zero, add_zero] at hs
  rw [hmid, hleft] at hs
  linarith only [hs]

theorem ratio_sum_odd_reflection {m t : ℕ} (hcount : 2 * t + 1 = m)
    (f : Fin m → ℝ) (hsym : ∀ j, f (Fin.rev j) = f j)
    (hzero : f ⟨t, by omega⟩ = 0) :
    (∑ j, f j) = 2 * ∑ j : Fin t, f ⟨t + 1 + j.val, by omega⟩ := by
  have hleft : (∑ j : Fin t, f ⟨j.val, by omega⟩) =
      ∑ j : Fin t, f ⟨t + 1 + j.val, by omega⟩ := by
    calc
      _ = ∑ j : Fin t, f ⟨t + 1 + (Fin.rev j).val, by omega⟩ := by
        apply sum_congr rfl
        intro j hj
        rw [← hsym ⟨t + 1 + (Fin.rev j).val, by omega⟩]
        congr 1
        apply Fin.ext
        simp only [Fin.val_rev]
        omega
      _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin t))
        (fun j => f ⟨t + 1 + j.val, by omega⟩)
  have hs := sum_fin_split_block (m := m) (a := t) (n := 1) (b := t) (by omega) f
  simp only [Fin.sum_univ_one, Fin.val_zero, hzero, zero_add] at hs
  rw [hleft] at hs
  linarith only [hs]

/-- The edge logarithms telescope, leaving the first root, the last retained
root, and the s discarded positive boundary roots. -/
theorem ratio_midpoint_sum_telescoping {m t s : ℕ} (hcount : t + 1 + s = m)
    (f : Fin m → ℝ) (g : Fin t → ℝ) :
    2 * (∑ j, g j) - 2 * (∑ j, f j) =
      (∑ j : Fin t, (2 * g j - f ⟨j.val, by omega⟩ - f ⟨j.val + 1, by omega⟩)) -
        f ⟨0, by omega⟩ - f ⟨t, by omega⟩ -
          2 * ∑ j : Fin s, f ⟨j.val + (t + 1), by omega⟩ := by
  let F : Fin (t + 1) → ℝ := fun j => f ⟨j.val, by omega⟩
  have h₀ := Fin.sum_univ_succ F
  have h₁ := Fin.sum_univ_castSucc F
  have hs := sum_fin_split_block (m := m) (a := t + 1) (n := s) (b := 0) (by omega) f
  simp only [Fin.sum_univ_zero, add_zero] at hs
  change (∑ j, f j) = (∑ j : Fin s, f ⟨j.val + (t + 1), by omega⟩) + ∑ j : Fin (t + 1), F j at hs
  change (∑ j : Fin (t + 1), F j) = f ⟨0, by omega⟩ + ∑ j : Fin t, f ⟨j.val + 1, by omega⟩ at h₀
  change (∑ j : Fin (t + 1), F j) = (∑ j : Fin t, f ⟨j.val, by omega⟩) + f ⟨t, by omega⟩ at h₁
  have he : (∑ j : Fin t, (2 * g j - f ⟨j.val, by omega⟩ - f ⟨j.val + 1, by omega⟩)) =
      2 * (∑ j, g j) - (∑ j : Fin t, f ⟨j.val, by omega⟩) -
        ∑ j : Fin t, f ⟨j.val + 1, by omega⟩ := by
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  rw [he]
  linarith only [h₀, h₁, hs]

end PottsDiscontinuity.Bethe
