module

public import PottsDiscontinuity.Bethe.RatioMidpointLimit
public import PottsDiscontinuity.Bethe.RatioOddSums

/-! # Exact logarithmic bookkeeping for the odd aligned-root quotient -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_odd_log_correction (c : ℝ) (s N : ℕ) (h4 : 4 ∣ N)
    (hr : 2 * s + 1 ≤ N / 2) (hn : 0 < N / 2 - (2 * s + 1))
    (p : Fin (N / 2) → ℝ) (hp : p ∈ S_n (N / 2)) :
    (∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) - (∑ j, ratioEll c (p j)) =
      (∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j) -
        ratioEll c (ratioPositiveRoot N h4 p ⟨0, by obtain ⟨z, hz⟩ := h4; omega⟩) -
        ratioEll c (p ⟨s, by omega⟩) -
        2 * ∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩) := by
  let m := N / 4
  let t := N / 4 - s - 1
  have hNcount : 2 * m = N / 2 := by dsimp [m]; obtain ⟨z, hz⟩ := h4; omega
  have hmt : t + 1 + s = m := by dsimp [m, t]; obtain ⟨z, hz⟩ := h4; omega
  have hqcount : 2 * t + 1 = N / 2 - (2 * s + 1) := by omega
  have hm : 0 < m := by omega
  have href (j : Fin (N / 2)) : ratioEll c (p (Fin.rev j)) = ratioEll c (p j) := by
    rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_ell_neg]
  let f : Fin m → ℝ := fun j => ratioEll c (ratioPositiveRoot N h4 p j)
  let g : Fin t → ℝ := fun j => ratioEll c
    ((ratioPositiveRoot N h4 p ⟨j.val, by omega⟩ +
      ratioPositiveRoot N h4 p ⟨j.val + 1, by omega⟩) / 2)
  have hP : (∑ j, ratioEll c (p j)) = 2 * ∑ j, f j :=
    ratio_sum_even_reflection hNcount (fun j => ratioEll c (p j)) href
  have hrev : Fin.rev (⟨t, by omega⟩ : Fin (N / 2 - (2 * s + 1))) = ⟨t, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hzeroRoot : alignedRoot N (2 * s + 1) hr p ⟨t, by omega⟩ = 0 := by
    have h := alignedRoot_rev hr hp ⟨t, by omega⟩
    rw [hrev] at h
    linarith
  have hA := ratio_sum_odd_reflection hqcount
    (fun j => ratioEll c (alignedRoot N (2 * s + 1) hr p j))
    (fun j => by rw [alignedRoot_rev hr hp, ratio_ell_neg])
    (by rw [hzeroRoot, ratio_ell_zero])
  have hmid (j : Fin t) : alignedRoot N (2 * s + 1) hr p ⟨t + 1 + j.val, by omega⟩ =
      (ratioPositiveRoot N h4 p ⟨j.val, by omega⟩ +
        ratioPositiveRoot N h4 p ⟨j.val + 1, by omega⟩) / 2 := by
    have hodd : (2 * s + 1) % 2 ≠ 0 := by omega
    have hidx₀ : (⟨t + 1 + j.val + (2 * s + 1 - 1) / 2, by omega⟩ : Fin (N / 2)) =
        ⟨m + j.val, by omega⟩ := by
      apply Fin.ext
      change t + 1 + j.val + (2 * s + 1 - 1) / 2 = m + j.val
      omega
    have hidx₁ : (⟨t + 1 + j.val + (2 * s + 1 + 1) / 2, by omega⟩ : Fin (N / 2)) =
        ⟨m + (j.val + 1), by omega⟩ := by
      apply Fin.ext
      change t + 1 + j.val + (2 * s + 1 + 1) / 2 = m + (j.val + 1)
      omega
    simp only [alignedRoot, ite_eq_right hodd]
    rw [hidx₀, hidx₁]
    rfl
  have hA' : (∑ j, ratioEll c (alignedRoot N (2 * s + 1) hr p j)) = 2 * ∑ j, g j := by
    simpa only [hmid] using hA
  have hft : f ⟨t, by omega⟩ = ratioEll c (p ⟨s, by omega⟩) := by
    have hidx : Fin.rev (⟨m + t, by omega⟩ : Fin (N / 2)) = ⟨s, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    change ratioEll c (p ⟨m + t, by omega⟩) = _
    rw [← href ⟨m + t, by omega⟩, hidx]
  have htail : (∑ j : Fin s, f ⟨j.val + (t + 1), by omega⟩) =
      ∑ j : Fin s, ratioEll c (p ⟨j.val, by omega⟩) := by
    calc
      _ = ∑ j : Fin s, ratioEll c (p ⟨(Fin.rev j).val, by omega⟩) := by
        apply sum_congr rfl
        intro j hj
        have hidx : Fin.rev (⟨m + (j.val + (t + 1)), by omega⟩ : Fin (N / 2)) =
            ⟨(Fin.rev j).val, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_rev]
          omega
        change ratioEll c (p ⟨m + (j.val + (t + 1)), by omega⟩) = _
        rw [← href ⟨m + (j.val + (t + 1)), by omega⟩, hidx]
      _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin s))
        (fun j => ratioEll c (p ⟨j.val, by omega⟩))
  have htel := ratio_midpoint_sum_telescoping hmt f g
  have hmidSum : (∑ j : Fin t, (2 * g j - f ⟨j.val, by omega⟩ - f ⟨j.val + 1, by omega⟩)) =
      ∑ j : Fin (N / 4 - s - 1), ratioMidpointLog c N h4 p s j := rfl
  rw [hA', hP, htel, hmidSum, hft, htail]

end PottsDiscontinuity.Bethe
