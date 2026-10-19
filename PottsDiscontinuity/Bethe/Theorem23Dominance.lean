module

public import PottsDiscontinuity.Bethe.Theorem23Diagonal
public import PottsDiscontinuity.Bethe.Theorem23Rows

/-! # Actual diagonal dominance from a uniform mesh -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- Every Bethe solution with the specified uniform mesh has a strictly
row-diagonally-dominant rescaled Jacobian once `N` is sufficiently large. -/
theorem exists_uniform_rescaled_diagonal_dominance {Δ₀ : ℝ}
    (hΔ₀ : Δ₀ < -1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      2 * (k + 1) ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      ∀ i : Fin ((k + 1) / 2),
        ∑ j ∈ Finset.univ.erase i, |discreteBetheMatrixATilde Δ N (k + 1) p i j| <
          |discreteBetheMatrixATilde Δ N (k + 1) p i i| := by
  obtain ⟨Cdiag, hCdiag, hdiag⟩ := exists_uniform_rescaled_diagonal_estimate hΔ₀
  obtain ⟨Crow, hCrow, hrow⟩ := exists_uniform_rescaled_row_cyclic_estimate hΔ₀
  let b₀ := 4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
  have hb₀ : b₀ < 2 * Real.pi :=
    (discreteBetheG_endpoint_bound hΔ₀ le_rfl
      (show -Real.pi ∈ Icc (-Real.pi) 0 from ⟨le_rfl, by linarith [Real.pi_pos]⟩)).2
  let E := Cdiag * (D ^ 2 + D) + Crow * D
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 0 (E / (2 * Real.pi - b₀)))
  have hpos : (0 : ℝ) < N₀ := (le_max_left _ _).trans_lt hN₀
  have hposNat : 0 < N₀ := by exact_mod_cast hpos
  refine ⟨N₀, hposNat, fun Δ hΔ N k hlarge hs p hp hBE hmesh i => ?_⟩
  have hN : 0 < N := lt_of_lt_of_le hposNat hlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : (N₀ : ℝ) ≤ N := by exact_mod_cast hlarge
  have hthreshold : E / (2 * Real.pi - b₀) < (N : ℝ) :=
    ((le_max_right _ _).trans_lt hN₀).trans_le hcast
  have hE : E / (N : ℝ) < 2 * Real.pi - b₀ := by
    apply (div_lt_iff₀ hNc).2
    have ht := (div_lt_iff₀ (sub_pos.mpr hb₀)).mp hthreshold
    nlinarith only [ht]
  have hd := hdiag Δ hΔ N (k + 1) hN hs p hp hBE D hD
    (discreteHalf_gap_le_of_cyclic_mesh (by omega) p hmesh) i
  have hr := hrow Δ hΔ N k hN p hp (D / (N : ℝ)) (div_nonneg hD hNc.le) hmesh i
  have hx : p (discreteHalfIndex (k + 1) i) ∈ Icc (-Real.pi) 0 :=
    ⟨(hp.1 _).1.le, (discreteS_n_half_coord_neg hp i).le⟩
  have hG := (discreteBetheG_endpoint_bound hΔ₀ hΔ hx).1
  have habs := le_abs_self (discreteBetheMatrixATilde Δ N (k + 1) p i i)
  have hdlower := (abs_le.mp hd).1
  have hrupper := (abs_le.mp hr).2
  dsimp only [E] at hE
  rw [add_div] at hE
  change _ ≤ b₀ at hG
  have hmul : Crow * (D / (N : ℝ)) = Crow * D / (N : ℝ) := by ring
  rw [hmul] at hrupper
  linarith only [hE, hdlower, hrupper, hG, habs]

/-- The symmetric-coordinate Jacobian itself is nonsingular. -/
theorem exists_uniform_Bethe_matrix_nonsingular {Δ₀ : ℝ}
    (hΔ₀ : Δ₀ < -1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      2 * (k + 1) ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      (discreteBetheMatrixA Δ N (k + 1) p).det ≠ 0 := by
  obtain ⟨N₀, hN₀, hdom⟩ := exists_uniform_rescaled_diagonal_dominance hΔ₀ D hD
  refine ⟨N₀, hN₀, fun Δ hΔ N k hlarge hs p hp hBE hmesh => ?_⟩
  have hdet := discrete_strict_row_diagonal_dominance_invertible
    (discreteBetheMatrixATilde Δ N (k + 1) p)
    (hdom Δ hΔ N k hlarge hs p hp hBE hmesh)
  rw [discreteBetheMatrixATilde, Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).1

end PottsDiscontinuity.Bethe
