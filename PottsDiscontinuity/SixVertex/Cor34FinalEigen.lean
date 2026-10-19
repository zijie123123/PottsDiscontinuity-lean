module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.ZeroRootTheorem
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Corollary 3.4: apply the coordinate Bethe Ansatz on the block -/

@[expose] public section

open Matrix

namespace PottsDiscontinuity.SixVertex

/-- Restrict a full transfer-matrix eigenvector supported on particle number `n` to the
`n`-particle block. -/
theorem cor34_final_restrict_full_eigen {N n : ℕ} {c Δ : ℝ}
    {p : Fin n → ℝ} {μ : ℂ}
    (hfull : (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.betheVector Δ p =
      μ • BetheAnsatz.betheVector Δ p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      μ • BetheAnsatz.blockWave Δ p := by
  classical
  ext x
  have hx := congrFun hfull x.1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun y : Finset (Fin N) => y.card = n)
    (fun y => ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y *
      BetheAnsatz.betheVector Δ p y)
  have hcompl :
      (∑ y : {y : Finset (Fin N) // y.card ≠ n},
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    simp [BetheAnsatz.betheVector_eq_zero Δ p y.2]
  have hrestr :
      (∑ y : State N n,
        ((transferMatrix N c).map (algebraMap ℝ ℂ)) x.1 y.1 *
          BetheAnsatz.betheVector Δ p y.1) =
      ∑ y : State N n,
        ((transferBlock N c n).map (algebraMap ℝ ℂ)) x y *
          BetheAnsatz.blockWave Δ p y := by
    apply Finset.sum_congr rfl
    intro y hy
    simp [transferBlock, BetheAnsatz.betheVector]
  rw [← hsplit, hcompl, add_zero] at hx
  rw [hrestr] at hx
  simpa [transferBlock, BetheAnsatz.betheVector, BetheAnsatz.extendByZero,
    BetheAnsatz.blockWave, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    State, x.2] using hx

/-- On the even branch, a Theorem 2.3 root tuple gives the regular Theorem 3.1
eigenvector equation on the transfer block. -/
theorem cor34_final_even_block_eigen {N n : ℕ} {c Δ : ℝ}
    (hc : 2 < c) (hΔ : BetheAnsatz.anisotropy c = Δ)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      BetheAnsatz.eigenvalueRegular c p • BetheAnsatz.blockWave Δ p := by
  have hBA : BetheAnsatz.BetheEquations N (BetheAnsatz.anisotropy c) p := by
    rw [hΔ]
    exact cor34_discreteBetheEquation_to_betheEquations p hBE
  have hbranches := BetheAnsatz.betheAnsatz_all hc p (fun j => hp.1 j)
    (cor34_S_n_injective hp) hBA
  rcases hbranches with ⟨hnonzero, hfull⟩ | ⟨l, hl, hfull⟩
  · have hfull' : (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.betheVector Δ p =
      BetheAnsatz.eigenvalueRegular c p • BetheAnsatz.betheVector Δ p := by
        simpa only [hΔ] using hfull
    exact cor34_final_restrict_full_eigen hfull'
  · exact (cor34_even_S_n_roots_nonzero hp hn l hl).elim

/-- On the odd branch, the centered momentum is zero and injectivity identifies the
Theorem 3.1 eigenvalue with its derivative-corrected zero-root expression. -/
theorem cor34_final_odd_block_eigen {N n q : ℕ} {c Δ : ℝ}
    (hc : 2 < c) (hΔ : BetheAnsatz.anisotropy c = Δ)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave Δ p =
      BetheAnsatz.eigenvalueZero N c p (⟨q - 1, by omega⟩ : Fin n) •
        BetheAnsatz.blockWave Δ p := by
  have hcenter : p (⟨q - 1, by omega⟩ : Fin n) = 0 :=
    cor34_odd_S_n_center_zero hp hnq
  have hBA : BetheAnsatz.BetheEquations N (BetheAnsatz.anisotropy c) p := by
    rw [hΔ]
    exact cor34_discreteBetheEquation_to_betheEquations p hBE
  have hbranches := BetheAnsatz.betheAnsatz_all hc p (fun j => hp.1 j)
    (cor34_S_n_injective hp) hBA
  rcases hbranches with ⟨hnonzero, hfull⟩ | ⟨l, hl, hfull⟩
  · exact (hnonzero ⟨q - 1, by omega⟩ hcenter).elim
  · have hl' : l = (⟨q - 1, by omega⟩ : Fin n) :=
      (cor34_S_n_injective hp) (hl.trans hcenter.symm)
    subst l
    have hfull' : (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.betheVector Δ p =
      BetheAnsatz.eigenvalueZero N c p (⟨q - 1, by omega⟩ : Fin n) •
        BetheAnsatz.betheVector Δ p := by
        simpa only [hΔ] using hfull
    exact cor34_final_restrict_full_eigen hfull'

end PottsDiscontinuity.SixVertex
