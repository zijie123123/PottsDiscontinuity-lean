module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootGapLimit

/-!
# The degenerate zero-momentum Bethe Ansatz branch

The coordinate identity is lifted to the full transfer matrix using the exact
gap-sum representation on the particle block and support of the zero-extended
vector away from that block.
-/

@[expose] public section

open Finset Complex Matrix Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Theorem 3.1, degenerate branch: if one distinct momentum is zero, the
full complex transfer matrix acts by the derivative-corrected eigenvalue. -/
theorem betheAnsatz_zeroRoot {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (m + 2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
      betheVector (anisotropy c) p =
      eigenvalueZero N c p l • betheVector (anisotropy c) p := by
  funext x
  by_cases hx : x.card = m + 2
  · let s : SixVertex.State N (m + 2) := ⟨x, hx⟩
    have htransfer := transfer_betheVector_eq_cyclicGapSum c
      (anisotropy_lt_neg_one hc) p hBE s
    have hgap := fixedAmplitudeGapSum_zero_eq_eigenvalueZero hc
      (positions s) (positions_strictMono s) (positions_span_lt s)
      p hp hinj l hpl hBE
    have hact :
        ((SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
          betheVector (anisotropy c) p) s.1 =
        eigenvalueZero N c p l * coordinateWave (anisotropy c) p (positions s) :=
      htransfer.trans hgap
    change ((SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
      extendByZero (blockWave (anisotropy c) p)) s.1 =
        eigenvalueZero N c p l * coordinateWave (anisotropy c) p (positions s) at hact
    change ((SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
      extendByZero (blockWave (anisotropy c) p)) s.1 =
        eigenvalueZero N c p l * extendByZero (blockWave (anisotropy c) p) s.1
    rw [extendByZero_coe]
    simpa [blockWave] using hact
  · rw [complex_transfer_mulVec_supported c (m + 2)
      (betheVector (anisotropy c) p)
      (fun y hy => betheVector_eq_zero _ _ hy) x hx]
    simp only [Pi.smul_apply, smul_eq_mul, betheVector_eq_zero _ _ hx, mul_zero]

/-- Theorem 3.1 for every sector with at least two particles, stated as the two
mutually exclusive momentum branches. Injectivity makes the zero-root index unique. -/
theorem betheAnsatz_twoOrMore {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (m + 2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (hBE : BetheEquations N (anisotropy c) p) :
    ((∀ j, p j ≠ 0) ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueRegular c p • betheVector (anisotropy c) p) ∨
    (∃ l, p l = 0 ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueZero N c p l • betheVector (anisotropy c) p) := by
  classical
  by_cases hnonzero : ∀ j, p j ≠ 0
  · exact Or.inl ⟨hnonzero, betheAnsatz_regular hc p hp hnonzero hBE⟩
  · push Not at hnonzero
    rcases hnonzero with ⟨l, hl⟩
    have hpl : p l = 0 := by simpa using hl
    exact Or.inr ⟨l, hpl, betheAnsatz_zeroRoot hc p hp hinj l hpl hBE⟩

/-- Theorem 3.1 in all particle sectors. The empty and one-particle cases are
handled directly; sectors of size at least two use the general regular and
zero-root branches above. The hypotheses imply the requested statement without
needing the half-filling bound. -/
theorem betheAnsatz_all {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin n → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (hBE : BetheEquations N (anisotropy c) p) :
    ((∀ j, p j ≠ 0) ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueRegular c p • betheVector (anisotropy c) p) ∨
    (∃ l, p l = 0 ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueZero N c p l • betheVector (anisotropy c) p) := by
  classical
  cases n with
  | zero =>
      have hnonzero : ∀ j : Fin 0, p j ≠ 0 := by
        intro j
        exact Fin.elim0 j
      exact Or.inl ⟨hnonzero, betheAnsatz_zero N c p⟩
  | succ n =>
      cases n with
      | zero =>
          by_cases hzero : p 0 = 0
          · exact Or.inr ⟨0, hzero, betheAnsatz_one_zero N c p 0 hzero⟩
          · have hnonzero : ∀ j : Fin 1, p j ≠ 0 := by
              intro j
              fin_cases j
              exact hzero
            exact Or.inl ⟨hnonzero, betheAnsatz_one_regular N c p hp hBE hnonzero⟩
      | succ m =>
          exact betheAnsatz_twoOrMore hc p hp hinj hBE

end PottsDiscontinuity.BetheAnsatz
