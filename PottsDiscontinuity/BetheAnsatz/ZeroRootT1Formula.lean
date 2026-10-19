module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Aggregate

/-!
# Evaluation of the paired zero-root contribution

The zipper reindexing separates the nonzero-root phase derivatives from the
single cyclic seam indicator. This module evaluates that sum and combines it
with the corrected constant-word limit.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The sum of the phase derivatives at all labels except the zero root. -/
noncomputable def t1RootDerivativeSum {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : ℂ :=
  ∑ j : {j : Fin (n + 1) // j ≠ l},
    (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)

/-- The real phase derivative is the derivative of the complexified phase. -/
theorem zeroRootPhaseDerivative_false_eq_complexDeriv {N : ℕ} {c p : ℝ}
    (hc : 2 < c) :
    (zeroRootPhaseDerivative (N := N) (anisotropy c) p False : ℂ) =
      deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t p : ℂ)) 0 := by
  have hθ :=
    (Bethe.analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 p).differentiableAt.hasDerivAt
  have hcomplex :
      deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t p : ℂ)) 0 =
        ((deriv (fun t : ℝ => Bethe.theta (anisotropy c) t p) 0 : ℝ) : ℂ) :=
    hθ.ofReal_comp.deriv
  calc
    (zeroRootPhaseDerivative (N := N) (anisotropy c) p False : ℂ) =
        ((deriv (fun t : ℝ => Bethe.theta (anisotropy c) t p) 0 : ℝ) : ℂ) := by
      simp [zeroRootPhaseDerivative]
    _ = deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t p : ℂ)) 0 := hcomplex.symm

/-- The subtype derivative sum is the source's erased finite sum. -/
theorem t1RootDerivativeSum_eq_erase {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    t1RootDerivativeSum (N := N) (anisotropy c) p l =
      ∑ j ∈ (univ : Finset (Fin (n + 1))).erase l,
        deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t (p j) : ℂ)) 0 := by
  classical
  let s : Finset (Fin (n + 1)) := (univ : Finset (Fin (n + 1))).erase l
  let e : {j : Fin (n + 1) // j ≠ l} ≃ {j : Fin (n + 1) // j ∈ s} := {
    toFun := fun j => ⟨j.1, by
      exact Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩⟩
    invFun := fun j => ⟨j.1, by
      have hj := (Finset.mem_erase.mp j.2).1
      exact hj⟩
    left_inv := by intro j; apply Subtype.ext; rfl
    right_inv := by intro j; apply Subtype.ext; rfl }
  change (∑ j : {j : Fin (n + 1) // j ≠ l},
      (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j.1) False : ℂ)) = _
  calc
    _ = ∑ j : {j : Fin (n + 1) // j ∈ s},
          (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j.1) False : ℂ) :=
      Equiv.sum_comp e (fun j : {j : Fin (n + 1) // j ∈ s} =>
        (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j.1) False : ℂ))
    _ = ∑ j ∈ s, (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j) False : ℂ) := by
      change (∑ j ∈ s.attach,
        (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j.1) False : ℂ)) = _
      exact Finset.sum_attach s
        (fun j : Fin (n + 1) =>
          (zeroRootPhaseDerivative (N := N) (anisotropy c) (p j) False : ℂ))
    _ = ∑ j ∈ (univ : Finset (Fin (n + 1))).erase l,
          deriv (fun t : ℝ => (Bethe.theta (anisotropy c) t (p j) : ℂ)) 0 := by
      simp_rw [zeroRootPhaseDerivative_false_eq_complexDeriv hc]
      simp [s]

/-- The regularized all-M word coefficient is the fixed product over nonzero
roots, times the ordinary coordinate plane wave. -/
theorem zeroRootRegularizedWordTerm_allM {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    zeroRootRegularizedWordTerm (N := N) c x p l σ (fun _ => false) =
      (c : ℂ)^2 * amplitude (anisotropy c) p σ *
        (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
        planeWave p σ x := by
  classical
  have himage :
      ((univ : Finset (Fin (n + 1))).erase (σ.symm l)).image σ =
        (univ : Finset (Fin (n + 1))).erase l := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply (Finset.mem_erase.mp hk).1
      apply σ.injective
      calc
        σ k = l := h
        _ = σ (σ.symm l) := (σ.apply_symm_apply l).symm
    · intro hj
      have hj' : j ≠ l := (Finset.mem_erase.mp hj).1
      apply Finset.mem_image.mpr
      refine ⟨σ.symm j, ?_, by simp⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      apply hj'
      have h' := congrArg σ h
      simpa using h'
  have hprod :
      (∏ k ∈ (univ : Finset (Fin (n + 1))).erase (σ.symm l),
        M c (z (p (σ k)))) =
        ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
          M c (z (p j)) := by
    calc
      _ = ∏ j ∈ ((univ : Finset (Fin (n + 1))).erase (σ.symm l)).image σ,
            M c (z (p j)) :=
        (Finset.prod_image σ.injective.injOn).symm
      _ = _ := by rw [himage]
  unfold zeroRootRegularizedWordTerm zeroRootRegularizedProduct zeroRootLetterWeight
  rw [wordPhase_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hprod]
  ring

/-- The finite paired T₁ limit after summing the allowed output slots. -/
theorem sum_t1SigmaLimitTerm_formula {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    (∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l},
      t1SigmaLimitTerm (N := N) c x p l q) =
      ((c : ℂ)^2 *
        (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)))) *
        ∑ σ : Equiv.Perm (Fin (n + 1)),
          amplitude (anisotropy c) p σ * planeWave p σ x *
            (t1RootDerivativeSum (N := N) (anisotropy c) p l +
              if σ (Fin.last n) = l then 0 else (N : ℂ)) := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
          ∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
            t1SigmaLimitTerm (N := N) c x p l ⟨σ, m⟩ := by
      simp_rw [Fintype.sum_sigma]
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
          zeroRootRegularizedWordTerm (N := N) c x p l σ (fun _ => false) *
            ∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
              t1OutputSlope (N := N) (anisotropy c) p σ m.1 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp only [t1SigmaLimitTerm]
      rw [Finset.mul_sum]
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
          ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
            (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
              M c (z (p j))) * planeWave p σ x) *
            (t1RootDerivativeSum (N := N) (anisotropy c) p l +
              if σ (Fin.last n) = l then 0 else (N : ℂ)) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [zeroRootRegularizedWordTerm_allM,
        sum_t1OutputSlope_slots (N := N) (n := n)
          (Δ := anisotropy c) p l σ,
        t1RootDerivativeSum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

/-- Adding the constant-word limit to all paired T₁ residues gives precisely
the degenerate scalar eigenvalue times the coordinate wave. -/
theorem t0_t1_pairLimits_eq_eigenvalueZero {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    t0RegularizedSum (N := N) c x p l 0 +
      ∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i =
        eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
  classical
  let P : ℂ :=
    ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))
  let D : ℂ := t1RootDerivativeSum (N := N) (anisotropy c) p l
  have hseam (σ : Equiv.Perm (Fin (n + 1))) :
      (σ.symm l = Fin.last n) ↔ (σ (Fin.last n) = l) := by
    constructor
    · intro h
      have h' := congrArg σ h
      simpa using h'.symm
    · intro h
      have h' := congrArg σ.symm h
      simpa using h'.symm
  have hcoef (σ : Equiv.Perm (Fin (n + 1))) :
      ((2 - (c : ℂ)^2) +
          if σ.symm l = Fin.last n then (c : ℂ)^2 * (N : ℂ) else 0) +
        (c : ℂ)^2 *
          (D + if σ (Fin.last n) = l then 0 else (N : ℂ)) =
        (2 + (c : ℂ)^2 * ((N : ℂ) - 1) + (c : ℂ)^2 * D) := by
    by_cases hs : σ (Fin.last n) = l
    · simp [hseam σ, hs]
      ring
    · simp [hseam σ, hs]
      ring
  have ht1 := tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm
    (N := N) (n := n) hc x p hp hinj l hpl hBE
  rw [ht1]
  rw [t0RegularizedSum_zero]
  simp only [coordinateWave]
  calc
    _ = (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
          M c (z (p j))) *
          ∑ σ : Equiv.Perm (Fin (n + 1)),
            amplitude (anisotropy c) p σ * planeWave p σ x *
              ((2 - (c : ℂ)^2) +
                if σ.symm l = Fin.last n then (c : ℂ)^2 * (N : ℂ) else 0) +
        ((c : ℂ)^2 *
          (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
            M c (z (p j)))) *
          ∑ σ : Equiv.Perm (Fin (n + 1)),
            amplitude (anisotropy c) p σ * planeWave p σ x *
              (D + if σ (Fin.last n) = l then 0 else (N : ℂ)) := by
      rw [sum_t1SigmaLimitTerm_formula]
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
          ((∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
            M c (z (p j))) *
            (amplitude (anisotropy c) p σ * planeWave p σ x) *
            ((2 - (c : ℂ)^2) +
              if σ.symm l = Fin.last n then (c : ℂ)^2 * (N : ℂ) else 0) +
          (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
            M c (z (p j))) *
            (amplitude (anisotropy c) p σ * planeWave p σ x) *
            ((c : ℂ)^2 *
              (D + if σ (Fin.last n) = l then 0 else (N : ℂ)))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
          (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l,
            M c (z (p j))) *
            (amplitude (anisotropy c) p σ * planeWave p σ x) *
            (2 + (c : ℂ)^2 * ((N : ℂ) - 1) + (c : ℂ)^2 * D) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [← hcoef σ]
      ring
    _ = eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
      have hD : D =
          ∑ j ∈ (univ : Finset (Fin (n + 1))).erase l,
            deriv (fun t : ℝ =>
              (Bethe.theta (anisotropy c) t (p j) : ℂ)) 0 := by
        dsimp [D]
        exact t1RootDerivativeSum_eq_erase (N := N) hc p l
      rw [hD]
      simp only [eigenvalueZero, coordinateWave]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

end PottsDiscontinuity.BetheAnsatz
