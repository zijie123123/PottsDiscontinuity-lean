module

public import PottsDiscontinuity.BetheAnsatz.Regular
public import PottsDiscontinuity.BetheAnsatz.ZeroRootAlgebra
public import PottsDiscontinuity.BetheAnsatz.ZeroRootPhases

/-!
# The two constant words in the zero-root limit

This is the corrected T₀ calculation. The boundary contribution uses
`L(z) * (z^(-N)-1)`, whose limit is `+c²N` as proved in `BoundaryLimit`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A cyclic predecessor followed by rotation selects the original coordinate,
except at the seam where it is smaller by N. -/
theorem cyclicPredecessor_rotate {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)
    (k : Fin (n + 1)) :
    cyclicPredecessorPositions N x (finRotate (n + 1) k) =
      x k - if k = Fin.last n then (N : ℤ) else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [finRotate_last, cyclicPredecessorPositions_zero]
    simp
  · have hr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    rw [hr, cyclicPredecessorPositions_succ]
    simp only [Fin.castSucc_ne_last, ↓reduceIte, sub_zero]

/-- Negative integer phases are inverse natural powers. -/
theorem positionPhase_neg_nat (t : ℝ) (d : ℕ) :
    positionPhase t (-(d : ℤ)) = (z t ^ d)⁻¹ := by
  have hmul : positionPhase t (-(d : ℤ)) * z t ^ d = 1 := by
    rw [← positionPhase_nat]
    rw [← positionPhase_add]
    simp [positionPhase]
  have hz : z t ^ d ≠ 0 := pow_ne_zero d (z_ne_zero t)
  calc
    positionPhase t (-(d : ℤ)) = positionPhase t (-(d : ℤ)) * 1 := by simp
    _ = positionPhase t (-(d : ℤ)) * (z t ^ d * (z t ^ d)⁻¹) := by
      rw [mul_inv_cancel₀ hz]
    _ = (positionPhase t (-(d : ℤ)) * z t ^ d) * (z t ^ d)⁻¹ := by ac_rfl
    _ = 1 * (z t ^ d)⁻¹ := by rw [hmul]
    _ = (z t ^ d)⁻¹ := by simp

/-- Shifting an integer coordinate down by N contributes the inverse Nth phase. -/
theorem positionPhase_sub_nat (t : ℝ) (y : ℤ) (N : ℕ) :
    positionPhase t (y - (N : ℤ)) = positionPhase t y * (z t ^ N)⁻¹ := by
  rw [show y - (N : ℤ) = y + (-(N : ℤ)) by ring, positionPhase_add,
    positionPhase_neg_nat]

/-- Product over the non-root indices is unchanged by the perturbation. -/
theorem prod_perturbed_erase_eq {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (f : ℝ → ℂ) :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (perturbedMomenta p l t j)) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [perturbedMomenta_of_ne p l j t (mem_erase.mp hj).1]

/-- Product of a one-root perturbed sequence is its root factor times the fixed remainder. -/
theorem prod_perturbed_factor {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (f : ℝ → ℂ) :
    (∏ j, f (perturbedMomenta p l t j)) =
      f (p l + t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) := by
  calc
    _ = f (perturbedMomenta p l t l) *
        ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (perturbedMomenta p l t j) :=
      (Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
        (fun j => f (perturbedMomenta p l t j)) (mem_univ l)).symm
    _ = f (p l + t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, f (p j) := by
      rw [perturbedMomenta_at]
      congr 1
      exact prod_perturbed_erase_eq p l t f

/-- The fixed-amplitude contribution of the two constant words at perturbation t. -/
noncomputable def constantWordSumPerturbed {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), amplitude (anisotropy c) p σ *
    (wordCoefficient c (perturbedMomenta p l t) σ (fun _ => false) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => false) +
     wordCoefficient c (perturbedMomenta p l t) σ (fun _ => true) *
        wordPhase (N := N) x (perturbedMomenta p l t) σ (fun _ => true))

/-- Reindexing identity for the L constant word with its one-root phase. -/
theorem toroidal_zero_root_L_phase {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (x : Fin (n + 1) → ℤ) (l : Fin (n + 1)) (t : ℝ) :
    (∑ σ, amplitude Δ p σ * positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
        planeWave p σ (cyclicPredecessorPositions N x)) =
      ∑ σ, amplitude Δ p σ * positionPhase t
        (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l)) *
        planeWave p σ x := by
  let f : Equiv.Perm (Fin (n + 1)) → ℂ := fun σ =>
    positionPhase t (cyclicPredecessorPositions N x ((σ * (finRotate (n + 1))⁻¹).symm l))
  have h := toroidal_change_of_variables hΔ p hBE x f
  have hf : ∀ σ, f (σ * finRotate (n + 1)) =
      positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) := by
    intro σ
    dsimp [f]
    have he : (σ * finRotate (n + 1)) * (finRotate (n + 1))⁻¹ = σ := by group
    rw [he]
  simpa only [f, hf, mul_assoc] using h.symm

/-- Exact T₀ decomposition before taking the limit. -/
theorem constantWordSumPerturbed_eq {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (t : ℝ) :
    constantWordSumPerturbed (N := N) c x p l t =
      (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
      ∑ σ, amplitude (anisotropy c) p σ *
        positionPhase t (x (σ.symm l)) * planeWave p σ x *
        (M c (z t) + L c (z t) *
          if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
  let q := perturbedMomenta p l t
  have hLM := prod_L_eq_prod_M_of_zero hc p hp hinj l hpl hBE
  have hM : (∏ j, M c (z (q j))) =
      M c (z t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
    change (∏ j, M c (z (perturbedMomenta p l t j))) = _
    rw [prod_perturbed_factor p l t (fun r => M c (z r)), hpl, zero_add]
  have hL : (∏ j, L c (z (q j))) =
      L c (z t) * ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
    change (∏ j, L c (z (perturbedMomenta p l t j))) = _
    rw [prod_perturbed_factor p l t (fun r => L c (z r)), hpl, zero_add, hLM]
  have hphaseM (σ : Equiv.Perm (Fin (n + 1))) :
      wordPhase (N := N) x q σ (fun _ => false) =
        positionPhase t (x (σ.symm l)) * planeWave p σ x := by
    rw [wordPhase_false, planeWave_perturbed_zero p l hpl t σ]
  have hphaseL (σ : Equiv.Perm (Fin (n + 1))) :
      wordPhase (N := N) x q σ (fun _ => true) =
        positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
          planeWave p σ (cyclicPredecessorPositions N x) := by
    rw [wordPhase_true, planeWave_perturbed_zero p l hpl t σ]
  dsimp only [q] at hphaseM hphaseL
  have htor := toroidal_zero_root_L_phase (anisotropy_lt_neg_one hc) p hBE x l t
  unfold constantWordSumPerturbed
  simp_rw [wordCoefficient_false, wordCoefficient_true]
  rw [hM, hL]
  simp_rw [hphaseM, hphaseL]
  let P := ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))
  have hsplit :
      (∑ σ, amplitude (anisotropy c) p σ *
        ((M c (z t) * P) *
            (positionPhase t (x (σ.symm l)) * planeWave p σ x) +
         (L c (z t) * P) *
            (positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
              planeWave p σ (cyclicPredecessorPositions N x)))) =
        (∑ σ, amplitude (anisotropy c) p σ *
          ((M c (z t) * P) *
            (positionPhase t (x (σ.symm l)) * planeWave p σ x))) +
        ∑ σ, amplitude (anisotropy c) p σ *
          ((L c (z t) * P) *
            (positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
              planeWave p σ (cyclicPredecessorPositions N x))) := by
    calc
      _ = ∑ σ, (amplitude (anisotropy c) p σ *
          ((M c (z t) * P) *
            (positionPhase t (x (σ.symm l)) * planeWave p σ x)) +
          amplitude (anisotropy c) p σ *
            ((L c (z t) * P) *
              (positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
                planeWave p σ (cyclicPredecessorPositions N x)))) := by
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = _ := Finset.sum_add_distrib
  have hMsum :
      (∑ σ, amplitude (anisotropy c) p σ *
          ((M c (z t) * P) *
            (positionPhase t (x (σ.symm l)) * planeWave p σ x))) =
        (P * M c (z t)) *
          ∑ σ, amplitude (anisotropy c) p σ *
            positionPhase t (x (σ.symm l)) * planeWave p σ x := by
    calc
      _ = ∑ σ, (P * M c (z t)) *
          (amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
            planeWave p σ x) := by
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hLsum :
      (∑ σ, amplitude (anisotropy c) p σ *
          ((L c (z t) * P) *
            (positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
              planeWave p σ (cyclicPredecessorPositions N x)))) =
        (L c (z t) * P) *
          ∑ σ, amplitude (anisotropy c) p σ *
            positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
              planeWave p σ (cyclicPredecessorPositions N x) := by
    calc
      _ = ∑ σ, (L c (z t) * P) *
          (amplitude (anisotropy c) p σ *
            positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
              planeWave p σ (cyclicPredecessorPositions N x)) := by
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hrot :
      (∑ σ, amplitude (anisotropy c) p σ *
        positionPhase t
          (cyclicPredecessorPositions N x
            ((σ * (finRotate (n + 1))⁻¹).symm l)) * planeWave p σ x) =
      ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
        planeWave p σ x * (if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
    apply Finset.sum_congr rfl
    intro σ _
    have hidx : (σ * (finRotate (n + 1))⁻¹).symm l =
        finRotate (n + 1) (σ.symm l) := by
      have hperm : (σ * (finRotate (n + 1))⁻¹).symm =
          finRotate (n + 1) * σ.symm := by
        change ((σ * (finRotate (n + 1))⁻¹)⁻¹) =
          finRotate (n + 1) * σ⁻¹
        group
      simpa only [Equiv.Perm.mul_apply] using
        congrArg (fun ρ : Equiv.Perm (Fin (n + 1)) => ρ l) hperm
    rw [hidx, cyclicPredecessor_rotate]
    by_cases hk : σ.symm l = Fin.last n
    · simp only [hk, ↓reduceIte]
      rw [positionPhase_sub_nat]
      ring
    · simp only [hk, ↓reduceIte]
      simp
  calc
    _ = P *
        ((M c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ *
              positionPhase t (x (σ.symm l)) * planeWave p σ x +
          (L c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ *
              positionPhase t (cyclicPredecessorPositions N x (σ.symm l)) *
                planeWave p σ (cyclicPredecessorPositions N x)) := by
      rw [hsplit, hMsum, hLsum]
      ring
    _ = P *
        ((M c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ *
              positionPhase t (x (σ.symm l)) * planeWave p σ x +
          (L c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ *
              positionPhase t
                (cyclicPredecessorPositions N x
                  ((σ * (finRotate (n + 1))⁻¹).symm l)) * planeWave p σ x) := by
      rw [htor]
    _ = P *
        ((M c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ *
              positionPhase t (x (σ.symm l)) * planeWave p σ x +
          (L c (z t)) *
            ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
              planeWave p σ x *
                (if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1)) := by
      rw [hrot]
    _ = P * ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
          planeWave p σ x *
            (M c (z t) + L c (z t) *
              if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1) := by
      let b : Equiv.Perm (Fin (n + 1)) → ℂ := fun σ =>
        amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) * planeWave p σ x
      let e : Equiv.Perm (Fin (n + 1)) → ℂ := fun σ =>
        if σ.symm l = Fin.last n then (z t ^ N)⁻¹ else 1
      have hfinal : P *
          (M c (z t) * (∑ σ, b σ) + L c (z t) * (∑ σ, b σ * e σ)) =
          P * ∑ σ, b σ * (M c (z t) + L c (z t) * e σ) := by
        calc
          _ = (P * M c (z t)) * (∑ σ, b σ) +
              (P * L c (z t)) * (∑ σ, b σ * e σ) := by ring
          _ = (∑ σ, (P * M c (z t)) * b σ) +
              (∑ σ, (P * L c (z t)) * (b σ * e σ)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
          _ = ∑ σ, ((P * M c (z t)) * b σ +
              (P * L c (z t)) * (b σ * e σ)) := by
            rw [← Finset.sum_add_distrib]
          _ = ∑ σ, P * (b σ * (M c (z t) + L c (z t) * e σ)) := by
            apply Finset.sum_congr rfl
            intro σ _
            ring
          _ = _ := by rw [Finset.mul_sum]
      simpa only [b, e] using hfinal

end PottsDiscontinuity.BetheAnsatz
