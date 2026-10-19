module

public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.TransferMatrix

/-!
# The coordinate Bethe Ansatz in the zero- and one-particle sectors

These are complete special cases of Theorem 3.1, with the actual transfer matrix and the
coordinate wave of `Defs`. The one-particle block has diagonal `2` and off-diagonal `c²`.
The regular case is a finite geometric sum; the zero-root case is the constant vector.
Neither case needs the restriction `n ≤ N / 2` or `c > 2`.

The final counterexample records a source correction: the companion paper's wraparound
transposition identity (9) requires `n ≥ 2`. For `n = 1` the transposition is the identity,
so the amplitude ratio is `1`, whereas the displayed right-hand side is `-1`.
-/

@[expose] public section

open Finset Complex Matrix

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex Bethe

variable {N : ℕ}

theorem interlaced_singletons (a b : Fin N) : Interlaced {a} {b} := by
  rcases le_total a b with hab | hba
  · left
    refine ⟨by simp, ?_, ?_⟩
    · intro k
      have ha := ({a} : Finset (Fin N)).orderEmbOfFin_mem rfl k
      have hb := ({b} : Finset (Fin N)).orderEmbOfFin_mem (by simp) k
      simp only [Finset.mem_singleton] at ha hb
      rwa [ha, hb]
    · intro k l hkl
      have hk : k.val < 1 := k.isLt
      have hl : l.val < 1 := l.isLt
      omega
  · right
    refine ⟨by simp, ?_, ?_⟩
    · intro k
      have hb := ({b} : Finset (Fin N)).orderEmbOfFin_mem rfl k
      have ha := ({a} : Finset (Fin N)).orderEmbOfFin_mem (by simp) k
      simp only [Finset.mem_singleton] at ha hb
      rwa [hb, ha]
    · intro k l hkl
      have hk : k.val < 1 := k.isLt
      have hl : l.val < 1 := l.isLt
      omega

theorem transferMatrix_singletons (c : ℝ) (a b : Fin N) :
    transferMatrix N c {a} {b} = (if a = b then 2 - c ^ 2 else 0) + c ^ 2 := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · have hs : ({a} : Finset (Fin N)) ≠ {b} := by simpa using hab
    rw [transferMatrix_apply_of_ne hs (interlaced_singletons a b)]
    have hf : (univ.filter fun i => Psi ({a} : Finset (Fin N)) i ≠ Psi {b} i) =
        {a, b} := by
      ext i
      by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [Psi]
    rw [hf]
    simp [hab]

/-- A function supported on one-element configurations is summed by its singleton values. -/
theorem sum_supported_singletons (f : Finset (Fin N) → ℂ)
    (hf : ∀ s, s.card ≠ 1 → f s = 0) :
    (∑ s, f s) = ∑ j : Fin N, f {j} := by
  classical
  let t := Finset.univ.image (fun j : Fin N => ({j} : Finset (Fin N)))
  have ht : (∑ s ∈ t, f s) = ∑ s, f s :=
    Finset.sum_subset (Finset.subset_univ t) (by
      intro s _ hst
      apply hf s
      intro hc
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
      exact hst (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  rw [← ht]
  exact Finset.sum_image Finset.singleton_injective.injOn

/-- Block preservation after extending the real transfer matrix to complex scalars. -/
theorem complex_transfer_mulVec_supported (c : ℝ) (n : ℕ)
    (v : Finset (Fin N) → ℂ) (hv : ∀ s, s.card ≠ n → v s = 0)
    (x : Finset (Fin N)) (hx : x.card ≠ n) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ v) x = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : y.card = n
  · have hxy : x.card ≠ y.card := by omega
    simp [Matrix.map_apply, transferMatrix_apply_eq_zero_of_card_ne hxy]
  · simp [hv y hy]

theorem complex_transfer_mulVec_singleton (c : ℝ) (v : Finset (Fin N) → ℂ)
    (hv : ∀ s, s.card ≠ 1 → v s = 0) (a : Fin N) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ v) {a} =
      (2 - (c : ℂ) ^ 2) * v {a} + (c : ℂ) ^ 2 * ∑ b : Fin N, v {b} := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [sum_supported_singletons _ (fun s hs => by simp [hv s hs])]
  calc
    _ = ∑ b : Fin N,
        ((if a = b then (2 - (c : ℂ) ^ 2) * v {b} else 0) +
          (c : ℂ) ^ 2 * v {b}) := by
      apply Finset.sum_congr rfl
      intro b _
      change (transferMatrix N c {a} {b} : ℂ) * v {b} = _
      rw [transferMatrix_singletons]
      split_ifs <;> push_cast <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

@[simp] theorem coordinateWave_zero (Δ : ℝ) (p : Fin 0 → ℝ) (x : Fin 0 → ℤ) :
    coordinateWave Δ p x = 1 := by
  rw [coordinateWave, Fintype.sum_subsingleton _ (Equiv.refl _)]
  simp [amplitude, planeWave]

@[simp] theorem betheVector_zero (Δ : ℝ) (p : Fin 0 → ℝ) (x : Finset (Fin N)) :
    betheVector Δ p x = if x = ∅ then 1 else 0 := by
  classical
  simp [betheVector, extendByZero, blockWave, Finset.card_eq_zero]

@[simp] theorem eigenvalueRegular_zero (c : ℝ) (p : Fin 0 → ℝ) :
    eigenvalueRegular c p = 2 := by norm_num [eigenvalueRegular]

/-- Theorem 3.1 for the empty set of momenta, including extension by zero to every block. -/
theorem betheAnsatz_zero (N : ℕ) (c : ℝ) (p : Fin 0 → ℝ) :
    (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueRegular c p • betheVector (N := N) (anisotropy c) p := by
  classical
  funext x
  by_cases hx : x = ∅
  · subst x
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_ite]
  · have hcard : x.card ≠ (∅ : Finset (Fin N)).card := by
      intro hc
      exact hx (Finset.card_eq_zero.mp hc)
    have he := transferMatrix_apply_eq_zero_of_card_ne (c := c) hcard
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_ite, hx, he]

@[simp] theorem amplitude_one (Δ : ℝ) (p : Fin 1 → ℝ) (σ : Equiv.Perm (Fin 1)) :
    amplitude Δ p σ = 1 := by
  have hσ : σ = Equiv.refl _ := Subsingleton.elim _ _
  subst σ
  simp [amplitude]

@[simp] theorem coordinateWave_one (Δ : ℝ) (p : Fin 1 → ℝ) (x : Fin 1 → ℤ) :
    coordinateWave Δ p x = Complex.exp (I * (p 0 : ℂ) * (x 0 : ℂ)) := by
  rw [coordinateWave, Fintype.sum_subsingleton _ (Equiv.refl _)]
  simp [planeWave]

theorem betheVector_singleton (Δ : ℝ) (p : Fin 1 → ℝ) (a : Fin N) :
    betheVector Δ p {a} = z (p 0) ^ a.val := by
  classical
  simp only [betheVector, extendByZero, Finset.card_singleton, ↓reduceDIte,
    blockWave, coordinateWave_one, positions, Finset.orderEmbOfFin_singleton]
  rw [z, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem BetheEquations.one_root {Δ : ℝ} {p : Fin 1 → ℝ}
    (hBE : BetheEquations N Δ p) : z (p 0) ^ N = 1 := by
  have h := hBE 0
  simp only [Fin.sum_univ_one, theta_self, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero, Nat.sub_self, pow_zero, one_mul] at h
  rw [z, ← Complex.exp_nat_mul]
  convert h using 1
  congr 1
  ring

theorem sum_one_particle_wave_eq_zero {Δ : ℝ} {p : Fin 1 → ℝ}
    (hBE : BetheEquations N Δ p) (hz : z (p 0) ≠ 1) :
    (∑ b : Fin N, betheVector Δ p {b}) = 0 := by
  simp_rw [betheVector_singleton]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hz, hBE.one_root]
  simp

theorem eigenvalueRegular_one (c : ℝ) (p : Fin 1 → ℝ) (hz : z (p 0) ≠ 1) :
    eigenvalueRegular c p = 2 - (c : ℂ) ^ 2 := by
  simpa only [eigenvalueRegular, Fin.prod_univ_one] using L_add_M c hz

/-- The nonzero-root branch of Theorem 3.1 in the one-particle sector.
The proof is valid for every `N` and `c`; no half-filling bound is needed in this sector. -/
theorem betheAnsatz_one_regular (N : ℕ) (c : ℝ) (p : Fin 1 → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hBE : BetheEquations N (anisotropy c) p) (hp0 : ∀ j, p j ≠ 0) :
    (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueRegular c p • betheVector (N := N) (anisotropy c) p := by
  classical
  have hz := z_ne_one (hp 0) (hp0 0)
  have hv : ∀ s : Finset (Fin N), s.card ≠ 1 → betheVector (anisotropy c) p s = 0 :=
    fun _ hs => betheVector_eq_zero (anisotropy c) p hs
  funext x
  by_cases hx : x.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hx
    rw [complex_transfer_mulVec_singleton c _ hv,
      sum_one_particle_wave_eq_zero hBE hz, eigenvalueRegular_one c p hz]
    simp
  · rw [complex_transfer_mulVec_supported c 1 _ hv x hx]
    simp [hv x hx]

@[simp] theorem eigenvalueZero_one (N : ℕ) (c : ℝ) (p : Fin 1 → ℝ) (l : Fin 1) :
    eigenvalueZero N c p l = 2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) := by
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  simp [eigenvalueZero]

/-- The zero-root branch of Theorem 3.1 in the one-particle sector.
The single zero root automatically satisfies the Bethe equations. -/
theorem betheAnsatz_one_zero (N : ℕ) (c : ℝ) (p : Fin 1 → ℝ)
    (l : Fin 1) (hpl : p l = 0) :
    (transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueZero N c p l • betheVector (N := N) (anisotropy c) p := by
  classical
  have hp0 : p 0 = 0 := (congrArg p (Subsingleton.elim 0 l)).trans hpl
  have hv : ∀ s : Finset (Fin N), s.card ≠ 1 → betheVector (anisotropy c) p s = 0 :=
    fun _ hs => betheVector_eq_zero (anisotropy c) p hs
  funext x
  by_cases hx : x.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hx
    rw [complex_transfer_mulVec_singleton c _ hv]
    simp [betheVector_singleton, hp0]
    ring
  · rw [complex_transfer_mulVec_supported c 1 _ hv x hx]
    simp [hv x hx]

/-- A concrete counterexample to equation (9) without the missing restriction `n ≥ 2`.
Here `N = 2`, `c = 3`, the single momentum is zero, and all Bethe equations hold. -/
theorem source_boundary_ratio_counterexample_one :
    BetheEquations 2 (anisotropy 3) (fun _ : Fin 1 => 0) ∧
      amplitude (anisotropy 3) (fun _ : Fin 1 => 0) (Equiv.swap 0 0) /
          amplitude (anisotropy 3) (fun _ : Fin 1 => 0) (Equiv.refl _) ≠
        -((z 0 / z 0) ^ 2) * Complex.exp (I * (theta (anisotropy 3) 0 0 : ℂ)) := by
  constructor
  · intro j
    simp [theta_self]
  · norm_num [theta_self]

end PottsDiscontinuity.BetheAnsatz
