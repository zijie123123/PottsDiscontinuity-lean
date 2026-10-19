module

public import PottsDiscontinuity.Bethe.Theta
public import PottsDiscontinuity.SixVertex.Defs

/-!
# Coordinate Bethe Ansatz: the objects of Theorem 3.1

Main source: arXiv:1611.09877v2, `thm:BA`, lines 1165–1189.
Companion source: arXiv:1611.09909v1, §2.2, equations `eq:BA_eigenvector`, `eq:A_si`.

The positions in a `State N n` are enumerated increasingly in `0, ..., N-1`.
`coordinateWave` also accepts arbitrary integer positions, as needed for the toroidal shift.
`betheVector` is exactly this wave on the n-particle block, extended by zero elsewhere.
The two eigenvalue expressions are separate definitions: using `eigenvalueRegular` at a zero
root does not assert that it is the eigenvalue there. No nonvanishing of the wave is asserted.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex Bethe

/-- The anisotropy for `a = b = 1`. -/
noncomputable def anisotropy (c : ℝ) : ℝ := (2 - c ^ 2) / 2

/-- The spectral parameter `e^{ip}`. -/
noncomputable def z (p : ℝ) : ℂ := Complex.exp (I * (p : ℂ))

/-- The companion paper's `S(x,y)`. -/
noncomputable def scattering (Δ x y : ℝ) : ℂ :=
  Complex.exp (-(I * (x : ℂ))) + z y - 2 * (Δ : ℂ)

/-- `L` in the paper. Its intended domain is `z ≠ 1`. -/
noncomputable def L (c : ℝ) (w : ℂ) : ℂ := 1 + (c : ℂ) ^ 2 * w / (1 - w)

/-- `M` in the paper. Its intended domain is `z ≠ 1`. -/
noncomputable def M (c : ℝ) (w : ℂ) : ℂ := 1 - (c : ℂ) ^ 2 / (1 - w)

/-- The equations (BE), with their original exponential sign and the sum including `k = j`.
For `n = 0` this predicate is vacuous, so the natural subtraction in the sign is immaterial. -/
def BetheEquations (N : ℕ) (Δ : ℝ) {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ j, Complex.exp (I * (N : ℂ) * (p j : ℂ)) =
    (-1 : ℂ) ^ (n - 1) * Complex.exp (-(I * ((∑ k, theta Δ (p j) (p k) : ℝ) : ℂ)))

/-- The coefficient `A_σ`, including the signature and every ordered pair `k < l`. -/
noncomputable def amplitude {n : ℕ} (Δ : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (Equiv.Perm.sign σ : ℤ) *
    ∏ k, ∏ l ∈ Finset.Ioi k, z (p (σ k)) * scattering Δ (p (σ k)) (p (σ l))

/-- The plane wave for a fixed permutation, on arbitrary integer positions. -/
noncomputable def planeWave {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) : ℂ :=
  ∏ k, Complex.exp (I * (p (σ k) : ℂ) * (x k : ℂ))

/-- The coordinate Bethe wave `ψ(x) = ∑σ A_σ ∏k exp(i p_{σ(k)} x_k)`. -/
noncomputable def coordinateWave {n : ℕ} (Δ : ℝ) (p : Fin n → ℝ)
    (x : Fin n → ℤ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), amplitude Δ p σ * planeWave p σ x

/-- Increasing zero-based positions of a state. -/
noncomputable def positions {N n : ℕ} (x : State N n) : Fin n → ℤ :=
  fun k => ((x.1.orderEmbOfFin x.2 k).val : ℤ)

/-- The coordinate wave on `Ω_n`. -/
noncomputable def blockWave {N n : ℕ} (Δ : ℝ) (p : Fin n → ℝ) (x : State N n) : ℂ :=
  coordinateWave Δ p (positions x)

/-- Extension by zero from the n-particle sector to all configurations. -/
noncomputable def extendByZero {N n : ℕ} (v : State N n → ℂ) (x : Finset (Fin N)) : ℂ :=
  if h : x.card = n then v ⟨x, h⟩ else 0

/-- The vector in Theorem 3.1, with zero-based positions and zero outside `Ω_n`. -/
noncomputable def betheVector {N n : ℕ} (Δ : ℝ) (p : Fin n → ℝ) : Finset (Fin N) → ℂ :=
  extendByZero (blockWave Δ p)

/-- Eigenvalue expression when no momentum is zero. -/
noncomputable def eigenvalueRegular {n : ℕ} (c : ℝ) (p : Fin n → ℝ) : ℂ :=
  (∏ j, L c (z (p j))) + ∏ j, M c (z (p j))

/-- Eigenvalue expression when `p l = 0`. The derivative is with respect to the first variable.
The integer `N - 1` in the source is represented as `(N : ℂ) - 1`, without truncated subtraction. -/
noncomputable def eigenvalueZero {n : ℕ} (N : ℕ) (c : ℝ) (p : Fin n → ℝ) (l : Fin n) : ℂ :=
  (2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
    ∑ j ∈ univ.erase l, (deriv (fun t => theta (anisotropy c) t (p j)) 0 : ℂ)) *
    ∏ j ∈ univ.erase l, M c (z (p j))

theorem anisotropy_lt_neg_one {c : ℝ} (hc : 2 < c) : anisotropy c < -1 := by
  unfold anisotropy
  nlinarith [sq_nonneg (c - 2)]

@[simp] theorem z_zero : z 0 = 1 := by
  simp [z]

theorem z_ne_zero (p : ℝ) : z p ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem extendByZero_coe {N n : ℕ} (v : State N n → ℂ) (x : State N n) :
    extendByZero v x.1 = v x := by
  simp only [extendByZero, x.2, ↓reduceDIte]

@[simp] theorem extendByZero_eq_zero {N n : ℕ} (v : State N n → ℂ)
    {x : Finset (Fin N)} (hx : x.card ≠ n) : extendByZero v x = 0 := by
  simp only [extendByZero, hx, ↓reduceDIte]

theorem betheVector_eq_zero {N n : ℕ} (Δ : ℝ) (p : Fin n → ℝ)
    {x : Finset (Fin N)} (hx : x.card ≠ n) : betheVector (N := N) Δ p x = 0 :=
  extendByZero_eq_zero _ hx

end PottsDiscontinuity.BetheAnsatz
