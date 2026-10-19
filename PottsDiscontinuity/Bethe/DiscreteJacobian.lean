module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteAnalysis
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# Finite matrices in the discrete Bethe argument

The entries below are the source's displayed symmetric-coordinate matrix and its
gap rescaling.  The estimates here concern only the off-diagonal sign; the later
comparison of its diagonal entries with `2π` uses the excluded `ρ` estimates.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace PottsDiscontinuity.Bethe

/-- First partial derivative of the Bethe phase. -/
noncomputable def thetaPartialFirst (Δ x y : ℝ) : ℝ :=
  deriv (fun s => theta Δ s y) x

/-- Second partial derivative of the Bethe phase. -/
noncomputable def thetaPartialSecond (Δ x y : ℝ) : ℝ :=
  deriv (fun t => theta Δ x t) y

/-- Chain rule for the phase along an affine path in both variables. -/
theorem hasDerivAt_theta_affine {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    HasDerivAt (fun t => theta Δ (x + t * a) (y + t * b))
      (a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y) 0 := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hF : HasFDerivAt F (fderiv ℝ F (x, y)) (x, y) :=
    (analyticAt_theta_xy hΔ x y).differentiableAt.hasFDerivAt
  have h₁ : HasDerivAt (fun s => theta Δ s y) (thetaPartialFirst Δ x y) x :=
    (analyticAt_theta_left hΔ x y).differentiableAt.hasDerivAt
  have h₂ : HasDerivAt (fun t => theta Δ x t) (thetaPartialSecond Δ x y) y :=
    (analyticAt_theta_right hΔ x y).differentiableAt.hasDerivAt
  have h₁path : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × ℝ)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h₂path : HasDerivAt (fun t : ℝ => ((x, t) : ℝ × ℝ)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h₁eq : thetaPartialFirst Δ x y = fderiv ℝ F (x, y) (1, 0) := by
    exact h₁.unique (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, y) : ℝ × ℝ))
      x hF h₁path)
  have h₂eq : thetaPartialSecond Δ x y = fderiv ℝ F (x, y) (0, 1) := by
    exact h₂.unique (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ))
      y hF h₂path)
  have hvec : (a, b) = a • (1, 0) + b • (0, 1) := by
    ext <;> simp
  have hfd : fderiv ℝ F (x, y) (a, b) =
      a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
    calc
      fderiv ℝ F (x, y) (a, b) =
          fderiv ℝ F (x, y) (a • (1, 0) + b • (0, 1)) := by rw [hvec]
      _ = a • fderiv ℝ F (x, y) (1, 0) + b • fderiv ℝ F (x, y) (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = a * thetaPartialFirst Δ x y + b * thetaPartialSecond Δ x y := by
        rw [← h₁eq, ← h₂eq]
        simp [smul_eq_mul]
  have hxa : HasDerivAt (fun t : ℝ => x + t * a) a 0 := by
    have hm := (hasDerivAt_id 0).mul_const a
    have hadd := (hasDerivAt_const 0 x).add hm
    have heq : (fun t : ℝ => x + t * a) = (fun t => x) + fun t => t * a := by
      funext t
      rfl
    rw [heq]
    simpa using hadd
  have hyb : HasDerivAt (fun t : ℝ => y + t * b) b 0 := by
    have hm := (hasDerivAt_id 0).mul_const b
    have hadd := (hasDerivAt_const 0 y).add hm
    have heq : (fun t : ℝ => y + t * b) = (fun t => y) + fun t => t * b := by
      funext t
      rfl
    rw [heq]
    simpa using hadd
  have hpath := hxa.prodMk hyb
  have hF0 : HasFDerivAt F (fderiv ℝ F (x, y)) (x + 0 * a, y + 0 * b) := by
    simpa using hF
  have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ =>
      ((x + t * a, y + t * b) : ℝ × ℝ)) 0 hF0 hpath
  rw [hfd] at hcomp
  have hfun : (fun t : ℝ => theta Δ (x + t * a) (y + t * b)) =
      F ∘ (fun t : ℝ => ((x + t * a, y + t * b) : ℝ × ℝ)) := by
    funext t
    rfl
  rw [hfun]
  exact hcomp

/-- The `j`th coordinate among the first `⌊n/2⌋` coordinates, regarded as a `Fin n`. -/
def discreteHalfIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self n 2)⟩

/-- The next full index after a first-half coordinate. -/
def discreteHalfNextIndex (n : ℕ) (j : Fin (n / 2)) : Fin n :=
  ⟨j.val + 1, by have := discreteHalfIndex n j |>.isLt; omega⟩

/-- Every first-half coordinate lies strictly before its reflected coordinate. -/
theorem discreteHalfIndex_lt_rev {n : ℕ} (j : Fin (n / 2)) :
    discreteHalfIndex n j < Fin.rev (discreteHalfIndex n j) := by
  have hj : 2 * j.val + 2 ≤ n := by omega
  change (discreteHalfIndex n j).val < (Fin.rev (discreteHalfIndex n j)).val
  simp only [discreteHalfIndex, Fin.val_mk, Fin.val_rev]
  omega

/-- Basis vector `e_j-e_(n+1-j)` for the symmetric subspace. -/
def discreteSymBasis (n : ℕ) (j : Fin (n / 2)) : Fin n → ℝ := fun ell =>
  if ell = discreteHalfIndex n j then 1
  else if ell = Fin.rev (discreteHalfIndex n j) then -1 else 0

/-- The basis vector has the required two point support. -/
theorem sum_discreteSymBasis_mul {n : ℕ} (j : Fin (n / 2)) (f : Fin n → ℝ) :
    (∑ ell : Fin n, discreteSymBasis n j ell * f ell) =
      f (discreteHalfIndex n j) - f (Fin.rev (discreteHalfIndex n j)) := by
  classical
  let a := discreteHalfIndex n j
  let b := Fin.rev a
  have hab : a ≠ b := (ne_of_lt (discreteHalfIndex_lt_rev j))
  have hpoint (ell : Fin n) : discreteSymBasis n j ell * f ell =
      (if ell = a then f a else 0) + (if ell = b then -f b else 0) := by
    by_cases h₁ : ell = a
    · subst ell
      simp [discreteSymBasis, a, b, hab]
    · by_cases h₂ : ell = b
      · subst ell
        simp [discreteSymBasis, a, b, h₁]
      · simp [discreteSymBasis, a, b, h₁, h₂]
  calc
    _ = ∑ ell : Fin n,
          ((if ell = a then f a else 0) + (if ell = b then -f b else 0)) :=
      Finset.sum_congr rfl (fun ell _ => hpoint ell)
    _ = (∑ ell : Fin n, if ell = a then f a else 0) +
          ∑ ell : Fin n, if ell = b then -f b else 0 := Finset.sum_add_distrib
    _ = f a - f b := by simp [Finset.sum_ite_eq', a, b]; ring

/-- A first-half basis vector is one at its own coordinate and zero at all other
first-half coordinates. -/
theorem discreteSymBasis_at_half {n : ℕ} (i k : Fin (n / 2)) :
    discreteSymBasis n k (discreteHalfIndex n i) = if i = k then 1 else 0 := by
  classical
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  have hinj : ri = rk ↔ i = k := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      change i.val = k.val at hv
      apply Fin.ext
      exact hv
    · rintro rfl
      rfl
  have hnot : ri ≠ Fin.rev rk := by
    intro h
    have hrev : Fin.rev ri = rk := by simpa using congrArg Fin.rev h
    have h₁ : ri < rk := by simpa [ri, rk, hrev] using discreteHalfIndex_lt_rev i
    have h₂ : rk < ri := by simpa [ri, rk, h] using discreteHalfIndex_lt_rev k
    exact (not_lt_of_ge (le_of_lt h₂)) h₁
  simp [discreteSymBasis, ri, rk, hinj, hnot]

/-- Each symmetric coordinate basis vector belongs to `R_n_sym`. -/
theorem discreteSymBasis_mem_R_n_sym {n : ℕ} (k : Fin (n / 2)) :
    discreteSymBasis n k ∈ R_n_sym n := by
  classical
  let a := discreteHalfIndex n k
  have haa : a ≠ Fin.rev a := ne_of_lt (discreteHalfIndex_lt_rev k)
  change ∀ j, discreteSymBasis n k (Fin.rev j) = -discreteSymBasis n k j
  intro j
  have hvalA : discreteSymBasis n k a = 1 := by
    simp [discreteSymBasis, a]
  have hvalRev : discreteSymBasis n k (Fin.rev a) = -1 := by
    by_cases h : Fin.rev a = a
    · exact (haa h.symm).elim
    · simp [discreteSymBasis, a, h]
  by_cases h₁ : j = a
  · subst j
    rw [hvalRev, hvalA]
  · by_cases h₂ : j = Fin.rev a
    · subst j
      simp only [Fin.rev_rev]
      rw [hvalA, hvalRev]
      norm_num
    · have hr₁ : Fin.rev j ≠ a := by
        intro h
        have h' := congrArg Fin.rev h
        have h'' : j = Fin.rev a := by simpa using h'
        exact h₂ h''
      have hr₂ : Fin.rev j ≠ Fin.rev a := by
        intro h
        have h' := congrArg Fin.rev h
        have h'' : j = a := by simpa using h'
        exact h₁ h''
      simp [discreteSymBasis, a, h₁, h₂, hr₁, hr₂]

/-- The source's explicit symmetric-coordinate matrix `A` for `d(I-T)`. -/
noncomputable def discreteBetheMatrixA (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := fun i k =>
  if i = k then
    1 + (∑ ell ∈ Finset.univ.erase (discreteHalfIndex n i),
      thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell)) / (N : ℝ) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n i))) / (N : ℝ)
  else
    (thetaPartialSecond Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n k)) -
      thetaPartialSecond Δ (p (discreteHalfIndex n i))
        (p (Fin.rev (discreteHalfIndex n k)))) / (N : ℝ)

/-- The source's gap matrix `B`, with diagonal entries `N (p_(j+1)-p_j)`. -/
noncomputable def discreteBetheMatrixB (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ := Matrix.diagonal fun j =>
      (N : ℝ) * (p (discreteHalfNextIndex n j) - p (discreteHalfIndex n j))

/-- The rescaled matrix `Ã = A B` from the source. -/
noncomputable def discreteBetheMatrixATilde (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Matrix (Fin (n / 2)) (Fin (n / 2)) ℝ :=
  discreteBetheMatrixA Δ N n p * discreteBetheMatrixB N n p

/-- The residual `I-T` whose differential is used in Theorem 2.3. -/
noncomputable def discreteBetheResidual (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) :
    Fin n → ℝ := fun j => p j - discreteBetheMap Δ N n p j

/-- Affine path through `p` in direction `v`. -/
def discreteBetheAffinePath {n : ℕ} (p v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => p j + t * v j

/-- Directional derivative formula for the residual `I-T`. -/
theorem hasDerivAt_discreteBetheResidual_path {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i)
      (v i + (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) / (N : ℝ)) 0 := by
  have hcoord (j : Fin n) : HasDerivAt (fun t : ℝ => p j + t * v j) (v j) 0 := by
    have hm := (hasDerivAt_id 0).mul_const (v j)
    have hadd := (hasDerivAt_const 0 (p j)).add hm
    have heq : (fun t : ℝ => p j + t * v j) =
        (fun t : ℝ => p j) + fun t => t * v j := by
      funext t
      rfl
    rw [heq]
    simpa using hadd
  have hterm (ell : Fin n) : HasDerivAt
      (fun t : ℝ => theta Δ (p i + t * v i) (p ell + t * v ell))
      (v i * thetaPartialFirst Δ (p i) (p ell) +
        v ell * thetaPartialSecond Δ (p i) (p ell)) 0 :=
    hasDerivAt_theta_affine hΔ (p i) (p ell) (v i) (v ell)
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ ell : Fin n,
        theta Δ (p i + t * v i) (p ell + t * v ell))
      (∑ ell : Fin n,
        (v i * thetaPartialFirst Δ (p i) (p ell) +
          v ell * thetaPartialSecond Δ (p i) (p ell))) 0 := by
    simpa using (HasDerivAt.fun_sum (u := Finset.univ)
      (fun ell _ => hterm ell))
  let c : ℝ := 2 * Real.pi * discreteBetheIndex n i / (N : ℝ)
  have hbase : HasDerivAt (fun t : ℝ => p i + t * v i - c) (v i) 0 := by
    have hsub := (hcoord i).sub (hasDerivAt_const 0 c)
    have heq : (fun t : ℝ => p i + t * v i - c) =
        (fun t : ℝ => p i + t * v i) - fun _ : ℝ => c := by
      funext t
      rfl
    rw [heq]
    simpa only [sub_zero] using hsub
  have hsumdiv := hsum.div_const (N : ℝ)
  have hres := hbase.add hsumdiv
  have hfun : (fun t : ℝ =>
      discreteBetheResidual Δ N n (discreteBetheAffinePath p v t) i) =
      (fun t => p i + t * v i - c) +
        (fun t => (∑ ell : Fin n,
          theta Δ (p i + t * v i) (p ell + t * v ell)) / (N : ℝ)) := by
    funext t
    simp [discreteBetheResidual, discreteBetheAffinePath, discreteBetheMap, c]
    ring
  rw [hfun]
  exact hres

/-- On the diagonal, the two partial derivatives of `Θ` cancel. -/
theorem thetaPartial_diag_sum {Δ x : ℝ} (hΔ : Δ < -1) :
    thetaPartialFirst Δ x x + thetaPartialSecond Δ x x = 0 := by
  simpa [thetaPartialFirst, thetaPartialSecond] using deriv_theta_diag hΔ x

/-- The explicit source matrix `A` is the derivative of `I-T` in symmetric
coordinates: its `k`th column is the directional derivative along
`e_k-e_(n+1-k)`, read at the `i`th first-half coordinate. -/
theorem hasDerivAt_discreteBetheResidual_basis {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (i k : Fin (n / 2)) :
    HasDerivAt
      (fun t => discreteBetheResidual Δ N n
        (discreteBetheAffinePath p (discreteSymBasis n k) t)
        (discreteHalfIndex n i))
      (discreteBetheMatrixA Δ N n p i k) 0 := by
  let ri := discreteHalfIndex n i
  let rk := discreteHalfIndex n k
  let v := discreteSymBasis n k
  have hgeneral := hasDerivAt_discreteBetheResidual_path (N := N) (n := n) hΔ p v ri
  have hv : v ri = if i = k then 1 else 0 := by
    simpa [v, ri] using discreteSymBasis_at_half i k
  have hsum1 : (∑ ell : Fin n,
      v ri * thetaPartialFirst Δ (p ri) (p ell)) =
      v ri * ∑ ell : Fin n, thetaPartialFirst Δ (p ri) (p ell) := by
    rw [Finset.mul_sum]
  have hsum2 : (∑ ell : Fin n,
      v ell * thetaPartialSecond Δ (p ri) (p ell)) =
      thetaPartialSecond Δ (p ri) (p rk) -
        thetaPartialSecond Δ (p ri) (p (Fin.rev rk)) := by
    simpa [v, rk] using sum_discreteSymBasis_mul k
      (fun ell => thetaPartialSecond Δ (p ri) (p ell))
  have hcoef : v ri +
      (∑ ell : Fin n,
        (v ri * thetaPartialFirst Δ (p ri) (p ell) +
          v ell * thetaPartialSecond Δ (p ri) (p ell))) / (N : ℝ) =
      discreteBetheMatrixA Δ N n p i k := by
    rw [Finset.sum_add_distrib, hsum1, hsum2, hv]
    by_cases hik : i = k
    · subst k
      simp only
      rw [discreteBetheMatrixA, ite_eq_left rfl]
      have hsplit :
          (∑ ell : Fin n, thetaPartialFirst Δ (p ri) (p ell)) =
            thetaPartialFirst Δ (p ri) (p ri) +
              ∑ ell ∈ Finset.univ.erase ri,
                thetaPartialFirst Δ (p ri) (p ell) := by
        exact (Finset.add_sum_erase Finset.univ
          (fun ell => thetaPartialFirst Δ (p ri) (p ell)) (Finset.mem_univ ri)).symm
      rw [hsplit]
      have hdiag := thetaPartial_diag_sum (Δ := Δ) (x := p ri) hΔ
      have hnum :
          (thetaPartialFirst Δ (p ri) (p ri) +
              ∑ ell ∈ Finset.univ.erase ri,
                thetaPartialFirst Δ (p ri) (p ell)) +
            (thetaPartialSecond Δ (p ri) (p ri) -
              thetaPartialSecond Δ (p ri) (p (Fin.rev ri))) =
          (∑ ell ∈ Finset.univ.erase ri,
                thetaPartialFirst Δ (p ri) (p ell)) -
              thetaPartialSecond Δ (p ri) (p (Fin.rev ri)) := by
        linear_combination hdiag
      simp only [ite_true, one_mul]
      rw [hnum]
      ring
    · simp only [ite_eq_right hik, zero_add]
      rw [discreteBetheMatrixA, ite_eq_right hik]
      ring
  rw [hcoef] at hgeneral
  simpa [v, ri, discreteBetheAffinePath] using hgeneral

/-- The second derivative of the phase difference is the difference of the two
second partial derivatives. -/
theorem deriv_discreteBetheG_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    deriv (fun t => discreteBetheG Δ x t) y =
      thetaPartialSecond Δ x y - thetaPartialSecond Δ (-x) y := by
  have h₁ : DifferentiableAt ℝ (fun t => theta Δ x t) y :=
    (analyticAt_theta_right hΔ x y).differentiableAt
  have h₂ : DifferentiableAt ℝ (fun t => theta Δ (-x) t) y :=
    (analyticAt_theta_right hΔ (-x) y).differentiableAt
  change deriv (fun t => theta Δ x t - theta Δ (-x) t) y = _
  rw [deriv_fun_sub h₁ h₂]
  rfl

/-- The derivative of `G` in the second coordinate is nonnegative on the
negative square. -/
theorem discreteBetheG_deriv_nonneg_neg {Δ x y : ℝ} (hΔ : Δ < -1)
    (hx : x ∈ Icc (-Real.pi) 0) (hy : y ∈ Icc (-Real.pi) 0) :
    0 ≤ deriv (fun t => discreteBetheG Δ x t) y := by
  let lam := lamOf Δ
  have hlam : 0 < lam := lamOf_pos hΔ
  have hx' : x ∈ Icc (-Real.pi) Real.pi :=
    ⟨hx.1, le_trans hx.2 Real.pi_pos.le⟩
  have hy' : y ∈ Icc (-Real.pi) Real.pi :=
    ⟨hy.1, le_trans hy.2 Real.pi_pos.le⟩
  obtain ⟨α, hα, hkx⟩ := (bijOn_kMap hlam).2.2 hx'
  obtain ⟨β, hβ, hky⟩ := (bijOn_kMap hlam).2.2 hy'
  have hαneg : α ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hα.1
    · by_contra h
      have hpos : 0 < α := lt_of_not_ge h
      have hka : kMap lam 0 < kMap lam α := (strictMono_kMap hlam) hpos
      rw [hkx, kMap_zero] at hka
      exact (not_lt_of_ge hx.2) hka
  have hβneg : β ∈ Icc (-Real.pi) 0 := by
    constructor
    · exact hβ.1
    · by_contra h
      have hpos : 0 < β := lt_of_not_ge h
      have hkb : kMap lam 0 < kMap lam β := (strictMono_kMap hlam) hpos
      rw [hky, kMap_zero] at hkb
      exact (not_lt_of_ge hy.2) hkb
  have hsα : Real.sin α ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hαneg.2 hαneg.1
  have hsβ : Real.sin β ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hβneg.2 hβneg.1
  have hcos : Real.cos (-α - β) ≤ Real.cos (α - β) := by
    have htrig : Real.cos (α - β) - Real.cos (-α - β) =
        2 * Real.sin α * Real.sin β := by
      rw [Real.cos_sub, Real.cos_sub]
      simp only [Real.cos_neg, Real.sin_neg]
      ring
    have hprod : 0 ≤ Real.sin α * Real.sin β := mul_nonneg_of_nonpos_of_nonpos hsα hsβ
    linarith
  have hkernel := Xi_le_of_cos_le (by linarith : 0 < 2 * lam) hcos
  have hlam2 : 0 < 2 * lam := by linarith
  have hchain : HasDerivAt
      (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t))
      (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β) β := by
    have hout : HasDerivAt (fun z => discreteBetheG Δ (kMap lam α) z)
        (deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β))
        (kMap lam β) := by
      have hfirst : HasDerivAt (fun z => theta Δ (kMap lam α) z)
          (thetaPartialSecond Δ (kMap lam α) (kMap lam β)) (kMap lam β) :=
        (analyticAt_theta_right hΔ (kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt
      have hsecond : HasDerivAt (fun z => theta Δ (-kMap lam α) z)
          (thetaPartialSecond Δ (-kMap lam α) (kMap lam β)) (kMap lam β) :=
        (analyticAt_theta_right hΔ (-kMap lam α) (kMap lam β)).differentiableAt.hasDerivAt
      rw [deriv_discreteBetheG_right hΔ (kMap lam α) (kMap lam β)]
      change HasDerivAt
        ((fun z => theta Δ (kMap lam α) z) - (fun z => theta Δ (-kMap lam α) z))
        _ _
      exact hfirst.sub hsecond
    exact hout.comp β (hasDerivAt_kMap hlam β)
  have hcompose := hasDerivAt_discreteBetheG_kMap hΔ α β
  have hcoeff := hchain.unique hcompose
  have hpos : 0 < Xi lam β := Xi_pos hlam β
  have hcoeff' :
      deriv (fun z => discreteBetheG Δ (kMap lam α) z) (kMap lam β) * Xi lam β =
        Xi (2 * lam) (α - β) - Xi (2 * lam) (-α - β) := by
    simpa [lam] using hcoeff
  rw [← hkx, ← hky]
  nlinarith [hcoeff']

/-- When `p∈S_n`, its first-half coordinates are negative. -/
theorem discreteS_n_half_coord_neg {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (j : Fin (n / 2)) : p (discreteHalfIndex n j) < 0 := by
  rcases hp with ⟨_, hmono, hsym⟩
  have hlt := hmono (discreteHalfIndex_lt_rev j)
  rw [hsym (discreteHalfIndex n j)] at hlt
  linarith

/-- Off-diagonal entries of `Ã=AB` telescope to the derivative of `G`. -/
theorem discreteBetheMatrixATilde_offdiag_eq {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) (hN : 0 < N)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    discreteBetheMatrixATilde Δ N n p i k =
      (p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k)) *
        deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex n i)) y)
          (p (discreteHalfIndex n k)) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [discreteBetheMatrixATilde, Matrix.mul_apply]
  simp [discreteBetheMatrixB, Matrix.diagonal_apply]
  rw [discreteBetheMatrixA, ite_eq_right hik]
  have hsym := hp (discreteHalfIndex n k)
  rw [hsym]
  simp only [thetaPartialSecond]
  rw [deriv_theta_right_neg, deriv_discreteBetheG_right hΔ]
  simp only [thetaPartialSecond]
  field_simp [hNne]

/-- The off-diagonal entries of `Ã` are nonnegative at every configuration in `S_n`. -/
theorem discreteBetheMatrixATilde_offdiag_nonneg {Δ : ℝ} {N n : ℕ}
    (hΔ : Δ < -1) (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (i k : Fin (n / 2)) (hik : i ≠ k) :
    0 ≤ discreteBetheMatrixATilde Δ N n p i k := by
  have hsym : p ∈ R_n_sym n := hp.2.2
  rw [discreteBetheMatrixATilde_offdiag_eq hΔ p hsym hN i k hik]
  have hxlo : -Real.pi < p (discreteHalfIndex n i) := (hp.1 (discreteHalfIndex n i)).1
  have hylo : -Real.pi < p (discreteHalfIndex n k) := (hp.1 (discreteHalfIndex n k)).1
  have hxhi : p (discreteHalfIndex n i) < 0 := discreteS_n_half_coord_neg hp i
  have hyhi : p (discreteHalfIndex n k) < 0 := discreteS_n_half_coord_neg hp k
  have hgap : 0 ≤ p (discreteHalfNextIndex n k) - p (discreteHalfIndex n k) := by
    have hidx : discreteHalfIndex n k < discreteHalfNextIndex n k := by
      simp only [discreteHalfIndex, discreteHalfNextIndex, Fin.mk_lt_mk]
      omega
    exact le_of_lt (sub_pos.mpr (hp.2.1 hidx))
  have hG : 0 ≤ deriv (fun y => discreteBetheG Δ (p (discreteHalfIndex n i)) y)
      (p (discreteHalfIndex n k)) :=
    discreteBetheG_deriv_nonneg_neg hΔ ⟨le_of_lt hxlo, le_of_lt hxhi⟩
      ⟨le_of_lt hylo, le_of_lt hyhi⟩
  exact mul_nonneg hgap hG

end PottsDiscontinuity.Bethe
