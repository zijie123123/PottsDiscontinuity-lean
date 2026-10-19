module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0
public import PottsDiscontinuity.BetheAnsatz.BoundaryLimit

/-!
# The corrected T₀ limit

The singular constant-word factors are first combined. Their regularized sum has
the positive seam contribution `c²N`, matching the corrected bracket in `lem:T0`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The continuous extension of `L(w) * (w^(-N) - 1)` at `w = 1`. -/
noncomputable def t0BoundaryRegularized (c : ℝ) (N : ℕ) (w : ℂ) : ℂ :=
  (1 - w + (c : ℂ) ^ 2 * w) * (∑ k ∈ range N, w ^ k) / w ^ N

/-- Regularized scalar multiplying a permutation in the constant-word limit. -/
noncomputable def t0ScalarRegularized (c : ℝ) (N : ℕ) (t : ℝ) (seam : Prop) : ℂ :=
  (2 - (c : ℂ) ^ 2) +
    if seam then t0BoundaryRegularized c N (z t) else 0

/-- The scalar factor in the exact T₀ expression equals its regularization off the pole. -/
theorem t0Scalar_eq_regularized {c : ℝ} {N : ℕ} {t : ℝ} {seam : Prop}
    [Decidable seam] (hzt : z t ≠ 1) :
    M c (z t) + L c (z t) *
        (if seam then (z t ^ N)⁻¹ else 1) = t0ScalarRegularized c N t seam := by
  have hsum : M c (z t) + L c (z t) = 2 - (c : ℂ) ^ 2 := by
    rw [add_comm]
    exact L_add_M c hzt
  by_cases hs : seam
  · simp only [ite_eq_left hs, t0ScalarRegularized]
    rw [constant_words_boundary_decomposition c (z t) N, hsum,
      L_mul_inv_pow_sub_one c N (z_ne_zero t) hzt]
    rfl
  · simp only [ite_eq_right hs, t0ScalarRegularized]
    simp only [mul_one, add_zero]
    exact hsum

/-- Continuity of the regularized scalar at every momentum. -/
theorem continuous_t0ScalarRegularized (c : ℝ) (N : ℕ) (seam : Prop) :
    Continuous (fun t : ℝ => t0ScalarRegularized c N t seam) := by
  classical
  have hz : Continuous (fun t : ℝ => z t) := by
    unfold z
    fun_prop
  have hnum : Continuous (fun t : ℝ => 1 - z t + (c : ℂ) ^ 2 * z t) := by
    fun_prop
  have hsum : Continuous (fun t : ℝ => ∑ k ∈ range N, z t ^ k) := by
    apply continuous_finsetSum
    intro k hk
    exact hz.pow k
  have hden : Continuous (fun t : ℝ => z t ^ N) := hz.pow N
  have hquot : Continuous (fun t : ℝ =>
      (1 - z t + (c : ℂ) ^ 2 * z t) * (∑ k ∈ range N, z t ^ k) / z t ^ N) :=
    (hnum.mul hsum).div hden (fun t => pow_ne_zero N (z_ne_zero t))
  by_cases hs : seam
  · simp only [t0ScalarRegularized, ite_eq_left hs]
    change Continuous ((fun _ : ℝ => (2 - (c : ℂ) ^ 2)) +
      fun t : ℝ => t0BoundaryRegularized c N (z t))
    simpa [t0BoundaryRegularized] using (continuous_const.add hquot)
  · simpa [t0ScalarRegularized, hs] using (continuous_const : Continuous fun _ : ℝ =>
      (2 - (c : ℂ) ^ 2))

/-- The finite regularized sum whose value at zero is the T₀ limit. -/
noncomputable def t0RegularizedSum {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ) : ℂ :=
  (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
    ∑ σ, amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
      planeWave p σ x * t0ScalarRegularized c N t (σ.symm l = Fin.last n)

/-- The regularized finite sum is continuous at the limiting parameter. -/
theorem continuous_t0RegularizedSum {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    Continuous (fun t : ℝ => t0RegularizedSum (N := N) c x p l t) := by
  have hphase (σ : Equiv.Perm (Fin (n + 1))) :
      Continuous (fun t : ℝ => positionPhase t (x (σ.symm l))) := by
    unfold positionPhase
    fun_prop
  have hsum : Continuous (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
          planeWave p σ x * t0ScalarRegularized c N t (σ.symm l = Fin.last n)) := by
    apply continuous_finsetSum
    intro σ hσ
    exact ((continuous_const.mul (hphase σ)).mul continuous_const).mul
      (continuous_t0ScalarRegularized c N (σ.symm l = Fin.last n))
  unfold t0RegularizedSum
  exact continuous_const.mul hsum

/-- Near zero, the exponential is in the principal momentum interval and is not one. -/
theorem eventually_z_ne_one_zero :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), z t ≠ 1 := by
  have hsmall : Set.Ioo (-Real.pi) Real.pi ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
  have hsmall' : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ∈ Set.Ioo (-Real.pi) Real.pi :=
    Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-Real.pi) Real.pi from hsmall)
  filter_upwards [hsmall', self_mem_nhdsWithin] with t ht ht0
  exact z_ne_one ht ht0

/-- The explicit zero value of the regularized sum. -/
theorem t0RegularizedSum_zero {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    t0RegularizedSum (N := N) c x p l 0 =
      (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
        ∑ σ, amplitude (anisotropy c) p σ * planeWave p σ x *
          ((2 - (c : ℂ) ^ 2) +
            if σ.symm l = Fin.last n then (c : ℂ) ^ 2 * (N : ℂ) else 0) := by
  unfold t0RegularizedSum
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [t0ScalarRegularized, t0BoundaryRegularized, positionPhase, z]

/-- The full corrected T₀ limit, with amplitudes fixed at the original Bethe roots. -/
theorem tendsto_constantWordSumPerturbed {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    Tendsto (fun t : ℝ => constantWordSumPerturbed (N := N) c x p l t)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j))) *
        ∑ σ, amplitude (anisotropy c) p σ * planeWave p σ x *
          ((2 - (c : ℂ) ^ 2) +
            if σ.symm l = Fin.last n then (c : ℂ) ^ 2 * (N : ℂ) else 0))) := by
  have hregular :
      (fun t : ℝ => constantWordSumPerturbed (N := N) c x p l t) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun t => t0RegularizedSum (N := N) c x p l t := by
    filter_upwards [eventually_z_ne_one_zero] with t hzt
    rw [constantWordSumPerturbed_eq hc x p hp hinj l hpl hBE t]
    unfold t0RegularizedSum
    congr 1
    apply Finset.sum_congr rfl
    intro σ hσ
    exact congrArg (fun a : ℂ =>
      amplitude (anisotropy c) p σ * positionPhase t (x (σ.symm l)) *
        planeWave p σ x * a)
      (t0Scalar_eq_regularized (c := c) (N := N) (t := t)
        (seam := σ.symm l = Fin.last n) hzt)
  have hcont := continuous_t0RegularizedSum (N := N) c x p l
  have hAt : ContinuousAt (fun t : ℝ => t0RegularizedSum (N := N) c x p l t) 0 :=
    hcont.continuousAt
  have ht0 : Tendsto (fun t : ℝ => t0RegularizedSum (N := N) c x p l t)
      (𝓝 (0 : ℝ)) (𝓝 (t0RegularizedSum (N := N) c x p l 0)) := hAt.tendsto
  have ht := ht0.mono_left (nhdsWithin_le_nhds :
    𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  rw [t0RegularizedSum_zero] at ht
  apply ht.congr'
  filter_upwards [hregular] with t ht
  exact ht.symm

end PottsDiscontinuity.BetheAnsatz
