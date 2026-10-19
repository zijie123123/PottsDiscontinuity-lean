module

public import Mathlib
public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusIrreducible

/-!
# Perron-Frobenius growth: `(1/M) log tr (A ^ M) → log ρ`

For a primitive symmetric nonnegative matrix `A` with largest eigenvalue `ρ = pfRoot A`:

* `tendsto_log_trace_pow_primitive`:  `(1/M) * log (trace (A ^ M)) → log ρ`;
* `tendsto_log_dotProduct_pow_mulVec_primitive`: the same for the pairing `x ⬝ᵥ A ^ M *ᵥ y` with
  nonzero nonnegative vectors `x`, `y`;
* `tendsto_log_sum_entries_pow_primitive`: the same for the sum of all entries of `A ^ M`.

The analytic input is `tendsto_log_sum_mul_pow`: if one weight-positive term `μ i0 = ρ > 0`
dominates, `(1/M) * log (∑ i, μ i ^ M * a i) → log ρ`.
-/

@[expose] public section

open Matrix Filter Topology

namespace PottsDiscontinuity.PerronFrobenius

section Analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑ i, μ i ^ M * a i` divided by `ρ ^ M` tends to `a i0` when `μ i0 = ρ` and all the other
`|μ i|` are `< ρ`. -/
theorem tendsto_sum_mul_pow_div (μ a : ι → ℝ) (i0 : ι) {ρ : ℝ} (hρ : 0 < ρ) (hi0 : μ i0 = ρ)
    (hgap : ∀ i, i ≠ i0 → |μ i| < ρ) :
    Tendsto (fun M : ℕ => (∑ i, μ i ^ M * a i) / ρ ^ M) atTop (𝓝 (a i0)) := by
  have hterm : ∀ i, Tendsto (fun M : ℕ => (μ i / ρ) ^ M * a i) atTop
      (𝓝 (if i = i0 then a i0 else 0)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [ite_true, hi0, div_self hρ.ne', one_pow, one_mul]
      exact tendsto_const_nhds
    · simp only [hi, ite_false]
      have h1 : |μ i / ρ| < 1 := by
        rw [abs_div, abs_of_pos hρ, div_lt_one hρ]
        exact hgap i hi
      have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h1).mul_const (a i)
      simpa using this
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hterm i)
  rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ => a i0)] at hsum
  simp only [Finset.mem_univ, ite_true] at hsum
  refine hsum.congr fun M => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_pow, div_mul_eq_mul_div]

theorem tendsto_log_sum_mul_pow (μ a : ι → ℝ) (i0 : ι) {ρ : ℝ} (hρ : 0 < ρ) (hi0 : μ i0 = ρ)
    (ha : 0 < a i0) (hgap : ∀ i, i ≠ i0 → |μ i| < ρ) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (∑ i, μ i ^ M * a i)) atTop
      (𝓝 (Real.log ρ)) := by
  have hT := tendsto_sum_mul_pow_div μ a i0 hρ hi0 hgap
  have hTpos : ∀ᶠ M : ℕ in atTop, 0 < (∑ i, μ i ^ M * a i) / ρ ^ M :=
    hT.eventually (lt_mem_nhds ha)
  have hlogT : Tendsto (fun M : ℕ => Real.log ((∑ i, μ i ^ M * a i) / ρ ^ M)) atTop
      (𝓝 (Real.log (a i0))) := hT.log ha.ne'
  have hinv : Tendsto (fun M : ℕ => (1 / (M : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h0 : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log ((∑ i, μ i ^ M * a i) / ρ ^ M))
      atTop (𝓝 0) := by
    simpa using hinv.mul hlogT
  have hlim : Tendsto (fun M : ℕ => Real.log ρ +
      (1 / (M : ℝ)) * Real.log ((∑ i, μ i ^ M * a i) / ρ ^ M)) atTop (𝓝 (Real.log ρ)) := by
    simpa using (tendsto_const_nhds (x := Real.log ρ)).add h0
  refine hlim.congr' ?_
  filter_upwards [hTpos, eventually_ge_atTop 1] with M hM hM1
  have hMne : (M : ℝ) ≠ 0 := by positivity
  have hpow : ρ ^ M ≠ 0 := (pow_pos hρ M).ne'
  have hSpos : (∑ i, μ i ^ M * a i) ≠ 0 := by
    intro h
    rw [h, zero_div] at hM
    exact lt_irrefl _ hM
  rw [Real.log_div hSpos hpow, Real.log_pow]
  field_simp
  ring

end Analytic

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}

/-- For a primitive symmetric nonnegative matrix there is a unique eigenvalue index attaining
`pfRoot A`, and all the other eigenvalues are strictly smaller in absolute value. -/
theorem exists_unique_top_eigenvalue (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j) {k : ℕ}
    (hk0 : 0 < k) (hk : ∀ i j, 0 < (A ^ k) i j) :
    ∃ i0, hA.eigenvalues i0 = pfRoot A ∧ ∀ i, i ≠ i0 → |hA.eigenvalues i| < pfRoot A := by
  have hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := fun i j => ⟨k, hk0, hk i j⟩
  obtain ⟨i0, hi0, huniq⟩ := existsUnique_eigenvalues_eq_pfRoot hnn hirr hA
  refine ⟨i0, hi0, fun i hi => ?_⟩
  exact abs_lt_pfRoot_of_primitive hnn hk0 hk hA (hA.eigenvalues_mem_spectrum_real i)
    fun h => hi (huniq i h)

/-- Positivity of the coefficient of the top eigenvalue in the spectral expansion of `x ⬝ᵥ Aᴹ y`
for nonzero nonnegative `x`, `y`. -/
theorem coeff_top_pos (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j)
    (hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j) {i0 : ι} (hi0 : hA.eigenvalues i0 = pfRoot A)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) :
    0 < (eigvec hA i0 ⬝ᵥ x) * (eigvec hA i0 ⬝ᵥ y) := by
  obtain ⟨u, hu, hu'⟩ := exists_pos_eigenvector hnn hirr hA
  have hb : A *ᵥ eigvec hA i0 = pfRoot A • eigvec hA i0 := by rw [mulVec_eigvec, hi0]
  obtain ⟨c, hc⟩ := eigenspace_pfRoot_eq hnn hirr hA hu hu' hb
  have hbb : eigvec hA i0 ⬝ᵥ eigvec hA i0 = 1 := by simpa using eigvec_dot hA i0 i0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hc] at hbb
    simp at hbb
  have hpair : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → z ≠ 0 → 0 < u ⬝ᵥ z := by
    intro z hz hz0
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz0 (funext hcon)
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hu i).le (hz i)) ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (hu j) (lt_of_le_of_ne (hz j) (Ne.symm hj))
  rw [hc, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have h1 := hpair x hx hx0
  have h2 := hpair y hy hy0
  have h3 : 0 < c * c := mul_self_pos.2 hc0
  have := mul_pos h3 (mul_pos h1 h2)
  nlinarith

/-- Growth of the bilinear forms `x ⬝ᵥ Aᴹ y` for a primitive symmetric nonnegative matrix. -/
theorem tendsto_log_dotProduct_pow_mulVec_primitive (hA : A.IsHermitian) (hprim : A.IsPrimitive)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0) (hy : ∀ i, 0 ≤ y i) (hy0 : y ≠ 0) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (x ⬝ᵥ ((A ^ M) *ᵥ y))) atTop
      (𝓝 (Real.log (pfRoot A))) := by
  obtain ⟨k, hk0, hk⟩ := hprim.exists_pos_pow
  have hnn := hprim.nonneg
  have hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := fun i j => ⟨k, hk0, hk i j⟩
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  obtain ⟨i0, hi0, hgap⟩ := exists_unique_top_eigenvalue hA hnn hk0 hk
  have := tendsto_log_sum_mul_pow hA.eigenvalues (fun i => (eigvec hA i ⬝ᵥ x) * (eigvec hA i ⬝ᵥ y))
    i0 hρ hi0 (coeff_top_pos hA hnn hirr hi0 hx hx0 hy hy0) hgap
  refine this.congr fun M => ?_
  rw [dotProduct_pow_mulVec hA]

theorem tendsto_log_trace_pow_primitive (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (A ^ M).trace) atTop
      (𝓝 (Real.log (pfRoot A))) := by
  obtain ⟨k, hk0, hk⟩ := hprim.exists_pos_pow
  have hnn := hprim.nonneg
  have hirr : ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := fun i j => ⟨k, hk0, hk i j⟩
  have hρ := pfRoot_pos_of_irreducible hnn hirr hA
  obtain ⟨i0, hi0, hgap⟩ := exists_unique_top_eigenvalue hA hnn hk0 hk
  have := tendsto_log_sum_mul_pow hA.eigenvalues (fun _ => (1 : ℝ)) i0 hρ hi0 one_pos hgap
  refine this.congr fun M => ?_
  rw [trace_pow_eq_sum hA]
  simp

theorem tendsto_log_sum_entries_pow_primitive (hA : A.IsHermitian) (hprim : A.IsPrimitive) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (∑ i, ∑ j, (A ^ M) i j)) atTop
      (𝓝 (Real.log (pfRoot A))) := by
  have h := tendsto_log_dotProduct_pow_mulVec_primitive hA hprim (x := fun _ => 1) (y := fun _ => 1)
    (fun _ => zero_le_one) (fun h => one_ne_zero (congrFun h (Classical.arbitrary ι)))
    (fun _ => zero_le_one) (fun h => one_ne_zero (congrFun h (Classical.arbitrary ι)))
  refine h.congr fun M => ?_
  simp [dotProduct, mulVec]

end Matrix

end PottsDiscontinuity.PerronFrobenius
