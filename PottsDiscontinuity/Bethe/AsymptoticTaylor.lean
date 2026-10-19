module

public import PottsDiscontinuity.Bethe.AsymptoticRegularity

/-! # Uniform phase Taylor estimates in the original root coordinates -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem fderiv_theta_apply {Δ : ℝ} (hΔ : Δ < -1) (x y a b : ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => theta Δ z.1 z.2) (x, y) (a, b) =
      d1Theta Δ x y * a + d2Theta Δ x y * b := by
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hf : DifferentiableAt ℝ F (x, y) := (analyticAt_theta_xy hΔ x y).differentiableAt
  have h₁ : fderiv ℝ F (x, y) (1, 0) = d1Theta Δ x y := by
    have h := (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)).hasDerivAt.deriv
    simpa only [d1Theta, F, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, Function.comp_def] using h.symm
  have h₂ : fderiv ℝ F (x, y) (0, 1) = d2Theta Δ x y := by
    have h := (hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).hasDerivAt.deriv
    simpa only [d2Theta, F, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Function.comp_def] using h.symm
  have he : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  change fderiv ℝ F (x, y) (a, b) = _
  rw [he, map_add, map_smul, map_smul, h₁, h₂]
  simp only [smul_eq_mul]
  ring

theorem theta_linearized_remainder {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (-Real.pi) Real.pi,
      ∀ y ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      ∀ v ∈ Icc (-Real.pi) Real.pi,
      |theta Δ u v - theta Δ x y - d1Theta Δ x y * (u - x) - d2Theta Δ x y * (v - y)| ≤
        K * (max |u - x| |v - y|) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := theta_quadratic_remainder hΔ
  refine ⟨K, hK, ?_⟩
  intro x hx y hy u hu v hv
  have hi := hb (x, y) ⟨hx, hy⟩ (u, v) ⟨hu, hv⟩
  rw [show (u, v) - (x, y) = (u - x, v - y) from rfl,
    fderiv_theta_apply hΔ] at hi
  simpa only [Prod.norm_def, Real.norm_eq_abs, sub_add_eq_sub_sub] using hi

/-- Summing the uniform second-order errors over at most `N` roots gives
the `O(1/N)` remainder required in the source's offset expansion. -/
theorem theta_sum_linearized_remainder {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N n : ℕ), 0 < N → n ≤ N →
      ∀ (x u : ℝ) (y v : Fin n → ℝ), x ∈ Icc (-Real.pi) Real.pi →
      u ∈ Icc (-Real.pi) Real.pi →
      (∀ j, y j ∈ Icc (-Real.pi) Real.pi) → (∀ j, v j ∈ Icc (-Real.pi) Real.pi) →
      ∀ B : ℝ, 0 ≤ B → |u - x| ≤ B / N → (∀ j, |v j - y j| ≤ B / N) →
      |(∑ j, (theta Δ u (v j) - theta Δ x (y j))) -
        (∑ j, d1Theta Δ x (y j)) * (u - x) -
        ∑ j, d2Theta Δ x (y j) * (v j - y j)| ≤ K * B ^ 2 / N := by
  obtain ⟨K, hK, hb⟩ := theta_linearized_remainder hΔ
  refine ⟨K, hK, ?_⟩
  intro N n hN hn x u y v hx hu hy hv B hB hux hvy
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have heq : (∑ j, (theta Δ u (v j) - theta Δ x (y j))) -
      (∑ j, d1Theta Δ x (y j)) * (u - x) -
      ∑ j, d2Theta Δ x (y j) * (v j - y j) =
      ∑ j, (theta Δ u (v j) - theta Δ x (y j) - d1Theta Δ x (y j) * (u - x) -
        d2Theta Δ x (y j) * (v j - y j)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [heq]
  calc
    _ ≤ ∑ j : Fin n, |theta Δ u (v j) - theta Δ x (y j) - d1Theta Δ x (y j) * (u - x) -
        d2Theta Δ x (y j) * (v j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, K * (B / N) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (hb x hx (y j) (hy j) u hu (v j) (hv j)).trans
      apply mul_le_mul_of_nonneg_left _ hK
      exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _))
        (max_le hux (hvy j)) 2
    _ = (n : ℝ) * (K * (B / N) ^ 2) := by simp
    _ ≤ (N : ℝ) * (K * (B / N) ^ 2) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) (by positivity)
    _ = K * B ^ 2 / N := by field_simp

end PottsDiscontinuity.Bethe
