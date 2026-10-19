module

public import PottsDiscontinuity.Bethe.Prop21Positivity
public import PottsDiscontinuity.Bethe.Prop21Regularity

/-! # Compact derivative estimates for the offset argument

All bounds here are for a fixed `Δ < -1`, which is the parameter scope of
Theorem 2.9. They follow from the already proved analyticity statements.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem exists_lipschitzOnWith_inv_rho {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K, LipschitzOnWith K (fun x => (rho Δ x)⁻¹) (Icc (-Real.pi) Real.pi) := by
  have ha (x : ℝ) : AnalyticAt ℝ (fun y => (rho Δ y)⁻¹) x :=
    (analyticAt_rho hΔ x).inv (rho_pos hΔ x).ne'
  have h : ContDiff ℝ 1 (fun x => (rho Δ x)⁻¹) :=
    contDiff_iff_contDiffAt.mpr (fun x => (ha x).contDiffAt)
  exact h.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc

/-- The derivative of the two-variable phase is Lipschitz on the physical
square. This supplies a uniform quadratic Taylor remainder. -/
theorem exists_lipschitzOnWith_fderiv_theta {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K, LipschitzOnWith K (fderiv ℝ (fun z : ℝ × ℝ => theta Δ z.1 z.2))
      ((Icc (-Real.pi) Real.pi) ×ˢ (Icc (-Real.pi) Real.pi)) := by
  have h : ContDiff ℝ 2 (fun z : ℝ × ℝ => theta Δ z.1 z.2) :=
    contDiff_iff_contDiffAt.mpr (fun z => (analyticAt_theta_xy hΔ z.1 z.2).contDiffAt)
  have hd : ContDiff ℝ 1 (fderiv ℝ (fun z : ℝ × ℝ => theta Δ z.1 z.2)) :=
    h.fderiv_right (by norm_num)
  exact hd.contDiffOn.exists_lipschitzOnWith one_ne_zero
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)

/-- A single constant bounds all second-order remainders on the physical
square; it depends only on the fixed phase parameter. -/
theorem theta_quadratic_remainder {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ ((Icc (-Real.pi) Real.pi) ×ˢ (Icc (-Real.pi) Real.pi)),
      ∀ y ∈ ((Icc (-Real.pi) Real.pi) ×ˢ (Icc (-Real.pi) Real.pi)),
      |theta Δ y.1 y.2 - theta Δ x.1 x.2 -
        fderiv ℝ (fun z : ℝ × ℝ => theta Δ z.1 z.2) x (y - x)| ≤ K * ‖y - x‖ ^ 2 := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_fderiv_theta hΔ
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx y hy
  let F : ℝ × ℝ → ℝ := fun z => theta Δ z.1 z.2
  have hconv : Convex ℝ ((Icc (-Real.pi) Real.pi) ×ˢ (Icc (-Real.pi) Real.pi)) :=
    (convex_Icc _ _).prod (convex_Icc _ _)
  have hseg := hconv.segment_subset hx hy
  have hd (z : ℝ × ℝ) (_hz : z ∈ segment ℝ x y) : DifferentiableAt ℝ F z :=
    (analyticAt_theta_xy hΔ z.1 z.2).differentiableAt
  have hbound (z : ℝ × ℝ) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    have hb := hK.dist_le_mul z (hseg hz) x hx
    rw [dist_eq_norm, dist_eq_norm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have hb := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le' hd hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hb

end PottsDiscontinuity.Bethe
