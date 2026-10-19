module

public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Spacing errors and the non-circular offset recurrence -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem abs_inv_sub_inv_le {a b m E : ℝ} (hm : 0 < m) (ha : m / 2 ≤ a)
    (hb : m ≤ b) (herror : |a - b| ≤ E) :
    |a⁻¹ - b⁻¹| ≤ 2 * E / m ^ 2 := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := hm.trans_le hb
  have hE : 0 ≤ E := (abs_nonneg _).trans herror
  have hden : m / 2 * m ≤ a * b := mul_le_mul ha hb hm.le hap.le
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hap hbp), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hap hbp)).mpr
  apply herror.trans
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hm)]
  nlinarith only [mul_le_mul_of_nonneg_left hden hE]

/-- Interior spacing regularity derived directly from the density formula.
The error is proportional to the uniform density error; a rate `O(1/N)` for
that error yields (2.6). -/
theorem root_spacing_error {N k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    {Δ m E : ℝ} (hm : 0 < m) (hsmall : E ≤ m / 2)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m ≤ rho Δ x)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ E)
    (j : Fin k) :
    |(N : ℝ) * (p j.succ - p j.castSucc) - (rho Δ (p j.castSucc))⁻¹| ≤
      2 * E / m ^ 2 := by
  have hgap : p j.castSucc < p j.succ :=
    hp.2.1 (show j.castSucc < j.succ from by change j.val < j.val + 1; omega)
  have hx : p j.castSucc ∈ Icc (-Real.pi) Real.pi :=
    ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩
  have he := herror _ hx
  rw [rootStepDensity_interior hp hs j ⟨le_rfl, hgap⟩] at he
  have hlow := hlower _ hx
  have hc : m / 2 ≤ 1 / ((N : ℝ) * (p j.succ - p j.castSucc)) := by
    have := (abs_le.mp he).1
    linarith
  have hi := abs_inv_sub_inv_le hm hc hlow he
  simpa only [one_div, inv_inv] using hi

/-- The precise local recurrence needed before any alignment bound is known.
It compares the two spacings at their own roots. No bound on the offsets is
used here. -/
theorem offset_increment_from_spacing {Δ N x x' y y' A B : ℝ}
    (hN : 0 < N) {L : NNReal}
    (hL : LipschitzOnWith L (fun z => (rho Δ z)⁻¹) (Icc (-Real.pi) Real.pi))
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hy : y ∈ Icc (-Real.pi) Real.pi)
    (hp : |N * (x' - x) - (rho Δ x)⁻¹| ≤ A / N)
    (hq : |N * (y' - y) - (rho Δ y)⁻¹| ≤ B / N) :
    |N * (y' - x') - N * (y - x)| ≤
      (A + B) / N + (L : ℝ) / N * |N * (y - x)| := by
  have hlip := hL.dist_le_mul y hy x hx
  rw [Real.dist_eq, Real.dist_eq] at hlip
  have heq : N * (y' - x') - N * (y - x) =
      (N * (y' - y) - (rho Δ y)⁻¹) - (N * (x' - x) - (rho Δ x)⁻¹) +
        ((rho Δ y)⁻¹ - (rho Δ x)⁻¹) := by ring
  rw [heq]
  calc
    _ ≤ |N * (y' - y) - (rho Δ y)⁻¹| + |N * (x' - x) - (rho Δ x)⁻¹| +
        |(rho Δ y)⁻¹ - (rho Δ x)⁻¹| := by
      have h1 := abs_add_le (N * (y' - y) - (rho Δ y)⁻¹ - (N * (x' - x) - (rho Δ x)⁻¹))
        ((rho Δ y)⁻¹ - (rho Δ x)⁻¹)
      have h2 := abs_sub (N * (y' - y) - (rho Δ y)⁻¹) (N * (x' - x) - (rho Δ x)⁻¹)
      linarith only [h1, h2]
    _ ≤ B / N + A / N + (L : ℝ) * |y - x| := add_le_add (add_le_add hq hp) hlip
    _ = (A + B) / N + (L : ℝ) / N * |N * (y - x)| := by
      rw [abs_mul, abs_of_pos hN]
      field_simp
      ring

end PottsDiscontinuity.Bethe
