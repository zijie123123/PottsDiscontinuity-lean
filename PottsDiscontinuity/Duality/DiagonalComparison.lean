module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.ConnectionSymmetry
public import PottsDiscontinuity.Duality.DiagonalRate

/-! FKG and the actual free-limit symmetries compare every direction with the
exact frozen diagonal sequence. The fourth power accounts for two reflections. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.Duality

open FK

lemma twoPoint_pow_four_le_diagonal (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (x : LatticeVertex) :
    twoPoint μ x ^ 4 ≤ twoPoint μ (2 * x.1, 2 * x.1) := by
  have h₁ := twoPoint_mul_le θ μ hμ x (x.1, -x.2)
  rw [twoPoint_flipY θ μ hμ] at h₁
  have heq : x + (x.1, -x.2) = (2 * x.1, 0) := by ext <;> simp; ring
  rw [heq, ← pow_two] at h₁
  have h₂ := twoPoint_mul_le θ μ hμ (2 * x.1, 0) (0, 2 * x.1)
  have hrot := twoPoint_quarterTurn θ μ hμ (2 * x.1, 0)
  simp only [neg_zero] at hrot
  rw [hrot, ← pow_two] at h₂
  have heq₂ : (2 * x.1, 0) + (0, 2 * x.1) = (2 * x.1, 2 * x.1) := by simp
  rw [heq₂] at h₂
  calc
    twoPoint μ x ^ 4 = (twoPoint μ x ^ 2) ^ 2 := by ring
    _ ≤ twoPoint μ (2 * x.1, 0) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ ≤ _ := h₂

lemma twoPoint_pow_four_le_diagonalSite_fst (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (x : LatticeVertex) :
    twoPoint μ x ^ 4 ≤ twoPoint μ (diagonalSite (4 * x.1.natAbs)) := by
  have hd (m : ℕ) : diagonalSite (4 * m) = (2 * (m : ℤ), 2 * (m : ℤ)) := by
    unfold diagonalSite
    have : 4 * m / 2 = 2 * m := by omega
    simp only [this, Nat.cast_mul, Nat.cast_ofNat]
  rw [hd]
  by_cases hx : 0 ≤ x.1
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hx] using
      twoPoint_pow_four_le_diagonal θ μ hμ x
  · have heq : (2 * (x.1.natAbs : ℤ), 2 * (x.1.natAbs : ℤ)) =
        -(2 * x.1, 2 * x.1) := by
      simp only [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hx), Prod.neg_mk]
      ring_nf
    rw [heq, twoPoint_neg θ μ hμ]
    exact twoPoint_pow_four_le_diagonal θ μ hμ x

/-- A uniform comparison with the diagonal at four times the larger coordinate. -/
theorem twoPoint_pow_four_le_diagonalSite (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (x : LatticeVertex) :
    twoPoint μ x ^ 4 ≤ twoPoint μ
      (diagonalSite (4 * max x.1.natAbs x.2.natAbs)) := by
  by_cases hx : x.2.natAbs ≤ x.1.natAbs
  · rw [max_eq_left hx]
    exact twoPoint_pow_four_le_diagonalSite_fst θ μ hμ x
  · rw [max_eq_right (le_of_not_ge hx)]
    have h := twoPoint_pow_four_le_diagonalSite_fst θ μ hμ (-x.2, x.1)
    simpa only [Int.natAbs_neg, twoPoint_quarterTurn θ μ hμ] using h

/-- Diagonal exponential decay implies exponential decay in every lattice direction.
The constants reflect the exact frozen diagonal indexing. -/
theorem free_exponential_decay_of_diagonal_bound (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hdiag : ∀ n : ℕ, twoPoint μ (diagonalSite n) ≤ C * Real.exp (-c * (n : ℝ))) :
    ∀ x : LatticeVertex, twoPoint μ x ≤
      (C + 1) * Real.exp (-(c / 2) * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)) := by
  intro x
  let m := max x.1.natAbs x.2.natAbs
  let s : ℝ := |(x.1 : ℝ)| + |(x.2 : ℝ)|
  have hm₁ : |(x.1 : ℝ)| ≤ (m : ℝ) := by
    have hi : |x.1| ≤ (m : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show x.1.natAbs ≤ m from le_max_left _ _)
    exact_mod_cast hi
  have hm₂ : |(x.2 : ℝ)| ≤ (m : ℝ) := by
    have hi : |x.2| ≤ (m : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show x.2.natAbs ≤ m from le_max_right _ _)
    exact_mod_cast hi
  have hs : s ≤ 2 * (m : ℝ) := by dsimp [s]; linarith
  have hcoeff : C ≤ (C + 1) ^ 4 := by
    have h₁ : 1 ≤ C + 1 := by linarith
    have h₂ : C + 1 ≤ (C + 1) ^ 4 := by
      exact le_self_pow₀ h₁ (by decide : 4 ≠ 0)
    linarith
  apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0)
    (mul_nonneg (by linarith : 0 ≤ C + 1) (Real.exp_nonneg _))
  calc
    twoPoint μ x ^ 4 ≤ twoPoint μ (diagonalSite (4 * m)) :=
      twoPoint_pow_four_le_diagonalSite θ μ hμ x
    _ ≤ C * Real.exp (-c * ((4 * m : ℕ) : ℝ)) := hdiag _
    _ ≤ (C + 1) ^ 4 * Real.exp (-2 * c * s) := by
      apply mul_le_mul hcoeff (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _)
        (by positivity)
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left hs hc.le]
    _ = ((C + 1) * Real.exp (-(c / 2) * s)) ^ 4 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring

/-- A positive logarithmic rate along the frozen diagonal implies full ℓ¹ decay
for every actual free infinite-volume limit. -/
theorem free_exponential_decay_of_pos_diagonal_rate (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
      Real.log (twoPoint μ (diagonalSite n))) atTop (𝓝 L)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : LatticeVertex,
      twoPoint μ x ≤ C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)) := by
  have := hμ.1
  obtain ⟨C, c, hC, hc, hb⟩ := diagonal_exponential_bound_of_pos_rate μ L hL hrate
  exact ⟨C + 1, c / 2, by positivity, by positivity,
    free_exponential_decay_of_diagonal_bound θ μ hμ C c hC hc hb⟩

end PottsDiscontinuity.Duality
