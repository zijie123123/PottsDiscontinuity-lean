module

public import PottsDiscontinuity.Bethe.AsymptoticBoundary

/-! # From mean alignment to alignment of both shifted roots -/

@[expose] public section

namespace PottsDiscontinuity.Bethe

theorem offsetLowerUpper_gap {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) {D : ℝ} (hD : 0 ≤ D)
    (hgap : ∀ j (hj : j + 1 < N / 2),
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N)
    (j : Fin (N / 2 - r)) :
    offsetLowerRoot N r hr p j ≤ offsetUpperRoot N r hr p j ∧
      offsetUpperRoot N r hr p j - offsetLowerRoot N r hr p j ≤ D / N := by
  constructor
  · apply hp.2.1.monotone
    change j.val + r / 2 ≤ j.val + (r - r / 2)
    omega
  · rcases (show r - r / 2 = r / 2 ∨ r - r / 2 = r / 2 + 1 by omega) with he | ho
    · have hi : (⟨j.val + (r - r / 2), by omega⟩ : Fin (N / 2)) =
          ⟨j.val + r / 2, by omega⟩ := Fin.ext (by
            change j.val + (r - r / 2) = j.val + r / 2
            omega)
      simp only [offsetLowerRoot, offsetUpperRoot, hi, sub_self]
      exact div_nonneg hD (Nat.cast_nonneg N)
    · have hi : (⟨j.val + (r - r / 2), by omega⟩ : Fin (N / 2)) =
          ⟨j.val + r / 2 + 1, by omega⟩ := Fin.ext (by
            change j.val + (r - r / 2) = j.val + r / 2 + 1
            omega)
      simpa only [offsetLowerRoot, offsetUpperRoot, hi] using hgap (j.val + r / 2) (by omega)

theorem offset_shifted_roots_near {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hN : 0 < N) {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : p ∈ S_n (N / 2)) {B D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ j, |offsetDisplacement N r h4 hr p q j| ≤ B)
    (hgap : ∀ j (hj : j + 1 < N / 2),
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N) :
    ∀ j, |offsetLowerRoot N r hr p j - q j| ≤ (B + D) / N ∧
      |offsetUpperRoot N r hr p j - q j| ≤ (B + D) / N := by
  intro j
  have hg := offsetLowerUpper_gap hr hp hD hgap j
  have he := hbound j
  rw [offsetDisplacement_eq_alignedRoot, abs_mul, abs_of_pos (Nat.cast_pos.mpr hN)] at he
  have hm : |q j - alignedRoot N r hr p j| ≤ B / (N : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr (by simpa only [mul_comm] using he)
  rw [alignedRoot_eq_mean hr] at hm
  rcases abs_le.mp hm with ⟨hm₁, hm₂⟩
  rw [add_div]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [hg.1, hg.2]

end PottsDiscontinuity.Bethe
