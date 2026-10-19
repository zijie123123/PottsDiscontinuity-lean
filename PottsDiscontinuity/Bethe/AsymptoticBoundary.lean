module

public import PottsDiscontinuity.Bethe.AsymptoticSumSplit

/-! # Exact boundary and bulk decomposition for both offset parities -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

noncomputable def offsetLowerRoot (N r : ℕ) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) : ℝ :=
  p ⟨j.val + r / 2, by omega⟩

noncomputable def offsetUpperRoot (N r : ℕ) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) : ℝ :=
  p ⟨j.val + (r - r / 2), by omega⟩

theorem alignedRoot_eq_mean {N r : ℕ} (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j =
      (offsetLowerRoot N r hr p j + offsetUpperRoot N r hr p j) / 2 :=
  alignedRoot_average hr p j

/-- The averaged contributions of roots outside the two shifted bulk
blocks. For even deficit both blocks coincide. For odd deficit the outer
root on each side has weight one half. -/
noncomputable def offsetBoundarySum (Δ : ℝ) (N r : ℕ) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (x : ℝ) : ℝ :=
  ((∑ k : Fin (r / 2), theta Δ x (p ⟨k.val, by omega⟩)) +
    (∑ k : Fin (r - r / 2), theta Δ x (p ⟨r / 2 + (N / 2 - r) + k.val, by omega⟩)) +
    (∑ k : Fin (r - r / 2), theta Δ x (p ⟨k.val, by omega⟩)) +
    (∑ k : Fin (r / 2), theta Δ x (p ⟨(r - r / 2) + (N / 2 - r) + k.val, by omega⟩))) / 2

theorem sum_theta_eq_bulk_add_boundary {Δ : ℝ} {N r : ℕ} (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (x : ℝ) :
    (∑ k, theta Δ x (p k)) =
      ((∑ k, theta Δ x (offsetLowerRoot N r hr p k)) +
        (∑ k, theta Δ x (offsetUpperRoot N r hr p k))) / 2 +
        offsetBoundarySum Δ N r hr p x := by
  have ha := sum_fin_split_block
    (show r / 2 + (N / 2 - r) + (r - r / 2) = N / 2 by omega)
    (fun k => theta Δ x (p k))
  have hb := sum_fin_split_block
    (show (r - r / 2) + (N / 2 - r) + r / 2 = N / 2 by omega)
    (fun k => theta Δ x (p k))
  dsimp only [offsetBoundarySum, offsetLowerRoot, offsetUpperRoot]
  linarith only [ha, hb]

theorem offsetDisplacement_bethe_bulk_boundary {Δ : ℝ} {N r : ℕ} (h4 : 4 ∣ N)
    (hr : r ≤ N / 2) {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : DiscreteBetheEquation Δ N (N / 2) p)
    (hq : DiscreteBetheEquation Δ N (N / 2 - r) q) (j : Fin (N / 2 - r)) :
    offsetDisplacement N r h4 hr p q j =
      (offsetBoundarySum Δ N r hr p (offsetLowerRoot N r hr p j) +
        offsetBoundarySum Δ N r hr p (offsetUpperRoot N r hr p j)) / 2 +
      ∑ k, ((theta Δ (offsetLowerRoot N r hr p j) (offsetLowerRoot N r hr p k) +
        theta Δ (offsetLowerRoot N r hr p j) (offsetUpperRoot N r hr p k) +
        theta Δ (offsetUpperRoot N r hr p j) (offsetLowerRoot N r hr p k) +
        theta Δ (offsetUpperRoot N r hr p j) (offsetUpperRoot N r hr p k)) / 4 -
        theta Δ (q j) (q k)) := by
  have he := offsetDisplacement_bethe_average h4 hr hp hq j
  change offsetDisplacement N r h4 hr p q j =
    ((∑ k, theta Δ (offsetLowerRoot N r hr p j) (p k)) +
      ∑ k, theta Δ (offsetUpperRoot N r hr p j) (p k)) / 2 - ∑ k, theta Δ (q j) (q k) at he
  rw [sum_theta_eq_bulk_add_boundary hr, sum_theta_eq_bulk_add_boundary hr] at he
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  linarith only [he]

end PottsDiscontinuity.Bethe
