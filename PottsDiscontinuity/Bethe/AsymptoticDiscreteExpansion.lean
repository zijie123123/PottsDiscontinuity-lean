module

public import PottsDiscontinuity.Bethe.AsymptoticBoundary
public import PottsDiscontinuity.Bethe.AsymptoticMeanTaylor

/-! # The discrete offset equation with a uniform Taylor error -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The bulk expansion for actual Bethe solutions, expressed with the
averaged boundary contribution. The alignment premises are quantitative
estimates to be supplied by the non-circular alignment lemmas. -/
theorem offset_bethe_taylor {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N r : ℕ) (h4 : 4 ∣ N) (hr : r ≤ N / 2), 0 < N →
      ∀ (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ),
      p ∈ S_n (N / 2) → q ∈ S_n (N / 2 - r) →
      DiscreteBetheEquation Δ N (N / 2) p → DiscreteBetheEquation Δ N (N / 2 - r) q →
      ∀ B : ℝ, 0 ≤ B →
      (∀ k, |offsetLowerRoot N r hr p k - q k| ≤ B / N ∧
        |offsetUpperRoot N r hr p k - q k| ≤ B / N) →
      ∀ j,
      |offsetDisplacement N r h4 hr p q j -
        (offsetBoundarySum Δ N r hr p (offsetLowerRoot N r hr p j) +
          offsetBoundarySum Δ N r hr p (offsetUpperRoot N r hr p j)) / 2 +
        ((∑ k, d1Theta Δ (q j) (q k)) / N) * offsetDisplacement N r h4 hr p q j +
        (∑ k, d2Theta Δ (q j) (q k) * offsetDisplacement N r h4 hr p q k) / N| ≤
        K * B ^ 2 / N := by
  obtain ⟨K, hK, ht⟩ := theta_sum_mean_remainder hΔ
  refine ⟨K, hK, ?_⟩
  intro N r h4 hr hN p q hp hq hpBE hqBE B hB hnear j
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmem (k : Fin (N / 2)) : p k ∈ Icc (-Real.pi) Real.pi := ⟨(hp.1 k).1.le, (hp.1 k).2.le⟩
  have hqmem (k : Fin (N / 2 - r)) : q k ∈ Icc (-Real.pi) Real.pi := ⟨(hq.1 k).1.le, (hq.1 k).2.le⟩
  have heps (k : Fin (N / 2 - r)) :
      (offsetLowerRoot N r hr p k + offsetUpperRoot N r hr p k) / 2 - q k =
        -offsetDisplacement N r h4 hr p q k / (N : ℝ) := by
    rw [offsetDisplacement_eq_alignedRoot, alignedRoot_eq_mean hr]
    field_simp
    ring
  have he := ht N (N / 2 - r) hN (by omega) (q j)
    (offsetLowerRoot N r hr p j) (offsetUpperRoot N r hr p j)
    q (offsetLowerRoot N r hr p) (offsetUpperRoot N r hr p)
    (hqmem j) (hmem _) (hmem _) hqmem (fun k => hmem _) (fun k => hmem _)
    B hB (hnear j).1 (hnear j).2 (fun k => (hnear k).1) (fun k => (hnear k).2)
  have hb := offsetDisplacement_bethe_bulk_boundary h4 hr hpBE hqBE j
  have hbulk : (∑ k, ((theta Δ (offsetLowerRoot N r hr p j) (offsetLowerRoot N r hr p k) +
      theta Δ (offsetLowerRoot N r hr p j) (offsetUpperRoot N r hr p k) +
      theta Δ (offsetUpperRoot N r hr p j) (offsetLowerRoot N r hr p k) +
      theta Δ (offsetUpperRoot N r hr p j) (offsetUpperRoot N r hr p k)) / 4 - theta Δ (q j) (q k))) =
      offsetDisplacement N r h4 hr p q j -
        (offsetBoundarySum Δ N r hr p (offsetLowerRoot N r hr p j) +
          offsetBoundarySum Δ N r hr p (offsetUpperRoot N r hr p j)) / 2 := by linarith only [hb]
  rw [hbulk, heps j] at he
  simp_rw [heps, mul_div, mul_neg, neg_div] at he
  rw [Finset.sum_neg_distrib, ← Finset.sum_div] at he
  convert he using 1; ring

end PottsDiscontinuity.Bethe
