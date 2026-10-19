module

public import PottsDiscontinuity.Bethe.AsymptoticGeometry

/-! # Central symmetry and separation of the positive roots -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem ratio_central_pair {m : ℕ} (hm : 0 < m) {p : Fin (2 * m) → ℝ}
    (hp : p ∈ S_n (2 * m)) :
    p ⟨m - 1, by omega⟩ = -p ⟨m, by omega⟩ := by
  have he : Fin.rev (⟨m, by omega⟩ : Fin (2 * m)) = ⟨m - 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  simpa only [he] using hp.2.2 ⟨m, by omega⟩

theorem ratio_central_positive {m : ℕ} (hm : 0 < m) {p : Fin (2 * m) → ℝ}
    (hp : p ∈ S_n (2 * m)) : 0 < p ⟨m, by omega⟩ := by
  have hmono := hp.2.1 (show (⟨m - 1, by omega⟩ : Fin (2 * m)) < ⟨m, by omega⟩ by
    change m - 1 < m
    omega)
  rw [ratio_central_pair hm hp] at hmono
  linarith

/-- Adjacent scaled separation makes the scaled roots minus their indices monotone. -/
theorem ratio_affine_root_monotone {n : ℕ} (p : Fin n → ℝ) (A : ℝ)
    (hstep : ∀ j (hj : j + 1 < n),
      1 ≤ A * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩)) :
    Monotone (fun j : Fin n => A * p j - (j.val : ℝ)) := by
  cases n with
  | zero => intro j; exact Fin.elim0 j
  | succ k =>
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    have h := hstep j.val (by omega)
    change 1 ≤ A * (p j.succ - p j.castSucc) at h
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    linarith

/-- A density upper bound gives a uniform lower bound at every positive rank. -/
theorem ratio_positive_rank_lower {m N : ℕ} (hm : 0 < m) {p : Fin (2 * m) → ℝ}
    (hp : p ∈ S_n (2 * m)) (hs : 2 * (2 * m) ≤ N) {M : ℝ}
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (2 * m) p hp (by omega) hs x ≤ M)
    (k : ℕ) (hk : k < m) :
    (k : ℝ) + 1 / 2 ≤ (M * N) * p ⟨m + k, by omega⟩ := by
  have hstep (j : ℕ) (hj : j + 1 < 2 * m) :
      1 ≤ (M * N) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) := by
    have h := root_spacing_lower_at hp (by omega) hs hupper j hj
    nlinarith only [h]
  have hcentral := hstep (m - 1) (by omega)
  have hidx : (⟨m - 1 + 1, by omega⟩ : Fin (2 * m)) = ⟨m, by omega⟩ := by
    apply Fin.ext
    change m - 1 + 1 = m
    omega
  rw [hidx, ratio_central_pair hm hp] at hcentral
  have hmono := ratio_affine_root_monotone p (M * N) hstep
  have hdiff := hmono (show (⟨m, by omega⟩ : Fin (2 * m)) ≤ ⟨m + k, by omega⟩ by
    change m ≤ m + k
    omega)
  simp only [Nat.cast_add] at hdiff
  nlinarith only [hcentral, hdiff]

/-- The smallest positive root is at most half the central mesh gap. -/
theorem ratio_central_le_mesh {m : ℕ} (hm : 0 < m) {p : Fin (2 * m) → ℝ}
    (hp : p ∈ S_n (2 * m)) {d : ℝ}
    (hmesh : ∀ j : Fin (2 * m + 1),
      rootPartitionPoint (2 * m) p (by omega) j.succ -
        rootPartitionPoint (2 * m) p (by omega) j.castSucc ≤ d) :
    p ⟨m, by omega⟩ ≤ d / 2 := by
  have h := root_interior_gap_of_mesh p (by omega) hmesh (m - 1) (by omega)
  have hidx : (⟨m - 1 + 1, by omega⟩ : Fin (2 * m)) = ⟨m, by omega⟩ := by
    apply Fin.ext
    change m - 1 + 1 = m
    omega
  rw [hidx, ratio_central_pair hm hp] at h
  linarith

end PottsDiscontinuity.Bethe
