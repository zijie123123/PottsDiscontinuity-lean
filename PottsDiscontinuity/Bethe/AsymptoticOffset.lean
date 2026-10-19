module

public import PottsDiscontinuity.Bethe.AsymptoticSpacing

/-! # Symmetry and aligned roots for the offset displacement -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- The full configuration root, or the mean of the two roots, aligned with
an index of the deficient configuration in (2.13). -/
noncomputable def alignedRoot (N r : ℕ) (hr : r ≤ N / 2)
    (p : Fin (N / 2) → ℝ) (j : Fin (N / 2 - r)) : ℝ :=
  if r % 2 = 0 then p ⟨j.val + r / 2, by omega⟩
  else (p ⟨j.val + (r - 1) / 2, by omega⟩ +
    p ⟨j.val + (r + 1) / 2, by omega⟩) / 2

theorem offsetDisplacement_eq_alignedRoot (N r : ℕ) (hN : 4 ∣ N)
    (hr : r ≤ N / 2) (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ)
    (j : Fin (N / 2 - r)) :
    offsetDisplacement N r hN hr p q j = (N : ℝ) * (q j - alignedRoot N r hr p j) := by
  simp only [offsetDisplacement, alignedRoot]
  split <;> rfl

theorem alignedRoot_mem_Icc {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p j ∈ Icc (-Real.pi) Real.pi := by
  unfold alignedRoot
  split
  · exact ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
  · constructor <;> linarith [(hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r - 1) / 2, by omega⟩).2,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).1,
      (hp.1 ⟨j.val + (r + 1) / 2, by omega⟩).2]

theorem alignedRoot_rev {N r : ℕ} (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} (hp : p ∈ S_n (N / 2)) (j : Fin (N / 2 - r)) :
    alignedRoot N r hr p (Fin.rev j) = -alignedRoot N r hr p j := by
  have hsym : ∀ i, p (Fin.rev i) = -p i := hp.2.2
  unfold alignedRoot
  split
  next he =>
    have hi : (⟨(Fin.rev j).val + r / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + r / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi, hsym]
  next ho =>
    have hi : (⟨(Fin.rev j).val + (r - 1) / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + (r + 1) / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    have hi' : (⟨(Fin.rev j).val + (r + 1) / 2, by omega⟩ : Fin (N / 2)) =
        Fin.rev ⟨j.val + (r - 1) / 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi, hi', hsym, hsym]
    ring

theorem offsetDisplacement_rev {N r : ℕ} (hN : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r))
    (j : Fin (N / 2 - r)) :
    offsetDisplacement N r hN hr p q (Fin.rev j) =
      -offsetDisplacement N r hN hr p q j := by
  rw [offsetDisplacement_eq_alignedRoot, offsetDisplacement_eq_alignedRoot,
    alignedRoot_rev hr hp, show q (Fin.rev j) = -q j from hq.2.2 j]
  ring

/-- The density-to-spacing estimate with arbitrary positive root count. -/
theorem root_spacing_error_at {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {Δ m E : ℝ} (hm : 0 < m) (hsmall : E ≤ m / 2)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m ≤ rho Δ x)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N n p hp hn hs x - rho Δ x| ≤ E)
    (j : ℕ) (hj : j + 1 < n) :
    |(N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) -
      (rho Δ (p ⟨j, by omega⟩))⁻¹| ≤ 2 * E / m ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact root_spacing_error hp hs hm hsmall hlower herror ⟨j, by omega⟩

end PottsDiscontinuity.Bethe
