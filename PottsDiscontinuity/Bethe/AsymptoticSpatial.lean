module

public import PottsDiscontinuity.Bethe.AsymptoticOffset
public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl

/-! # Linear control and asymptotic equicontinuity of the step offsets -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem abs_sub_le_mul_root_dist_of_pos {n : ℕ} (hn : 0 < n)
    (q u : Fin n → ℝ) {K : ℝ} (hq : Monotone q)
    (hstep : ∀ j (hj : j + 1 < n), |u ⟨j + 1, hj⟩ - u ⟨j, by omega⟩| ≤
      K * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩)) :
    ∀ i j, |u i - u j| ≤ K * |q i - q j| := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact abs_sub_le_mul_root_dist q u hq (fun j => hstep j.val (by omega))

theorem root_spacing_lower_at {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {M : ℝ}
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi, rootStepDensity N n p hp hn hs x ≤ M)
    (j : ℕ) (hj : j + 1 < n) :
    1 ≤ M * ((N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hg : p (⟨j, by omega⟩ : Fin k).castSucc < p (⟨j, by omega⟩ : Fin k).succ :=
    hp.2.1 (by change j < j + 1; omega)
  have he := hupper (p (⟨j, by omega⟩ : Fin k).castSucc)
    ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
  rw [rootStepDensity_interior hp hs ⟨j, by omega⟩ ⟨le_rfl, hg⟩] at he
  exact (div_le_iff₀ (mul_pos (by exact_mod_cast (show 0 < N by omega)) (sub_pos.mpr hg))).mp he

theorem offset_root_lipschitz {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hN : 0 < N) (hn : 0 < N / 2 - r)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hq : q ∈ S_n (N / 2 - r)) {M H : ℝ} (hH : 0 ≤ H)
    (hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (N / 2 - r) q hq hn (by omega) x ≤ M)
    (hinc : ∀ j (hj : j + 1 < N / 2 - r),
      |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
        offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤ H / N) :
    ∀ i j, |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤
      H * M * |q i - q j| := by
  have hlocal (j : ℕ) (hj : j + 1 < N / 2 - r) :
      |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
        offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤
        (H * M) * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩) := by
    apply (hinc j hj).trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mpr
    have hb := mul_le_mul_of_nonneg_left (root_spacing_lower_at hq hn (by omega) hupper j hj) hH
    nlinarith only [hb]
  exact abs_sub_le_mul_root_dist_of_pos hn q (offsetDisplacement N r h4 hr p q)
    hq.2.1.monotone hlocal

/-- Quantitative spatial control, valid for the step functions themselves.
The additive mesh term tends to zero and replaces an invalid direct use of
Arzelà--Ascoli on discontinuous functions. -/
theorem offsetFunction_spatial_control {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r))
    {K d : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ i j,
      |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤ K * |q i - q j|)
    (hmesh : ∀ j : Fin (N / 2 - r + 1),
      rootPartitionPoint (N / 2 - r) q hn j.succ -
        rootPartitionPoint (N / 2 - r) q hn j.castSucc ≤ d) :
    (∀ x ∈ Icc (-Real.pi) Real.pi,
      |offsetFunction N r h4 hr p q hn x| ≤ K * |x| + K * d) ∧
    (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
      |offsetFunction N r h4 hr p q hn x - offsetFunction N r h4 hr p q hn y| ≤
        K * |x - y| + 2 * K * d) := by
  have hroot (j : Fin (N / 2 - r)) : |offsetDisplacement N r h4 hr p q j| ≤ K * |q j| := by
    have hi := hpair j (Fin.rev j)
    rw [offsetDisplacement_rev h4 hr hp hq, show q (Fin.rev j) = -q j from hq.2.2 j] at hi
    have he (a : ℝ) : |a - -a| = 2 * |a| := by
      rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [he, he] at hi
    linarith
  constructor
  · intro x hx
    obtain ⟨j, hj, hdist⟩ := offsetFunction_near_root h4 hr hn hq hmesh hx
    rw [hj]
    apply (hroot j).trans
    have hi : |q j| ≤ |x| + d := by
      have := abs_add_le (q j - x) x
      rw [sub_add_cancel, abs_sub_comm] at this
      linarith
    have := mul_le_mul_of_nonneg_left hi hK
    linarith
  · intro x hx y hy
    obtain ⟨i, hi, hdi⟩ := offsetFunction_near_root h4 hr hn hq hmesh hx
    obtain ⟨j, hj, hdj⟩ := offsetFunction_near_root h4 hr hn hq hmesh hy
    rw [hi, hj]
    apply (hpair i j).trans
    have hd : |q i - q j| ≤ |x - y| + 2 * d := by
      have h₁ := abs_add_le (q i - x) (x - y + (y - q j))
      have h₂ := abs_add_le (x - y) (y - q j)
      rw [show q i - x + (x - y + (y - q j)) = q i - q j by ring,
        abs_sub_comm (q i) x] at h₁
      linarith
    have := mul_le_mul_of_nonneg_left hd hK
    nlinarith only [this]

end PottsDiscontinuity.Bethe
