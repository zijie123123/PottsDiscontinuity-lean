module

public import PottsDiscontinuity.Bethe.AsymptoticNorm

/-! # Cyclic root cells and their gap estimates -/

@[expose] public section

open Set
open scoped BigOperators
open Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem rootPartitionPoint_zero {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) :
    rootPartitionPoint n p hn ⟨0, by omega⟩ = p ⟨n - 1, by omega⟩ - 2 * Real.pi := by
  simp [rootPartitionPoint]

theorem rootPartitionPoint_end {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) :
    rootPartitionPoint n p hn ⟨n + 1, by omega⟩ = p ⟨0, hn⟩ + 2 * Real.pi := by
  simp [rootPartitionPoint]

theorem rootPartitionPoint_root {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) (j : Fin n) :
    rootPartitionPoint n p hn ⟨j.val + 1, by omega⟩ = p j := by
  simp only [rootPartitionPoint,
    dite_eq_right (by omega : j.val + 1 ≠ 0), dite_eq_right (by omega : j.val + 1 ≠ n + 1)]
  congr 1

theorem rootPartitionPoint_strictMono {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) : StrictMono (rootPartitionPoint n p hn) := by
  intro i j hij
  have hv : i.val < j.val := hij
  by_cases hi0 : i.val = 0
  · have hi : rootPartitionPoint n p hn i = p ⟨n - 1, by omega⟩ - 2 * Real.pi := by
      simp only [rootPartitionPoint, dite_eq_left hi0]
    rw [hi]
    have hlast := (hp.1 ⟨n - 1, by omega⟩).2
    by_cases hjend : j.val = n + 1
    · have hj : rootPartitionPoint n p hn j = p ⟨0, hn⟩ + 2 * Real.pi := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_left hjend]
      rw [hj]
      have hfirst := (hp.1 ⟨0, hn⟩).1
      linarith [Real.pi_pos]
    · have hj : rootPartitionPoint n p hn j = p ⟨j.val - 1, by omega⟩ := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_right hjend]
      rw [hj]
      have hbound := (hp.1 ⟨j.val - 1, by omega⟩).1
      linarith
  · have hiend : i.val ≠ n + 1 := by omega
    have hi : rootPartitionPoint n p hn i = p ⟨i.val - 1, by omega⟩ := by
      simp only [rootPartitionPoint, dite_eq_right hi0, dite_eq_right hiend]
    rw [hi]
    by_cases hjend : j.val = n + 1
    · have hj : rootPartitionPoint n p hn j = p ⟨0, hn⟩ + 2 * Real.pi := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_left hjend]
      rw [hj]
      have hfirst := (hp.1 ⟨0, hn⟩).1
      have hbound := (hp.1 ⟨i.val - 1, by omega⟩).2
      linarith
    · have hj : rootPartitionPoint n p hn j = p ⟨j.val - 1, by omega⟩ := by
        simp only [rootPartitionPoint, dite_eq_right (by omega : j.val ≠ 0), dite_eq_right hjend]
      rw [hj]
      exact hp.2.1 (show (⟨i.val - 1, by omega⟩ : Fin n) < ⟨j.val - 1, by omega⟩ from
        by change i.val - 1 < j.val - 1; omega)

theorem rootPartition_gap_pos {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (j : Fin (n + 1)) :
    0 < rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc := by
  apply sub_pos.mpr
  exact rootPartitionPoint_strictMono hp hn (show j.castSucc < j.succ from by
    change j.val < j.val + 1; omega)

theorem rootStepDensity_on_cell {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {x : ℝ} (hx : rootPartitionPoint n p hn j.castSucc ≤ x ∧
      x < rootPartitionPoint n p hn j.succ) :
    rootStepDensity N n p hp hn hs x = rootGapMultiplicity N n hs j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)) := by
  have hm := (rootPartitionPoint_strictMono hp hn).monotone
  unfold rootStepDensity
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left hx]
  · intro k _ hkj
    have hk : ¬ (rootPartitionPoint n p hn k.castSucc ≤ x ∧
        x < rootPartitionPoint n p hn k.succ) := by
      intro hk
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · have hle : k.succ ≤ j.castSucc := by change k.val + 1 ≤ j.val; exact hlt
        have := hm hle
        linarith [hx.1, hk.2]
      · have hle : j.succ ≤ k.castSucc := by change j.val + 1 ≤ k.val; exact hgt
        have := hm hle
        linarith [hx.2, hk.1]
    exact ite_eq_right hk
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Every cyclic root cell meets the physical interval. -/
theorem rootPartition_cell_meets_Icc {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (j : Fin (n + 1)) :
    ∃ x ∈ Icc (-Real.pi) Real.pi,
      rootPartitionPoint n p hn j.castSucc ≤ x ∧
        x < rootPartitionPoint n p hn j.succ := by
  have hm := rootPartitionPoint_strictMono hp hn
  have hlo : -Real.pi < rootPartitionPoint n p hn j.succ := by
    have hfirst : rootPartitionPoint n p hn ⟨1, by omega⟩ = p ⟨0, hn⟩ := by
      simpa using rootPartitionPoint_root p hn ⟨0, hn⟩
    have := hm.monotone (show (⟨1, by omega⟩ : Fin (n + 2)) ≤ j.succ from by
      change 1 ≤ j.val + 1; omega)
    rw [hfirst] at this
    exact (hp.1 ⟨0, hn⟩).1.trans_le this
  have hhi : rootPartitionPoint n p hn j.castSucc < Real.pi := by
    have hlast : rootPartitionPoint n p hn ⟨n, by omega⟩ = p ⟨n - 1, by omega⟩ := by
      convert rootPartitionPoint_root p hn ⟨n - 1, by omega⟩ using 1
      congr 1; apply Fin.ext; dsimp; omega
    have := hm.monotone (show j.castSucc ≤ (⟨n, by omega⟩ : Fin (n + 2)) from by
      change j.val ≤ n; omega)
    rw [hlast] at this
    exact this.trans_lt (hp.1 ⟨n - 1, by omega⟩).2
  refine ⟨max (-Real.pi) (rootPartitionPoint n p hn j.castSucc),
    ⟨le_max_left _ _, max_le (by linarith [Real.pi_pos]) hhi.le⟩, le_max_right _ _, ?_⟩
  exact max_lt hlo (sub_pos.mp (rootPartition_gap_pos hp hn j))

/-- A positive lower bound for the density gives the required gap bound. -/
theorem rootPartition_gap_le_of_density_lower {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) {m : ℝ} (hm : 0 < m)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m / 2 ≤ rootStepDensity N n p hp hn hs x)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n hs j / (m * (N : ℝ)) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hgap := rootPartition_gap_pos hp hn j
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hn j
  have hb := hlower x hx
  rw [rootStepDensity_on_cell hp hn hs j hcell] at hb
  have hb' := (le_div_iff₀ (mul_pos hN hgap)).mp hb
  apply (le_div_iff₀ (mul_pos hm hN)).mpr
  nlinarith only [hb']

theorem rootGapMultiplicity_le_offset {N n r : ℕ} (hs : 2 * n ≤ N)
    (hcount : N = 2 * (n + r)) (j : Fin (n + 1)) :
    rootGapMultiplicity N n hs j ≤ (2 * r + 1 : ℝ) := by
  have hnat : N + 1 - 2 * n = 2 * r + 1 := by omega
  unfold rootGapMultiplicity
  split_ifs
  · rw [hnat]
    push_cast
    rfl
  · linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))]

/-- The missing gap estimate for Theorem 2.6: only convergence of the
weighted density norm is assumed; no Bethe equation or convergence rate is
needed. The count identity is exactly `n = N/2-r` for even `N`. -/
theorem eventually_rootPartition_gap_le {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (hn : ∀ i, 0 < n i)
    (hs : ∀ i, 2 * n i ≤ N i) (hcount : ∀ i, N i = 2 * (n i + r))
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i) (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i) x - rho Δ x)
      (hb i)) l (𝓝 0)) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ i in l, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (p i) (hn i) j.succ -
        rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤
          2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ)) := by
  obtain ⟨m, hm, hlower⟩ := eventually_density_ge_half hΔ
    (fun i => rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i)) hb hlim
  refine ⟨m, hm, ?_⟩
  filter_upwards [hlower] with i hi j
  apply (rootPartition_gap_le_of_density_lower (hp i) (hn i) (hs i) hm hi j).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset (hs i) (hcount i) j)
    (by norm_num)

end PottsDiscontinuity.Bethe
