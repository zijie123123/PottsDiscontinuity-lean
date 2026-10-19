module

public import PottsDiscontinuity.Bethe.AsymptoticNearRoots
public import PottsDiscontinuity.Bethe.AsymptoticSpatial
public import PottsDiscontinuity.Bethe.AsymptoticUniformOffset

/-! # Geometric estimates derived from the source density rate -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- A package of finite estimates used by the compactness and Taylor steps.
It contains no limit equation or convergence conclusion. -/
structure OffsetEstimatesAt (N r : ℕ) (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    (hn : 0 < N / 2 - r) (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ)
    (B R DP DQ : ℝ) (K : NNReal) : Prop where
  bound : ∀ j, |offsetDisplacement N r h4 hr p q j| ≤ B
  pair : ∀ j k, |offsetDisplacement N r h4 hr p q j - offsetDisplacement N r h4 hr p q k| ≤
    (K : ℝ) * |q j - q k|
  near : ∀ j, |offsetLowerRoot N r hr p j - q j| ≤ R / N ∧
    |offsetUpperRoot N r hr p j - q j| ≤ R / N
  meshP : ∀ j : Fin (N / 2 + 1),
    rootPartitionPoint (N / 2) p (by omega) j.succ -
      rootPartitionPoint (N / 2) p (by omega) j.castSucc ≤ DP / N
  meshQ : ∀ j : Fin (N / 2 - r + 1),
    rootPartitionPoint (N / 2 - r) q hn j.succ -
      rootPartitionPoint (N / 2 - r) q hn j.castSucc ≤ DQ / N

theorem root_mesh_le_of_density_lower {N n r : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    (hcount : N = 2 * (n + r)) {m : ℝ} (hm : 0 < m)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m / 2 ≤ rootStepDensity N n p hp hn hs x)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      (2 * (2 * r + 1 : ℝ) / m) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (rootPartition_gap_le_of_density_lower hp hn hs hm hlower j).trans
  have he : (2 * (2 * r + 1 : ℝ) / m) / N = 2 * (2 * r + 1 : ℝ) / (m * N) := by ring
  rw [he]
  apply (div_le_div_iff_of_pos_right (mul_pos hm hN)).mpr
  have := rootGapMultiplicity_le_offset hs hcount j
  linarith

theorem root_interior_gap_of_mesh {n : ℕ} (p : Fin n → ℝ) (hn : 0 < n) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤ d)
    (j : ℕ) (hj : j + 1 < n) : p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ d := by
  have hi := hmesh ⟨j + 1, by omega⟩
  change rootPartitionPoint n p hn ⟨j + 1 + 1, by omega⟩ -
    rootPartitionPoint n p hn ⟨j + 1, by omega⟩ ≤ d at hi
  rw [rootPartitionPoint_root p hn ⟨j + 1, hj⟩,
    rootPartitionPoint_root p hn ⟨j, by omega⟩] at hi
  exact hi

theorem eventually_offset_estimates_of_density_rate {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N : ι → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop) {E : ℝ} (hE : 0 ≤ E)
    (herror : ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x -
        rho Δ x| ≤ E / N i ∧
      |rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x -
        rho Δ x| ≤ E / N i) :
    ∃ B R DP DQ : ℝ, 0 ≤ B ∧ 0 ≤ R ∧ 0 ≤ DP ∧ 0 ≤ DQ ∧ ∃ K : NNReal,
      ∀ᶠ i in l, OffsetEstimatesAt (N i) r (h4 i) (hr i) (hn i) (p i) (q i) B R DP DQ K := by
  obtain ⟨m, hm, hmρ⟩ := rho_uniform_lower_bound hΔ
  have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m ≤ rho Δ x := hmρ Δ le_rfl
  obtain ⟨C, hC, halign⟩ := offset_alignment_of_density_error hΔ hm hE hlower
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  let M := max M₀ 1 + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith [le_max_right M₀ 1]
  let B := 2 * Real.exp C
  let H := C * (B + 1)
  let DP := 2 / m
  let DQ := 2 * (2 * r + 1 : ℝ) / m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hDP : 0 ≤ DP := by dsimp [DP]; positivity
  have hDQ : 0 ≤ DQ := by dsimp [DQ]; positivity
  let K : NNReal := ⟨H * M, mul_nonneg hH hM⟩
  refine ⟨B, B + DP, DP, DQ, hB, add_nonneg hB hDP, hDP, hDQ, K, ?_⟩
  have hElim : Tendsto (fun i => E / (N i : ℝ)) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hNlim).const_mul E
  filter_upwards [herror, hNlim.eventually (eventually_ge_atTop C),
    hElim.eventually (gt_mem_nhds (show (0 : ℝ) < m / 2 by positivity)),
    hElim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with i hi hlarge hsmall hsmall1
  have hep := fun x hx => (hi x hx).1
  have heq := fun x hx => (hi x hx).2
  have hb := halign (N i) r (h4 i) (hr i) (hN i) (hn i) (p i) (q i) (hp i) (hq i)
    hlarge hsmall.le hep heq
  have hlowp : ∀ x ∈ Icc (-Real.pi) Real.pi,
      m / 2 ≤ rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x := by
    intro x hx
    have := (abs_le.mp (hep x hx)).1
    have := hlower x hx
    linarith
  have hlowq : ∀ x ∈ Icc (-Real.pi) Real.pi,
      m / 2 ≤ rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x := by
    intro x hx
    have := (abs_le.mp (heq x hx)).1
    have := hlower x hx
    linarith
  have hcountp : N i = 2 * (N i / 2 + 0) := by obtain ⟨z, hz⟩ := h4 i; omega
  have hcountq : N i = 2 * (N i / 2 - r + r) := by
    obtain ⟨z, hz⟩ := h4 i
    have := hr i
    omega
  have hmeshp : ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.succ -
        rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.castSucc ≤ DP / N i := by
    intro j
    simpa only [Nat.cast_zero, mul_zero, zero_add, mul_one] using
      root_mesh_le_of_density_lower (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) hcountp hm hlowp j
  have hmeshq := root_mesh_le_of_density_lower (hq i) (hn i) (two_mul_half_sub_le N r i) hcountq hm hlowq
  have hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x ≤ M := by
    intro x hx
    have he := (abs_le.mp (heq x hx)).2
    have hρ : rho Δ x ≤ M₀ := (le_abs_self _).trans (by simpa using hM₀ x hx)
    dsimp [M]
    linarith [le_max_left M₀ 1]
  refine ⟨hb.1, ?_, ?_, hmeshp, hmeshq⟩
  · exact offset_root_lipschitz (h4 i) (hr i) (hN i) (hn i) (hq i) hH hupper hb.2
  · exact offset_shifted_roots_near (h4 i) (hr i) (hN i) (hp i) hDP hb.1
      (root_interior_gap_of_mesh (p i) (by have := hn i; omega) hmeshp)

end PottsDiscontinuity.Bethe
