module

public import PottsDiscontinuity.Bethe.RatioCentralGeometry
public import PottsDiscontinuity.Bethe.RatioDensityMoving

/-! # Fixed positive ranks at the central scale

Only density norm convergence and a vanishing mesh are needed for the
fixed-rank limits. Uniform-in-rank lower bounds are proved separately.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_central_root_tendsto_zero {ι : Type*} {l : Filter ι}
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (p : ∀ i, Fin (2 * m i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (2 * m i)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hmesh : ∀ᶠ i in l, ∀ j : Fin (2 * m i + 1),
      rootPartitionPoint (2 * m i) (p i) (by have := hm i; omega) j.succ -
        rootPartitionPoint (2 * m i) (p i) (by have := hm i; omega) j.castSucc ≤ d i) :
    Tendsto (fun i => p i ⟨m i, by have := hm i; omega⟩) l (𝓝 0) := by
  have ht : Tendsto (fun i => d i / 2) l (𝓝 0) := by simpa using hd.div_const 2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hmesh, ht.eventually (gt_mem_nhds hε)] with i hi hdi
  rw [Real.dist_eq, sub_zero, abs_of_pos (ratio_central_positive (hm i) (hp i))]
  exact (ratio_central_le_mesh (hm i) (hp i) hi).trans_lt hdi

section

variable {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (N m : ι → ℕ) (hm : ∀ i, 0 < m i) (p : ∀ i, Fin (2 * m i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (2 * m i)) (hs : ∀ i, 2 * (2 * m i) ≤ N i)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (2 * m i) (p i) (hp i)
        (by have := hm i; omega) (hs i) (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (2 * m i) (p i) (hp i)
        (by have := hm i; omega) (hs i) x - rho Δ x) (hb i)) l (𝓝 0))
    (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hmesh : ∀ᶠ i in l, ∀ j : Fin (2 * m i + 1),
      rootPartitionPoint (2 * m i) (p i) (by have := hm i; omega) j.succ -
        rootPartitionPoint (2 * m i) (p i) (by have := hm i; omega) j.castSucc ≤ d i)

include hΔ hp hs hb hlim hd hmesh

/-- The central half-gap constant, with the source's positive density normalization. -/
theorem ratio_central_root_scaling :
    Tendsto (fun i => (N i : ℝ) * p i ⟨m i, by have := hm i; omega⟩) l
      (𝓝 (1 / (2 * rho Δ 0))) := by
  have hzero := ratio_central_root_tendsto_zero m hm p hp d hd hmesh
  have hpair (i : ι) : p i ⟨m i - 1, by have := hm i; omega⟩ =
      -p i ⟨m i, by have := hm i; omega⟩ := ratio_central_pair (hm i) (hp i)
  have hneg : Tendsto (fun i => p i ⟨m i - 1, by have := hm i; omega⟩) l (𝓝 0) := by
    simpa only [hpair, neg_zero] using hzero.neg
  have hgap := ratio_gap_tendsto_at_zero hΔ N (fun i => 2 * m i) p hp
    (fun i => by have := hm i; omega) hs hb hlim
    (fun i => ⟨m i - 1, by have := hm i; omega⟩)
    (fun i => by change m i - 1 + 1 < 2 * m i; have := hm i; omega) hneg
  have hidx (i : ι) :
      (⟨m i - 1 + 1, by have := hm i; omega⟩ : Fin (2 * m i)) = ⟨m i, by have := hm i; omega⟩ := by
    apply Fin.ext
    change m i - 1 + 1 = m i
    have := hm i
    omega
  simp_rw [hidx, hpair] at hgap
  have ht := hgap.div_const 2
  have hvalue : (rho Δ 0)⁻¹ / 2 = 1 / (2 * rho Δ 0) := by ring
  rw [hvalue] at ht
  apply ht.congr
  intro i
  ring

/-- Every fixed positive rank has the half-integer central scaling.
The rank premise expresses that the selected root exists for every index;
as usual it can be obtained by discarding a finite initial segment. -/
theorem ratio_positive_rank_scaling (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (k : ℕ) (hk : ∀ i, k < m i) :
    Tendsto (fun i => (N i : ℝ) * p i ⟨m i + k, by have := hk i; omega⟩) l
      (𝓝 (((k : ℝ) + 1 / 2) / rho Δ 0)) := by
  revert hk
  induction k with
  | zero =>
    intro hk
    simpa only [Nat.add_zero, Nat.cast_zero, zero_add, div_div] using
      ratio_central_root_scaling hΔ N m hm p hp hs hb hlim d hd hmesh
  | succ k ih =>
    intro hk
    have hklow (i : ι) : k < m i := by have := hk i; omega
    have hprev := ih hklow
    have hzero : Tendsto (fun i => p i ⟨m i + k, by have := hklow i; omega⟩) l (𝓝 0) := by
      have ht := hprev.div_atTop hNlim
      apply ht.congr
      intro i
      have hNi : (N i : ℝ) ≠ 0 := by
        exact_mod_cast (show N i ≠ 0 by have := hs i; have := hm i; omega)
      field_simp
    have hgap := ratio_gap_tendsto_at_zero hΔ N (fun i => 2 * m i) p hp
      (fun i => by have := hm i; omega) hs hb hlim
      (fun i => ⟨m i + k, by have := hklow i; omega⟩)
      (fun i => by change m i + k + 1 < 2 * m i; have := hk i; omega) hzero
    have ht := hprev.add hgap
    have hvalue : ((k : ℝ) + 1 / 2) / rho Δ 0 + (rho Δ 0)⁻¹ =
        (((k + 1 : ℕ) : ℝ) + 1 / 2) / rho Δ 0 := by push_cast; ring
    rw [hvalue] at ht
    apply ht.congr
    intro i
    have hidx : (⟨m i + k + 1, by have := hk i; omega⟩ : Fin (2 * m i)) =
        ⟨m i + (k + 1), by have := hk i; omega⟩ := Fin.ext rfl
    rw [hidx]
    ring

end

end PottsDiscontinuity.Bethe
