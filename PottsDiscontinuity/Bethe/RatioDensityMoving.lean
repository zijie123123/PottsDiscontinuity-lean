module

public import PottsDiscontinuity.Bethe.Asymptotic26Cast

/-! # Moving-point density limits and central root gaps -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_density_moving_tendsto {ι : Type*} {l : Filter ι} {Δ x₀ : ℝ}
    (hΔ : Δ < -1) (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i)) l (𝓝 0))
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (-Real.pi) Real.pi) (hxlim : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => f i (x i)) l (𝓝 (rho Δ x₀)) := by
  have he := tendsto_densityNorm_div hΔ (fun i y => f i y - rho Δ y) hb hlim
  have hρ := (continuous_rho hΔ).continuousAt.tendsto.comp hxlim
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)),
    Metric.tendsto_nhds.mp hρ (ε / 2) (by positivity)] with i hi hρi
  have herr := abs_le_densityNorm_div hΔ (fun y => f i y - rho Δ y) (hb i) (hx i)
  rw [Real.dist_eq] at hρi ⊢
  dsimp only [Function.comp_def] at hρi
  have htri := abs_add_le (f i (x i) - rho Δ (x i)) (rho Δ (x i) - rho Δ x₀)
  rw [sub_add_sub_cancel] at htri
  linarith

/-- At a moving root converging to zero, the rescaled next gap converges
to `1/ρ(0)`. This uses the exact interior step-density formula. -/
theorem ratio_gap_tendsto_at_zero {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ι → ℕ) (q : ∀ i, Fin (n i) → ℝ) (hq : ∀ i, q i ∈ S_n (n i))
    (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i) x - rho Δ x) (hb i)) l (𝓝 0))
    (j : ∀ i, Fin (n i)) (hj : ∀ i, (j i).val + 1 < n i)
    (hzero : Tendsto (fun i => q i (j i)) l (𝓝 0)) :
    Tendsto (fun i => (N i : ℝ) * (q i ⟨(j i).val + 1, hj i⟩ - q i (j i))) l
      (𝓝 (rho Δ 0)⁻¹) := by
  have ht := ratio_density_moving_tendsto hΔ
    (fun i => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)) hb hlim
    (fun i => q i (j i)) (fun i => ⟨((hq i).1 _).1.le, ((hq i).1 _).2.le⟩) hzero
  have hinv := ht.inv₀ (rho_pos hΔ 0).ne'
  apply hinv.congr
  intro i
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (hn i).ne'
  have hcast := rootStepDensity_cast hk.symm (q i) (hq i) (by omega) (hn i)
    (by have := hs i; omega) (hs i)
  let q' : Fin (k + 1) → ℝ := fun t => q i (Fin.cast hk.symm t)
  have hq' : q' ∈ S_n (k + 1) := mem_S_n_cast hk.symm (hq i)
  let t : Fin k := ⟨(j i).val, by have := hj i; omega⟩
  have he₀ : Fin.cast hk.symm t.castSucc = j i := Fin.ext rfl
  have he₁ : Fin.cast hk.symm t.succ = ⟨(j i).val + 1, hj i⟩ := Fin.ext rfl
  have hcell : q' t.castSucc ≤ q i (j i) ∧ q i (j i) < q' t.succ := by
    dsimp only [q']
    rw [he₀, he₁]
    exact ⟨le_rfl, (hq i).2.1 (by change (j i).val < (j i).val + 1; omega)⟩
  rw [← congrFun hcast (q i (j i)), rootStepDensity_interior hq' (by have := hs i; omega) t hcell]
  dsimp only [q']
  rw [he₀, he₁, one_div, inv_inv]

end PottsDiscontinuity.Bethe
