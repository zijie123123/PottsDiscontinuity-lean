module

public import PottsDiscontinuity.Bethe.Theorem23Comparison

/-! # Mesh bootstrap for compact continuation -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The step-density error has a finite weighted supremum for every valid
configuration; boundedness is proved rather than imposed on solutions. -/
theorem rootStepDensity_error_bddAbove {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) := by
  let c : Fin (n + 1) → ℝ := fun j => rootGapMultiplicity N n hs j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  let B := ∑ j, |c j|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hstep (x : ℝ) : |rootStepDensity N n p hp hn hs x| ≤ B := by
    unfold rootStepDensity
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    change |if _ then c j else 0| ≤ |c j|
    split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using abs_nonneg (c j)
  obtain ⟨X, hX, hupper⟩ := exists_uniform_Xi_upper_bound hΔ
  obtain ⟨M, hρ⟩ := rho_uniform_upper_bound hΔ
  refine ⟨X * (B + M), ?_⟩
  rintro _ ⟨α, rfl⟩
  have hXi : |Xi (lamOf Δ) α| ≤ X := by
    rw [abs_of_pos (Xi_pos (lamOf_pos hΔ) _)]
    exact hupper Δ le_rfl α
  have hρabs : |rho Δ (kMap (lamOf Δ) α)| ≤ M := by
    rw [abs_of_pos (rho_pos hΔ _)]
    exact hρ Δ le_rfl _
  change |Xi (lamOf Δ) α * (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
    rho Δ (kMap (lamOf Δ) α))| ≤ X * (B + M)
  rw [abs_mul]
  apply mul_le_mul hXi _ (abs_nonneg _) hX.le
  calc
    _ ≤ |rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α)| +
        |rho Δ (kMap (lamOf Δ) α)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α)) (-rho Δ (kMap (lamOf Δ) α))
    _ ≤ B + M := add_le_add (hstep _) hρabs

/-- For Bethe solutions a fixed mesh implies the `O(1/N)` density estimate.
The constant does not depend on any prior density error bound. -/
theorem exists_uniform_density_bound_of_Bethe_mesh (r : ℕ) {Δ₀ : ℝ}
    (hΔ₀ : Δ₀ < -1) (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀), ∀ (N k : ℕ),
      N = 2 * ((k + 1) + r) → ∀ (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
      (hs : 2 * (k + 1) ≤ N), DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
        (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x)
        (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs) ≤ K / N := by
  obtain ⟨m, hm, _, hctr⟩ := exists_uniform_counting_contraction hΔ₀
  obtain ⟨A, hA, hcmp⟩ := exists_uniform_step_counting_comparison hΔ₀
  obtain ⟨E, hE, hestimate⟩ := hctr r D hD
  let C := E + A * D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C / m, div_pos hC hm, fun Δ hΔ N k hcount p hp hs hBE hmesh => ?_⟩
  let hb := rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) p hp (by omega) hs
  have hc := hcmp Δ hΔ N k p hp hs hBE D hD hb hmesh
  have ht := hestimate Δ hΔ N k p hp hs hcount hb hmesh
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmix : m * densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x) hb ≤ C / (N : ℝ) := by
    dsimp [C]
    rw [add_div]
    nlinarith only [hc, ht]
  have hh := (le_div_iff₀ hm).2 (show _ * m ≤ C / (N : ℝ) by
    simpa only [mul_comm] using hmix)
  convert hh using 1
  ring

end PottsDiscontinuity.Bethe
