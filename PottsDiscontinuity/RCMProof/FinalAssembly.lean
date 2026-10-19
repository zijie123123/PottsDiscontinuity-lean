module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Duality.Discontinuity
public import PottsDiscontinuity.Infra.Lambda

/-!
# Theorem 1.2 final assembly from its item-3 input

This module proves the box-limit and discontinuity assembly after the analytic
item-3 rate statement has been established for every free limit.  It does not
import the theorem-statement modules (`Frozen/`) or the provider modules (`Provider/`).
-/

@[expose] public section

open MeasureTheory Filter Topology Real

namespace PottsDiscontinuity.RCMProof

/-- Item 3 of Theorem 1.2, uniformly for every free critical box limit. -/
def rcItem3ForEveryFreeLimit (q : ℝ) (hq : 4 < q) : Prop :=
  ∀ (μ : Measure (squareLattice.edgeSet → Bool)),
    IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ 0 μ →
  ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
    ∃ S : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
          Real.log (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0)
            (diagonalSite n)})) atTop (𝓝 (lam + 2 * S))

/-- Exact Theorem 1.2 conclusion from FK box-limit existence and the item-3
rate statement.  The rate is positive by Identity (4.4), so the existing
critical-discontinuity theorem supplies items 1 and 2. -/
theorem rc_theorem_1_2_from_item3 (q : ℝ) (hq : 4 < q)
    (hitem3 : rcItem3ForEveryFreeLimit q hq) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit
        (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable
                (0, 0) (diagonalSite n)})) atTop (𝓝 (lam + 2 * S))) := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩
  let qO : Set.Ioi (0 : ℝ) := ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩
  have hq1 : 1 ≤ q := by linarith
  obtain ⟨μ₀, hμ₀⟩ := FK.exists_isRCInfiniteVolumeLimit
    (rcCriticalParameter qI) qO hq1 0
  obtain ⟨μ₁, hμ₁⟩ := FK.exists_isRCInfiniteVolumeLimit
    (rcCriticalParameter qI) qO hq1 1
  let φ : Fin 2 → Measure (squareLattice.edgeSet → Bool) :=
    fun i => if i = 0 then μ₀ else μ₁
  have hφ : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter qI) qO i (φ i) := by
    intro i
    fin_cases i <;> simp [φ, hμ₀, hμ₁]
  have hφFrozen : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ i (φ i) := by
    intro i
    simpa [qI, qO] using hφ i
  have hfree : IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ 0 (φ 0) := hφFrozen 0
  have hitem3free := hitem3 (φ 0) hfree
  obtain ⟨hLam, hcosh⟩ := PottsDiscontinuity.arcosh_pos_of_gt4 q hq
  let lam := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨S, hS, hRate⟩ := hitem3free lam hLam hcosh
  obtain ⟨S₀, _T, hS₀, _hT, hpositive, _hidentity⟩ :=
    PottsDiscontinuity.identity44 lam hLam
  have hS₀' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * lam))
      atTop (𝓝 S₀) := by
    simpa [lam] using hS₀
  have hS' : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * lam))
      atTop (𝓝 S) := by
    simpa [lam] using hS
  have hSS : S = S₀ := tendsto_nhds_unique hS hS₀'
  have hL : 0 < lam + 2 * S := by
    rw [hSS]
    exact hpositive
  have hitems := Duality.rcm_items_one_two_of_pos_diagonal_rate
    q hq φ hφFrozen (lam + 2 * S) hL hRate
  refine ⟨φ, hφFrozen, hitems.1, hitems.2, ?_⟩
  intro lam hlam hcoshlam
  exact hitem3free lam hlam hcoshlam

end PottsDiscontinuity.RCMProof
