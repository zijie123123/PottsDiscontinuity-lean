module

public import PottsDiscontinuity.Bethe.Theorem23Quadrature

/-! # Exact physical masses of the discrete and continuous densities -/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem root_step_subcell_mass {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {a b : ℝ} (hab : a ≤ b) (ha : rootPartitionPoint n p hn j.castSucc ≤ a)
    (hb : b ≤ rootPartitionPoint n p hn j.succ) :
    (∫ x in a..b, rootStepDensity N n p hp hn hs x) =
      (b - a) * rootGapMultiplicity N n hs j /
        ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)) := by
  have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) hab
    (f := rootStepDensity N n p hp hn hs)
    (g := fun _ : ℝ => rootGapMultiplicity N n hs j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)))
    (fun x hx => rootStepDensity_on_cell hp hn hs j ⟨ha.trans hx.1.le, hx.2.trans_le hb⟩)
  rw [heq, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem root_step_physical_mass {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) :
    (∫ x in (-Real.pi)..Real.pi, rootStepDensity N (k + 1) p hp (by omega) hs x) =
      1 / 2 + (r : ℝ) / N := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  have hi : ∀ a b, IntervalIntegrable s volume a b := by
    intro a b
    simpa [s] using intervalIntegrable_mul_rootStepDensity p hp (by omega) hs
      (g := fun _ => (1 : ℝ)) continuous_const a b
  have hsym : p (Fin.last k) = -p 0 := by
    have h := hp.2.2 (0 : Fin (k + 1))
    simpa using h
  have hfirstpos : 0 < p 0 + Real.pi := by linarith [(hp.1 0).1]
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := by
    convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
  have hfirst : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
    convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 1
    congr 1
  have hlast : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
      p (Fin.last k) := by
    convert rootPartitionPoint_root p (by omega) (Fin.last k) using 1
    congr 1
  have hend : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
      p 0 + 2 * Real.pi := by
    convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
  have hnat : N + 1 - 2 * (k + 1) = 2 * r + 1 := by omega
  have hmult (j : Fin (k + 2)) (hj : j.val = 0 ∨ j.val = k + 1) :
      rootGapMultiplicity N (k + 1) hs j = (2 * r + 1 : ℝ) := by
    rw [rootGapMultiplicity, ite_eq_left hj, hnat]
    push_cast
    ring
  have hleft : (∫ x in (-Real.pi)..p 0, s x) = (2 * r + 1 : ℝ) / (2 * (N : ℝ)) := by
    have h := root_step_subcell_mass hp (by omega) hs (0 : Fin (k + 2))
      (hp.1 0).1.le (by rw [hzero]; linarith [(hp.1 (Fin.last k)).2]) (by rw [hfirst])
    change (∫ x in (-Real.pi)..p 0, s x) = _ at h
    rw [hzero, hfirst, hmult _ (by simp), hsym] at h
    rw [h]
    have hden : p 0 - (-p 0 - 2 * Real.pi) = 2 * (p 0 + Real.pi) := by ring
    rw [hden]
    field_simp [ne_of_gt hN, ne_of_gt hfirstpos]
    ring
  have hright : (∫ x in p (Fin.last k)..Real.pi, s x) =
      (2 * r + 1 : ℝ) / (2 * (N : ℝ)) := by
    have h := root_step_subcell_mass hp (by omega) hs (Fin.last (k + 1))
      (hp.1 (Fin.last k)).2.le (by rw [hlast])
      (by rw [hend]; linarith [(hp.1 0).1])
    change (∫ x in p (Fin.last k)..Real.pi, s x) = _ at h
    rw [hlast, hend, hmult _ (by simp), hsym] at h
    rw [hsym, h]
    have hden : p 0 + 2 * Real.pi - -p 0 = 2 * (p 0 + Real.pi) := by ring
    rw [hden]
    field_simp [ne_of_gt hN, ne_of_gt hfirstpos]
    ring
  have hcell (j : Fin k) : (∫ x in p j.castSucc..p j.succ, s x) = 1 / (N : ℝ) := by
    let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
    have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
      convert rootPartitionPoint_root p (by omega) j.castSucc using 1
      congr 1
    have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
      convert rootPartitionPoint_root p (by omega) j.succ using 1
      congr 1
    have hm : rootGapMultiplicity N (k + 1) hs cell = 1 := by
      simp only [rootGapMultiplicity, cell,
        ite_eq_right (by omega : ¬ (j.val + 1 = 0 ∨ j.val + 1 = k + 1))]
    simpa only [ha, hb, hm] using root_step_full_cell_mass hp (by omega) hs cell
  have hmiddle : (∫ x in p 0..p (Fin.last k), s x) = (k : ℝ) / N := by
    rw [← sum_fin_step_integrals_adjacent k p hi]
    simp_rw [hcell]
    simp
    ring
  have hsplit : (∫ x in (-Real.pi)..Real.pi, s x) =
      (∫ x in (-Real.pi)..p 0, s x) + (∫ x in p 0..p (Fin.last k), s x) +
        (∫ x in p (Fin.last k)..Real.pi, s x) := by
    rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  rw [hsplit, hleft, hright, hmiddle]
  have hcountc : (N : ℝ) = 2 * ((k : ℝ) + 1 + (r : ℝ)) := by exact_mod_cast hcount
  field_simp [ne_of_gt hN]
  nlinarith only [hcountc]

theorem integral_Rsech {lam : ℝ} (hlam : 0 < lam) :
    (∫ α in (-Real.pi)..Real.pi, Rsech lam α) = Real.pi := by
  have heq : Rsech lam = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) :=
    funext (Rsech_eq_trigSeries hlam)
  have h := cosCoeff_trigSeries_zero (summable_secCoeff hlam) summable_zero (1 / 2)
  rw [← heq, cosCoeff_zero] at h
  linarith

theorem integral_rho_mass {Δ : ℝ} (hΔ : Δ < -1) :
    (∫ x in (-Real.pi)..Real.pi, rho Δ x) = 1 / 2 := by
  have hlam := lamOf_pos hΔ
  rw [integral_Icc_comp_kMap hlam]
  have heq : (fun α => Xi (lamOf Δ) α * rho Δ (kMap (lamOf Δ) α)) =
      fun α => (2 * Real.pi)⁻¹ * Rsech (lamOf Δ) α := by
    funext α
    have h := Rtrans_rho hΔ α
    rw [Rtrans_eq hΔ] at h
    field_simp
    nlinarith only [h]
  rw [heq, intervalIntegral.integral_const_mul, integral_Rsech hlam]
  field_simp

end PottsDiscontinuity.Bethe
