module

public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Quantitative quadrature against the root step density -/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem intervalIntegrable_mul_rootStepDensity {N n : ℕ} (p : Fin n → ℝ)
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * rootStepDensity N n p hp hn hs x) volume a b := by
  classical
  let c : Fin (n + 1) → ℝ := fun j => rootGapMultiplicity N n hs j /
    ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc))
  have heq : (fun x => g x * rootStepDensity N n p hp hn hs x) =
      ∑ j : Fin (n + 1),
        (Ico (rootPartitionPoint n p hn j.castSucc) (rootPartitionPoint n p hn j.succ)).indicator
          (fun x => g x * c j) := by
    funext x
    simp [rootStepDensity, Finset.mul_sum, c, Set.indicator, Set.mem_Ico, mul_ite]
  rw [heq]
  apply IntervalIntegrable.sum
  intro j _
  rw [intervalIntegrable_iff]
  exact ((hg.mul continuous_const).intervalIntegrable a b).def'.indicator measurableSet_Ico

theorem rootGapMultiplicity_nonneg {N n : ℕ} (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    0 ≤ rootGapMultiplicity N n hs j := by
  unfold rootGapMultiplicity
  split <;> positivity

/-- The integral over any subinterval of one cell is bounded by its full cell
mass times a bound for the test function. -/
theorem root_step_cell_integral_bound {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    (j : Fin (n + 1)) {a b G : ℝ} (hG : 0 ≤ G)
    (hab : a ≤ b) (ha : rootPartitionPoint n p hn j.castSucc ≤ a)
    (hb : b ≤ rootPartitionPoint n p hn j.succ)
    {g : ℝ → ℝ} (hbound : ∀ x ∈ Icc a b, |g x| ≤ G) :
    |∫ x in a..b, g x * rootStepDensity N n p hp hn hs x| ≤
      G * rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hgap := rootPartition_gap_pos hp hn j
  let d := rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc
  let c := rootGapMultiplicity N n hs j / ((N : ℝ) * d)
  have hc : 0 ≤ c := div_nonneg (rootGapMultiplicity_nonneg hs j) (by positivity)
  have hpoint : ∀ᵐ x : ℝ, x ∈ uIoc a b →
      ‖g x * rootStepDensity N n p hp hn hs x‖ ≤ G * c := by
    filter_upwards [volume.ae_ne b] with x hne hx
    rw [uIoc_of_le hab] at hx
    have hxlt : x < b := lt_of_le_of_ne hx.2 hne
    have hcell : rootPartitionPoint n p hn j.castSucc ≤ x ∧
        x < rootPartitionPoint n p hn j.succ :=
      ⟨ha.trans hx.1.le, hxlt.trans_le hb⟩
    rw [rootStepDensity_on_cell hp hn hs j hcell, Real.norm_eq_abs, abs_mul]
    change |g x| * |c| ≤ G * c
    rw [abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le, hx.2⟩) hc
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := a) (b := b) hpoint
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  have hlen : b - a ≤ d := by dsimp [d]; linarith
  calc
    _ ≤ (G * c) * (b - a) := hi
    _ ≤ (G * c) * d := mul_le_mul_of_nonneg_left hlen (mul_nonneg hG hc)
    _ = G * rootGapMultiplicity N n hs j / (N : ℝ) := by
      dsimp [c, d]
      field_simp [ne_of_gt hN, ne_of_gt hgap]

theorem root_step_full_cell_mass {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1)) :
    (∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
      rootStepDensity N n p hp hn hs x) = rootGapMultiplicity N n hs j / (N : ℝ) := by
  have hgap := rootPartition_gap_pos hp hn j
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (sub_pos.mp hgap).le
    (f := rootStepDensity N n p hp hn hs)
    (g := fun _ : ℝ => rootGapMultiplicity N n hs j /
      ((N : ℝ) * (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)))
    (fun x hx => rootStepDensity_on_cell hp hn hs j ⟨hx.1.le, hx.2⟩)
  rw [heq, intervalIntegral.integral_const, smul_eq_mul]
  field_simp [ne_of_gt hN, ne_of_gt hgap]

theorem root_step_full_cell_error {N n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N) (j : Fin (n + 1))
    {g : ℝ → ℝ} (hg : Continuous g) {w : ℝ} (hw : 0 ≤ w)
    (hmod : ∀ x ∈ Icc (rootPartitionPoint n p hn j.castSucc)
      (rootPartitionPoint n p hn j.succ),
      |g x - g (rootPartitionPoint n p hn j.castSucc)| ≤ w) :
    |(∫ x in rootPartitionPoint n p hn j.castSucc..rootPartitionPoint n p hn j.succ,
        g x * rootStepDensity N n p hp hn hs x) -
      g (rootPartitionPoint n p hn j.castSucc) * rootGapMultiplicity N n hs j / (N : ℝ)| ≤
      w * rootGapMultiplicity N n hs j / (N : ℝ) := by
  let a := rootPartitionPoint n p hn j.castSucc
  let b := rootPartitionPoint n p hn j.succ
  let s := rootStepDensity N n p hp hn hs
  have hgap := rootPartition_gap_pos hp hn j
  have hi := root_step_cell_integral_bound hp hn hs j hw (sub_pos.mp hgap).le
    le_rfl le_rfl (g := fun x => g x - g a) hmod
  have hf := intervalIntegrable_mul_rootStepDensity p hp hn hs hg a b
  have hc := intervalIntegrable_mul_rootStepDensity p hp hn hs
    (g := fun _ => g a) continuous_const a b
  have heq : (fun x => (g x - g a) * s x) = fun x => g x * s x - g a * s x := by
    funext x
    ring
  have hid : (∫ x in a..b, (g x - g a) * s x) =
      (∫ x in a..b, g x * s x) - g a * rootGapMultiplicity N n hs j / (N : ℝ) := by
    rw [heq, intervalIntegral.integral_sub hf hc, intervalIntegral.integral_const_mul]
    change _ - g a * (∫ x in a..b, rootStepDensity N n p hp hn hs x) = _
    rw [root_step_full_cell_mass hp hn hs j]
    ring
  change |∫ x in a..b, (g x - g a) * s x| ≤ _ at hi
  rw [hid] at hi
  exact hi

theorem sum_fin_step_integrals_adjacent (k : ℕ) (p : Fin (k + 1) → ℝ)
    {F : ℝ → ℝ} (hF : ∀ a b, IntervalIntegrable F volume a b) :
    (∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, F x) =
      ∫ x in p 0..p (Fin.last k), F x := by
  let P : ℝ → ℝ := fun y => ∫ x in p 0..y, F x
  have heq (j : Fin k) : (∫ x in p j.castSucc..p j.succ, F x) =
      P (p j.succ) - P (p j.castSucc) :=
    (intervalIntegral.integral_interval_sub_left (hF _ _) (hF _ _)).symm
  simp_rw [heq]
  rw [sum_fin_adjacent_sub k (fun j => P (p j))]
  simp only [P, integral_same, sub_zero]

theorem root_step_boundary_integral_bounds {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) {g : ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G) :
    |∫ x in (-Real.pi)..p 0, g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) ∧
      |∫ x in p (Fin.last k)..Real.pi,
        g x * rootStepDensity N (k + 1) p hp (by omega) hs x| ≤
        G * (2 * r + 1 : ℝ) / (N : ℝ) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) ≤ N := by positivity
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
  constructor
  · have hi := root_step_cell_integral_bound hp (by omega) hs (0 : Fin (k + 2)) hG
      (hp.1 0).1.le (by rw [hzero]; linarith [(hp.1 (Fin.last k)).2])
      (by rw [hfirst]) (g := g)
      (fun x hx => hbound x ⟨hx.1, hx.2.trans (hp.1 0).2.le⟩)
    apply hi.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hG) hN
  · have hi := root_step_cell_integral_bound hp (by omega) hs (Fin.last (k + 1)) hG
      (hp.1 (Fin.last k)).2.le (by rw [hlast])
      (by rw [hend]; linarith [(hp.1 0).1]) (g := g)
      (fun x hx => hbound x ⟨(hp.1 (Fin.last k)).1.le.trans hx.1, hx.2⟩)
    apply hi.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hs hcount _) hG) hN

/-- Finite quadrature for the actual step density. No closeness to `ρ` is
assumed. The two boundary masses are retained in the error term. -/
theorem root_step_quadrature_error {N k r : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    (hcount : N = 2 * ((k + 1) + r)) {g : ℝ → ℝ} (hg : Continuous g)
    {G L d : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hLip : ∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
      |g x - g y| ≤ L * |x - y|)
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) :
    |(∫ x in (-Real.pi)..Real.pi,
        g x * rootStepDensity N (k + 1) p hp (by omega) hs x) -
      (∑ j, g (p j)) / (N : ℝ)| ≤
        L * d + (2 * G * (2 * r + 1 : ℝ) + G) / (N : ℝ) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hkc : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
  let s := rootStepDensity N (k + 1) p hp (by omega) hs
  let F := fun x => g x * s x
  have hF : ∀ a b, IntervalIntegrable F volume a b :=
    intervalIntegrable_mul_rootStepDensity p hp (by omega) hs hg
  obtain ⟨_, _, hinterior⟩ := root_mesh_consequences hp hmesh
  have hcell (j : Fin k) :
      |(∫ x in p j.castSucc..p j.succ, F x) - g (p j.castSucc) / (N : ℝ)| ≤
        L * d / (N : ℝ) := by
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
    have hmod : ∀ x ∈ Icc (rootPartitionPoint (k + 1) p (by omega) cell.castSucc)
        (rootPartitionPoint (k + 1) p (by omega) cell.succ),
        |g x - g (rootPartitionPoint (k + 1) p (by omega) cell.castSucc)| ≤ L * d := by
      rw [ha, hb]
      intro x hx
      have hxpi : x ∈ Icc (-Real.pi) Real.pi :=
        ⟨(hp.1 j.castSucc).1.le.trans hx.1, hx.2.trans (hp.1 j.succ).2.le⟩
      have hjpi : p j.castSucc ∈ Icc (-Real.pi) Real.pi :=
        ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩
      apply (hLip x hxpi _ hjpi).trans
      apply mul_le_mul_of_nonneg_left _ hL
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      exact (sub_le_sub_right hx.2 _).trans (hinterior j)
    have hi := root_step_full_cell_error hp (by omega) hs cell hg (mul_nonneg hL hd) hmod
    rw [ha, hb, hm, mul_one, mul_one] at hi
    exact hi
  have hmiddle : |(∫ x in p 0..p (Fin.last k), F x) -
      (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)| ≤ L * d := by
    calc
      _ = |∑ j : Fin k, ((∫ x in p j.castSucc..p j.succ, F x) -
          g (p j.castSucc) / (N : ℝ))| := by
        rw [Finset.sum_sub_distrib, sum_fin_step_integrals_adjacent k p hF, Finset.sum_div]
      _ ≤ ∑ j : Fin k, |(∫ x in p j.castSucc..p j.succ, F x) -
          g (p j.castSucc) / (N : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, L * d / (N : ℝ) := Finset.sum_le_sum (fun j _ => hcell j)
      _ = (k : ℝ) * (L * d / (N : ℝ)) := by simp
      _ = ((k : ℝ) * (L * d)) / (N : ℝ) := by ring
      _ ≤ L * d := (div_le_iff₀ hN).2 (by
        have h := mul_le_mul_of_nonneg_right hkc (mul_nonneg hL hd)
        nlinarith only [h])
  obtain ⟨hleft, hright⟩ := root_step_boundary_integral_bounds hp hs hcount hG hbound
  have hlast : |g (p (Fin.last k)) / (N : ℝ)| ≤ G / (N : ℝ) := by
    rw [abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right
      (hbound _ ⟨(hp.1 (Fin.last k)).1.le, (hp.1 (Fin.last k)).2.le⟩) hN.le
  have hsplit : (∫ x in (-Real.pi)..Real.pi, F x) =
      (∫ x in (-Real.pi)..p 0, F x) +
      (∫ x in p 0..p (Fin.last k), F x) +
      (∫ x in p (Fin.last k)..Real.pi, F x) := by
    rw [integral_add_adjacent_intervals (hF _ _) (hF _ _),
      integral_add_adjacent_intervals (hF _ _) (hF _ _)]
  change |(∫ x in (-Real.pi)..Real.pi, F x) - _| ≤ _
  rw [hsplit, Fin.sum_univ_castSucc, add_div]
  have htri (a b c u v : ℝ) : |a + b + c - (u + v)| ≤
      |a| + |b - u| + |c| + |v| := by
    have h1 := abs_sub (a + (b - u) + c) v
    have h2 := abs_add_le (a + (b - u)) c
    have h3 := abs_add_le a (b - u)
    have heq : a + b + c - (u + v) = a + (b - u) + c - v := by ring
    rw [heq]
    linarith only [h1, h2, h3]
  calc
    _ ≤ |∫ x in (-Real.pi)..p 0, F x| +
        |(∫ x in p 0..p (Fin.last k), F x) -
          (∑ j : Fin k, g (p j.castSucc)) / (N : ℝ)| +
        |∫ x in p (Fin.last k)..Real.pi, F x| +
        |g (p (Fin.last k)) / (N : ℝ)| := htri _ _ _ _ _
    _ ≤ G * (2 * r + 1 : ℝ) / (N : ℝ) + L * d +
        G * (2 * r + 1 : ℝ) / (N : ℝ) + G / (N : ℝ) := by gcongr
    _ = _ := by ring

/-- The Bethe derivative kernel has quadrature error `O(1/N)` against the
step density, uniformly in the first coordinate and in `Δ ≤ Δ₀`. -/
theorem exists_uniform_step_kernel_quadrature {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀, ∀ x ∈ Icc (-Real.pi) Real.pi,
      ∀ (N k r : ℕ) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
        (hs : 2 * (k + 1) ≤ N), N = 2 * ((k + 1) + r) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ j : Fin (k + 2),
        rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ D / (N : ℝ)) →
      |(∫ y in (-Real.pi)..Real.pi,
          d1Theta Δ x y * rootStepDensity N (k + 1) p hp (by omega) hs y) -
        (∑ j, d1Theta Δ x (p j)) / (N : ℝ)| ≤
          (C * D + 2 * C * (2 * r + 1 : ℝ) + C) / (N : ℝ) := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_d1Theta_bounds hΔ₀
  refine ⟨C, hC, fun Δ hΔ x hx N k r p hp hs hcount D hD hmesh => ?_⟩
  have hΔvalid := lt_of_le_of_lt hΔ hΔ₀
  have hbound : ∀ y ∈ Icc (-Real.pi) Real.pi, |d1Theta Δ x y| ≤ C :=
    fun y hy => ((hkernel Δ hΔ).1 x hx y hy).1
  have hLip : ∀ y ∈ Icc (-Real.pi) Real.pi, ∀ z ∈ Icc (-Real.pi) Real.pi,
      |d1Theta Δ x y - d1Theta Δ x z| ≤ C * |y - z| := by
    intro y hy z hz
    simpa using (hkernel Δ hΔ).2 x hx y hy x hx z hz
  have hi := root_step_quadrature_error hp hs hcount (continuous_d1Theta_right hΔvalid x)
    hC.le hC.le (div_nonneg hD (Nat.cast_nonneg _)) hbound hLip hmesh
  calc
    _ ≤ C * (D / (N : ℝ)) + (2 * C * (2 * r + 1 : ℝ) + C) / (N : ℝ) := hi
    _ = _ := by ring

end PottsDiscontinuity.Bethe
