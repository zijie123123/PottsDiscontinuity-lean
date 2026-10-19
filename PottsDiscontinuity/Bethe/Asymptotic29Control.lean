module

public import PottsDiscontinuity.Bethe.AsymptoticSpatial
public import PottsDiscontinuity.Bethe.AsymptoticUniformOffset

/-! # The linear bound in Theorem 2.9 -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem offsetFunction_control_of_density_rate {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N : ι → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    {K : ℝ} (hK : 0 ≤ K)
    (herror : ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x -
        rho Δ x| ≤ K / N i ∧
      |rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x -
        rho Δ x| ≤ K / N i) :
    ∃ C > 0, ∃ D ≥ 0, ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x| ≤ C * |x| + D / N i := by
  obtain ⟨m, hm, hmρ⟩ := rho_uniform_lower_bound hΔ
  have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m ≤ rho Δ x := hmρ Δ le_rfl
  obtain ⟨C₀, hC₀, halign⟩ := offset_alignment_of_density_error hΔ hm hK hlower
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  let M := max M₀ 1 + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith [le_max_right M₀ 1]
  let H := C₀ * (2 * Real.exp C₀ + 1)
  let B := H * M
  let D := B * (2 * (2 * r + 1 : ℝ) / m)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hB : 0 ≤ B := mul_nonneg hH hM
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨B + 1, by linarith, D, hD, ?_⟩
  have hinv := tendsto_inv_atTop_zero.comp hNlim
  have hKlim : Tendsto (fun i => K / (N i : ℝ)) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using hinv.const_mul K
  filter_upwards [herror, hNlim.eventually (eventually_ge_atTop C₀),
    hKlim.eventually (gt_mem_nhds (show (0 : ℝ) < m / 2 by positivity)),
    hKlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with i hi hlarge hsmall hsmall1
  have hep : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x| ≤
        K / N i := fun x hx => (hi x hx).1
  have heq : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x - rho Δ x| ≤
        K / N i := fun x hx => (hi x hx).2
  have hb := halign (N i) r (h4 i) (hr i) (hN i) (hn i) (p i) (q i) (hp i) (hq i)
    hlarge hsmall.le hep heq
  have hupper : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x ≤ M := by
    intro x hx
    have he := (abs_le.mp (heq x hx)).2
    have hρ : rho Δ x ≤ M₀ := (le_abs_self _).trans (by simpa using hM₀ x hx)
    dsimp [M]
    linarith [le_max_left M₀ 1]
  have hpair := offset_root_lipschitz (h4 i) (hr i) (hN i) (hn i) (hq i) hH hupper hb.2
  let d := 2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ))
  have hlowq : ∀ x ∈ Icc (-Real.pi) Real.pi,
      m / 2 ≤ rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x := by
    intro x hx
    have := (abs_le.mp (heq x hx)).1
    have := hlower x hx
    linarith
  have hmesh (j : Fin (N i / 2 - r + 1)) :
      rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.succ -
        rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.castSucc ≤ d := by
    apply (rootPartition_gap_le_of_density_lower (hq i) (hn i) (two_mul_half_sub_le N r i) hm hlowq j).trans
    apply (div_le_div_iff_of_pos_right (mul_pos hm (Nat.cast_pos.mpr (hN i)))).mpr
    have hc : N i = 2 * (N i / 2 - r + r) := by
      obtain ⟨z, hz⟩ := h4 i
      have := hr i
      omega
    have hg := rootGapMultiplicity_le_offset (by omega : 2 * (N i / 2 - r) ≤ N i) hc j
    linarith
  have hsp := (offsetFunction_spatial_control (h4 i) (hr i) (hn i) (hp i) (hq i) hB hpair hmesh).1
  intro x hx
  apply (hsp x hx).trans
  have he : B * d = D / (N i : ℝ) := by dsimp [d, D]; ring
  rw [he]
  nlinarith only [abs_nonneg x]

/-- **Theorem 2.9, item 2**, with the source's weighted norm assumptions.
The conclusion holds for all sufficiently large indices, uniformly in `x`.
In fact this part uses only density control and symmetry. -/
theorem theorem29_control {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N : ι → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in l,
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) ≤ K / N i ∧
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
        (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) ≤ K / N i) :
    ∃ C > 0, ∃ D ≥ 0, ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x| ≤ C * |x| + D / N i := by
  let w := Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)
  have hw : 0 < w := density_weight_lower_pos hΔ
  apply offsetFunction_control_of_density_rate hΔ r N h4 hr hN hn p q hp hq hNlim
    (K := K / w) (div_nonneg hK hw.le)
  filter_upwards [hrate] with i hi x hx
  constructor
  · calc
      _ ≤ densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
          (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) / w :=
        abs_le_densityNorm_div hΔ _ (hbp i) hx
      _ ≤ (K / (N i : ℝ)) / w := div_le_div_of_nonneg_right hi.1 hw.le
      _ = (K / w) / (N i : ℝ) := by ring
  · calc
      _ ≤ densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
          (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) / w :=
        abs_le_densityNorm_div hΔ _ (hbq i) hx
      _ ≤ (K / (N i : ℝ)) / w := div_le_div_of_nonneg_right hi.2 hw.le
      _ = (K / w) / (N i : ℝ) := by ring

end PottsDiscontinuity.Bethe
