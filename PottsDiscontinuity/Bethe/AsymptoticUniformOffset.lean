module

public import PottsDiscontinuity.Bethe.AsymptoticAlignment
public import PottsDiscontinuity.Bethe.AsymptoticGronwall
public import PottsDiscontinuity.Bethe.AsymptoticRegularity

/-! # Uniform offset bounds from density errors -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem fin_centered_discrete_gronwall {n N : ℕ} (hn : 0 < n)
    (hN : 0 < N) (hnN : n ≤ N) {C : ℝ} (hC : 0 ≤ C) (hsmall : C ≤ N)
    (u : Fin n → ℝ) (hsym : ∀ j, u (Fin.rev j) = -u j)
    (hstep : ∀ j (hj : j + 1 < n),
      |u ⟨j + 1, hj⟩ - u ⟨j, by omega⟩| ≤ C / N * (|u ⟨j, by omega⟩| + 1)) :
    (∀ j, |u j| ≤ 2 * Real.exp C) ∧
      (∀ j (hj : j + 1 < n),
        |u ⟨j + 1, hj⟩ - u ⟨j, by omega⟩| ≤ C * (2 * Real.exp C + 1) / N) := by
  let v : ℕ → ℝ := fun j => u ⟨min j (n - 1), by omega⟩
  have hv (j : ℕ) (hj : j < n) : v j = u ⟨j, hj⟩ := by
    dsimp [v]
    congr 1
    exact Fin.ext (min_eq_left (by omega))
  have hs (j : ℕ) (hj : j ≤ n - 1) : v (n - 1 - j) = -v j := by
    rw [hv _ (by omega), hv _ (by omega)]
    convert hsym ⟨j, by omega⟩ using 1
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hd (j : ℕ) (hj : j < n - 1) :
      |v (j + 1) - v j| ≤ C / N * (|v j| + 1) := by
    simpa only [hv _ (by omega : j + 1 < n), hv _ (by omega : j < n)] using hstep j (by omega)
  obtain ⟨hb, hi⟩ := centered_discrete_gronwall hN (show n - 1 ≤ N by omega) hC hsmall hs hd
  constructor
  · intro j
    simpa only [hv j.val j.isLt] using hb j.val (by omega)
  · intro j hj
    simpa only [hv _ hj, hv _ (by omega : j < n)] using hi j (by omega)

/-- Finite uniform alignment and increment bounds for both parity clauses of
(2.13). The premises here are spacing estimates, and are proved from the
density error in `offset_alignment_of_density_error` below. -/
theorem offset_alignment_of_spacing {N r : ℕ} (h4 : 4 ∣ N)
    (hr : r ≤ N / 2) (hN : 0 < N) (hn : 0 < N / 2 - r)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r))
    {Δ A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) {L : NNReal}
    (hL : LipschitzOnWith L (fun z => (rho Δ z)⁻¹) (Icc (-Real.pi) Real.pi))
    (hsmall : A + (L : ℝ) * D + B + L ≤ N)
    (hpSpacing : ∀ j (hj : j + 1 < N / 2),
      |(N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) -
        (rho Δ (p ⟨j, by omega⟩))⁻¹| ≤ A / N)
    (hqSpacing : ∀ j (hj : j + 1 < N / 2 - r),
      |(N : ℝ) * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩) -
        (rho Δ (q ⟨j, by omega⟩))⁻¹| ≤ B / N)
    (hpGap : ∀ j (hj : j + 1 < N / 2),
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N) :
    let C := A + (L : ℝ) * D + B + L
    (∀ j, |offsetDisplacement N r h4 hr p q j| ≤ 2 * Real.exp C) ∧
      (∀ j (hj : j + 1 < N / 2 - r),
        |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
          offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤
          C * (2 * Real.exp C + 1) / N) := by
  let C := A + (L : ℝ) * D + B + L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply fin_centered_discrete_gronwall hn hN (by omega) hC hsmall
    (offsetDisplacement N r h4 hr p q) (offsetDisplacement_rev h4 hr hp hq)
  intro j hj
  have hi := offsetDisplacement_increment h4 hr hN hp hq hD hL hpSpacing hqSpacing hpGap j hj
  apply hi.trans
  have h₁ : A + (L : ℝ) * D + B ≤ C := by dsimp [C]; linarith [L.coe_nonneg]
  have h₂ : (L : ℝ) ≤ C := by dsimp [C]; linarith [mul_nonneg L.coe_nonneg hD]
  have he := mul_le_mul_of_nonneg_right
    ((div_le_div_iff_of_pos_right hNp).mpr h₂)
    (abs_nonneg (offsetDisplacement N r h4 hr p q ⟨j, by omega⟩))
  have hd := (div_le_div_iff_of_pos_right hNp).mpr h₁
  dsimp [C] at *
  nlinarith only [he, hd]

/-- The missing alignment estimate in the printed proof, derived from the
actual density errors. In particular no alignment premise, Bethe-equation
expansion, or increment estimate is assumed. The constants work for both
parities of the deficit. -/
theorem offset_alignment_of_density_error {Δ m K : ℝ} (hΔ : Δ < -1)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hlower : ∀ x ∈ Icc (-Real.pi) Real.pi, m ≤ rho Δ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N r : ℕ) (h4 : 4 ∣ N) (hr : r ≤ N / 2)
      (hN : 0 < N) (hn : 0 < N / 2 - r)
      (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ)
      (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r)),
      C ≤ N → K / N ≤ m / 2 →
      (∀ x ∈ Icc (-Real.pi) Real.pi,
        |rootStepDensity N (N / 2) p hp (by omega) (by omega) x - rho Δ x| ≤ K / N) →
      (∀ x ∈ Icc (-Real.pi) Real.pi,
        |rootStepDensity N (N / 2 - r) q hq hn (by omega) x - rho Δ x| ≤ K / N) →
      (∀ j, |offsetDisplacement N r h4 hr p q j| ≤ 2 * Real.exp C) ∧
      (∀ j (hj : j + 1 < N / 2 - r),
        |offsetDisplacement N r h4 hr p q ⟨j + 1, hj⟩ -
          offsetDisplacement N r h4 hr p q ⟨j, by omega⟩| ≤
          C * (2 * Real.exp C + 1) / N) := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_inv_rho hΔ
  let A := 2 * K / m ^ 2
  let D := 1 / m + A
  let C := A + (L : ℝ) * D + A + L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N r h4 hr hN hn p q hp hq hlarge hsmall hpError hqError
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hAdiv : A / N ≤ A := (div_le_iff₀ hNp).mpr (by nlinarith)
  have hpSpacing (j : ℕ) (hj : j + 1 < N / 2) :
      |(N : ℝ) * (p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩) -
        (rho Δ (p ⟨j, by omega⟩))⁻¹| ≤ A / N := by
    have hi := root_spacing_error_at hp (by omega) (by omega) hm hsmall hlower hpError j hj
    convert hi using 1; dsimp [A]; ring
  have hqSpacing (j : ℕ) (hj : j + 1 < N / 2 - r) :
      |(N : ℝ) * (q ⟨j + 1, hj⟩ - q ⟨j, by omega⟩) -
        (rho Δ (q ⟨j, by omega⟩))⁻¹| ≤ A / N := by
    have hi := root_spacing_error_at hq hn (by omega) hm hsmall hlower hqError j hj
    convert hi using 1; dsimp [A]; ring
  have hpGap (j : ℕ) (hj : j + 1 < N / 2) :
      p ⟨j + 1, hj⟩ - p ⟨j, by omega⟩ ≤ D / N := by
    have he := (abs_le.mp (hpSpacing j hj)).2
    have hρ := hlower (p ⟨j, by omega⟩) ⟨(hp.1 _).1.le, (hp.1 _).2.le⟩
    have hi : (rho Δ (p ⟨j, by omega⟩))⁻¹ ≤ 1 / m := by
      simpa only [one_div] using one_div_le_one_div_of_le hm hρ
    apply (le_div_iff₀ hNp).mpr
    dsimp [D]
    nlinarith only [he, hi, hAdiv]
  exact offset_alignment_of_spacing h4 hr hN hn hp hq hA hA hD hL hlarge
    hpSpacing hqSpacing hpGap

end PottsDiscontinuity.Bethe
