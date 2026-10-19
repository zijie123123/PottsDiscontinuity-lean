module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Density

/-!
# Density control of cyclic root gaps

These are consequences of a weighted density error bound.  They isolate the
gap estimate used in the source's regularity consequences without assuming
that the discrete and continuous densities have matching total mass.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- A weighted density norm error gives an unweighted pointwise error on the
physical interval. -/
theorem densityNorm_rootStepDensity_pointwise {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |rootStepDensity N n p hp hn hs x - rho Δ x| ≤
      E / mXi := by
  exact densityNorm_x_pointwise_le hΔ₀ hΔ
    (fun y => rootStepDensity N n p hp hn hs y - rho Δ y)
    hbdd E mXi hmXi (hXi Δ hΔ) hE hx

/-- If the density error is at most half the uniform lower bound for `ρ`,
then the step density has a positive lower bound on every physical root cell. -/
theorem rootStepDensity_lower_of_densityNorm {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {N n : ℕ} (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
    (mρ : ℝ) (_hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hsmall : E / mXi ≤ mρ / 2) :
    ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N n p hp hn hs x := by
  have herr (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) :
      |rootStepDensity N n p hp hn hs x - rho Δ x| ≤ E / mXi :=
    densityNorm_x_pointwise_le hΔ₀ hΔ
      (fun y => rootStepDensity N n p hp hn hs y - rho Δ y)
      hbdd E mXi hmXi (hXi Δ hΔ) hE hx
  have hsmall' : E / mXi ≤ mρ / 2 := hsmall
  intro x hx
  have hρx := hρ Δ hΔ x hx
  have hxerr := herr x hx
  rw [abs_sub_comm] at hxerr
  have hupper := (abs_le.mp hxerr).2
  linarith

/-- A norm error small compared with the uniform density lower bound forces
an upper bound on every cyclic root gap. -/
theorem rootPartition_gap_upper_of_densityNorm {Δ₀ Δ : ℝ}
    (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
    (mρ : ℝ) (hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hsmall : E / mXi ≤ mρ / 2)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n hs j / (mρ * (N : ℝ)) := by
  have hlower : ∀ x ∈ Icc (-Real.pi) Real.pi,
      mρ / 2 ≤ rootStepDensity N n p hp hn hs x := by
    apply rootStepDensity_lower_of_densityNorm hΔ₀ hΔ p hp hn hs hmXi hXi hbdd hE
      mρ hmρ hρ
    exact hsmall
  exact rootPartition_gap_le_of_density_lower hp hn hs hmρ hlower j

/-- The source's upper root-gap estimate, derived from a `K/N` density error.
The explicit smallness condition is the finite-`N` requirement that the
unweighted error be at most half the uniform lower bound for `ρ`. -/
theorem rootPartition_gap_upper_of_norm_le {Δ₀ Δ : ℝ}
    (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (mρ : ℝ) (hmρ : 0 < mρ)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ →
      ∀ x ∈ Icc (-Real.pi) Real.pi, mρ ≤ rho Δ' x)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ}
    (hNorm : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ K / N)
    (hsmall : K / ((N : ℝ) * mXi) ≤ mρ / 2)
    (j : Fin (n + 1)) :
    rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤
      2 * rootGapMultiplicity N n hs j / (mρ * (N : ℝ)) := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hsmall' : (K / (N : ℝ)) / mXi ≤ mρ / 2 := by
    have heq : (K / (N : ℝ)) / mXi = K / ((N : ℝ) * mXi) := by
      field_simp
    rw [heq]
    exact hsmall
  exact rootPartition_gap_upper_of_densityNorm hΔ₀ hΔ p hp hn hs
    hmXi hXi hbdd hNorm mρ hmρ hρ hsmall' j

/-- The same pointwise estimate gives an upper bound for the step density when
the continuous density has a uniform upper bound. -/
theorem rootStepDensity_upper_of_densityNorm {Δ₀ Δ : ℝ}
    (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E M : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x : ℝ, rho Δ' x ≤ M)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    rootStepDensity N n p hp hn hs x ≤ M + E / mXi := by
  have herr : |rootStepDensity N n p hp hn hs x - rho Δ x| ≤ E / mXi :=
    densityNorm_rootStepDensity_pointwise hΔ₀ hΔ p hp hn hs hmXi hXi
      hbdd hE hx
  have hupper := (abs_le.mp herr).2
  have hρx := hρ Δ hΔ x
  linarith

/-- An upper bound on `ρ_p` gives a lower bound for each cyclic root gap. -/
theorem rootPartition_gap_lower_of_densityNorm {Δ₀ Δ : ℝ}
    (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) {N n : ℕ}
    (p : Fin n → ℝ) (hp : p ∈ S_n n) (hn : 0 < n) (hs : 2 * n ≤ N)
    {mXi : ℝ} (hmXi : 0 < mXi)
    (hXi : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ α : ℝ, mXi ≤ Xi (lamOf Δ') α)
    (hbdd : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity N n p hp hn hs (kMap (lamOf Δ) α) -
          rho Δ (kMap (lamOf Δ) α))|))
    {E M : ℝ} (hE : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
      (fun x => rootStepDensity N n p hp hn hs x - rho Δ x) hbdd ≤ E)
    (hρ : ∀ Δ' : ℝ, Δ' ≤ Δ₀ → ∀ x : ℝ, rho Δ' x ≤ M)
    (hbound : 0 < M + E / mXi) (j : Fin (n + 1)) :
    rootGapMultiplicity N n hs j /
        ((N : ℝ) * (M + E / mXi)) ≤
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc := by
  have hNnat : 0 < N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hgap : 0 < rootPartitionPoint n p hn j.succ -
      rootPartitionPoint n p hn j.castSucc :=
    rootPartition_gap_pos hp hn j
  obtain ⟨x, hx, hcell⟩ := rootPartition_cell_meets_Icc hp hn j
  have hρp := rootStepDensity_upper_of_densityNorm hΔ₀ hΔ p hp hn hs
    hmXi hXi hbdd hE hρ hx
  rw [rootStepDensity_on_cell hp hn hs j hcell] at hρp
  have hden : 0 < (N : ℝ) *
      (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc) :=
    mul_pos hN hgap
  have hmul := (div_le_iff₀ hden).mp hρp
  apply (div_le_iff₀ (mul_pos hN hbound)).2
  calc
    rootGapMultiplicity N n hs j ≤
        (M + E / mXi) * ((N : ℝ) *
          (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc)) := hmul
    _ = (rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc) *
        ((N : ℝ) * (M + E / mXi)) := by ring

end PottsDiscontinuity.Bethe
