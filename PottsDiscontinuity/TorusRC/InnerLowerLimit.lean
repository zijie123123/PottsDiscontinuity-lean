module

public import PottsDiscontinuity.TorusRC.LowerEstimate
public import PottsDiscontinuity.TorusRC.BoxProbability
public import PottsDiscontinuity.TorusRC.LogRateLimits

/-! # The height limit in the lower bound of Lemma 3.15 -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

/-- Height-normalized log probability of U=1 along positive even heights.
The extended-real carrier permits an unbounded negative rate. -/
noncomputable def torusRCUOneRateE {N : ℕ} (hN : Even N)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) : EReal :=
  ((Real.log (torusRCProbability hN (positiveEvenPeriod_even m) q
    {A | rcVerticalWinding hN (positiveEvenPeriod_even m)
      ⟨0,positiveEvenPeriod_pos m⟩ A = 1}) / (positiveEvenPeriod m:ℝ):ℝ):EReal)

/-- The inner M→∞ passage of (3.15), with actual native free-box
probabilities. All finite-energy losses are independent of M. -/
theorem torusRCU_one_inner_liminf_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (N n : ℕ) (hN : Even N)
      (_hN4 : 4 ≤ N) (_hNdiv : 8 ∣ N) (_hn : 2 ≤ n) (_h8nN : 8*n ≤ N),
      ((Real.log (c/(9*(n:ℝ)^2))/(n:ℝ) +
        Real.log (liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
          rotatedLatticeOrigin (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n)) /
          ((2*n:ℕ):ℝ):ℝ):EReal) ≤ liminf (torusRCUOneRateE hN q) atTop := by
  obtain ⟨c,hc,hc1,hfinite⟩ := torusRCU_one_lower_of_h319 q hh319
  refine ⟨c,hc,hc1,?_⟩
  intro N n hN hN4 hNdiv hn h8nN
  let height := positiveEvenPeriod
  have hheight : Tendsto height atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with m hm
    dsimp [height,positiveEvenPeriod]
    omega
  let p : ℕ → ℝ := fun m => torusRCProbability hN (positiveEvenPeriod_even m) q
    {A | rcVerticalWinding hN (positiveEvenPeriod_even m)
      ⟨0,positiveEvenPeriod_pos m⟩ A = 1}
  let b := liftedBoxFreeConnectionProbability (torusRCBridgeParameters q)
    rotatedLatticeOrigin (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n)
  let C := fkOpenEnergy (torusRCBridgeParameters q) ^ (2*(N/4+2*n)) *
    torusRCSurgeryEnergy q ^ (2*n+N) / q.val^2
  have hC : 0 < C := div_pos
    (mul_pos (pow_pos (fkOpenEnergy_pos _) _) (pow_pos (torusRCSurgeryEnergy_pos q) _))
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)
  have hb : 0 < b := liftedBoxFreeDiagonalProbability_pos _ n (N/4) (by omega)
    ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  have hp : ∀ᶠ m in atTop,
      C * (c/(9*(n:ℝ)^2))^((height m:ℝ)/(n:ℝ)) * b^(height m/(2*n)) ≤ p m := by
    filter_upwards [hheight.eventually (eventually_ge_atTop (max 4 (max (4*n) (N/2+1))))]
      with m hm
    have hM4 : 4 ≤ height m := (le_max_left _ _).trans hm
    have h4nM : 4*n ≤ height m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
    have hNM : N/2 < height m := by
      have h := (le_max_right (4*n) (N/2+1)).trans ((le_max_right _ _).trans hm)
      omega
    have h := hfinite N (height m) n hN (positiveEvenPeriod_even m) hN4 hM4 hNdiv hn h8nN h4nM hNM
    change _ ≤ p m at h
    convert h using 1; dsimp [C,b]; ring
  exact log_block_product_liminf height hheight p C (c/(9*(n:ℝ)^2)) b hC
    (by positivity) hb n (2*n) (by omega) (by omega) hp

end PottsDiscontinuity.TorusRC
