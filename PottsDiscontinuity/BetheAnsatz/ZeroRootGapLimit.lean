module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Formula
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordLimit

/-!
# The punctured gap-sum identity at a zero root

Away from the singular value, the cyclic gap sum is exactly its finite word
expansion. Combining that expansion with the root-slot partition gives the
T₀ plus paired T₁ decomposition on a punctured neighborhood.
-/

@[expose] public section

open Finset Complex Classical Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- Near a zero momentum, every perturbed spectral parameter is away from one. -/
theorem eventually_perturbedMomenta_z_ne_one {m : ℕ} (p : Fin (m + 2) → ℝ)
    (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0) :
    ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ k, z (perturbedMomenta p l t k) ≠ 1 := by
  have hpk0 : ∀ k, k ≠ l → p k ≠ 0 := by
    intro k hkl hk
    apply hkl
    exact hinj (hk.trans hpl.symm)
  filter_upwards [eventually_z_ne_one_zero] with t ht k
  by_cases hkl : k = l
  · subst k
    simpa [perturbedMomenta_at, hpl] using ht
  · rw [perturbedMomenta_of_ne p l k t hkl]
    exact z_ne_one (hp k) (hpk0 k hkl)

/-- On a punctured neighborhood, the fixed-amplitude cyclic gap sum is the
constant T₀ expression plus the canonical paired T₁ terms. -/
theorem eventually_fixedAmplitudeGapSum_eq_constant_plus_t1 {N m : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (m + 2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (m + 1)) - x 0 < (N : ℤ))
    (p : Fin (m + 2) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ *
          cyclicGapSum c N x (perturbedMomenta p l t) σ) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ =>
        constantWordSumPerturbed (N := N) c x p l t +
          ∑ i : T1PairIndex (m + 1) l, t1PairTerm (N := N) c x p l t i) := by
  have hq := eventually_perturbedMomenta_z_ne_one p hp hinj l hpl
  filter_upwards [hq] with t ht
  let q := perturbedMomenta p l t
  calc
    _ = ∑ σ : Equiv.Perm (Fin (m + 2)),
        ∑ w : Fin (m + 2) → Bool,
          fixedAmplitudeWordTerm (N := N) c x p q σ w := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [cyclicGapSum_eq_sum_words c x q σ hx hspan ht]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      unfold fixedAmplitudeWordTerm
      ring
    _ = constantWordSumPerturbed (N := N) c x p l t +
        ∑ i : T1PairIndex (m + 1) l, t1PairTerm (N := N) c x p l t i := by
      exact fixedAmplitudeWordSum_eq_constant_plus_t1 hc (by omega) x p hp hinj l hpl hBE t

/-- The fixed-amplitude cyclic gap sum converges to the degenerate eigenvalue
times the coordinate wave. This identifies the perturbed transfer action without
assuming that the perturbed momenta satisfy the Bethe equations. -/
theorem tendsto_fixedAmplitudeGapSum_zeroRoot {N m : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (m + 2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (m + 1)) - x 0 < (N : ℤ))
    (p : Fin (m + 2) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    Tendsto (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ *
          cyclicGapSum c N x (perturbedMomenta p l t) σ)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (eigenvalueZero N c p l * coordinateWave (anisotropy c) p x)) := by
  have hGap := tendsto_fixedAmplitude_gapSum (N := N) (n := m + 1)
    c (anisotropy c) x p l
  have hGap' := hGap.mono_left (nhdsWithin_le_nhds :
    𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hConst := tendsto_constantWordSumPerturbed hc x p hp hinj l hpl hBE
  rw [← t0RegularizedSum_zero] at hConst
  have hT1 := tendsto_sum_t1PairTerm hc x p hp hinj l hpl hBE
  have hParts : Tendsto
      (fun t : ℝ => constantWordSumPerturbed (N := N) c x p l t +
        ∑ i : T1PairIndex (m + 1) l, t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (t0RegularizedSum (N := N) c x p l 0 +
        ∑ i : T1PairIndex (m + 1) l, t1PairLimit (N := N) c x p l i)) := by
    exact hConst.add hT1
  have hGapParts : Tendsto
      (fun t : ℝ => constantWordSumPerturbed (N := N) c x p l t +
        ∑ i : T1PairIndex (m + 1) l, t1PairTerm (N := N) c x p l t i)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ)) := by
    apply hGap'.congr'
    filter_upwards [eventually_fixedAmplitudeGapSum_eq_constant_plus_t1
      hc x hx hspan p hp hinj l hpl hBE] with t ht
    exact ht
  have hlimit := tendsto_nhds_unique hGapParts hParts
  have hscalar := t0_t1_pairLimits_eq_eigenvalueZero hc x p hp hinj l hpl hBE
  have hfinal :
      (∑ σ : Equiv.Perm (Fin (m + 2)),
        amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ) =
        eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
    calc
      _ = t0RegularizedSum (N := N) c x p l 0 +
          ∑ i : T1PairIndex (m + 1) l, t1PairLimit (N := N) c x p l i := hlimit
      _ = eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := hscalar
  rw [← hfinal]
  exact hGap'

/-- The limiting fixed-amplitude gap sum agrees with its value at the original
zero-root tuple, by continuity of the gap expression. -/
theorem fixedAmplitudeGapSum_zero_eq_eigenvalueZero {N m : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (m + 2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (m + 1)) - x 0 < (N : ℤ))
    (p : Fin (m + 2) → ℝ) (hp : ∀ k, p k ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (m + 2)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∑ σ : Equiv.Perm (Fin (m + 2)),
      amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ) =
      eigenvalueZero N c p l * coordinateWave (anisotropy c) p x := by
  have hcont := tendsto_fixedAmplitude_gapSum (N := N) (n := m + 1)
    c (anisotropy c) x p l
  have hcont' := hcont.mono_left (nhdsWithin_le_nhds :
    𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hdeg := tendsto_fixedAmplitudeGapSum_zeroRoot hc x hx hspan p hp hinj l hpl hBE
  exact tendsto_nhds_unique hcont' hdeg

end PottsDiscontinuity.BetheAnsatz
