module

public import PottsDiscontinuity.TorusLoops.LoopDensityLogBounds
public import PottsDiscontinuity.TorusLoops.LoopTailBoundaryDecay

/-!
# Corrected Lemma 3.14

The source proof yields a limsup estimate, not the existence of a width limit.
This is the corrected statement, with the rotated-lattice free one-arm decay
provided as its sole additional premise.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

/-- At the critical point, the normalized logarithm of the loop observable has
vanishing limsup in absolute value as the even circumference tends to infinity.
The only additional input is decay of the rotated-lattice free one-arm
probability. -/
theorem lemma_3_14_corrected_limsup
    (q : Set.Ici (1 : ℝ))
    (hzero : Tendsto
      (fun n => (((Classical.choose (freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (boundaryConnectionEvent n) : NNReal) : ℝ))
      atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N₀ : {k : ℕ // 2 ≤ k}, ∀ N, (hN : Even N) →
      (hN₀ : N₀.val ≤ N) →
      Filter.limsup
        (fun n => abs (windingLoopDensityLogRate hN (by omega) q n)) atTop ≤ ε := by
  intro ε hε
  have hdecay := tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact windingLoopDensityLogOffset_nonneg q
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; exact windingLoopDensityLogSlope_nonneg q
  obtain ⟨r, hrlarge⟩ := exists_nat_gt (C₁ / ε)
  have hr : 0 < r := by
    by_contra hn
    have : (r : ℝ) = 0 := by exact_mod_cast (Nat.eq_zero_of_not_pos hn)
    rw [this] at hrlarge
    have hC1div : 0 ≤ C₁ / ε := div_nonneg hC₁ hε.le
    linarith
  have hrR : (C₁ / ε) < (r : ℝ) := hrlarge
  have hfirst : C₁ / (2 * (r : ℝ)) < ε / 2 := by
    have hmul : C₁ < ε * (r : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hrR
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [hmul]
  let τ := windingLoopTailArmThreshold q r
  have hτ : 0 < τ := by dsimp [τ]; exact windingLoopTailArmThreshold_pos q r
  have harmEventually : ∀ᶠ N : ℕ in atTop,
      rectangleFreeOneArmProbability q (N / 2 - 1) ≤ τ := by
    filter_upwards [hdecay.eventually (Iio_mem_nhds hτ)] with N hN
    exact hN.le
  obtain ⟨Narm, hNarm⟩ := Filter.eventually_atTop.1 harmEventually
  refine ⟨⟨max Narm 2, ?_⟩, ?_⟩
  · exact le_max_right _ _
  · intro N hN hN₀
    have hmax : 2 ≤ max Narm 2 := le_max_right _ _
    have h2N : 2 ≤ N := hmax.trans hN₀
    have hNp : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) h2N
    have hNarm' : Narm ≤ N := (le_max_left Narm 2).trans hN₀
    have harm : rectangleFreeOneArmProbability q (N / 2 - 1) ≤ τ := hNarm N hNarm'
    let C := C₀ + C₁
    have hC : 0 ≤ C := by dsimp [C]; exact add_nonneg hC₀ hC₁
    obtain ⟨Kε, hKε⟩ := exists_nat_gt (C / ε)
    have hKεbound : C / (2 * ((Kε + 1 : ℕ) : ℝ)) < ε / 2 := by
      have hmul : C < ε * (Kε : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hε).mp hKε
      have hcastK : ((Kε + 1 : ℕ) : ℝ) = (Kε : ℝ) + 1 := by norm_cast
      have hgrowth : ε * (Kε : ℝ) < ε / 2 *
          (2 * ((Kε + 1 : ℕ) : ℝ)) := by rw [hcastK]; nlinarith [hε]
      apply (div_lt_iff₀ (by positivity)).2
      exact hmul.trans hgrowth
    let Kgeom := max N (r * (9 * N))
    let K := max Kgeom Kε
    have hEventually : ∀ᶠ n : ℕ in atTop,
        |windingLoopDensityLogRate hN hNp q n| ≤ ε := by
      filter_upwards [eventually_ge_atTop K] with n hn
      have hnGeom : Kgeom ≤ n := le_trans (le_max_left Kgeom Kε) hn
      have hnN : N ≤ n := le_trans (le_max_left N (r * (9 * N))) hnGeom
      have hNle : N ≤ 2 * (n + 1) := by omega
      have hmul : (9 * N) * r ≤ n + 1 := by
        calc
          (9 * N) * r = r * (9 * N) := Nat.mul_comm _ _
          _ ≤ Kgeom := le_max_right N (r * (9 * N))
          _ ≤ n := hnGeom
          _ ≤ n + 1 := Nat.le_succ _
      have hdiv : 9 * N ≤ (n + 1) / r := (Nat.le_div_iff_mul_le hr).2 hmul
      have hthreshold : 9 * N ≤ (n + 1) / r + 1 := by omega
      have hrate := abs_windingLoopDensityLogRate_le hN hNp q r n hr
        hNle hthreshold (by simpa [τ] using harm)
      have hnKε : Kε ≤ n := le_trans (le_max_right Kgeom Kε) hn
      have hden : 2 * ((Kε + 1 : ℕ) : ℝ) ≤
          2 * ((n + 1 : ℕ) : ℝ) := by
        have hncast : ((Kε + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ hnKε
        nlinarith
      have hrem : (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) < ε / 2 := by
        have hdenN : 0 < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
        have hdenK : 0 < 2 * ((Kε + 1 : ℕ) : ℝ) := by positivity
        have hmono : C / (2 * ((n + 1 : ℕ) : ℝ)) ≤
            C / (2 * ((Kε + 1 : ℕ) : ℝ)) := by
          apply (div_le_div_iff₀ hdenN hdenK).2
          exact mul_le_mul_of_nonneg_left hden hC
        exact hmono.trans_lt (by simpa [C] using hKεbound)
      have hrate' : |windingLoopDensityLogRate hN hNp q n| < ε := by
        calc
          |windingLoopDensityLogRate hN hNp q n| ≤
              C₁ / (2 * (r : ℝ)) +
                (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := hrate
          _ < ε / 2 + ε / 2 := add_lt_add hfirst hrem
          _ = ε := by ring
      exact hrate'.le
    have hCob : IsCoboundedUnder (· ≤ ·) atTop
        (fun n => abs (windingLoopDensityLogRate hN hNp q n)) :=
      Filter.isCoboundedUnder_le_of_le atTop (fun n => abs_nonneg _)
    exact Filter.limsup_le_of_le hCob hEventually

end PottsDiscontinuity.TorusLoops
