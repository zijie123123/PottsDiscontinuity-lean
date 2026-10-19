module

public import PottsDiscontinuity.TorusRC.AnnularExclusion
public import PottsDiscontinuity.TorusRC.PrimalWindingLower
public import PottsDiscontinuity.TorusRC.TiltDuality
public import PottsDiscontinuity.TorusRC.RateRescaling

/-! # The source barrier lower bound from crossing, surgery, and duality -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Translated complementary duality transfers the genuine winding event into
B, with exactly the q-squared loss of the source. -/
theorem barrier_probability_ge_winding (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))
    (K n : ℕ) (hmargin : K+1 ≤ 3*n) :
    torusRCProbability hN hM q (primalWindingSingleSeam hNp hMp hM K) / q.val^2 ≤
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n) := by
  have hsub : primalWindingSingleSeam hNp hMp hM K ⊆
      translatedDualConfig ⁻¹' torusRCBarrier hNp hMp n := by
    intro A hA
    exact primalWinding_translatedDual_mem_barrier hM hNp hMp K n hmargin A hA
  have hm := torusRCProbability_mono hN hM q hsub
  have hd := div_le_div_of_nonneg_right hm (sq_nonneg q.val)
  exact hd.trans (torusRCProbability_translatedDual_lower hN hM q
    (torusRCBarrier hNp hMp n))

/-- Uniform source barrier estimate. The one-unit strip margin from the
explicit terminal zigzag is recorded by B(n+1); the constant is independent
of all three integer parameters. -/
theorem barrier_lower_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hn : 0 < n)
      (h3nN : 3*n ≤ N) (h4nM : 4*n ≤ M),
      let hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      (torusRCSurgeryEnergy q ^ (2*n+N) *
        (c/(9*(n:ℝ)^2)) ^ ((M:ℝ)/(n:ℝ))) / q.val^2 ≤
        torusRCProbability hN hM q (torusRCBarrier hNp hMp (n+1)) := by
  obtain ⟨c,hc,hc1,h⟩ := primal_winding_lower_of_h319 q hh319
  refine ⟨c,hc,hc1,?_⟩
  intro N M n hN hM hN4 hM4 hn h3nN h4nM
  exact (div_le_div_of_nonneg_right
    (h N M n hN hM hN4 hM4 hn h3nN h4nM) (sq_nonneg q.val)).trans
    (barrier_probability_ge_winding hN hM (by omega) (by omega) q
      (3*n+1) (n+1) (by omega))

/-- The source B(n) lower bound, with the terminal margin absorbed into c.
The restriction n≥2 is harmless in the final n→∞ passage. -/
theorem barrier_source_lower_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hn : 2 ≤ n)
      (h3nN : 3*n ≤ N) (h4nM : 4*n ≤ M),
      let hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      (torusRCSurgeryEnergy q ^ (2*n+N) *
        (c/(9*(n:ℝ)^2)) ^ ((M:ℝ)/(n:ℝ))) / q.val^2 ≤
        torusRCProbability hN hM q (torusRCBarrier hNp hMp n) := by
  obtain ⟨c,hc,hc1,h⟩ := barrier_lower_of_h319 q hh319
  let d := c^2/(9*Real.exp 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    have he : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp (by norm_num)
    have hc2 : c^2 ≤ 1 := pow_le_one₀ hc.le hc1
    apply (div_le_one (by positivity)).mpr
    nlinarith
  refine ⟨d,hd,hd1,?_⟩
  intro N M n hN hM hN4 hM4 hn h3nN h4nM
  let m := n-1
  have hm : 0 < m := by omega
  have hmn : m+1 = n := by omega
  have hbase := block_rate_rescaling c hc hc1 m hm (M:ℝ) (Nat.cast_nonneg M)
  rw [hmn] at hbase
  have henergy := pow_le_pow_of_le_one (torusRCSurgeryEnergy_pos q).le
    (torusRCSurgeryEnergy_le_one q) (show 2*m+N ≤ 2*n+N by omega)
  have hprod := mul_le_mul henergy hbase (Real.rpow_nonneg (by positivity) _)
    (pow_nonneg (torusRCSurgeryEnergy_pos q).le (2*m+N))
  have hfinal := h N M m hN hM hN4 hM4 hm (by omega) (by omega)
  rw [hmn] at hfinal
  exact (div_le_div_of_nonneg_right hprod (sq_nonneg q.val)).trans hfinal

end PottsDiscontinuity.TorusRC
