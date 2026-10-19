module

public import PottsDiscontinuity.FK.BoxLaw
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph

/-!
# Exponential two-point decay excludes an infinite origin cluster

The hypothesis below uses the integer lattice's ℓ¹ distance, explicitly
`|x₁| + |x₂|`. This module works for any measure with the stated bound; it
requires neither a Gibbs property nor planar duality. It does not prove wired
percolation or the discontinuity implication.
-/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

/-- The actual open cluster, with no boundary identifications. -/
def cluster (ω : FK.LatticeConfiguration) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {x | (rcInfiniteOpenGraph ω).Reachable v x}

/-- The two-point event for actual open connectivity. -/
def connectionEvent (v x : ℤ × ℤ) : Set FK.LatticeConfiguration :=
  {ω | x ∈ cluster ω v}

/-- The event that the actual open cluster of `v` has infinitely many vertices. -/
def infiniteClusterAt (v : ℤ × ℤ) : Set FK.LatticeConfiguration :=
  {ω | (cluster ω v).Infinite}

/-- Existence of an infinite actual open cluster. -/
def existsInfiniteCluster : Set FK.LatticeConfiguration :=
  {ω | ∃ v : ℤ × ℤ, (cluster ω v).Infinite}

lemma summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.2
  have h := Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc)
  constructor
  · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h

lemma summable_exp_neg_l1 {c : ℝ} (hc : 0 < c) :
    Summable (fun x : ℤ × ℤ => Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
  have h := summable_exp_neg_abs_int hc
  have hh := h.mul_of_nonneg h (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  simpa only [mul_add, Real.exp_add] using hh

/-- Finite susceptibility implies that the specified actual cluster is finite
almost surely. This is the first Borel–Cantelli lemma, indexed by vertices. -/
theorem ae_finite_cluster_of_tsum_ne_top
    (μ : Measure FK.LatticeConfiguration) (v : ℤ × ℤ)
    (h : ∑' x : ℤ × ℤ, μ (connectionEvent v x) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (cluster ω v).Finite := by
  exact ae_finite_setOfPred_mem h

/-- An explicit ℓ¹ exponential bound implies finite susceptibility. -/
theorem susceptibility_ne_top_of_exponential_decay
    (μ : Measure FK.LatticeConfiguration) (v : ℤ × ℤ)
    (C c : ℝ) (hc : 0 < c)
    (hdecay : ∀ x : ℤ × ℤ, μ (connectionEvent v x) ≤
      ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))) :
    ∑' x : ℤ × ℤ, μ (connectionEvent v x) ≠ ⊤ := by
  have hs := ((summable_exp_neg_l1 hc).mul_left C).tsum_ofReal_ne_top
  exact ne_top_of_le_ne_top hs (ENNReal.tsum_le_tsum hdecay)

/-- Under the precise two-point bound, the actual cluster at `v` is finite
almost surely. For the free critical measure take `v = 0`. -/
theorem ae_finite_cluster_of_exponential_decay
    (μ : Measure FK.LatticeConfiguration) (v : ℤ × ℤ)
    (C c : ℝ) (hc : 0 < c)
    (hdecay : ∀ x : ℤ × ℤ, μ (connectionEvent v x) ≤
      ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))) :
    ∀ᵐ ω ∂μ, (cluster ω v).Finite :=
  ae_finite_cluster_of_tsum_ne_top μ v
    (susceptibility_ne_top_of_exponential_decay μ v C c hc hdecay)

/-- In particular the infinite-cluster event at the origin is null. -/
theorem infiniteClusterAt_zero_of_exponential_decay
    (μ : Measure FK.LatticeConfiguration) (C c : ℝ) (hc : 0 < c)
    (hdecay : ∀ x : ℤ × ℤ, μ (connectionEvent 0 x) ≤
      ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))) :
    μ (infiniteClusterAt 0) = 0 := by
  have h := ae_finite_cluster_of_exponential_decay μ 0 C c hc hdecay
  rw [ae_iff] at h
  exact h

end PottsDiscontinuity.Duality
