module

public import PottsDiscontinuity.Bethe.Asymptotic26

/-! # Theorem 2.6 with an arbitrary positive root count -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem mem_S_n_cast {n m : ℕ} (h : n = m) {p : Fin m → ℝ} (hp : p ∈ S_n m) :
    (fun j : Fin n => p (Fin.cast h j)) ∈ S_n n := by
  subst m
  exact hp

theorem rootStepDensity_cast {N n m : ℕ} (h : n = m) (p : Fin m → ℝ)
    (hp : p ∈ S_n m) (hn : 0 < n) (hm : 0 < m) (hs : 2 * n ≤ N) (ht : 2 * m ≤ N) :
    rootStepDensity N n (fun j => p (Fin.cast h j)) (mem_S_n_cast h hp) hn hs =
      rootStepDensity N m p hp hm ht := by
  subst m
  rfl

theorem theorem26_sums_of_pos {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hcount : ∀ i, N i = 2 * (n i + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i) x - rho Δ x) (hb i)) l (𝓝 0))
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun i => (∑ j, g (p i j)) / (N i : ℝ)) l
      (𝓝 (∫ x in (-Real.pi)..Real.pi, g x * rho Δ x)) := by
  let k : ι → ℕ := fun i => n i - 1
  have hc (i : ι) : k i + 1 = n i := by dsimp [k]; have := hn i; omega
  let q : ∀ i, Fin (k i + 1) → ℝ := fun i j => p i (Fin.cast (hc i) j)
  have hq (i : ι) : q i ∈ S_n (k i + 1) := mem_S_n_cast (hc i) (hp i)
  have hqs (i : ι) : 2 * (k i + 1) ≤ N i := by rw [hc]; exact hs i
  have hqc (i : ι) : N i = 2 * (k i + 1 + r) := by rw [hc]; exact hcount i
  have hρ (i : ι) : rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hqs i) =
      rootStepDensity (N i) (n i) (p i) (hp i) (hn i) (hs i) :=
    rootStepDensity_cast (hc i) (p i) (hp i) (by omega) (hn i) (hqs i) (hs i)
  have hqb (i : ι) : BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hqs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) := by
    simpa only [hρ i] using hb i
  have hql : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hqs i) x - rho Δ x)
      (hqb i)) l (𝓝 0) := by
    simpa only [hρ] using hlim
  have ht := theorem26_integrals hΔ r N k q hq hqs hqc hNlim hqb hql g hg
  have hsum (i : ι) : (∑ j, g (q i j)) = ∑ j, g (p i j) :=
    Equiv.sum_comp (finCongr (hc i)) (fun j => g (p i j))
  simpa only [integral_empiricalMeasure, hsum] using ht

end PottsDiscontinuity.Bethe
