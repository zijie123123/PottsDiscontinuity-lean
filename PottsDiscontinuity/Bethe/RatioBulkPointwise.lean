module

public import PottsDiscontinuity.Bethe.RatioInteriorQuadrature
public import PottsDiscontinuity.Bethe.RatioPredecessor
public import PottsDiscontinuity.Bethe.RatioScaledIncrement

/-! # Pointwise convergence of the logarithmic quadrature tests

This general calculus lemma takes a root-density limit and a scaled
displacement limit. In the source application they are supplied by
Theorems 2.6/2.9 and the geometric estimates, not new assumptions on the
eigenvalue ratio.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_log_step_tendsto {ι : Type*} {l : Filter ι} {c : ℝ} (hc : 2 < c)
    (N k : ι → ℕ) (hN : ∀ i, 0 < N i)
    (q a : ∀ i, Fin (k i + 1) → ℝ) (hq : ∀ i, q i ∈ S_n (k i + 1))
    (hs : ∀ i, 2 * (k i + 1) ≤ N i)
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (d : ι → ℝ) (hd : Tendsto d l (𝓝 0)) (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ᶠ i in l, ∀ j : Fin (k i + 1 + 1),
      rootPartitionPoint (k i + 1) (q i) (by omega) j.succ -
        rootPartitionPoint (k i + 1) (q i) (by omega) j.castSucc ≤ d i)
    (w E : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0)
    (hρ : Tendsto (fun i => rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hs i) x)
      l (𝓝 (w x)))
    (he : Tendsto (fun i => (N i : ℝ) *
      (q i (ratioRootIndex (by omega) (q i) x) - a i (ratioRootIndex (by omega) (q i) x)))
      l (𝓝 (E x))) :
    Tendsto (fun i => ratioInteriorTest (N i) (q i) (hq i)
      (fun j => (N i : ℝ) * (ratioEll c (q i j) - ratioEll c (a i j))) x) l
      (𝓝 (ratioEllPrime c x * E x * w x)) := by
  let u : ι → ℝ := fun i => q i (ratioRootIndex (by omega) (q i) x)
  let v : ι → ℝ := fun i => a i (ratioRootIndex (by omega) (q i) x)
  have hu : Tendsto u l (𝓝 x) :=
    ratio_rootIndex_tendsto (fun i => k i + 1) (fun i => by omega) q hq d hd hdnonneg hmesh hx
  have hdiv : Tendsto (fun i => ((N i : ℝ) * (u i - v i)) / N i) l (𝓝 0) :=
    he.div_atTop hNlim
  have hv : Tendsto v l (𝓝 x) := by
    have ht := hu.sub hdiv
    rw [sub_zero] at ht
    apply ht.congr
    intro i
    have hn : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    field_simp
    ring
  have hlog := ratio_scaled_ell_tendsto hc hx hx0 u v (fun i => (N i : ℝ)) hu hv he
  have hprod := hlog.mul hρ
  have hfirst := ratio_tendsto_root_left_of_eventual_mesh (fun i => k i + 1)
    (fun i => by omega) q hq d hd hdnonneg hmesh (fun i => 0) 0 (fun i => le_rfl)
  have hlast : Tendsto (fun i => q i (Fin.last (k i))) l (𝓝 Real.pi) := by
    have heq (i : ι) : q i (Fin.last (k i)) = -q i 0 := by
      simpa only [Fin.rev_zero] using (hq i).2.2 0
    simpa only [heq, neg_neg] using hfirst.neg
  apply hprod.congr'
  filter_upwards [hfirst.eventually (gt_mem_nhds hx.1), hlast.eventually (lt_mem_nhds hx.2)]
    with i hleft hright
  obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell (show 0 < k i + 1 by omega) (q i) (hq i).2.1
    (show q i ⟨0, by omega⟩ ≤ x from hleft.le)
    (show x < q i ⟨k i + 1 - 1, by omega⟩ from hright)
  let j : Fin (k i) := ⟨(ratioRootIndex (by omega) (q i) x).val, by omega⟩
  have hjcast : j.castSucc = ratioRootIndex (by omega) (q i) x := Fin.ext rfl
  have hjsucc : j.succ = ⟨(ratioRootIndex (by omega) (q i) x).val + 1, hj⟩ := Fin.ext rfl
  have hcell' : q i j.castSucc ≤ x ∧ x < q i j.succ := by
    rw [hjcast, hjsucc]
    exact hcell
  rw [ratio_interiorTest_eq_density (hq i) (hs i) _ j hcell', hjcast]

end PottsDiscontinuity.Bethe
