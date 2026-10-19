module

public import PottsDiscontinuity.Bethe.AsymptoticGeometry
public import PottsDiscontinuity.Bethe.RatioBoundary

/-! # Canonical left-root projection for the interior quadrature

The projection chooses the last root at or to the left of x. To the left
of the first root it is clamped to that first root; to the right of the
last it is the last root. These are the intended boundary conventions.
-/

@[expose] public section

open Set Filter Finset
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- The canonical predecessor root index, clamped at the first root. -/
noncomputable def ratioRootIndex {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (x : ℝ) : Fin n :=
  if h : (univ.filter (fun j => q j ≤ x)).Nonempty then
    (univ.filter (fun j => q j ≤ x)).max' h
  else ⟨0, hn⟩

theorem ratio_rootIndex_on_cell {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : StrictMono q) (j : Fin n) (hj : j.val + 1 < n) {x : ℝ}
    (hx : q j ≤ x ∧ x < q ⟨j.val + 1, hj⟩) : ratioRootIndex hn q x = j := by
  classical
  let s := univ.filter (fun j => q j ≤ x)
  have hjmem : j ∈ s := mem_filter.mpr ⟨mem_univ _, hx.1⟩
  have hs : s.Nonempty := ⟨j, hjmem⟩
  have hmax : s.max' hs = j := by
    apply le_antisymm
    · apply Finset.max'_le
      intro i hi
      by_contra h
      have hle : (⟨j.val + 1, hj⟩ : Fin n) ≤ i := by
        change j.val + 1 ≤ i.val
        have : j.val < i.val := lt_of_not_ge h
        omega
      have hqi : q i ≤ x := (mem_filter.mp hi).2
      have := hq.monotone hle
      linarith [hx.2]
    · exact Finset.le_max' s j hjmem
  change (if h : s.Nonempty then s.max' h else ⟨0, hn⟩) = j
  rw [dite_eq_left hs]
  exact hmax

theorem ratio_rootIndex_cell {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : StrictMono q) {x : ℝ}
    (hleft : q ⟨0, hn⟩ ≤ x) (hright : x < q ⟨n - 1, by omega⟩) :
    ∃ hj : (ratioRootIndex hn q x).val + 1 < n,
      q (ratioRootIndex hn q x) ≤ x ∧
        x < q ⟨(ratioRootIndex hn q x).val + 1, hj⟩ := by
  obtain ⟨j, hj, hcell⟩ := exists_interior_root_cell hn q hleft hright
  rw [ratio_rootIndex_on_cell hn q hq j hj hcell]
  exact ⟨hj, hcell⟩

theorem ratio_rootIndex_dist_le_mesh {n : ℕ} (hn : 0 < n)
    {q : Fin n → ℝ} (hq : q ∈ S_n n) {x d : ℝ}
    (hleft : q ⟨0, hn⟩ ≤ x) (hright : x < q ⟨n - 1, by omega⟩)
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint n q hn j.succ - rootPartitionPoint n q hn j.castSucc ≤ d) :
    |q (ratioRootIndex hn q x) - x| ≤ d := by
  obtain ⟨hj, hcell⟩ := ratio_rootIndex_cell hn q hq.2.1 hleft hright
  have hgap := root_interior_gap_of_mesh q hn hmesh (ratioRootIndex hn q x).val hj
  rw [abs_of_nonpos (sub_nonpos.mpr hcell.1)]
  linarith [hcell.2]

/-- The root projection converges to every interior point when the mesh vanishes. -/
theorem ratio_rootIndex_tendsto {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (q : ∀ i, Fin (n i) → ℝ)
    (hq : ∀ i, q i ∈ S_n (n i)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ᶠ i in l, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (q i) (hn i) j.succ -
        rootPartitionPoint (n i) (q i) (hn i) j.castSucc ≤ d i)
    {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    Tendsto (fun i => q i (ratioRootIndex (hn i) (q i) x)) l (𝓝 x) := by
  have hfirst := ratio_tendsto_root_left_of_eventual_mesh n hn q hq d hd hdnonneg hmesh
    (fun i => ⟨0, hn i⟩) 0 (fun i => le_rfl)
  have hlast : Tendsto (fun i => q i ⟨n i - 1, by have := hn i; omega⟩) l (𝓝 Real.pi) := by
    have he (i : ι) : q i ⟨n i - 1, by have := hn i; omega⟩ = -q i ⟨0, hn i⟩ := by
      have h := (hq i).2.2 ⟨0, hn i⟩
      simpa only [Fin.rev, Nat.sub_zero] using h
    simpa only [he, neg_neg] using hfirst.neg
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hmesh, hfirst.eventually (gt_mem_nhds hx.1), hlast.eventually (lt_mem_nhds hx.2),
    hd.eventually (gt_mem_nhds hε)] with i hi hleft hright hdi
  rw [Real.dist_eq]
  exact (ratio_rootIndex_dist_le_mesh (hn i) (hq i) hleft.le hright hi).trans_lt hdi

end PottsDiscontinuity.Bethe
