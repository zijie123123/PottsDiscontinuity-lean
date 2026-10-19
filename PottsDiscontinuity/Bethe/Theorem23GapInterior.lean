module

public import PottsDiscontinuity.Bethe.Theorem23Admissible

/-! # Interior of the separated gap region -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem mem_interior_betheGapRegion {k : ℕ} {ell u : ℝ}
    {q : Fin ((k + 1) / 2) → ℝ}
    (hq : ∀ j : Fin (k + 2), rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q)
      (by omega) j.succ - rootPartitionPoint (k + 1) (discreteSymLift (k + 1) q)
      (by omega) j.castSucc ∈ Ioo ell u) : q ∈ interior (betheGapRegion k ell u) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hnear (j : Fin (k + 2)) : ∀ᶠ v in 𝓝 q,
      rootPartitionPoint (k + 1) (discreteSymLift (k + 1) v) (by omega) j.succ -
        rootPartitionPoint (k + 1) (discreteSymLift (k + 1) v) (by omega) j.castSucc ∈ Ioo ell u := by
    have hc (i : Fin (k + 3)) : Continuous (fun v : Fin ((k + 1) / 2) → ℝ =>
        rootPartitionPoint (k + 1) (discreteSymLift (k + 1) v) (by omega) i) :=
      (continuous_rootPartitionPoint k i).comp (discreteSymLift (k + 1)).continuous_of_finiteDimensional
    exact ((hc j.succ).sub (hc j.castSucc)).continuousAt.eventually
      (isOpen_Ioo.mem_nhds (hq j))
  filter_upwards [eventually_all.mpr hnear] with v hv
  exact fun j => ⟨(hv j).1.le, (hv j).2.le⟩

end PottsDiscontinuity.Bethe
