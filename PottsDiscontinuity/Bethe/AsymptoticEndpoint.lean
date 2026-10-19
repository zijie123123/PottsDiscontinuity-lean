module

public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Fixed-rank roots approach the endpoints -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem root_distance_from_boundary {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ S_n n) (hn : 0 < n) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint n p hn j.succ - rootPartitionPoint n p hn j.castSucc ≤ d)
    (j : Fin n) :
    p j + Real.pi ≤ ((j.val : ℝ) + 1) * d ∧
      Real.pi - p j ≤ ((n - j.val : ℕ) : ℝ) * d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨hfirst, hlast, hgap⟩ := root_mesh_consequences hp hmesh
  have hmono : Monotone (fun i : Fin (k + 1) => (i.val : ℝ) * d - p i) :=
    Fin.monotone_iff_le_succ.mpr (fun i => by
      have := hgap i
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      linarith)
  have hleft := hmono (show (⟨0, by omega⟩ : Fin (k + 1)) ≤ j from by change 0 ≤ j.val; omega)
  have hright := hmono (show j ≤ (⟨k, by omega⟩ : Fin (k + 1)) from by change j.val ≤ k; omega)
  dsimp only at hleft hright
  simp only [Nat.cast_zero, zero_mul, zero_sub] at hleft
  have hz : (⟨0, hn⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp)
  have hl : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [hz] at hleft
  rw [hl] at hright
  constructor
  · nlinarith only [hleft, hfirst]
  · rw [Nat.cast_sub (show j.val ≤ k + 1 by omega), Nat.cast_add, Nat.cast_one]
    nlinarith only [hright, hlast]

theorem tendsto_root_at_left_of_mesh {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ i, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (p i) (hn i) j.succ -
        rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤ d i)
    (j : ∀ i, Fin (n i)) (J : ℕ) (hrank : ∀ i, (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) l (𝓝 (-Real.pi)) := by
  have hboundlim : Tendsto (fun i => ((J : ℝ) + 1) * d i) l (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul ((J : ℝ) + 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hboundlim.eventually (gt_mem_nhds hε)] with i hi
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (by have := ((hp i).1 (j i)).1; linarith)]
  have hb := (root_distance_from_boundary (hp i) (hn i) (hmesh i) (j i)).1
  have hr : ((j i).val : ℝ) + 1 ≤ (J : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (hrank i) 1
  exact hb.trans_lt ((mul_le_mul_of_nonneg_right hr (hdnonneg i)).trans_lt hi)

theorem tendsto_root_at_right_of_mesh {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ i, ∀ j : Fin (n i + 1),
      rootPartitionPoint (n i) (p i) (hn i) j.succ -
        rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤ d i)
    (j : ∀ i, Fin (n i)) (J : ℕ) (hrank : ∀ i, n i - 1 - (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) l (𝓝 Real.pi) := by
  have hboundlim : Tendsto (fun i => ((J : ℝ) + 1) * d i) l (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul ((J : ℝ) + 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hboundlim.eventually (gt_mem_nhds hε)] with i hi
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (((hp i).1 (j i)).2.le))]
  have hb := (root_distance_from_boundary (hp i) (hn i) (hmesh i) (j i)).2
  have hr : ((n i - (j i).val : ℕ) : ℝ) ≤ (J : ℝ) + 1 := by
    have hnat : n i - (j i).val ≤ J + 1 := by have := (j i).isLt; have := hrank i; omega
    exact_mod_cast hnat
  have he := hb.trans_lt ((mul_le_mul_of_nonneg_right hr (hdnonneg i)).trans_lt hi)
  linarith

end PottsDiscontinuity.Bethe
