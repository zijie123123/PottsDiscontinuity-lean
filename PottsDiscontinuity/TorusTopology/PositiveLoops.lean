module

public import PottsDiscontinuity.TorusTopology.ClusterVerticalValues

/-! U counts positive winding with multiplicity. Positive-winding loops belong
to different original primal clusters, by the degree-two conservation law. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}
noncomputable section

/-- The loops with strictly positive signed vertical winding. -/
def positiveVerticalLoops (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :
    Finset (Loop hN hM (rcSmoothing A)) :=
  univ.filter fun q => 0 < loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q

/-- The phase slots of all positive loops, with their actual winding multiplicity. -/
abbrev VerticalPhaseIndex (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :=
  Σ q : (positiveVerticalLoops hN hM j A),
    Fin ((loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q.val).toNat)

lemma sum_vertical_winding_zero (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :
    (∑ q : Loop hN hM (rcSmoothing A),
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q) = 0 := by
  let : Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise univ (loopPrimalCluster hN hM A)
    (fun q => loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q)]
  simp only [sum_vertical_winding_at_cluster_zero,Finset.sum_const_zero]

/-- Positive winding, summed with multiplicity, is exactly U. -/
theorem sum_positive_vertical_winding_eq_U
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :
    (∑ q ∈ positiveVerticalLoops hN hM j A,
      (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat) =
        rcVerticalWinding hN hM j A := by
  have hid (z : ℤ) : (z.natAbs : ℤ)+z = 2*(z.toNat : ℤ) := by
    rw [Int.natCast_natAbs]
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz,Int.toNat_of_nonneg hz]
      ring
    · rw [abs_of_neg (lt_of_not_ge hz),Int.toNat_of_nonpos (le_of_not_ge hz)]
      simp
  have hs := Finset.sum_congr (s₁ := (univ : Finset (Loop hN hM (rcSmoothing A)))) rfl
    (fun q _ => hid (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q))
  rw [Finset.sum_add_distrib,sum_vertical_winding_zero,add_zero,← Finset.mul_sum] at hs
  have hnat : verticalMass _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j =
      2 * ∑ q : Loop hN hM (rcSmoothing A),
        (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat := by
    unfold verticalMass
    exact_mod_cast hs
  have hU := two_mul_verticalWindingCount hN (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j
  change 2 * rcVerticalWinding hN hM j A = _ at hU
  have hall : (∑ q : Loop hN hM (rcSmoothing A),
      (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat) =
      rcVerticalWinding hN hM j A := by omega
  rw [← hall]
  unfold positiveVerticalLoops
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : 0 < loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q
  · simp [hq]
  · simp [hq,Int.toNat_of_nonpos (le_of_not_gt hq)]

/-- The number of phase slots is U, including all multiple windings. -/
theorem card_verticalPhaseIndex (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :
    Fintype.card (VerticalPhaseIndex hN hM j A) = rcVerticalWinding hN hM j A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_coe_sort (positiveVerticalLoops hN hM j A)
    (fun q => (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q).toNat)).trans
      (sum_positive_vertical_winding_eq_U hN hM j A)

lemma width_pos_of_loop (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) : 0 < N := by
  induction q using Quotient.inductionOn with
  | h d => exact Fin.pos d.val.1.1

/-- Distinct positive-winding loops are incident to distinct primal clusters. -/
theorem positive_vertical_loops_primalCluster_injective
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) :
    Function.Injective (fun q : positiveVerticalLoops hN hM j A => loopPrimalCluster hN hM A q.val) := by
  intro q r hqr
  apply Subtype.ext
  by_contra hne
  have hq := (Finset.mem_filter.1 q.property).2
  have hr := (Finset.mem_filter.1 r.property).2
  let c := loopPrimalCluster hN hM A q.val
  let S := (univ : Finset (Loop hN hM (rcSmoothing A))).filter fun t =>
    loopPrimalCluster hN hM A t=c ∧
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t ≠ 0
  have hsub : S ⊆ (windingLoopSet hN hM ⟨0,width_pos_of_loop hN hM A q.val⟩ j A).filter
      (fun t => loopPrimalCluster hN hM A t=c) := by
    intro t ht
    have ht' := (Finset.mem_filter.1 ht).2
    refine Finset.mem_filter.2 ⟨?_,ht'.1⟩
    simp only [windingLoopSet,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inl ht'.2
  have hcard : S.card ≤ 2 := (Finset.card_le_card hsub).trans
    (windingLoops_per_primalCluster_le_two hN hM ⟨0,width_pos_of_loop hN hM A q.val⟩ j A c)
  have hpair : ({q.val,r.val} : Finset (Loop hN hM (rcSmoothing A))) ⊆ S := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · subst t
      simp [S,c,hq.ne']
    · have h := Finset.mem_singleton.1 h
      subst t
      simp [S,c,hqr,hr.ne']
  have hc : ({q.val,r.val} : Finset (Loop hN hM (rcSmoothing A))).card=2 := by simp [hne]
  have he : S={q.val,r.val} := (Finset.eq_of_subset_of_card_le hpair (by omega)).symm
  have hsum : ∑ t ∈ S,
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t = 0 := by
    have hS : S = (univ.filter fun t => loopPrimalCluster hN hM A t=c).filter
        (fun t => loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j t ≠ 0) := by
      ext t
      simp [S]
    rw [hS,Finset.sum_filter_ne_zero]
    exact sum_vertical_winding_at_cluster_zero hN hM j A c
  rw [he,Finset.sum_pair hne] at hsum
  omega

end
end PottsDiscontinuity.TorusTopology
