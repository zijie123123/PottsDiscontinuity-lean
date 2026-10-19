module

public import PottsDiscontinuity.TorusLoops.WindingCirculations
public import PottsDiscontinuity.TorusLoops.WindingLoopCount

/-!
# At most two winding boundary loops per primal cluster

The two conserved displacement coordinates form circulations in the same
at-most-one-dimensional incidence circulation space. A scalar combination can
be chosen with exactly their joint support. The finite support-degree theorem
then gives the factor two in the loop-to-cluster count.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

private theorem exists_combination_joint_support {E : Type*} [Fintype E]
    (x y : E → ℚ) : ∃ a : ℚ, ∀ e, x e + a * y e = 0 ↔ x e = 0 ∧ y e = 0 := by
  classical
  obtain ⟨a, ha⟩ := (Finset.univ.image fun e => -x e / y e).exists_notMem
  refine ⟨a, fun e => ?_⟩
  by_cases hy : y e = 0
  · simp [hy]
  · have hn : a ≠ -x e / y e := by
      intro h
      exact ha (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, h.symm⟩)
    have hz : x e + a * y e ≠ 0 := by
      intro h
      apply hn
      apply (eq_div_iff hy).mpr
      linarith
    simp [hz, hy]

theorem mem_windingLoopSet_iff_displacement (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    q ∈ windingLoopSet hN hM i j A ↔
      loopDisplacementX hN hM A q ≠ 0 ∨ loopDisplacementY hN hM A q ≠ 0 := by
  classical
  have hx : loopDisplacementX hN hM A q = 0 ↔
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q = 0 := by
    rw [loopDisplacementX, loop_horizontal_displacement _ _ _ i q]
    simp only [Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero,
      Int.cast_eq_zero, (Fin.pos i).ne', false_or]
  have hy : loopDisplacementY hN hM A q = 0 ↔
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q = 0 := by
    rw [loopDisplacementY, loop_vertical_displacement _ _ _ j q]
    simp only [Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero,
      Int.cast_eq_zero, (Fin.pos j).ne', false_or]
  simp only [windingLoopSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ne_eq]
  rw [hx, hy]
  exact or_comm

open scoped Classical in
/-- No actual primal cluster has more than two incident essential boundary loops. -/
theorem windingLoops_per_primalCluster_le_two (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    ((windingLoopSet hN hM i j A).filter fun q => loopPrimalCluster hN hM A q = c).card ≤ 2 := by
  classical
  let : Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := exists_combination_joint_support
    (loopDisplacementX hN hM A) (loopDisplacementY hN hM A)
  let f : Loop hN hM (rcSmoothing A) → ℚ := fun q =>
    loopDisplacementX hN hM A q + a * loopDisplacementY hN hM A q
  have hf : f ∈ LinearMap.ker (loopIncidenceBoundary hN hM A) :=
    (LinearMap.ker _).add_mem (loopDisplacementX_mem_incidenceCycleSpace hN hM A)
      ((LinearMap.ker _).smul_mem a (loopDisplacementY_mem_incidenceCycleSpace hN hM A))
  have hk := finrank_loopIncidenceCycleSpace_le_one hN hM (Fin.pos i) (Fin.pos j) A
  change Module.finrank ℚ (LinearMap.ker (Bipartite.boundary
    (loopPrimalCluster hN hM A) (loopDualCluster hN hM A))) ≤ 1 at hk
  have hb := Bipartite.primal_support_degree_le_two
    (loopPrimalCluster hN hM A) (loopDualCluster hN hM A) f hf hk c
  have he : (Finset.univ.filter fun q => f q ≠ 0 ∧ loopPrimalCluster hN hM A q = c) =
      (windingLoopSet hN hM i j A).filter (fun q => loopPrimalCluster hN hM A q = c) := by
    ext q
    have hs : f q ≠ 0 ↔ loopDisplacementX hN hM A q ≠ 0 ∨
        loopDisplacementY hN hM A q ≠ 0 := by
      change ¬(_ + a * _ = 0) ↔ _
      rw [ha q, not_and_or]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
    rw [mem_windingLoopSet_iff_displacement]
  rwa [he] at hb

end PottsDiscontinuity.TorusLoops
