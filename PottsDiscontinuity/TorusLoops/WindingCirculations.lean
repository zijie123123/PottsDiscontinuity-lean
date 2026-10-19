module

public import PottsDiscontinuity.TorusLoops.LoopIncidence
public import PottsDiscontinuity.TorusLoops.BipartiteCirculations

/-!
# Winding is conserved at both primal and dual clusters

The sum of the boundary chains incident to one primal cluster is zero.
Dual translation reverses both displacement coordinates, giving the same
conservation law at dual clusters.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

noncomputable section

local instance clusterFintype (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Fintype (diamondOpenGraph hN hM true A).ConnectedComponent := Fintype.ofFinite _

def loopDisplacementX (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) : ℚ :=
  (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) horizontalIncrement q : ℤ)

def loopDisplacementY (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A)) : ℚ :=
  (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) verticalIncrement q : ℤ)

open scoped Classical in
theorem sum_loopBoundaryCycle_fiber (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster hN hM A q = c, (loopBoundaryCycle hN hM A q).val) = 0 := by
  ext e
  simp only [Finset.sum_apply, Pi.zero_apply]
  change (∑ q with loopPrimalCluster hN hM A q = c,
    ((if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (ribbonEndEquiv hN hM (e.val, true)) = q then (1 : ℚ) else 0) -
      (if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (ribbonEndEquiv hN hM (e.val, false)) = q then (1 : ℚ) else 0))) = 0
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and,
    loopPrimalCluster_end, sub_self]

open scoped Classical in
theorem loopDisplacementX_primal_sum (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster hN hM A q = c, loopDisplacementX hN hM A q) = 0 := by
  simp only [loopDisplacementX, ← loopBoundaryCycle_displacement_x, diamondHorizontalDisplacement]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have he := congrFun (sum_loopBoundaryCycle_fiber hN hM A c) e
  simp only [Finset.sum_apply, Pi.zero_apply] at he
  rw [he, mul_zero]

open scoped Classical in
theorem loopDisplacementY_primal_sum (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster hN hM A q = c, loopDisplacementY hN hM A q) = 0 := by
  simp only [loopDisplacementY, ← loopBoundaryCycle_displacement_y, diamondVerticalDisplacement]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro e _
  have he := congrFun (sum_loopBoundaryCycle_fiber hN hM A c) e
  simpa only [Finset.sum_apply, Pi.zero_apply] using he

theorem loopDisplacementX_translatedDual (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    loopDisplacementX hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q) =
      -loopDisplacementX hN hM A q := by
  unfold loopDisplacementX
  rw [loopSum_translatedDual]
  have hf : (fun d : Dart N M => horizontalIncrement (dartColumnShift (edgeReverse d))) =
      fun d => -horizontalIncrement d := by
    funext d
    rcases d with ⟨v, p⟩
    cases p <;> rfl
  rw [hf]
  simp only [loopSum, Finset.sum_neg_distrib, Int.cast_neg]

theorem loopDisplacementY_translatedDual (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    loopDisplacementY hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q) =
      -loopDisplacementY hN hM A q := by
  unfold loopDisplacementY
  rw [loopSum_translatedDual]
  have hf : (fun d : Dart N M => verticalIncrement (dartColumnShift (edgeReverse d))) =
      fun d => -verticalIncrement d := by
    funext d
    rcases d with ⟨v, p⟩
    cases p <;> rfl
  rw [hf]
  simp only [loopSum, Finset.sum_neg_distrib, Int.cast_neg]

open scoped Classical in
theorem loopDisplacementX_dual_sum (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent) :
    (∑ q with loopDualCluster hN hM A q = c, loopDisplacementX hN hM A q) = 0 := by
  have h := loopDisplacementX_primal_sum hN hM (translatedDual A) c
  rw [Finset.sum_filter, ← (translatedDualLoopEquiv hN hM A).sum_comp] at h
  have he : (∑ q, if loopPrimalCluster hN hM (translatedDual A)
        (translatedDualLoopEquiv hN hM A q) = c then
        loopDisplacementX hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q) else 0) =
      -(∑ q with loopDualCluster hN hM A q = c, loopDisplacementX hN hM A q) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    rw [loopDisplacementX_translatedDual]
    by_cases hc : loopDualCluster hN hM A q = c <;> simp [loopDualCluster] at hc ⊢ <;> simp [hc]
  rw [he] at h
  exact neg_eq_zero.mp h

open scoped Classical in
theorem loopDisplacementY_dual_sum (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent) :
    (∑ q with loopDualCluster hN hM A q = c, loopDisplacementY hN hM A q) = 0 := by
  have h := loopDisplacementY_primal_sum hN hM (translatedDual A) c
  rw [Finset.sum_filter, ← (translatedDualLoopEquiv hN hM A).sum_comp] at h
  have he : (∑ q, if loopPrimalCluster hN hM (translatedDual A)
        (translatedDualLoopEquiv hN hM A q) = c then
        loopDisplacementY hN hM (translatedDual A) (translatedDualLoopEquiv hN hM A q) else 0) =
      -(∑ q with loopDualCluster hN hM A q = c, loopDisplacementY hN hM A q) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    rw [loopDisplacementY_translatedDual]
    by_cases hc : loopDualCluster hN hM A q = c <;> simp [loopDualCluster] at hc ⊢ <;> simp [hc]
  rw [he] at h
  exact neg_eq_zero.mp h

theorem loopDisplacementX_mem_incidenceCycleSpace (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    loopDisplacementX hN hM A ∈ LinearMap.ker (loopIncidenceBoundary hN hM A) := by
  classical
  have he : loopIncidenceBoundary hN hM A =
      Bipartite.boundary (loopPrimalCluster hN hM A) (loopDualCluster hN hM A) := rfl
  ext v
  rw [he]
  cases v with
  | inl c => rw [Bipartite.boundary_inl, loopDisplacementX_primal_sum]; rfl
  | inr c => rw [Bipartite.boundary_inr, loopDisplacementX_dual_sum]; rfl

theorem loopDisplacementY_mem_incidenceCycleSpace (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    loopDisplacementY hN hM A ∈ LinearMap.ker (loopIncidenceBoundary hN hM A) := by
  classical
  have he : loopIncidenceBoundary hN hM A =
      Bipartite.boundary (loopPrimalCluster hN hM A) (loopDualCluster hN hM A) := rfl
  ext v
  rw [he]
  cases v with
  | inl c => rw [Bipartite.boundary_inl, loopDisplacementY_primal_sum]; rfl
  | inr c => rw [Bipartite.boundary_inr, loopDisplacementY_dual_sum]; rfl

end
end PottsDiscontinuity.TorusLoops
