module

public import PottsDiscontinuity.Torus.LoopOrientation
public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Changing loop orientations preserves the underlying cyclic edge partition

The quotient equivalence below aligns each edge with the new arrow field. It does
not assume anything about the homology or turning numbers of the loops.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}
variable (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M)
variable (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s)

/-- Send a reference-oriented cyclic class to the same edge loop in another orientation. -/
def reorientLoop : DirectedLoop ω₀ s h₀ → DirectedLoop ω₁ s h₁ :=
  Quotient.lift (fun d : DirectedDart ω₀ => loopOfDart ω₁ s h₁ d.val) (by
    intro d e hde
    exact sameCycle_invariant (directedStep ω₀ s h₀) (fun x => loopOfDart ω₁ s h₁ x.val)
      (fun x => loopOfDart_step ω₁ s h₁ x.val) hde)

theorem reorientLoop_loopOfDart (d : Dart N M) :
    reorientLoop ω₀ ω₁ s h₀ h₁ (loopOfDart ω₀ s h₀ d) = loopOfDart ω₁ s h₁ d := by
  change loopOfDart ω₁ s h₁ (arrowDart ω₀ (dartEdge d)) = loopOfDart ω₁ s h₁ d
  unfold loopOfDart
  rw [dartEdge_arrowDart]

theorem reorientLoop_inverse (q : DirectedLoop ω₀ s h₀) :
    reorientLoop ω₁ ω₀ s h₁ h₀ (reorientLoop ω₀ ω₁ s h₀ h₁ q) = q := by
  refine Quotient.inductionOn q ?_
  intro d
  change reorientLoop ω₁ ω₀ s h₁ h₀ (loopOfDart ω₁ s h₁ d.val) =
    directedLoopOf ω₀ s h₀ d
  rw [reorientLoop_loopOfDart, loopOfDart_of_out ω₀ s h₀ d.val d.property]

/-- An explicit equivalence of the actual loop carriers before and after reversal choices. -/
def loopReorientEquiv : DirectedLoop ω₀ s h₀ ≃ DirectedLoop ω₁ s h₁ where
  toFun := reorientLoop ω₀ ω₁ s h₀ h₁
  invFun := reorientLoop ω₁ ω₀ s h₁ h₀
  left_inv := reorientLoop_inverse ω₀ ω₁ s h₀ h₁
  right_inv := reorientLoop_inverse ω₁ ω₀ s h₁ h₀

/-- Align the representative of each indexed edge with the new arrow field. -/
def edgeReorientEquiv : DirectedDart ω₀ ≃ DirectedDart ω₁ :=
  (edgeDirectedEquiv ω₀).symm.trans (edgeDirectedEquiv ω₁)

@[simp] theorem edgeReorientEquiv_val (d : DirectedDart ω₀) :
    (edgeReorientEquiv ω₀ ω₁ d).val = arrowDart ω₁ (dartEdge d.val) := rfl

theorem loopReorientEquiv_apply (d : DirectedDart ω₀) :
    loopReorientEquiv ω₀ ω₁ s h₀ h₁ (directedLoopOf ω₀ s h₀ d) =
      directedLoopOf ω₁ s h₁ (edgeReorientEquiv ω₀ ω₁ d) := rfl

/-- A cycle sum after reorientation is a sum over the same indexed edges. -/
theorem loopSum_reorient_edges (f : Dart N M → ℤ) (q : DirectedLoop ω₀ s h₀) :
    loopSum ω₁ s h₁ f (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      loopSum ω₀ s h₀ (fun d => f (arrowDart ω₁ (dartEdge d))) q := by
  classical
  unfold loopSum
  rw [Finset.sum_filter, ← (edgeReorientEquiv ω₀ ω₁).sum_comp, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← loopReorientEquiv_apply ω₀ ω₁ s h₀ h₁ d]
  simp only [Equiv.apply_eq_iff_eq, edgeReorientEquiv_val]

/-- An edge-antisymmetric function changes sign exactly when its loop is reversed. -/
theorem edgeReorient_value (f : Dart N M → ℤ)
    (hf : ∀ d, f (edgeReverse d) = -f d) (d : DirectedDart ω₀) :
    f (edgeReorientEquiv ω₀ ω₁ d).val =
      if loopOrientation ω₀ s h₀ ω₁ h₁ (directedLoopOf ω₀ s h₀ d)
      then f d.val else -f d.val := by
  rw [loopOrientation_apply]
  change f (arrowDart ω₁ (dartEdge d.val)) = _
  by_cases hd : dartOut ω₁ d.val = true
  · simp only [hd, ite_true]
    rw [arrowDart_dartEdge ω₁ ⟨d.val, hd⟩]
  · have hd' : dartOut ω₁ (edgeReverse d.val) = true := by
      rw [dartOut_edgeReverse, Bool.eq_false_iff.mpr hd]
      rfl
    simp only [Bool.eq_false_iff.mpr hd, Bool.false_eq_true, ite_false]
    rw [← dartEdge_edgeReverse d.val, arrowDart_dartEdge ω₁ ⟨edgeReverse d.val, hd'⟩, hf]

/-- A signed cycle sum of an edge-antisymmetric function is preserved or negated. -/
theorem loopSum_reorient (f : Dart N M → ℤ) (hf : ∀ d, f (edgeReverse d) = -f d)
    (q : DirectedLoop ω₀ s h₀) :
    loopSum ω₁ s h₁ f (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ ω₁ h₁ q then loopSum ω₀ s h₀ f q
      else -loopSum ω₀ s h₀ f q := by
  classical
  rw [loopSum_reorient_edges]
  unfold loopSum
  have hv : (∑ d : DirectedDart ω₀ with directedLoopOf ω₀ s h₀ d = q,
      f (arrowDart ω₁ (dartEdge d.val))) =
      ∑ d : DirectedDart ω₀ with directedLoopOf ω₀ s h₀ d = q,
        if loopOrientation ω₀ s h₀ ω₁ h₁ q then f d.val else -f d.val := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← edgeReorientEquiv_val ω₀ ω₁ d]
    rw [edgeReorient_value ω₀ ω₁ s h₀ h₁ f hf]
    rw [(Finset.mem_filter.mp hd).2]
  rw [hv]
  by_cases hq : loopOrientation ω₀ s h₀ ω₁ h₁ q = true
  · simp only [hq, ite_true]
  · simp only [Bool.eq_false_iff.mpr hq, Bool.false_eq_true, ite_false]
    rw [Finset.sum_neg_distrib]

end PottsDiscontinuity.Torus
