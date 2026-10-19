module

public import PottsDiscontinuity.Torus.RibbonEuler

/-!
# Duality as an actual translation of indexed torus configurations

Translation by one column exchanges the primal and dual face colours. Complement
the edge states at the same time. Reversing the directed medial edges then
identifies the boundary loops, with their directions reversed.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

def columnShift : Equiv.Perm (Fin N × Fin M) :=
  Equiv.prodCongr (finRotate N) (Equiv.refl _)

def dartColumnShift : Equiv.Perm (Dart N M) :=
  Equiv.prodCongr columnShift (Equiv.refl _)

/-- The dual indexed configuration, translated back to the primal face colour. -/
def translatedDual (A : RCConfig N M) : RCConfig N M :=
  fun v => !(A (prv v.1, v.2))

@[simp] theorem translatedDual_shift (A : RCConfig N M) (v : Fin N × Fin M) :
    translatedDual A (columnShift v) = !A v := by
  rcases v with ⟨i, j⟩
  change (!(A ((finRotate N).symm (finRotate N i), j))) = (!(A (i, j)))
  rw [Equiv.symm_apply_apply]

theorem smoothing_translatedDual_shift (hN : Even N) (A : RCConfig N M)
    (v : Fin N × Fin M) :
    rcSmoothing (translatedDual A) (columnShift v) = rcSmoothing A v := by
  simp only [rcSmoothing]
  rw [translatedDual_shift]
  change Bool.xor (checker (nxt v.1, v.2)) (!A v) = _
  rw [checker_nxt_x hN]
  cases checker v <;> cases A v <;> rfl

theorem edgeReverse_columnShift (d : Dart N M) :
    edgeReverse (dartColumnShift d) = dartColumnShift (edgeReverse d) := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartColumnShift, columnShift, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, edgeReverse, nxt, prv, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

theorem leftFace_columnShift (d : Dart N M) :
    leftFace (dartColumnShift d) = columnShift (leftFace d) := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartColumnShift, columnShift, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, leftFace, prv, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

theorem step_columnShift (hN : Even N) (A : RCConfig N M) (d : Dart N M) :
    stepPerm (rcSmoothing (translatedDual A)) (dartColumnShift d) =
      dartColumnShift (stepPerm (rcSmoothing A) d) := by
  rw [stepPerm_apply, edgeReverse_columnShift]
  change (columnShift (edgeReverse d).1,
    pairedPort (rcSmoothing (translatedDual A) (columnShift (edgeReverse d).1))
      (edgeReverse d).2) = _
  rw [smoothing_translatedDual_shift hN]
  rfl

theorem dartOut_columnShift (hN : Even N) (hM : Even M) (d : Dart N M) :
    dartOut (checkerArrows N M) (dartColumnShift d) =
      !dartOut (checkerArrows N M) d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  change dartOut (checkerArrows N M) ((nxt i, j), p) = _
  rw [dartOut_checker_at hN hM, dartOut_checker_at hN hM, checker_nxt_x hN]
  cases p <;> simp

/-- Reverse an edge and translate it into the canonical dual orientation. -/
def dualDartEquiv (hN : Even N) (hM : Even M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  ((edgePerm N M).trans dartColumnShift).subtypeEquiv (fun d => by
    change dartOut (checkerArrows N M) d = true ↔
      dartOut (checkerArrows N M) (dartColumnShift (edgeReverse d)) = true
    rw [dartOut_columnShift hN hM, dartOut_edgeReverse, Bool.not_not])

@[simp] theorem dualDartEquiv_val (hN : Even N) (hM : Even M)
    (d : DirectedDart (checkerArrows N M)) :
    (dualDartEquiv hN hM d).val = dartColumnShift (edgeReverse d.val) := rfl

theorem dualDartEquiv_step (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) :
    dualDartEquiv hN hM (directedStep _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      (directedStep _ _ (checkerArrows_compatible hN hM
        (rcSmoothing (translatedDual A)))).symm (dualDartEquiv hN hM d) := by
  apply (directedStep _ _ (checkerArrows_compatible hN hM
    (rcSmoothing (translatedDual A)))).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change stepPerm (rcSmoothing (translatedDual A))
      (dartColumnShift (edgeReverse (stepPerm (rcSmoothing A) d.val))) =
    dartColumnShift (edgeReverse d.val)
  rw [step_columnShift hN, edgeReverse_step, Equiv.apply_symm_apply]

/-- Dual translation identifies the loop partitions, reversing their traversal. -/
def translatedDualLoopEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Loop hN hM (rcSmoothing A) ≃ Loop hN hM (rcSmoothing (translatedDual A)) := by
  let P := directedStep _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
  let Q := directedStep _ _ (checkerArrows_compatible hN hM
    (rcSmoothing (translatedDual A)))
  let g := dualDartEquiv hN hM
  have he : g * P * g⁻¹ = Q⁻¹ := by
    apply Equiv.ext
    intro d
    change g (P (g.symm d)) = Q.symm d
    calc
      g (P (g.symm d)) = Q.symm (g (g.symm d)) := dualDartEquiv_step hN hM A _
      _ = Q.symm d := by rw [Equiv.apply_symm_apply]
  exact Quotient.congr g (fun d e => by
    change P.SameCycle d e ↔ Q.SameCycle (g d) (g e)
    have hc := Equiv.Perm.sameCycle_conj (f := P) (g := g) (x := g d) (y := g e)
    rw [he] at hc
    simpa using hc.symm)

@[simp] theorem translatedDualLoopEquiv_loopOf (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    translatedDualLoopEquiv hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing (translatedDual A)))
        (dualDartEquiv hN hM d) := rfl

theorem loopSum_translatedDual (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : Dart N M → ℤ) (q : Loop hN hM (rcSmoothing A)) :
    loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing (translatedDual A))) f
      (translatedDualLoopEquiv hN hM A q) =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (fun d => f (dartColumnShift (edgeReverse d))) q := by
  classical
  unfold loopSum
  rw [Finset.sum_filter, ← Equiv.sum_comp (dualDartEquiv hN hM), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [← translatedDualLoopEquiv_loopOf hN hM A d]
  simp only [Equiv.apply_eq_iff_eq, dualDartEquiv_val]

/-- The two primal ribbon ends become the two dual endpoints, with the
checkerboard-dependent endpoint order. -/
theorem ribbonFace_dualDart_end (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) (b : Bool) :
    ribbonFace hN hM (dualDartEquiv hN hM (ribbonEndEquiv hN hM (v, b))) =
      faceEndpoint hN hM true (columnShift v) (Bool.xor (checker v) b) := by
  apply Subtype.ext
  change leftFace (dartColumnShift (edgeReverse (ribbonEnd v b))) =
    faceEndpointRaw true (columnShift v) (Bool.xor (checker v) b)
  rw [leftFace_columnShift]
  rcases v with ⟨i, j⟩
  change columnShift (leftFace (edgeReverse (ribbonEnd (i, j) b))) =
    faceEndpointRaw true (nxt i, j) (Bool.xor (checker (i, j)) b)
  cases hc : checker (i, j) <;> cases b <;>
    simp only [ribbonEnd, Bool.false_eq_true, ite_true, ite_false, edgeReverse,
      leftFace, faceEndpointRaw, checker_nxt_x hN, hc, Bool.not_true, Bool.not_false,
      Bool.false_xor, Bool.true_xor,
      columnShift, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
      nxt, prv, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem rcLoopCount_translatedDual (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    rcLoopCount hN hM (translatedDual A) = rcLoopCount hN hM A :=
  (Fintype.card_congr (translatedDualLoopEquiv hN hM A)).symm

theorem openCount_translatedDual (A : RCConfig N M) :
    openCount (translatedDual A) = closedCount A := by
  classical
  have hf : (univ.filter fun v => translatedDual A v = true) =
      (univ.filter fun v => A v = false).image columnShift := by
    ext v
    constructor
    · intro hv
      refine Finset.mem_image.mpr ⟨columnShift.symm v, ?_, by simp⟩
      have ht := translatedDual_shift A (columnShift.symm v)
      rw [Equiv.apply_symm_apply] at ht
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      rw [ht] at hv
      cases hh : A (columnShift.symm v) <;> simp_all
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hw' := (Finset.mem_filter.mp hw).2
      simp [translatedDual_shift, hw']
  unfold openCount closedCount
  rw [hf, Finset.card_image_of_injective _ columnShift.injective]

/-- The primal/dual cluster incidence graph has at most one independent cycle:
its edge count (the loop count) does not exceed its vertex count. -/
theorem rcLoopCount_le_primal_dual_clusters (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    rcLoopCount hN hM A ≤
      clusterCount hN hM true A + clusterCount hN hM true (translatedDual A) := by
  have hp := euler_ribbonHandleCount hN hM A
  have hd := euler_ribbonHandleCount hN hM (translatedDual A)
  rw [rcLoopCount_translatedDual, openCount_translatedDual] at hd
  have he := openCount_add_closedCount A
  have hv : 2 * (N * M / 2) = N * M := Nat.mul_div_cancel' (hN.mul_right M).two_dvd
  omega

end PottsDiscontinuity.TorusLoops
