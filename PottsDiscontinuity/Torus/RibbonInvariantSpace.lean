module

public import PottsDiscontinuity.Torus.PermutationInvariantSpace
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-!
# Invariant functions on ribbon components

Functions invariant under both vertex rotation and open-edge pairing are exactly
functions on the components of the actual ribbon subgraph.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

/-- Rational functions on corners, invariant under both generating permutations. -/
def ribbonFunctions (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Submodule ℚ (DirectedDart (checkerArrows N M) → ℚ) :=
  cycleFunctions (faceRotation hN hM) ⊓ cycleFunctions (ribbonEdgePairing hN hM A)

theorem ribbonFunctions_invariant (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : ribbonFunctions hN hM A) {d e : DirectedDart (checkerArrows N M)}
    (h : RibbonConnected hN hM A d e) : f.val d = f.val e := by
  induction h with
  | rel d e h =>
    rcases h with h | rfl
    · exact sameCycle_invariant _ f.val f.property.1 h
    · exact (f.property.2 d).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Invariant corner functions descend to components and pull back uniquely. -/
def ribbonFunctionEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    (RibbonComponent hN hM A → ℚ) ≃ₗ[ℚ] ribbonFunctions hN hM A where
  toFun f := ⟨fun d => f (Quotient.mk _ d), by
    constructor
    · intro d
      exact congrArg f (Quotient.sound (Relation.EqvGen.rel _ _
        (Or.inl (Equiv.Perm.SameCycle.rfl.apply_left))))
    · intro d
      exact congrArg f (Quotient.sound (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (Or.inr rfl))))⟩
  invFun f := Quotient.lift f.val (fun _ _ h => ribbonFunctions_invariant hN hM A f h)
  left_inv f := by
    funext q
    exact Quotient.inductionOn q (fun _ => rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The invariant-function dimension is the actual primal cluster count. -/
theorem finrank_ribbonFunctions (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    finrank ℚ (ribbonFunctions hN hM A) = clusterCount hN hM true A := by
  let : Fintype (RibbonComponent hN hM A) := Fintype.ofFinite _
  rw [← (ribbonFunctionEquiv hN hM A).finrank_eq, Module.finrank_pi,
    ← Nat.card_eq_fintype_card, card_ribbonComponent]

/-- Evaluation difference of the two ends of an indexed ribbon on component functions. -/
def ribbonDifference (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : Fin N × Fin M) : ribbonFunctions hN hM A →ₗ[ℚ] ℚ :=
  ((LinearMap.proj (ribbonEndEquiv hN hM (v, false)) :
      (DirectedDart (checkerArrows N M) → ℚ) →ₗ[ℚ] ℚ) -
    LinearMap.proj (ribbonEndEquiv hN hM (v, true))).comp
      (ribbonFunctions hN hM A).subtype

@[simp] theorem ribbonDifference_apply (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : Fin N × Fin M) (f : ribbonFunctions hN hM A) :
    ribbonDifference hN hM A v f =
      f.val (ribbonEndEquiv hN hM (v, false)) -
        f.val (ribbonEndEquiv hN hM (v, true)) := rfl

theorem ribbonDifference_eq_zero_of_connected (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (h : RibbonConnected hN hM A (ribbonEndEquiv hN hM (v, false))
      (ribbonEndEquiv hN hM (v, true))) : ribbonDifference hN hM A v = 0 := by
  apply LinearMap.ext
  intro f
  exact sub_eq_zero.mpr (ribbonFunctions_invariant hN hM A f h)

theorem ribbonDifference_ne_zero_of_not_connected (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (h : ¬RibbonConnected hN hM A (ribbonEndEquiv hN hM (v, false))
      (ribbonEndEquiv hN hM (v, true))) : ribbonDifference hN hM A v ≠ 0 := by
  classical
  let q : RibbonComponent hN hM A := Quotient.mk _ (ribbonEndEquiv hN hM (v, false))
  let f := ribbonFunctionEquiv hN hM A (fun z => if q = z then 1 else 0)
  intro hz
  have he := LinearMap.congr_fun hz f
  change (if q = q then (1 : ℚ) else 0) -
    (if q = Quotient.mk _ (ribbonEndEquiv hN hM (v, true)) then 1 else 0) = 0 at he
  have hq : q ≠ Quotient.mk _ (ribbonEndEquiv hN hM (v, true)) :=
    fun he => h (Quotient.exact he)
  simp only [hq, ite_true, ite_false, sub_zero, one_ne_zero] at he

end PottsDiscontinuity.Torus
