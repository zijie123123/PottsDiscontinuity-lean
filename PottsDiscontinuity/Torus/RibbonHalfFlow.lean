module

public import PottsDiscontinuity.Torus.RibbonChainComplex

/-!
# Conserved flows on ribbon ends

Extend an open-edge chain by zero on the closed indexed edges and assign opposite
outward flows to its two ends. Vertex conservation becomes a zero sum at the four
corners of each primal face.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Extension of an indexed open-edge chain by zero on precisely the closed edges. -/
def extendDiamondChain (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) : ℚ := if h : A v = true then f ⟨v, h⟩ else 0

@[simp] theorem extendDiamondChain_open (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) (hv : A v = true) : extendDiamondChain A f v = f ⟨v, hv⟩ := by
  simp only [extendDiamondChain, hv, dite_true]

@[simp] theorem extendDiamondChain_closed (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) (hv : A v = false) : extendDiamondChain A f v = 0 := by
  simp only [extendDiamondChain, hv, Bool.false_eq_true, dite_false]

/-- Outward half-edge flow at a canonical ribbon corner. -/
def ribbonHalfFlow (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) : ℚ :=
  let x := (ribbonEndEquiv hN hM).symm d
  if x.2 then -extendDiamondChain A f x.1 else extendDiamondChain A f x.1

@[simp] theorem ribbonHalfFlow_end (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (v : Fin N × Fin M) (b : Bool) :
    ribbonHalfFlow hN hM A f (ribbonEndEquiv hN hM (v, b)) =
      if b then -extendDiamondChain A f v else extendDiamondChain A f v := by
  simp only [ribbonHalfFlow, Equiv.symm_apply_apply]

theorem sum_ribbonHalfFlow_pairing (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (g : FaceVertex N M true → ℚ) :
    (∑ d : DirectedDart (checkerArrows N M),
      g (ribbonFace hN hM d) * ribbonHalfFlow hN hM A f d) =
      -(∑ u, g u * diamondBoundary hN hM A f u) := by
  classical
  rw [diamondBoundary_pairing, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_lhs => rw [Fintype.sum_prod_type]
  change (∑ v, ∑ b : Bool,
    g (ribbonFace hN hM (ribbonEndEquiv hN hM (v, b))) *
      ribbonHalfFlow hN hM A f (ribbonEndEquiv hN hM (v, b))) = _
  have hc : (∑ e, diamondCoboundary hN hM A g e * f e) =
      ∑ e : OpenDiamondEdge A,
        (g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false)) *
          extendDiamondChain A f e.val := by
    exact Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open A f e.val e.property]; rfl)
  rw [hc]
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v =>
      (g (faceEndpoint hN hM true v true) - g (faceEndpoint hN hM true v false)) *
        extendDiamondChain A f v), Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.sum_bool, ribbonFace_end, ribbonHalfFlow_end,
    Bool.false_eq_true, ite_true, ite_false]
  cases ha : A v
  · simp only [extendDiamondChain_closed A f v ha, Bool.false_eq_true, ite_false,
      mul_zero, neg_zero, add_zero]
  · simp only [ite_true]
    ring

/-- Vertex conservation is the four-corner zero-sum identity on every primal disc. -/
theorem sum_ribbonHalfFlow_corners (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (v : FaceVertex N M true) :
    (∑ p : Port, ribbonHalfFlow hN hM A f.val (ribbonCornerEquiv hN hM (v, p))) = 0 := by
  classical
  have he := sum_ribbonHalfFlow_pairing hN hM A f.val (fun w => if v = w then 1 else 0)
  have hf : diamondBoundary hN hM A f.val = 0 := f.property
  rw [hf] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero] at he
  rw [← (ribbonCornerEquiv hN hM).sum_comp, Fintype.sum_prod_type] at he
  have hx : ∀ (w : FaceVertex N M true) (p : Port),
      ribbonFace hN hM (ribbonCornerEquiv hN hM (w, p)) = w :=
    fun w p => Subtype.ext (leftFace_faceCorner w.val p)
  simp only [hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at he
  exact he

end PottsDiscontinuity.Torus
