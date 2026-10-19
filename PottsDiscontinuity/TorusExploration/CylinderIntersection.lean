module

public import PottsDiscontinuity.Torus.RibbonIntersection
public import PottsDiscontinuity.Torus.DiamondFullFlows

/-! Local intersection coefficients for cutting a cylinder along a crossing cluster. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus
open PottsDiscontinuity.SixVertex
variable {N M : ℕ}

/-- Read an actual full-torus indexed chain coefficient. -/
def fullFlowAt (f : OpenDiamondEdge (openRCConfig N M) → ℚ) (v : Fin N × Fin M) : ℚ :=
  f ⟨v,rfl⟩

lemma full_halfFlow_corner (hN : Even N) (hM : Even M)
    (f : OpenDiamondEdge (openRCConfig N M) → ℚ)
    (v : FaceVertex N M true) (p : Port) :
    ribbonHalfFlow hN hM (openRCConfig N M) f (ribbonCornerEquiv hN hM (v,p)) =
      match p with
      | .east => fullFlowAt f v.val
      | .north => fullFlowAt f (nxt v.val.1,v.val.2)
      | .west => -fullFlowAt f (nxt v.val.1,nxt v.val.2)
      | .south => -fullFlowAt f (v.val.1,nxt v.val.2) := by
  cases p <;> simp only [ribbonHalfFlow_raw,ribbonCornerEquiv_val,faceCorner,
    ribbonEndSide,extendDiamondChain,openRCConfig,fullFlowAt,
    Bool.false_eq_true,ite_true,ite_false] <;> rfl

lemma full_primitive_raw (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M))
    (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) f d =
      match d.val.2 with
      | .east => 0
      | .north => -fullFlowAt f.val (nxt (leftFace d.val).1,(leftFace d.val).2)
      | .west => -fullFlowAt f.val (nxt (leftFace d.val).1,(leftFace d.val).2) +
          fullFlowAt f.val (nxt (leftFace d.val).1,nxt (leftFace d.val).2)
      | .south => fullFlowAt f.val (leftFace d.val) := by
  obtain ⟨⟨v,p⟩,rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner]
  simp_rw [full_halfFlow_corner]
  cases p <;> simp only [cornerPrimitiveValue,ribbonCornerEquiv_val,faceCorner,leftFace,
    nxt,prv,Equiv.symm_apply_apply,sub_neg_eq_add]

/-- The coefficient only samples the indexed edge immediately below e. -/
theorem full_intersectionCoefficient_eq_below (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M))
    (e : OpenDiamondEdge (openRCConfig N M)) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) f e =
      (if checker e.val then -1 else 1) * fullFlowAt f.val (e.val.1,prv e.val.2) := by
  unfold ribbonIntersectionCoefficient
  rw [full_primitive_raw,full_primitive_raw]
  cases hc : checker e.val <;>
    simp only [ribbonEndEquiv_val,ribbonEnd,hc,Bool.false_eq_true,ite_false,ite_true,
      leftFace,fullFlowAt,nxt,prv,Equiv.apply_symm_apply,
      neg_one_mul,one_mul] <;> ring

end PottsDiscontinuity.TorusExploration
