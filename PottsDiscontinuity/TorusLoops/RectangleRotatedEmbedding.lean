module

public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.TorusLoops.RectangleFK

/-!
# Embedding the cut diamond rectangle in a finite square FK box

The face coordinates of the cut rectangle are the coordinates of vertices in
the rotated lattice. The rotated-to-square coordinate map places all of them
inside a finite square box and sends each retained diamond edge to a square
lattice edge.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- A face centre, unwrapped from the torus, as a vertex of the rotated lattice. -/
def rectangleFaceToRotated (u : FaceVertex N M true) : RotatedVertex := by
  have he : Even (u.val.1.val + u.val.2.val) := by
    rw [Nat.even_iff]
    have hp := u.property
    change decide ((u.val.1.val + u.val.2.val) % 2 = 0) = true at hp
    exact of_decide_eq_true hp
  refine ⟨(u.val.1.val, u.val.2.val), ?_⟩
  change Even ((u.val.1.val : ℤ) + (u.val.2.val : ℤ))
  have hei : Even (Int.ofNat (u.val.1.val + u.val.2.val)) := he.natCast
  simpa [Nat.cast_add] using hei

private theorem rectangleFaceToRotated_injective :
    Function.Injective (rectangleFaceToRotated (N := N) (M := M)) := by
  intro u v huv
  have hval := congrArg Subtype.val huv
  have hx : (u.val.1.val : ℤ) = (v.val.1.val : ℤ) := by
    simpa [rectangleFaceToRotated] using congrArg Prod.fst hval
  have hy : (u.val.2.val : ℤ) = (v.val.2.val : ℤ) := by
    simpa [rectangleFaceToRotated] using congrArg Prod.snd hval
  have hx' : u.val.1.val = v.val.1.val := by exact_mod_cast hx
  have hy' : u.val.2.val = v.val.2.val := by exact_mod_cast hy
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> assumption

/-- A finite box large enough to contain the square-coordinate image of every
face of the cut rectangle. -/
abbrev RectangleRotatedBoxRadius (N M : ℕ) := N + M + 2

/-- The face-vertex embedding into an origin-centred square box. -/
def rectangleFaceBoxEmbedding (_hN : Even N) (_hM : Even M) :
    FaceVertex N M true ↪ BoxVertex (0, 0) (RectangleRotatedBoxRadius N M) where
  toFun u := ⟨rotatedToSquareVertex (rectangleFaceToRotated u), by
    rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    dsimp [rotatedToSquareVertex, rectangleFaceToRotated]
    have hi := u.val.1.isLt
    have hj := u.val.2.isLt
    omega⟩
  inj' := by
    intro u v huv
    apply rectangleFaceToRotated_injective
    apply rotatedVertexEquiv.injective
    exact congrArg Subtype.val huv

private theorem rectangleEndpointXFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.1.val =
      if checker v then v.1.val else (prv v.1).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointXTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.1.val =
      if checker v then (prv v.1).val else v.1.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYFalse (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v false).val.2.val = v.2.val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleEndpointYTrue (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) :
    (faceEndpoint hN hM true v true).val.2.val = (prv v.2).val := by
  cases hc : checker v <;> simp [faceEndpoint, faceEndpointRaw, hc]

private theorem rectangleFaceEndpointToRotated_adj (hN : Even N) (hM : Even M)
    (e : RectangleEdgeIndex (N := N) (M := M)) :
    rotatedLattice.Adj
      (rectangleFaceToRotated (faceEndpoint hN hM true e.val false))
      (rectangleFaceToRotated (faceEndpoint hN hM true e.val true)) := by
  have hip : 0 < e.val.1.val := Nat.pos_of_ne_zero e.property.1
  have hjp : 0 < e.val.2.val := Nat.pos_of_ne_zero e.property.2
  have hi := prv_val_of_pos e.val.1 hip
  have hj := prv_val_of_pos e.val.2 hjp
  have hiZ : ((prv e.val.1).val : ℤ) = (e.val.1.val : ℤ) - 1 := by
    rw [hi, Nat.cast_sub (by omega)]
    norm_num
  have hjZ : ((prv e.val.2).val : ℤ) = (e.val.2.val : ℤ) - 1 := by
    rw [hj, Nat.cast_sub (by omega)]
    norm_num
  change |((faceEndpoint hN hM true e.val false).val.1.val : ℤ) -
      ((faceEndpoint hN hM true e.val true).val.1.val : ℤ)| = 1 ∧
    |((faceEndpoint hN hM true e.val false).val.2.val : ℤ) -
      ((faceEndpoint hN hM true e.val true).val.2.val : ℤ)| = 1
  rw [rectangleEndpointXFalse hN hM, rectangleEndpointXTrue hN hM,
    rectangleEndpointYFalse hN hM, rectangleEndpointYTrue hN hM]
  by_cases hc : checker e.val
  · simp only [ite_eq_left hc]
    rw [hiZ, hjZ]
    constructor
    · calc
        |(e.val.1.val : ℤ) - ((e.val.1.val : ℤ) - 1)| = |1| :=
          congrArg abs (by ring)
        _ = 1 := abs_one
    · calc
        |(e.val.2.val : ℤ) - ((e.val.2.val : ℤ) - 1)| = |1| :=
          congrArg abs (by ring)
        _ = 1 := abs_one
  · simp only [ite_eq_right hc]
    rw [hiZ, hjZ]
    constructor
    · calc
        |((e.val.1.val : ℤ) - 1) - (e.val.1.val : ℤ)| = |-1| :=
          congrArg abs (by ring)
        _ = 1 := by norm_num
    · calc
        |(e.val.2.val : ℤ) - ((e.val.2.val : ℤ) - 1)| = |1| :=
          congrArg abs (by ring)
        _ = 1 := abs_one

/-- The rectangle base graph maps into the indicated finite square box graph. -/
theorem rectangleBaseGraph_map_rectangleFaceBoxEmbedding
    (hN : Even N) (hM : Even M) :
    (rectangleBaseGraph hN hM).map (rectangleFaceBoxEmbedding hN hM) ≤
      boxGraph (0, 0) (RectangleRotatedBoxRadius N M) := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  rw [rectangleBaseGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases huv with ⟨⟨e, he⟩, hne⟩
  have hadj := (rotatedLattice_adj_iff_square
    (rectangleFaceToRotated (faceEndpoint hN hM true e.val false))
    (rectangleFaceToRotated (faceEndpoint hN hM true e.val true))).mp
      (rectangleFaceEndpointToRotated_adj hN hM e)
  rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    rw [boxGraph_adj_iff]
    change squareLattice.Adj
      (rotatedToSquareVertex (rectangleFaceToRotated
        (faceEndpoint hN hM true e.val false)))
      (rotatedToSquareVertex (rectangleFaceToRotated
        (faceEndpoint hN hM true e.val true)))
    exact hadj
  · subst u
    subst v
    rw [boxGraph_adj_iff]
    change squareLattice.Adj
      (rotatedToSquareVertex (rectangleFaceToRotated
        (faceEndpoint hN hM true e.val true)))
      (rotatedToSquareVertex (rectangleFaceToRotated
        (faceEndpoint hN hM true e.val false)))
    exact hadj.symm

end PottsDiscontinuity.TorusLoops
