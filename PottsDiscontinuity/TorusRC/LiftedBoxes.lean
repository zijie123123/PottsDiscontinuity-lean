module

public import PottsDiscontinuity.TorusRC.CylinderFiberComparison
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Native square boxes in the integer cover and their torus embeddings -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Vertices of the actual square of radius R about the prescribed lift c. -/
abbrev LiftedBoxVertex (c : RotatedVertex) (R : ℕ) :=
  {z : RotatedVertex // inLiftedBox R c z}

instance liftedBoxVertex_finite (c : RotatedVertex) (R : ℕ) :
    Finite (LiftedBoxVertex c R) := by
  let f : LiftedBoxVertex c R →
      ↥(Set.Icc (c.val.1 - (R : ℤ)) (c.val.1 + R)) ×
      ↥(Set.Icc (c.val.2 - (R : ℤ)) (c.val.2 + R)) := fun z =>
    (⟨z.val.val.1, by
      have h := abs_le.mp z.property.1
      constructor <;> omega⟩,
     ⟨z.val.val.2, by
      have h := abs_le.mp z.property.2
      constructor <;> omega⟩)
  apply Finite.of_injective f
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) huv) (congrArg (fun z => z.2.val) huv)

/-- The native induced graph in the lifted square, with no periodic edges. -/
def liftedBoxGraph (c : RotatedVertex) (R : ℕ) : SimpleGraph (LiftedBoxVertex c R) :=
  rotatedLattice.induce {z | inLiftedBox R c z}

noncomputable local instance liftedBoxEdgeFintype (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

noncomputable section

/-- Free-box connection means an actual sampled-edge connection inside the
native box. If an endpoint is outside the box, the event is empty. -/
def liftedBoxFreeConnectionEvent (c : RotatedVertex) (R : ℕ)
    (u v : RotatedVertex) : Set (FK.Configuration (liftedBoxGraph c R)) :=
  {A | ∃ hu : inLiftedBox R c u, ∃ hv : inLiftedBox R c v,
    FK.ActualConnected (liftedBoxGraph c R) A ⟨u, hu⟩ ⟨v, hv⟩}

def liftedBoxFreeConnectionProbability (θ : FK.Parameters) (c : RotatedVertex)
    (R : ℕ) (u v : RotatedVertex) : ℝ :=
  torusRCFiberEventProbability (FK.law (liftedBoxGraph c R) θ (FK.BoundaryCondition.free ∅))
    (liftedBoxFreeConnectionEvent c R u v)

theorem liftedBoxFreeConnectionEvent_upper (c : RotatedVertex) (R : ℕ)
    (u v : RotatedVertex) : IsUpperSet (liftedBoxFreeConnectionEvent c R u v) := by
  rintro A B hAB ⟨hu, hv, hconn⟩
  exact ⟨hu, hv, FK.actualConnected_mono hAB hconn⟩

/-- Reduction modulo a period is injective on any half-open interval of that
period's length. This permits boxes with negative lifted coordinates. -/
theorem periodicCoordinate_eq_of_interval (hp : 0 < N) (L a b : ℤ)
    (ha : L ≤ a ∧ a < L + (N : ℤ)) (hb : L ≤ b ∧ b < L + (N : ℤ))
    (hab : periodicCoordinate hp a = periodicCoordinate hp b) : a = b := by
  have hmod := congrArg (fun z : Fin N => (z.val : ℤ)) hab
  simp only [periodicCoordinate_val] at hmod
  have hshift := (show Int.ModEq (N : ℤ) a b from hmod).sub_right L
  change (a - L) % (N : ℤ) = (b - L) % (N : ℤ) at hshift
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hshift
  omega

/-- An injective vertex projection of a box whose diameter is smaller than
both periods. -/
def liftedBoxProjection (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (c : RotatedVertex) (R : ℕ) (hRN : 2 * R < N) (hRM : 2 * R < M) :
    LiftedBoxVertex c R ↪ FaceVertex N M true where
  toFun z := liftedFaceVertex hN hM hNp hMp z.val
  inj' := by
    intro u v huv
    have hx := congrArg (fun z : FaceVertex N M true => z.val.1) huv
    have hy := congrArg (fun z : FaceVertex N M true => z.val.2) huv
    have hux := abs_le.mp u.property.1
    have hvx := abs_le.mp v.property.1
    have huy := abs_le.mp u.property.2
    have hvy := abs_le.mp v.property.2
    have hxeq : u.val.val.1 = v.val.val.1 :=
      periodicCoordinate_eq_of_interval hNp (c.val.1 - R) _ _
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hx
    have hyeq : u.val.val.2 = v.val.val.2 :=
      periodicCoordinate_eq_of_interval hMp (c.val.2 - R) _ _
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hy
    exact Subtype.ext (Subtype.ext (Prod.ext hxeq hyeq))

/-- Every native box edge projects to its actual indexed diamond edge. -/
theorem liftedBoxGraph_map_projection_le (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (c : RotatedVertex) (R : ℕ)
    (hRN : 2 * R < N) (hRM : 2 * R < M) :
    (liftedBoxGraph c R).map (liftedBoxProjection hN hM hNp hMp c R hRN hRM) ≤
      fullDiamondGraph hN hM := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨u, v, huv, rfl, rfl⟩
  have hlat : rotatedLattice.Adj u.val v.val := huv
  have hne := (liftedBoxProjection hN hM hNp hMp c R hRN hRM).injective.ne huv.ne
  change (diamondOpenGraph hN hM true (fun _ => true)).Adj _ _
  rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨liftedEdgeIndex hNp hMp u.val v.val, rfl,
    liftedFaceEndpoints_eq hN hM hNp hMp u.val v.val hlat⟩, hne⟩

end

end PottsDiscontinuity.TorusRC
