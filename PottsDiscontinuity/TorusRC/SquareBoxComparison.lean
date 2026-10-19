module

public import PottsDiscontinuity.CorrLength.RotatedFreeLimit
public import PottsDiscontinuity.TorusRC.FiniteConnectionTransport
public import PottsDiscontinuity.TorusRC.LiftedBoxes

/-! # Comparison of rotated-lattice image boxes with native lifted square boxes -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

/-- An image box of radius r lies in the native square of radius 2r. -/
theorem squareBox_mem_liftedBox (r R : ℕ) (hR : 2*r ≤ R)
    (v : BoxVertex (0,0) r) : inLiftedBox R rotatedLatticeOrigin (squareToRotatedVertex v.val) := by
  have hv := (mem_latticeBox (0,0) v.val r).mp v.property
  dsimp at hv
  dsimp [inLiftedBox,rotatedLatticeOrigin,squareToRotatedVertex]
  constructor <;> apply abs_le.mpr <;> constructor <;> omega

/-- The original square-lattice coordinates, embedded in the actual native
rotated square; this retains the induced graph and every sampled edge. -/
def squareBoxToLiftedBox (r R : ℕ) (hR : 2*r ≤ R) :
    BoxVertex (0,0) r ↪ LiftedBoxVertex rotatedLatticeOrigin R where
  toFun v := ⟨squareToRotatedVertex v.val,squareBox_mem_liftedBox r R hR v⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    have hh := congrArg (fun z : LiftedBoxVertex rotatedLatticeOrigin R =>
      rotatedToSquareVertex z.val) h
    simpa only [rotatedToSquare_squareToRotated] using hh

theorem squareBoxGraph_map_le_liftedBox (r R : ℕ) (hR : 2*r ≤ R) :
    (boxGraph (0,0) r).map (squareBoxToLiftedBox r R hR) ≤
      liftedBoxGraph rotatedLatticeOrigin R := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := hxy
  change rotatedLattice.Adj (squareToRotatedVertex u.val) (squareToRotatedVertex v.val)
  rw [rotatedLattice_adj_iff_square,rotatedToSquare_squareToRotated,rotatedToSquare_squareToRotated]
  exact huv

noncomputable section

local instance squareBoxComparisonEdgeFintype (r : ℕ) : Fintype (boxGraph (0,0) r).edgeSet :=
  Fintype.ofFinite _
local instance nativeBoxComparisonEdgeFintype (R : ℕ) :
    Fintype (liftedBoxGraph rotatedLatticeOrigin R).edgeSet := Fintype.ofFinite _

/-- Every finite square-box connection probability is dominated by the
native lifted-box free law once the image box fits. -/
theorem squareBox_connection_probability_le_native (θ : Parameters)
    (r R : ℕ) (hR : 2*r ≤ R) (u v : BoxVertex (0,0) r) :
    torusRCFiberEventProbability (law (boxGraph (0,0) r) θ (BoundaryCondition.free ∅))
      {A | ActualConnected (boxGraph (0,0) r) A u v} ≤
    liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
      (squareToRotatedVertex u.val) (squareToRotatedVertex v.val) := by
  classical
  let G := boxGraph (0,0) r
  let H := liftedBoxGraph rotatedLatticeOrigin R
  let f := squareBoxToLiftedBox r R hR
  let hGH := squareBoxGraph_map_le_liftedBox r R hR
  let E : Set (Configuration G) := {A | ActualConnected G A u v}
  let F : Configuration G → ℝ := E.indicator (fun _ => 1)
  have hF0 : ∀ A, 0 ≤ F A := by
    intro A
    by_cases hA : A ∈ E <;> simp [F,hA]
  have hF : Monotone F := by
    intro A B hAB
    by_cases hA : A ∈ E
    · have hB : B ∈ E := actualConnected_mono hAB hA
      simp [F,hA,hB]
    · by_cases hB : B ∈ E <;> simp [F,hA,hB]
  have h := embedded_free_expectation_le G H f hGH θ ∅ ∅ F hF0 hF
  apply h.trans
  apply FiniteProbability.expectation_mono
  intro A
  by_cases hA : embeddedConfigurationRestriction G H f hGH A ∈ E
  · have hconn := actualConnected_embeddedRestriction f hGH A u v hA
    have hevent : A ∈ liftedBoxFreeConnectionEvent rotatedLatticeOrigin R
        (squareToRotatedVertex u.val) (squareToRotatedVertex v.val) :=
      ⟨squareBox_mem_liftedBox r R hR u,squareBox_mem_liftedBox r R hR v,hconn⟩
    simp [F,Set.indicator,hA,hevent]
  · simp only [F,Set.indicator_of_notMem hA]
    by_cases hB : A ∈ liftedBoxFreeConnectionEvent rotatedLatticeOrigin R
      (squareToRotatedVertex u.val) (squareToRotatedVertex v.val) <;>
      simp [Set.indicator,hB]

end
end PottsDiscontinuity.TorusRC
