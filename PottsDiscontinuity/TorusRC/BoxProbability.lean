module

public import PottsDiscontinuity.CorrLength.RotatedFreeLimit
public import PottsDiscontinuity.TorusRC.ColumnZigzag
public import PottsDiscontinuity.TorusRC.LiftedBoxes

/-! # Positivity and normalization of the native box connection probability -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength
open scoped BigOperators

noncomputable section

local instance boxProbabilityBoxEdgeFintype (c : RotatedVertex) (R : ℕ) : Fintype (liftedBoxGraph c R).edgeSet :=
  Fintype.ofFinite _

/-- Every nonempty finite event has positive probability under an everywhere
positive mass function. -/
theorem torusRCFiberEventProbability_pos_of_mem {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α) (a : α) (ha : a ∈ E) (hp : 0 < p a) :
    0 < torusRCFiberEventProbability p E := by
  classical
  unfold torusRCFiberEventProbability FK.FiniteProbability.expectation
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (fun b _ => mul_nonneg ENNReal.toReal_nonneg (by
      by_cases hb : b ∈ E <;> simp [Set.indicator,hb])) (Finset.mem_univ a))
  simpa only [Set.indicator_of_mem ha, mul_one] using
    (ENNReal.toReal_pos hp.ne' (p.apply_ne_top a))

/-- The explicit two-column zigzag fits in every native box of radius at
least 2n. Thus the connection probability used in (3.15) is strictly positive. -/
theorem liftedBoxFreeDiagonalProbability_pos (θ : FK.Parameters)
    (n R : ℕ) (hn : 0 < n) (hR : 2*n ≤ R) :
    0 < liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
      rotatedLatticeOrigin (rotatedDiagonalSite n) := by
  classical
  have hz (k : ℕ) (hk : k ≤ 2*n) :
      inLiftedBox R rotatedLatticeOrigin (columnZigzagSite 0 ⟨0,rfl⟩ k) := by
    dsimp [inLiftedBox,rotatedLatticeOrigin,columnZigzagSite]
    constructor <;> apply abs_le.mpr <;> constructor <;> omega
  let z (k : ℕ) (hk : k ≤ 2*n) : LiftedBoxVertex rotatedLatticeOrigin R :=
    ⟨columnZigzagSite 0 ⟨0,rfl⟩ k,hz k hk⟩
  let A : FK.Configuration (liftedBoxGraph rotatedLatticeOrigin R) := Finset.univ
  have hreach (k : ℕ) (hk : k ≤ 2*n) :
      FK.ActualConnected (liftedBoxGraph rotatedLatticeOrigin R) A (z 0 (by omega)) (z k hk) := by
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      apply (ih (by omega)).trans
      apply FK.actualConnected_of_adj
      rw [FK.openGraph_adj]
      have hadj : (liftedBoxGraph rotatedLatticeOrigin R).Adj (z k (by omega)) (z (k+1) hk) :=
        columnZigzagSite_adj 0 ⟨0,rfl⟩ k
      exact ⟨⟨s(z k (by omega),z (k+1) hk),(liftedBoxGraph rotatedLatticeOrigin R).mem_edgeSet.mpr hadj⟩,
        Finset.mem_univ _,rfl⟩
  have hzero : columnZigzagSite 0 ⟨0,rfl⟩ 0 = rotatedLatticeOrigin := by
    apply Subtype.ext
    rfl
  have hend : columnZigzagSite 0 ⟨0,rfl⟩ (2*n) = rotatedDiagonalSite n := by
    apply Subtype.ext
    simp [columnZigzagSite,rotatedDiagonalSite]
  have hA : A ∈ liftedBoxFreeConnectionEvent rotatedLatticeOrigin R
      rotatedLatticeOrigin (rotatedDiagonalSite n) := by
    have h := hreach (2*n) le_rfl
    have hu : inLiftedBox R rotatedLatticeOrigin rotatedLatticeOrigin := by
      simpa only [hzero] using hz 0 (by omega)
    have hv : inLiftedBox R rotatedLatticeOrigin (rotatedDiagonalSite n) := by
      simpa only [hend] using hz (2*n) le_rfl
    have hzu : z 0 (by omega) = ⟨rotatedLatticeOrigin,hu⟩ := Subtype.ext hzero
    have hzv : z (2*n) le_rfl = ⟨rotatedDiagonalSite n,hv⟩ := Subtype.ext hend
    rw [hzu,hzv] at h
    exact ⟨hu,hv,h⟩
  exact torusRCFiberEventProbability_pos_of_mem _ _ A hA (FK.law_pos _ _ _ _)

end
end PottsDiscontinuity.TorusRC
