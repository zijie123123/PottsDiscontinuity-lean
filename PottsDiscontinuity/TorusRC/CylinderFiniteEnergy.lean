module

public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.ElementaryTail
public import PottsDiscontinuity.TorusLoops.FiniteEnergy

/-! # Finite-energy cost of cutting the torus seam -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

/-- The indexed seam edges, represented by row zero of the medial coordinates. -/
def torusRCSeamRow (hM : 0 < M) : Finset (Fin N × Fin M) :=
  Finset.univ.image fun i : Fin N => (i, (⟨0, hM⟩ : Fin M))

theorem torusRCSeamRow_card (hM : 0 < M) :
    (torusRCSeamRow (N := N) hM).card = N := by
  rw [torusRCSeamRow, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

/-- Configurations with every edge in the seam row closed. -/
def torusRCSeamRowClosed (hM : 0 < M) : Set (RCConfig N M) :=
  {A | ∀ i : Fin N, A (i, (⟨0, hM⟩ : Fin M)) = false}

/-- A seam-closed cylinder crossing event, read after forcing the seam closed. -/
def torusRCSeamClosedCrossingEvent (hN : Even N) (hM : Even M)
    (r : ℕ) : Set (RCConfig N M) :=
  {A | torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A)}

theorem torusRCSeamClosed_toggle (A : RCConfig N M) (v : Fin N × Fin M)
    (hv : v.2.val = 0) :
    torusRCSeamClosed (toggleEdge A v) = torusRCSeamClosed A := by
  funext e
  by_cases he : e.2.val = 0
  · simp [torusRCSeamClosed, he]
  · have hne : e ≠ v := by
      intro h
      subst e
      exact he hv
    simp only [torusRCSeamClosed, he, ite_false]
    rw [toggleEdge_away A hne]

theorem torusRCSeamClosedCrossingEvent_toggle_stable
    (hN : Even N) (hM : Even M) (r : ℕ)
    (v : Fin N × Fin M) (hv : v.2.val = 0) (A : RCConfig N M) :
    A ∈ torusRCSeamClosedCrossingEvent hN hM r ↔
      toggleEdge A v ∈ torusRCSeamClosedCrossingEvent hN hM r := by
  change torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) ↔
    torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed (toggleEdge A v))
  rw [torusRCSeamClosed_toggle A v hv]

/-- Forcing all seam edges closed costs at most one finite-energy factor per
edge for an event determined by the seam-closed configuration. -/
theorem torusRCProbability_close_seam (hN : Even N) (hM : Even M)
    (hMpos : 0 < M) (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    (1 - (rcCriticalParameter q).val) ^ N *
        torusRCProbability hN hM q (torusRCSeamClosedCrossingEvent hN hM r) ≤
      torusRCProbability hN hM q
        (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMpos) := by
  let S := torusRCSeamRow (N := N) hMpos
  let E := torusRCSeamClosedCrossingEvent hN hM r
  have hstable : ∀ v ∈ S, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E := by
    intro v hv A
    have hv0 : v.2.val = 0 := by
      obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hv
      rw [← hEq]
    exact torusRCSeamClosedCrossingEvent_toggle_stable hN hM r v hv0 A
  have hfinite := TorusLoops.torusRCProbability_close_finite_set hN hM q S E hstable
  change (1 - (rcCriticalParameter q).val) ^ S.card *
      TorusLoops.phi_T_probability hN hM q E ≤
        TorusLoops.phi_T_probability hN hM q (E ∩ {A | ∀ v ∈ S, A v = false}) at hfinite
  have hcard : S.card = N := torusRCSeamRow_card hMpos
  have hclosed :
      (E ∩ {A | ∀ v ∈ S, A v = false}) = E ∩ torusRCSeamRowClosed hMpos := by
    ext A
    constructor
    · rintro ⟨hE, hcl⟩
      refine ⟨hE, ?_⟩
      intro i
      exact hcl (i, (⟨0, hMpos⟩ : Fin M)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · rintro ⟨hE, hcl⟩
      refine ⟨hE, ?_⟩
      intro v hv
      obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hv
      rw [← hEq]
      exact hcl i
  rw [hclosed, hcard] at hfinite
  simpa [E, TorusLoops.phi_T_probability] using hfinite

/-- The premise `hUr` (`U ≥ r` forces `r` distinct bottom-to-top clusters after the seam
row is closed) turns the vertical-winding tail into the seam-closed cylinder crossing event. -/
theorem torusRCVerticalTail_subset_seamClosedCrossings
    (hN : Even N) (hM : Even M) (hMpos : 0 < M) (r : ℕ)
    (hhUr : hUr hN hM hMpos r) :
    torusRCVerticalTail hN hM ⟨0, hMpos⟩ r ⊆
      torusRCSeamClosedCrossingEvent hN hM r := by
  intro A hA
  exact hhUr A hA

/-- Under the premise `hUr`, the winding tail is bounded by the probability of
the distinct-crossing event with the seam closed, up to its finite-energy
cost. This is the seam-cut step in the reduction to (3.21). -/
theorem torusRCVerticalTail_close_seam_le
    (hN : Even N) (hM : Even M) (hMpos : 0 < M)
    (q : Set.Ici (1 : ℝ)) (r : ℕ)
    (hhUr : hUr hN hM hMpos r) :
    (1 - (rcCriticalParameter q).val) ^ N *
        torusRCProbability hN hM q
          (torusRCVerticalTail hN hM ⟨0, hMpos⟩ r) ≤
      torusRCProbability hN hM q
        (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMpos) := by
  have hsub := torusRCVerticalTail_subset_seamClosedCrossings hN hM hMpos r hhUr
  have hmono := torusRCProbability_mono hN hM q hsub
  have hclose := torusRCProbability_close_seam hN hM hMpos q r
  have hclosePos : 0 < 1 - (rcCriticalParameter q).val :=
    sub_pos.mpr (criticalParameter_lt_one q)
  have hfac : 0 ≤ (1 - (rcCriticalParameter q).val) ^ N :=
    pow_nonneg hclosePos.le N
  calc
    (1 - (rcCriticalParameter q).val) ^ N *
        torusRCProbability hN hM q
          (torusRCVerticalTail hN hM ⟨0, hMpos⟩ r) ≤
      (1 - (rcCriticalParameter q).val) ^ N *
        torusRCProbability hN hM q (torusRCSeamClosedCrossingEvent hN hM r) :=
      mul_le_mul_of_nonneg_left hmono hfac
    _ ≤ torusRCProbability hN hM q
          (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMpos) := hclose

end PottsDiscontinuity.TorusRC
