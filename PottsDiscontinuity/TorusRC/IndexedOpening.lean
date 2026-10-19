module

public import PottsDiscontinuity.TorusRC.FiberFiniteEnergy
public import PottsDiscontinuity.TorusRC.Association

/-! # Finite-energy opening of prescribed indexed torus edges -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

noncomputable local instance indexedOpeningEdges (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _
noncomputable local instance indexedOpeningEdgeEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

noncomputable section

/-- Exact indexed finite-energy bound, obtained through the simple-edge
bijection rather than forgetting indexed-edge multiplicity. -/
theorem torusRCProbability_allOpen_ge (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (s : Finset (Fin N × Fin M)) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ s.card ≤
      torusRCProbability hN hM q {A | ∀ e ∈ s, A e = true} := by
  classical
  let f := torusIndexedEdgeEquiv hN hM hN4 hM4
  let g := torusRCConfigurationEquiv hN hM hN4 hM4
  have hmem (A : RCConfig N M) (e : Fin N × Fin M) : f e ∈ g A ↔ A e = true := by
    change torusIndexedEdgeEmbedding hN hM hN4 hM4 e ∈ g A ↔ _
    exact mem_torusRCConfigurationEquiv hN hM hN4 hM4 A e
  have himage : g '' {A | ∀ e ∈ s, A e = true} = {C | s.map f.toEmbedding ⊆ C} := by
    ext C
    constructor
    · rintro ⟨A,hA,rfl⟩ e he
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp he
      exact (hmem A v).mpr (hA v hv)
    · intro hC
      refine ⟨g.symm C,?_,g.apply_symm_apply C⟩
      intro e he
      apply (hmem (g.symm C) e).mp
      rw [g.apply_symm_apply]
      exact hC (Finset.mem_map.mpr ⟨e,he,rfl⟩)
  rw [torusRCProbability_eq_fk_image hN hM hN4 hM4 q, himage]
  have h := fk_allOpen_probability_ge (fullDiamondGraph hN hM)
    (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅) (s.map f.toEmbedding)
  simpa only [Finset.card_map,MeasureTheory.Measure.real] using h

/-- Prescribing open edges costs its finite-energy factor even when combined
with any increasing event. -/
theorem torusRCProbability_allOpen_inter_ge (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (s : Finset (Fin N × Fin M)) (E : Set (RCConfig N M))
    (hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ s.card * torusRCProbability hN hM q E ≤
      torusRCProbability hN hM q ({A | ∀ e ∈ s, A e = true} ∩ E) := by
  have hupper : ∀ ⦃A B : RCConfig N M⦄, A ≤ B →
      (∀ e ∈ s, A e = true) → ∀ e ∈ s, B e = true := by
    intro A B hAB hA e he
    have h := hAB e
    rw [hA e he] at h
    cases hB : B e
    · exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa only [hB] using h))
    · rfl
  exact (mul_le_mul_of_nonneg_right
    (torusRCProbability_allOpen_ge hN hM hN4 hM4 q s)
    (torusRCProbability_nonneg hN hM q E)).trans
      (torusRCProbability_inter_ge_mul hN hM q _ E hupper hE)

end

end PottsDiscontinuity.TorusRC
