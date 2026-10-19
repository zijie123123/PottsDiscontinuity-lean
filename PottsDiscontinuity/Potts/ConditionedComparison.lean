module

public import PottsDiscontinuity.Potts.FiniteEnergyBounds

/-! Conditional comparisons for the literal boundary correction. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
attribute [local instance] FK.configurationMeasurableSpace

/-- Conditioning an FK law on a decreasing event lowers every increasing
 event probability. The denominator is the actual probability of that event. -/
theorem conditioned_decreasing_event_le (q : FK.Parameters) (ξ : FK.BoundaryCondition V)
    (S B : Set (FK.Configuration G)) (hS : IsUpperSet S) (hB : IsLowerSet B)
    (hpos : 0 < (FK.measure G q ξ B).toReal) :
    (FK.measure G q ξ (S ∩ B)).toReal / (FK.measure G q ξ B).toReal ≤
      (FK.measure G q ξ S).toReal := by
  have hc : IsUpperSet Bᶜ := hB.compl
  have hfkg := FK.measure_positive_association q ξ S Bᶜ hS hc
  have hsplit := measureReal_inter_add_sdiff (μ := FK.measure G q ξ)
    (s := S) (MeasurableSpace.measurableSet_top (s := Bᶜ))
  have hcompl := measureReal_compl (μ := FK.measure G q ξ)
    (MeasurableSpace.measurableSet_top (s := B))
  have hdiff : S \ Bᶜ = S ∩ B := by ext x; simp
  rw [hdiff] at hsplit
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hcompl
  change (FK.measure G q ξ Bᶜ).toReal = 1 - (FK.measure G q ξ B).toReal at hcompl
  rw [hcompl] at hfkg
  apply (div_le_iff₀ hpos).mpr
  change (FK.measure G q ξ (S ∩ Bᶜ)).toReal +
    (FK.measure G q ξ (S ∩ B)).toReal = (FK.measure G q ξ S).toReal at hsplit
  nlinarith

omit [Finite V] in
/-- The corner correction event is decreasing. -/
theorem isLowerSet_allClosedEdges (F : Finset G.edgeSet) : IsLowerSet (allClosedEdges F) := by
  intro A C hAC hC
  exact Finset.disjoint_of_subset_right hAC hC

/-- Algebraic form of the comparison squeeze, with a fixed positive lower
bound on the conditioning probabilities. -/
theorem conditioned_squeeze_bounds {u c g b δ : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b) (hgu : g ≤ u) (hcu : u ≤ c)
    (hsplit : u ≤ b * g + (1 - b) * c) :
    u - (c - u) / δ ≤ g ∧ g ≤ u := by
  have hb0 : 0 < b := hδ.trans_le hδb
  have h1 : b * (u - g) ≤ (1 - b) * (c - u) := by nlinarith
  have h2 : δ * (u - g) ≤ c - u := by
    have ha := mul_le_mul_of_nonneg_right hδb (sub_nonneg.mpr hgu)
    have hright : (1 - b) * (c - u) ≤ c - u := by
      nlinarith [mul_nonneg hb0.le (sub_nonneg.mpr hcu)]
    linarith
  constructor
  · have := (le_div_iff₀ hδ).mpr (by nlinarith : (u - g) * δ ≤ c - u)
    linarith
  · exact hgu

/-- Ratio form of the numerical squeeze, retaining the joint mass as an atom. -/
theorem conditioned_ratio_squeeze_bounds {u c a b δ : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b)
    (hau : a / b ≤ u) (huc : u ≤ c) (ht : u ≤ a + c * (1 - b)) :
    u - (c - u) / δ ≤ a / b ∧ a / b ≤ u := by
  apply conditioned_squeeze_bounds hδ hδb hau huc
  have hb0 : b ≠ 0 := ne_of_gt (hδ.trans_le hδb)
  rw [mul_comm b (a / b), div_mul_cancel₀ _ hb0, mul_comm (1 - b) c]
  exact ht

end
end PottsDiscontinuity.Potts
