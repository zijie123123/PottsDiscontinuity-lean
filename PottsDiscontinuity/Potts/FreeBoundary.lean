module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.GraphCoupling
public import PottsDiscontinuity.Potts.LiteralBoundary

/-!
# Free Edwards–Sokal coupling for the frozen finite Potts law

Boundary index zero makes every literal boundary field vanish, because the
spin palette is `{1,...,q}`. The spin and bond marginals below are the frozen
`pottsProb` and `rcProb`, with no change of Hamiltonian or vertex carrier.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

local instance freeVertexDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq ↥(V : Set (ℤ × ℤ)) := fun _ _ => Classical.propDecidable _

local instance freeVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype ↥(V : Set (ℤ × ℤ)) := Fintype.ofFinite _

local instance freeEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet :=
  fun _ _ => Classical.propDecidable _

local instance freeEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- With boundary index zero, the literal boundary field is identically zero. -/
theorem freeGibbsWeight_eq (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (σ : SpinConfiguration q V) :
    constraintGibbsWeight β (edgeAgreement (squareLattice.induce (V : Set (ℤ × ℤ)))) σ =
      Real.exp (-β * pottsHamiltonian q V 0 σ) := by
  have hz (x : ↥(V : Set (ℤ × ℤ))) : ¬ (σ x : ℕ) = 0 := by
    have := (σ x).property.1
    omega
  simp only [constraintGibbsWeight, pottsHamiltonian, Fin.val_zero, hz, and_false,
    ↓reduceIte, Finset.sum_const_zero, sub_zero, neg_mul_neg, edgeAgreement]
  congr 1
  apply congrArg (fun t : ℝ => β * t)
  apply Finset.sum_congr (by ext e; simp)
  intro e _
  congr 1

/-- The free normalized graph Gibbs weight is the exact frozen Potts mass. -/
theorem freeGibbsProbability_eq_pottsProb (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (σ : SpinConfiguration q V) :
    constraintGibbsWeight β (edgeAgreement (squareLattice.induce (V : Set (ℤ × ℤ)))) σ /
        ∑ τ : SpinConfiguration q V,
          constraintGibbsWeight β (edgeAgreement (squareLattice.induce (V : Set (ℤ × ℤ)))) τ =
      pottsProb q V β 0 σ := by
  simp only [freeGibbsWeight_eq, pottsProb]
  congr 1
  apply Finset.sum_congr (by ext τ; simp)
  intro τ _
  rfl

/-- The free finite joint mass, using only the actual induced lattice edges. -/
abbrev freeJointProbability (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (σ : SpinConfiguration q V)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  constraintJointProbability β (edgeAgreement (squareLattice.induce (V : Set (ℤ × ℤ)))) σ ω

theorem freeConfigurationProbability_eq_rcProb (q : ℕ) (hq : 2 ≤ q)
    (V : Finset (ℤ × ℤ)) (β : ℝ) (hβ : 0 < β)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    FK.configurationProbability _ (fkParameters q hq β hβ) (FK.BoundaryCondition.free ∅)
        (FK.boolConfigurationEquiv _ ω) =
      rcProb V (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 0 ω :=
  FK.configurationProbability_eq_rcProb (fkParameters q hq β hβ) V 0 ω

/-- The finite free coupling is a genuine probability mass function. -/
def freeJointLaw (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ) (hβ : 0 < β) :
    PMF (SpinConfiguration q V × ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool)) := by
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  exact PMF.ofFintype (fun z => ENNReal.ofReal (freeJointProbability q V β z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
      constraintJointProbability_nonneg hβ _ z.1 z.2), Fintype.sum_prod_type]
    simp only [freeJointProbability, 
      sum_constraintJointProbability, ENNReal.ofReal_one])

@[simp] theorem freeJointLaw_apply (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (β : ℝ) (hβ : 0 < β) (σ : SpinConfiguration q V)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    freeJointLaw q hq V β hβ (σ, ω) = ENNReal.ofReal (freeJointProbability q V β σ ω) := rfl

theorem pottsProb_free_event_eq_clusterMixture (q : ℕ) (hq : 2 ≤ q)
    (V : Finset (ℤ × ℤ)) (β : ℝ) (hβ : 0 < β) (s : Set (SpinConfiguration q V)) :
    (∑ σ : SpinConfiguration q V, if σ ∈ s then pottsProb q V β 0 σ else 0) =
      ∑ ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool,
        rcProb V (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 0 ω *
          ∑ σ : SpinConfiguration q V,
            if σ ∈ s then clusterColoringProbability (rcOpenGraph V ω).reachableSetoid σ else 0 := by
  simpa only [freeGibbsProbability_eq_pottsProb, freeConfigurationProbability_eq_rcProb,
    FK.rcOpenGraph_eq] using
    graphGibbsProbability_event_eq_clusterMixture
      (squareLattice.induce (V : Set (ℤ × ℤ))) q hq β hβ s

/-- Exact free cylinder formula: the integrand depends only on the connection
partition of the observed vertices. -/
theorem pottsProb_free_cylinder (q : ℕ) (hq : 2 ≤ q)
    (V : Finset (ℤ × ℤ)) (β : ℝ) (hβ : 0 < β)
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q V, if ∀ a, σ (v a) = ξ a then pottsProb q V β 0 σ else 0) =
      ∑ ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool,
        rcProb V (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 0 ω *
          clusterCylinderProbability (rcOpenGraph V ω).reachableSetoid v ξ := by
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have h := pottsProb_free_event_eq_clusterMixture q hq V β hβ {σ | ∀ a, σ (v a) = ξ a}
  simpa only [Set.mem_ofPred_eq, clusterColoringProbability_cylinder] using h

end

end PottsDiscontinuity.Potts
