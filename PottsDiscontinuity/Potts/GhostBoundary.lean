module

public import PottsDiscontinuity.Potts.LiteralBoundary
public import PottsDiscontinuity.Potts.GraphCoupling

/-!
# The literal boundary model as a pinned ghost colouring

The vertex `none` is the ghost. Interior edges are the open induced lattice
edges; there is exactly one possible edge from each boundary vertex to `none`.
The ghost component has its prescribed colour, so the number of compatible
spin configurations is `q ^ (k - 1)`, including when the ghost is isolated.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

local instance ghostLiteralBondDecidableEq (V : Finset (ℤ × ℤ)) : DecidableEq (LiteralBond V) :=
  fun _ _ => Classical.propDecidable _

local instance ghostBoundaryVertexFintype (V : Finset (ℤ × ℤ)) : Fintype (BoundaryVertex V) :=
  Fintype.ofFinite _

/-- The actual open graph, with one extra vertex for the boundary colour. -/
def ghostOpenGraph (V : Finset (ℤ × ℤ)) (ω : LiteralBond V → Bool) :
    SimpleGraph (Option ↥(V : Set (ℤ × ℤ))) where
  Adj
    | none, none => False
    | some x, some y =>
        (FK.openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
          (FK.boolConfigurationEquiv _ (fun e => ω (.inl e)))).Adj x y
    | some x, none => ∃ hx : x.val ∈ vertexBoundary V, ω (.inr ⟨x, hx⟩) = true
    | none, some x => ∃ hx : x.val ∈ vertexBoundary V, ω (.inr ⟨x, hx⟩) = true
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro x h
    cases x
    · exact h
    · exact SimpleGraph.irrefl _ h

/-- The positive boundary index as an allowed Potts colour. -/
def boundaryColor (q : ℕ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) : Set.Icc 1 q :=
  ⟨i, hi, by have := i.isLt; omega⟩

/-- Extend spins by fixing the ghost colour. -/
def ghostExtension {q : ℕ} {V : Finset (ℤ × ℤ)} (c : Set.Icc 1 q)
    (σ : SpinConfiguration q V) : Option ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q
  | none => c
  | some x => σ x

theorem literalAgreement_iff_ghost (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (σ : SpinConfiguration q V) (ω : LiteralBond V → Bool) :
    (∀ e, ω e = true → literalAgreement q V i σ e) ↔
      (ghostOpenGraph V ω).reachableSetoid ≤
        Setoid.ker (ghostExtension (boundaryColor q i hi) σ) := by
  constructor
  · intro h
    have hI := (bool_edgeAgreement_iff (squareLattice.induce (V : Set (ℤ × ℤ)))
      σ (fun e => ω (.inl e))).mp (fun e he => h (.inl e) he)
    apply FK.reachableSetoid_le_of_adj
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y =>
        obtain ⟨hy, he⟩ := hxy
        apply Subtype.ext
        exact (h (.inr ⟨y, hy⟩) he).symm
    | some x =>
      cases y with
      | none =>
        obtain ⟨hx, he⟩ := hxy
        apply Subtype.ext
        exact h (.inr ⟨x, hx⟩) he
      | some y =>
        exact hI (show (FK.openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
          (FK.boolConfigurationEquiv _ (fun e => ω (.inl e)))).Adj x y from hxy).reachable
  · intro h
    have hI : (FK.openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
        (FK.boolConfigurationEquiv _ (fun e => ω (.inl e)))).reachableSetoid ≤
          Setoid.ker σ := by
      apply FK.reachableSetoid_le_of_adj
      intro x y hxy
      exact h (show (ghostOpenGraph V ω).Adj (some x) (some y) from hxy).reachable
    intro e he
    cases e with
    | inl e => exact (bool_edgeAgreement_iff _ σ (fun e => ω (.inl e))).mpr hI e he
    | inr x =>
      have ha : (ghostOpenGraph V ω).Adj (some x.val) none := ⟨x.property, he⟩
      exact congrArg Subtype.val (h ha.reachable)

/-- Compatible literal spins are exactly ghost-pinned component colourings. -/
def literalColoringEquiv (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool) :
    {σ : SpinConfiguration q V // ∀ e, ω e = true → literalAgreement q V i σ e} ≃
      PinnedClusterColoring (ghostOpenGraph V ω).reachableSetoid none (boundaryColor q i hi) where
  toFun σ := ⟨⟨ghostExtension (boundaryColor q i hi) σ.val,
    (literalAgreement_iff_ghost q V i hi σ.val ω).mp σ.property⟩, rfl⟩
  invFun τ := ⟨fun x => τ.val.val (some x), by
    apply (literalAgreement_iff_ghost q V i hi _ ω).mpr
    have he : ghostExtension (boundaryColor q i hi) (fun x => τ.val.val (some x)) =
        τ.val.val := by
      funext x
      cases x with
      | none => exact τ.property.symm
      | some x => rfl
    rw [he]
    exact τ.val.property⟩
  left_inv σ := rfl
  right_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    cases x with
    | none => exact τ.property.symm
    | some x => rfl

/-- The ghost class is the only class whose colour is fixed. -/
theorem card_literalAgreement (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool) :
    Nat.card {σ : SpinConfiguration q V // ∀ e, ω e = true → literalAgreement q V i σ e} =
      q ^ (Nat.card (Quotient (ghostOpenGraph V ω).reachableSetoid) - 1) := by
  rw [Nat.card_congr (literalColoringEquiv q V i hi ω), card_pinnedClusterColoring,
    card_pottsColors]

/-- Number of open components, counting the ghost component. -/
def ghostComponentCount (V : Finset (ℤ × ℤ)) (ω : LiteralBond V → Bool) : ℕ :=
  Nat.card (Quotient (ghostOpenGraph V ω).reachableSetoid)

theorem ghostComponentCount_pos (V : Finset (ℤ × ℤ)) (ω : LiteralBond V → Bool) :
    0 < ghostComponentCount V ω := Nat.card_pos

/-- Random-cluster weight with the ghost component's common factor removed. -/
def ghostRCWeight (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (ω : LiteralBond V → Bool) : ℝ :=
  bernoulliBondWeight β ω * (q : ℝ) ^ (ghostComponentCount V ω - 1)

def ghostRCPartition (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ) : ℝ :=
  ∑ ω : LiteralBond V → Bool, ghostRCWeight q V β ω

/-- The ghost random-cluster probability, independent of the pinned colour. -/
def ghostRCProbability (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (ω : LiteralBond V → Bool) : ℝ :=
  ghostRCWeight q V β ω / ghostRCPartition q V β

/-- Multiplication by the constant `q` restores the usual RC weight `q^k`. -/
theorem ghostRCWeight_mul_q (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (ω : LiteralBond V → Bool) :
    ghostRCWeight q V β ω * q =
      bernoulliBondWeight β ω * (q : ℝ) ^ ghostComponentCount V ω := by
  rw [ghostRCWeight, mul_assoc, ← pow_succ,
    Nat.sub_add_cancel (ghostComponentCount_pos V ω)]

theorem sum_literalJointWeight_spins (q : ℕ) (V : Finset (ℤ × ℤ))
    (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool) :
    (∑ σ : SpinConfiguration q V, constraintJointWeight β (literalAgreement q V i) σ ω) =
      ghostRCWeight q V β ω := by
  rw [sum_constraintJointWeight_spins, card_literalAgreement q V i hi, Nat.cast_pow]
  rfl

theorem literalJointPartition_eq_ghost (q : ℕ) (V : Finset (ℤ × ℤ))
    (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    constraintJointPartition β (literalAgreement q V i) = ghostRCPartition q V β := by
  unfold constraintJointPartition ghostRCPartition
  rw [Finset.sum_comm]
  simp only [sum_literalJointWeight_spins q V β i hi]

/-- The bond marginal of the literal joint law is the ghost RC law. -/
theorem literalJointProbability_bond_marginal (q : ℕ) (V : Finset (ℤ × ℤ))
    (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool) :
    (∑ σ : SpinConfiguration q V, literalJointProbability q V β i σ ω) =
      ghostRCProbability q V β ω := by
  simp only [literalJointProbability, constraintJointProbability, ← Finset.sum_div,
    sum_literalJointWeight_spins q V β i hi, literalJointPartition_eq_ghost q V β i hi,
    ghostRCProbability]

theorem ghostRCPartition_pos (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ) :
    0 < ghostRCPartition q V β := by
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  let i : Fin (q + 1) := ⟨1, by omega⟩
  rw [← literalJointPartition_eq_ghost q V β i (by exact le_rfl)]
  exact constraintJointPartition_pos β _

theorem ghostRCProbability_nonneg (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (β : ℝ) (hβ : 0 < β) (ω : LiteralBond V → Bool) :
    0 ≤ ghostRCProbability q V β ω := by
  apply div_nonneg _ (ghostRCPartition_pos q hq V β).le
  apply mul_nonneg _ (by positivity)
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact (bondProbability_pos hβ).le
  · exact (Real.exp_pos _).le

theorem sum_ghostRCProbability (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ) :
    ∑ ω : LiteralBond V → Bool, ghostRCProbability q V β ω = 1 := by
  simp only [ghostRCProbability, ← Finset.sum_div]
  exact div_self (ghostRCPartition_pos q hq V β).ne'

/-- A probability mass function for the actual ghost random-cluster law. -/
def ghostRCLaw (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ) (hβ : 0 < β) :
    PMF (LiteralBond V → Bool) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (ghostRCProbability q V β ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => ghostRCProbability_nonneg q hq V β hβ ω),
      sum_ghostRCProbability q hq, ENNReal.ofReal_one])

@[simp] theorem ghostRCLaw_apply (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (β : ℝ) (hβ : 0 < β) (ω : LiteralBond V → Bool) :
    ghostRCLaw q hq V β hβ ω = ENNReal.ofReal (ghostRCProbability q V β ω) := rfl

/-- Uniform colour mass on all components except the pinned ghost component. -/
def ghostColoringProbability (q : ℕ) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool)
    (σ : SpinConfiguration q V) : ℝ :=
  if (ghostOpenGraph V ω).reachableSetoid ≤
      Setoid.ker (ghostExtension (boundaryColor q i hi) σ)
  then ((q : ℝ) ^ (ghostComponentCount V ω - 1))⁻¹ else 0

/-- Exact ghost Edwards–Sokal disintegration for the literal boundary law. -/
theorem literalJointProbability_eq_ghost_mul_coloring (q : ℕ) (hq : 2 ≤ q)
    (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (σ : SpinConfiguration q V) (ω : LiteralBond V → Bool) :
    literalJointProbability q V β i σ ω =
      ghostRCProbability q V β ω * ghostColoringProbability q V i hi ω σ := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [literalJointProbability, constraintJointProbability, constraintJointWeight_eq,
    literalJointPartition_eq_ghost q V β i hi, ghostRCProbability, ghostRCWeight,
    ghostColoringProbability]
  simp only [literalAgreement_iff_ghost q V i hi]
  split_ifs
  · simp only [mul_one]
    field_simp
  · simp

/-- The frozen Potts probability is the ghost RC mixture of pinned cluster colours. -/
theorem pottsProb_eq_ghostMixture (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (σ : SpinConfiguration q V) :
    pottsProb q V β i σ =
      ∑ ω : LiteralBond V → Bool,
        ghostRCProbability q V β ω * ghostColoringProbability q V i hi ω σ := by
  rw [← literalJointProbability_spin_marginal q hq V β i σ]
  apply Finset.sum_congr rfl
  intro ω _
  exact literalJointProbability_eq_ghost_mul_coloring q hq V β i hi σ ω

/-- Every spin event, including each prescribed finite cylinder, has the ghost
cluster-colouring mixture formula for the exact frozen Hamiltonian. -/
theorem pottsProb_event_eq_ghostMixture (q : ℕ) (hq : 2 ≤ q)
    (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (s : Set (SpinConfiguration q V)) :
    (∑ σ : SpinConfiguration q V, if σ ∈ s then pottsProb q V β i σ else 0) =
      ∑ ω : LiteralBond V → Bool, ghostRCProbability q V β ω *
        ∑ σ : SpinConfiguration q V,
          if σ ∈ s then ghostColoringProbability q V i hi ω σ else 0 := by
  simp_rw [pottsProb_eq_ghostMixture q hq V β i hi]
  calc
    _ = ∑ σ : SpinConfiguration q V, ∑ ω : LiteralBond V → Bool,
        ghostRCProbability q V β ω *
          (if σ ∈ s then ghostColoringProbability q V i hi ω σ else 0) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hs : σ ∈ s <;> simp only [hs, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

@[simp] theorem literalJointLaw_apply (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1))
    (σ : SpinConfiguration q V) (ω : LiteralBond V → Bool) :
    literalJointLaw q hq V β hβ i (σ, ω) =
      ENNReal.ofReal (literalJointProbability q V β i σ ω) := rfl

end

end PottsDiscontinuity.Potts
