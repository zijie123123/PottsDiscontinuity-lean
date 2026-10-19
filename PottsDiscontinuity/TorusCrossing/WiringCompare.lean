module

public import PottsDiscontinuity.FK.IncreasingEvents

/-!
# Comparing two wirings that differ by one identification

If a boundary condition `η` is obtained from `ξ` by wiring one more pair `(b₀, t₀)` of classes
together, then the number of clusters changes by at most one, and not at all on the event that
`b₀` and `t₀` are already connected.  Consequently the two FK measures are comparable on
increasing events whose configurations already connect `b₀` to `t₀`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

section Count

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The coarsening of a setoid obtained by wiring the classes of `b₀` and `t₀`. -/
def wireSetoid (s : Setoid V) (b₀ t₀ : V) : Setoid V where
  r x y := s.r x y ∨ ((s.r x b₀ ∨ s.r x t₀) ∧ (s.r y b₀ ∨ s.r y t₀))
  iseqv :=
    { refl := fun x => Or.inl (s.refl x)
      symm := by
        rintro x y (h | h)
        · exact Or.inl (s.symm h)
        · exact Or.inr ⟨h.2, h.1⟩
      trans := by
        rintro x y z (h | h) (h' | h')
        · exact Or.inl (s.trans h h')
        · refine Or.inr ⟨?_, h'.2⟩
          rcases h'.1 with h1 | h1
          · exact Or.inl (s.trans h h1)
          · exact Or.inr (s.trans h h1)
        · refine Or.inr ⟨h.1, ?_⟩
          rcases h.2 with h1 | h1
          · exact Or.inl (s.trans (s.symm h') h1)
          · exact Or.inr (s.trans (s.symm h') h1)
        · exact Or.inr ⟨h.1, h'.2⟩ }

/-- Adding one identification changes the number of classes by at most one. -/
theorem card_quotient_le_wire (s t : Setoid V) (b₀ t₀ : V) (hst : s ≤ t)
    (hbt : t ≤ wireSetoid s b₀ t₀) :
    Nat.card (Quotient s) ≤ Nat.card (Quotient t) + 1 := by
  let F : Quotient s → Quotient t := Quotient.map' id (fun x y h => hst h)
  let S' : Set (Quotient s) := {q | q ≠ Quotient.mk s t₀}
  have hinj : Function.Injective (fun q : S' => F q.1) := by
    rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q₁
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q₂
    apply Subtype.ext
    simp only
    have hxy : t.r x y := Quotient.exact h
    rcases hbt hxy with h3 | ⟨hx, hy⟩
    · exact Quotient.sound h3
    · have hx' : s.r x b₀ := by
        rcases hx with h4 | h4
        · exact h4
        · exact absurd (Quotient.sound h4) h₁
      have hy' : s.r y b₀ := by
        rcases hy with h4 | h4
        · exact h4
        · exact absurd (Quotient.sound h4) h₂
      exact Quotient.sound (s.trans hx' (s.symm hy'))
  have h1 : Nat.card S' ≤ Nat.card (Quotient t) := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (Quotient s) ≤ Nat.card S' + 1 := by
    have : Finite (Quotient s) := Quotient.finite s
    have hc : Nat.card S' + Nat.card ({q : Quotient s | q = Quotient.mk s t₀} : Set _) =
        Nat.card (Quotient s) := by
      have := Nat.card_congr (Equiv.Set.sumCompl ({q : Quotient s | q = Quotient.mk s t₀} : Set _))
      rw [Nat.card_sum] at this
      have e : ({q : Quotient s | q = Quotient.mk s t₀} : Set _)ᶜ = S' := by
        ext q; simp [S']
      rw [e] at this
      omega
    have : Nat.card ({q : Quotient s | q = Quotient.mk s t₀} : Set _) = 1 := by
      simp
    omega
  omega

end Count

section Weights

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable local instance wcEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
noncomputable local instance wcEdgeDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Hypothesis: `η` is obtained from `ξ` by additionally wiring the classes of `b₀` and `t₀`. -/
def IsWireStep (ξ η : FK.BoundaryCondition V) (b₀ t₀ : V) : Prop :=
  ξ.partition ≤ η.partition ∧
    ∀ x y, η.partition.r x y → ξ.partition.r x y ∨
      ((ξ.partition.r x b₀ ∨ ξ.partition.r x t₀) ∧ (ξ.partition.r y b₀ ∨ ξ.partition.r y t₀))

omit [Finite V] in
theorem setoid_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentSetoid G η A ≤ wireSetoid (FK.componentSetoid G ξ A) b₀ t₀ := by
  apply FK.componentSetoid_le
  · intro u v huv
    exact Or.inl (FK.actualConnected_component G ξ A huv)
  · intro x y hxy
    rcases h.2 x y hxy with h1 | ⟨hx, hy⟩
    · exact Or.inl (FK.boundary_component G ξ A h1)
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hx with h3 | h3
        · exact Or.inl (FK.boundary_component G ξ A h3)
        · exact Or.inr (FK.boundary_component G ξ A h3)
      · rcases hy with h3 | h3
        · exact Or.inl (FK.boundary_component G ξ A h3)
        · exact Or.inr (FK.boundary_component G ξ A h3)

theorem count_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentCount G ξ A ≤ FK.componentCount G η A + 1 := by
  unfold FK.componentCount
  exact card_quotient_le_wire _ _ b₀ t₀
    (FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _))
    (setoid_le_wire h A)

theorem count_eq_of_connected {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (A : FK.Configuration G)
    (hc : (FK.componentSetoid G ξ A).r b₀ t₀) :
    FK.componentCount G η A = FK.componentCount G ξ A := by
  have hle := FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _)
  have hge : FK.componentSetoid G η A ≤ FK.componentSetoid G ξ A := by
    intro x y hxy
    rcases setoid_le_wire h A hxy with h3 | ⟨hx, hy⟩
    · exact h3
    · have hx' : (FK.componentSetoid G ξ A).r x b₀ := by
        rcases hx with h4 | h4
        · exact h4
        · exact (FK.componentSetoid G ξ A).trans h4 ((FK.componentSetoid G ξ A).symm hc)
      have hy' : (FK.componentSetoid G ξ A).r y b₀ := by
        rcases hy with h4 | h4
        · exact h4
        · exact (FK.componentSetoid G ξ A).trans h4 ((FK.componentSetoid G ξ A).symm hc)
      exact (FK.componentSetoid G ξ A).trans hx' ((FK.componentSetoid G ξ A).symm hy')
  have : FK.componentSetoid G η A = FK.componentSetoid G ξ A := le_antisymm hge hle
  unfold FK.componentCount
  rw [this]

/-- On an event on which `b₀` and `t₀` are connected, the measure with the extra wiring is at most
`q` times the measure without it. -/
theorem measure_wire_le (q : FK.Parameters) {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (S : Set (FK.Configuration G))
    (hS : ∀ A ∈ S, (FK.componentSetoid G ξ A).r b₀ t₀) :
    (FK.measure G q η S).toReal ≤ q.val * (FK.measure G q ξ S).toReal := by
  have hq : 0 < q.val := FK.clusterWeight_pos q
  -- pointwise weight comparison
  have hw : ∀ A, FK.weight G q ξ A ≤ q.val * FK.weight G q η A := by
    intro A
    unfold FK.weight
    have := count_le_wire (G := G) h A
    have h1 : q.val ^ FK.componentCount G ξ A ≤ q.val ^ (FK.componentCount G η A + 1) :=
      pow_le_pow_right₀ q.property this
    rw [pow_succ] at h1
    have hp1 : 0 ≤ FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) :=
      mul_nonneg (pow_nonneg (FK.edgeParameter_pos q).le _) (pow_nonneg (FK.one_sub_edgeParameter_pos q).le _)
    calc FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) *
          q.val ^ FK.componentCount G ξ A
        ≤ FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) *
          (q.val ^ FK.componentCount G η A * q.val) := mul_le_mul_of_nonneg_left h1 hp1
      _ = q.val * (FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) *
          q.val ^ FK.componentCount G η A) := by ring
  have hZ : FK.partitionFunction G q ξ ≤ q.val * FK.partitionFunction G q η := by
    unfold FK.partitionFunction FK.FiniteProbability.partition
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun A _ => hw A)
  have heq : ∀ A ∈ S, FK.weight G q η A = FK.weight G q ξ A := by
    intro A hA
    unfold FK.weight
    rw [count_eq_of_connected h A (hS A hA)]
  rw [FK.measure_toReal_eq_indicator_sum, FK.measure_toReal_eq_indicator_sum]
  have hZp := FK.partitionFunction_pos G q ξ
  have hZq := FK.partitionFunction_pos G q η
  have key : ∀ A, FK.configurationProbability G q η A * S.indicator (fun _ => (1 : ℝ)) A =
      (FK.partitionFunction G q ξ / FK.partitionFunction G q η) *
        (FK.configurationProbability G q ξ A * S.indicator (fun _ => (1 : ℝ)) A) := by
    intro A
    by_cases hA : A ∈ S
    · simp only [Set.indicator, hA, ite_true, mul_one]
      unfold FK.configurationProbability
      rw [heq A hA]
      field_simp
    · simp [Set.indicator, hA]
  simp_rw [key]
  rw [← Finset.mul_sum]
  have hsum : 0 ≤ ∑ A, FK.configurationProbability G q ξ A * S.indicator (fun _ => (1 : ℝ)) A :=
    Finset.sum_nonneg (fun A _ => mul_nonneg (FK.configurationProbability_pos G q ξ A).le
      (Set.indicator_nonneg (fun _ _ => zero_le_one) A))
  calc FK.partitionFunction G q ξ / FK.partitionFunction G q η *
        ∑ A, FK.configurationProbability G q ξ A * S.indicator (fun _ => (1 : ℝ)) A
      ≤ q.val * ∑ A, FK.configurationProbability G q ξ A * S.indicator (fun _ => (1 : ℝ)) A := by
        apply mul_le_mul_of_nonneg_right _ hsum
        rw [div_le_iff₀ hZq]
        exact hZ
    _ = _ := rfl

end Weights

end PottsDiscontinuity.TorusCrossing
