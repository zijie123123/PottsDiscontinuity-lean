module

public import Mathlib

/-!
# Counting cluster colourings

Colourings are functions constant on the classes of an explicit equivalence
relation. Isolated vertices are included. Pinning the class of a distinguished
vertex removes exactly one independent colour choice.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

variable {V C : Type*}

/-- Vertex colourings constant on every class of `R`. -/
abbrev ClusterColoring (R : Setoid V) (C : Type*) :=
  {σ : V → C // R ≤ Setoid.ker σ}

/-- Assigning one colour to each class is equivalent to a compatible colouring. -/
def clusterColoringEquiv (R : Setoid V) : ClusterColoring R C ≃ (Quotient R → C) :=
  Setoid.liftEquiv R

theorem card_clusterColoring [Finite V] (R : Setoid V) :
    Nat.card (ClusterColoring R C) = Nat.card C ^ Nat.card (Quotient R) := by
  rw [Nat.card_congr (clusterColoringEquiv R), Nat.card_fun]

/-- Colourings with the entire class of `g` fixed to `i`. -/
abbrev PinnedClusterColoring (R : Setoid V) (g : V) (i : C) :=
  {σ : ClusterColoring R C // σ.val g = i}

/-- Pinning a vertex is exactly pinning its quotient class. -/
def pinnedClusterColoringEquiv (R : Setoid V) (g : V) (i : C) :
    PinnedClusterColoring R g i ≃ {f : Quotient R → C // f (Quotient.mk R g) = i} :=
  (clusterColoringEquiv R).subtypeEquiv (fun _ => Iff.rfl)

theorem card_pinned_functions [Finite V] [Finite C] (g : V) (i : C) :
    Nat.card {f : V → C // f g = i} = Nat.card C ^ (Nat.card V - 1) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite C
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset C) g
      (Finset.mem_univ i)

theorem card_pinnedClusterColoring [Finite V] [Finite C]
    (R : Setoid V) (g : V) (i : C) :
    Nat.card (PinnedClusterColoring R g i) =
      Nat.card C ^ (Nat.card (Quotient R) - 1) := by
  rw [Nat.card_congr (pinnedClusterColoringEquiv R g i), card_pinned_functions]

/-- The exact probability of a vertex colouring under independent uniform class colours. -/
def clusterColoringProbability [Finite V] [Finite C] (R : Setoid V) (σ : V → C) : ℝ :=
  if R ≤ Setoid.ker σ then ((Nat.card C : ℝ) ^ Nat.card (Quotient R))⁻¹ else 0

theorem clusterColoringProbability_nonneg [Finite V] [Finite C]
    (R : Setoid V) (σ : V → C) : 0 ≤ clusterColoringProbability R σ := by
  unfold clusterColoringProbability
  split_ifs <;> positivity

theorem sum_clusterColoringProbability [Fintype V] [Fintype C] [Nonempty C]
    (R : Setoid V) : ∑ σ : V → C, clusterColoringProbability R σ = 1 := by
  classical
  have hc : (Nat.card C : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := C)).ne'
  have hn : (Nat.card (ClusterColoring R C) : ℝ) =
      (Nat.card C : ℝ) ^ Nat.card (Quotient R) := by
    exact_mod_cast card_clusterColoring (C := C) R
  unfold clusterColoringProbability
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [hn, mul_inv_cancel₀ (pow_ne_zero _ hc)]

/-- A genuine finite probability law for uniform independent cluster colours. -/
def clusterColoringLaw [Fintype V] [Fintype C] [Nonempty C] (R : Setoid V) : PMF (V → C) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (clusterColoringProbability R σ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => clusterColoringProbability_nonneg R σ),
      sum_clusterColoringProbability, ENNReal.ofReal_one])

@[simp] theorem clusterColoringLaw_apply [Fintype V] [Fintype C] [Nonempty C]
    (R : Setoid V) (σ : V → C) :
    clusterColoringLaw R σ = ENNReal.ofReal (clusterColoringProbability R σ) := rfl

end

end PottsDiscontinuity.Potts
