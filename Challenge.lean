module

public import Mathlib

/-!
# Theorems 1.1 and 1.2 of arXiv:1611.09877v2 — statement surface

H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu and V. Tassion,
*Discontinuity of the phase transition for the planar random-cluster and Potts models
with q > 4*, arXiv:1611.09877v2.

This module states the three main results and every non-Mathlib definition their statements
use. It imports only Mathlib. The proofs are deliberately `sorry`; `Solution.lean` provides
the proved declarations, and Comparator checks that the names, types and definitions agree.

Definitions, in dependency order: the square lattice `ℤ²`; boxes `Λₙ = [-n, n]²` and their
vertex boundary; the finite-volume random-cluster model (open subgraph, free and wired
cluster counts, weight, probability) and its infinite-volume limits along boxes; the
finite-volume Potts model (Hamiltonian, Gibbs probability) and its infinite-volume limits;
translation ergodicity; the critical parameters `p_c(q) = √q / (1 + √q)` and
`β_c(q) = log(1 + √q)`; the open graph of an infinite-volume configuration; and the diagonal
site `xₙ = (⌊n/2⌋, ⌊n/2⌋)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The box `Λₙ = [-n, n]² ∩ ℤ²`. -/
def box (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `xₙ`: the site of `ℤ²` with both coordinates equal to `⌊n/2⌋`. -/
def diagonalSite (n : ℕ) : ℤ × ℤ :=
  (((n / 2 : ℕ) : ℤ), ((n / 2 : ℕ) : ℤ))

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- The square lattice `ℤ²`: vertices `x = (x₁, x₂)`, edges between nearest neighbours. -/
def squareLattice : SimpleGraph (ℤ × ℤ) where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by rwa [abs_sub_comm y.1, abs_sub_comm y.2]⟩
  loopless := ⟨fun x h => by simp at h⟩

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `∂V`: the vertices of `V` having at least one neighbour in `ℤ²` outside of `V`. -/
def vertexBoundary (V : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {x | x ∈ V ∧ ∃ y, squareLattice.Adj x y ∧ y ∉ V}

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- The Potts Hamiltonian `Hⁱ_G(σ) = -∑_{{x,y} ∈ E} 1[σₓ = σ_y] - ∑_{x ∈ ∂V} 1[σₓ = i]`
on the subgraph induced by `V`, spins in `{1, …, q}`, boundary condition `i ∈ {0, …, q}`. -/
noncomputable def pottsHamiltonian (q : ℕ) (V : Finset (ℤ × ℤ)) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  -(∑ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      if ∀ x ∈ e.1, ∀ y ∈ e.1, σ x = σ y then (1 : ℝ) else 0) -
    ∑ x : ↥(V : Set (ℤ × ℤ)),
      if x.1 ∈ vertexBoundary V ∧ (σ x : ℕ) = (i : ℕ) then (1 : ℝ) else 0

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- The finite-volume Potts measure `μⁱ_{G,β}[σ] = exp(-β Hⁱ_G(σ)) / ∑_{σ'} exp(-β Hⁱ_G(σ'))`. -/
noncomputable def pottsProb (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  Real.exp (-β * pottsHamiltonian q V i σ) /
    ∑ σ' : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q, Real.exp (-β * pottsHamiltonian q V i σ')

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- `μ` is the infinite-volume Potts Gibbs measure `μⁱ_β`: the probability measure on
`{1,…,q}^{ℤ²}` to which `μⁱ_{Λₙ,β}` converge, tested on all finite-dimensional cylinder events.
The finite volumes are the boxes `Λₙ` (author ruling R1); the Hamiltonian is the paper's literal
one, with one boundary term per vertex of `∂Λₙ`. -/
def IsPottsInfiniteVolumeLimit (q : ℕ) (β : ℝ) (i : Fin (q + 1))
    (μ : Measure (ℤ × ℤ → Set.Icc 1 q)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Set.Icc 1 q),
      Tendsto
        (fun n : ℕ =>
          ∑ σ : ↥(box n : Set (ℤ × ℤ)) → Set.Icc 1 q,
            if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x
            then pottsProb q (box n) β i σ else 0)
        atTop (𝓝 (μ.real {σ | ∀ x ∈ A, σ x = ξ x}))

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- The open subgraph of a percolation configuration `ω ∈ {0,1}^E` on the finite subgraph
`G = (V, E)` of `ℤ²` induced by `V` (vertex set `V`, open edges `{e ∈ E : ω(e) = 1}`). -/
def rcOpenGraph (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    SimpleGraph (V : Set (ℤ × ℤ)) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet, ω ⟨e, h⟩ = true}

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `k₀(ω)`: the number of clusters (connected components, isolated vertices included). -/
noncomputable def rcFreeClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card (rcOpenGraph V ω).ConnectedComponent

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- `k₁(ω)`: the number of clusters when all clusters intersecting `∂V` count as one. -/
noncomputable def rcWiredClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card {c : (rcOpenGraph V ω).ConnectedComponent //
      ∀ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c →
        x.1 ∉ vertexBoundary V} +
    if ∃ c : (rcOpenGraph V ω).ConnectedComponent,
        ∃ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c ∧
          x.1 ∈ vertexBoundary V then 1 else 0

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- The unnormalized weight `p^{o(ω)} (1-p)^{c(ω)} q^{kᵢ(ω)}`, `i ∈ {0, 1}`. -/
noncomputable def rcWeight (V : Finset (ℤ × ℤ)) (p q : ℝ) (i : Fin 2)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  p ^ Nat.card {e // ω e = true} * (1 - p) ^ Nat.card {e // ω e = false} *
    q ^ (if i = 0 then rcFreeClusterCount V ω else rcWiredClusterCount V ω)

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- The finite-volume random-cluster measure `φⁱ_{G,p,q}(ω) = weight / Zⁱ(G,p,q)`, for the
source parameter range `p ∈ [0, 1]`, `q > 0`. -/
noncomputable def rcProb (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  rcWeight V p q i ω / ∑ ω', rcWeight V p q i ω'

end PottsDiscontinuity

namespace PottsDiscontinuity

open Classical in
/-- `μ` is the infinite-volume random-cluster measure with boundary condition `i`: the
probability measure on `{0,1}^{E(ℤ²)}` to which `φⁱ_{Λₙ,p,q}` converge weakly, tested on all
finite-dimensional cylinder events. The finite volumes are the boxes `Λₙ` (author ruling R1). -/
def IsRCInfiniteVolumeLimit (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool),
      Tendsto
        (fun n : ℕ =>
          ∑ ω : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet → Bool,
            if ∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
                Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
            then rcProb (box n) p q i ω else 0)
        atTop (𝓝 (μ.real {ω | ∀ e ∈ A, ω e = ξ e}))

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `μ` is invariant under every translation of `ℤ²`, and every measurable event invariant under
all translations of `ℤ²` is null or conull (ergodicity with respect to the translations of `ℤ²`). -/
def IsTranslationErgodic {S : Type*} [MeasurableSpace S] (μ : Measure (ℤ × ℤ → S)) : Prop :=
  (∀ a : ℤ × ℤ, μ.map (fun σ x => σ (x + a)) = μ) ∧
    ∀ s : Set (ℤ × ℤ → S), MeasurableSet s →
      (∀ a : ℤ × ℤ, (fun σ x => σ (x + a)) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `β_c(q) = log(1 + √q)`: the value of the critical inverse temperature stated on p. 2
(identified in [3]); criticality itself is not asserted here. -/
noncomputable def pottsCriticalBeta (q : ℕ) : ℝ :=
  Real.log (1 + Real.sqrt q)

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- `p_c(q) = √q / (1 + √q)` for `q ≥ 1`, as an element of `[0, 1]`: the value of the critical
parameter stated on p. 4 (identified in [3]); criticality itself is not asserted here. -/
noncomputable def rcCriticalParameter (q : Set.Ici (1 : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt q / (1 + Real.sqrt q),
    div_nonneg (Real.sqrt_nonneg _) (by positivity),
    (div_le_one (by positivity)).2 (by linarith)⟩

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- The open subgraph of `ℤ²` of an infinite-volume configuration `ω ∈ {0,1}^{E(ℤ²)}`. -/
def rcInfiniteOpenGraph (ω : squareLattice.edgeSet → Bool) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ squareLattice.edgeSet, ω ⟨e, h⟩ = true}

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- **Theorem 1.2**, the final assertions: positivity of the right side of (1.2) and (1.3)
(arXiv:1611.09877v2, p. 4). Here `λ = arcosh(√q / 2)` is the `λ > 0` with `cosh λ = √q / 2`. -/
theorem rc_theorem_1_2_positivity_eq_1_3 :
    (∀ q : ℝ, 4 < q → ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∃ S T : ℝ,
        Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
        HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
        0 < lam + 2 * S ∧ lam + 2 * S = T) ∧
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) := by
  sorry

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- **Theorem 1.2**, items 1–3 including (1.2) (arXiv:1611.09877v2, p. 4). -/
theorem rc_theorem_1_2 (q : ℝ) (hq : 4 < q) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i
        (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S))) := by
  sorry

end PottsDiscontinuity

namespace PottsDiscontinuity

/-- **Theorem 1.1** (arXiv:1611.09877v2, p. 2). -/
theorem potts_theorem_1_1 (q : ℕ) (hq : 4 < q) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) := by
  sorry

end PottsDiscontinuity
