/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.WiredPotentialSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped Matrix

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A : Configuration G)

/-- The genuine finite index set of open edges, retaining every selected unordered edge. -/
abbrev OpenEdgeIndex := {e : G.edgeSet // e ∈ A}

/-- An orientation is chosen for each actual open edge; its unordered endpoints
are required to be the edge itself. -/
structure SignedFlowOrientation where
  source : OpenEdgeIndex G A → V
  target : OpenEdgeIndex G A → V
  endpoints : ∀ e, s(source e, target e) = e.1.1

local instance openEdgeIndexFintype : Fintype (OpenEdgeIndex G A) := Fintype.ofFinite _
local instance openEdgeIndexDecidableEq : DecidableEq (OpenEdgeIndex G A) := Classical.decEq _

/-- Signed vertex-edge incidence matrix: +1 at the source and −1 at the target. -/
def signedIncidenceMatrix (o : SignedFlowOrientation G A) :
    Matrix (OpenEdgeIndex G A) V ℝ := fun e v =>
  if v = o.source e then 1 else if v = o.target e then -1 else 0

/-- The signed gradient is the genuine incidence map from vertex potentials to edge differences. -/
def signedGradient (o : SignedFlowOrientation G A) :
    (V → ℝ) →ₗ[ℝ] (OpenEdgeIndex G A → ℝ) :=
  Matrix.mulVecLin (signedIncidenceMatrix G A o)

/-- The signed divergence is the transpose incidence map, with outflow minus inflow. -/
def signedDivergence (o : SignedFlowOrientation G A) :
    (OpenEdgeIndex G A → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Matrix.mulVecLin ((signedIncidenceMatrix G A o)ᵀ)

omit [Fintype V] [DecidableEq V] in
lemma signedFlow_source_ne_target (o : SignedFlowOrientation G A) (e : OpenEdgeIndex G A) :
    o.source e ≠ o.target e := by
  have hdiag : ¬ (e.1.1).IsDiag := G.not_isDiag_of_mem_edgeSet e.1.2
  have hnot : ¬ (s(o.source e, o.target e)).IsDiag := by simpa [o.endpoints e] using hdiag
  intro heq
  exact hnot ((Sym2.mk_isDiag_iff).2 heq)

theorem signedGradient_apply (o : SignedFlowOrientation G A)
    (f : V → ℝ) (e : OpenEdgeIndex G A) :
    signedGradient G A o f e = f (o.source e) - f (o.target e) := by
  change (∑ v : V, signedIncidenceMatrix G A o e v * f v) = _
  calc
    _ = ∑ v : V, ((if v = o.source e then f v else 0) +
          (if v = o.target e then -f v else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [signedIncidenceMatrix]
      by_cases hs : v = o.source e
      · subst v
        simp [signedFlow_source_ne_target G A o e]
      · by_cases ht : v = o.target e
        · subst v
          simp [hs]
        · simp [hs, ht]
    _ = f (o.source e) - f (o.target e) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq']
      ring

theorem signedDivergence_apply (o : SignedFlowOrientation G A)
    (F : OpenEdgeIndex G A → ℝ) (v : V) :
    signedDivergence G A o F v =
      (∑ e : OpenEdgeIndex G A, if o.source e = v then F e else 0) -
      (∑ e : OpenEdgeIndex G A, if o.target e = v then F e else 0) := by
  change (∑ e : OpenEdgeIndex G A,
    (signedIncidenceMatrix G A o e v) * F e) = _
  have hterm (e : OpenEdgeIndex G A) :
      (signedIncidenceMatrix G A o e v) * F e =
        (if o.source e = v then F e else 0) +
          (if o.target e = v then -F e else 0) := by
    simp only [signedIncidenceMatrix]
    by_cases hs : v = o.source e
    · subst v
      have hne := signedFlow_source_ne_target G A o e
      simp [hne.symm]
    · by_cases ht : v = o.target e
      · subst v
        have hne := signedFlow_source_ne_target G A o e
        simp [hs, hne]
      · simp [hs, ht, eq_comm]
  calc
    _ = ∑ e : OpenEdgeIndex G A,
        ((if o.source e = v then F e else 0) +
          (if o.target e = v then -F e else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact hterm e
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have hneg : (∑ e : OpenEdgeIndex G A,
          if o.target e = v then -F e else 0) =
          -(∑ e : OpenEdgeIndex G A, if o.target e = v then F e else 0) := by
        rw [← Finset.sum_neg_distrib]
        congr 1
        funext e
        by_cases he : o.target e = v <;> simp [he]
      rw [hneg]
      ring

theorem signedGradient_mem_ker_iff (o : SignedFlowOrientation G A) (f : V → ℝ) :
    f ∈ LinearMap.ker (signedGradient G A o) ↔
      ∀ e : OpenEdgeIndex G A, f (o.source e) = f (o.target e) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h e
    have he := congrFun h e
    have he' : f (o.source e) - f (o.target e) = 0 := by
      simpa [signedGradient_apply] using he
    linarith
  · intro h
    funext e
    simp [signedGradient_apply, h e]

theorem signedGradient_ker_eq_componentConstantFunctions
    (o : SignedFlowOrientation G A) :
    LinearMap.ker (signedGradient G A o) =
      componentConstantFunctions G (BoundaryCondition.free (∅ : Set V)) A := by
  ext f
  rw [signedGradient_mem_ker_iff G A o f, componentConstant_iff_local]
  constructor
  · intro h
    constructor
    · intro u v hadj
      have hmem : s(u, v) ∈ openEdges G A := (openGraph_adj G A u v).mp hadj
      rcases hmem with ⟨edge, hedgeA, hval⟩
      have hedgeA' : edge ∈ A := by simpa using hedgeA
      let e : OpenEdgeIndex G A := ⟨edge, hedgeA'⟩
      have hpair : s(u, v) = s(o.source e, o.target e) := by
        rw [o.endpoints e]
        exact hval.symm
      rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · subst u
        subst v
        exact h e
      · subst u
        subst v
        exact (h e).symm
    · intro u v hboundary
      exact congrArg f ((BoundaryCondition.free_rel (∅ : Set V) u v).mp hboundary)
  · rintro ⟨hopen, hboundary⟩ e
    have hadj : (openGraph G A).Adj (o.source e) (o.target e) :=
      (openGraph_adj G A _ _).2 ⟨e.1, by simp, (o.endpoints e).symm⟩
    exact hopen hadj

omit [DecidableEq V] in
theorem openEdgeIndex_card : Fintype.card (OpenEdgeIndex G A) = A.card := by
  classical
  simp [OpenEdgeIndex]

private theorem finrank_range_signedGradient (o : SignedFlowOrientation G A) :
    Module.finrank ℝ (LinearMap.range (signedGradient G A o)) =
      (signedIncidenceMatrix G A o).rank := by
  let bV : Module.Basis V ℝ (V → ℝ) := Pi.basisFun ℝ V
  let bE : Module.Basis (OpenEdgeIndex G A) ℝ (OpenEdgeIndex G A → ℝ) :=
    Pi.basisFun ℝ (OpenEdgeIndex G A)
  have h := Matrix.rank_eq_finrank_range_toLin (signedIncidenceMatrix G A o) bE bV
  have hmap : Matrix.toLin bV bE (signedIncidenceMatrix G A o) = signedGradient G A o := by
    simp [signedGradient, bV, bE, Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  rw [← hmap]
  exact h.symm

private theorem finrank_range_signedDivergence (o : SignedFlowOrientation G A) :
    Module.finrank ℝ (LinearMap.range (signedDivergence G A o)) =
      (signedIncidenceMatrix G A o).rank := by
  let bV : Module.Basis V ℝ (V → ℝ) := Pi.basisFun ℝ V
  let bE : Module.Basis (OpenEdgeIndex G A) ℝ (OpenEdgeIndex G A → ℝ) :=
    Pi.basisFun ℝ (OpenEdgeIndex G A)
  have h := Matrix.rank_eq_finrank_range_toLin
    ((signedIncidenceMatrix G A o)ᵀ) bV bE
  have hmap : Matrix.toLin bE bV ((signedIncidenceMatrix G A o)ᵀ) =
      signedDivergence G A o := by
    simp [signedDivergence, bV, bE, Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  calc
    Module.finrank ℝ (LinearMap.range (signedDivergence G A o)) =
        ((signedIncidenceMatrix G A o)ᵀ).rank := by
      rw [← hmap]
      exact h.symm
    _ = (signedIncidenceMatrix G A o).rank := Matrix.rank_transpose _

theorem signedFlowDimension (o : SignedFlowOrientation G A) :
    Module.finrank ℝ (LinearMap.ker (signedDivergence G A o)) + Fintype.card V =
      A.card + componentCount G (BoundaryCondition.free (∅ : Set V)) A := by
  classical
  have hgrad := LinearMap.finrank_range_add_finrank_ker (signedGradient G A o)
  rw [signedGradient_ker_eq_componentConstantFunctions G A o,
    componentConstantFunctions_finrank, Module.finrank_fintype_fun_eq_card] at hgrad
  have hgradRank : (signedIncidenceMatrix G A o).rank +
      componentCount G (BoundaryCondition.free (∅ : Set V)) A = Fintype.card V := by
    rw [← finrank_range_signedGradient G A o]
    exact hgrad
  have hdiv := LinearMap.finrank_range_add_finrank_ker (signedDivergence G A o)
  rw [finrank_range_signedDivergence G A o, Module.finrank_fintype_fun_eq_card, openEdgeIndex_card] at hdiv
  omega

end
end PottsDiscontinuity.FK
