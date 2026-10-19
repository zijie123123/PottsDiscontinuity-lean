/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- A finite dual potential with the wired exterior normalized to zero. -/
abbrev RectangleExteriorPotential (a : LatticeVertex) (w h : ℕ) :=
  {φ : RectangleDualVertex a w h → ℝ //
    ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}

def rectangleExtendedPotential (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

@[simp] theorem rectangleExtendedPotential_of_mem (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h φ z = φ.1 ⟨z, hz⟩ := by
  simp [rectangleExtendedPotential, hz]

@[simp] theorem rectangleExtendedPotential_of_not_mem (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex)
    (hz : z ∉ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h φ z = 0 := by
  simp [rectangleExtendedPotential, hz]

/-- Primal curl of a dual potential: above-minus-below horizontally and
left-minus-right vertically. -/
def rectangleCurlFlow (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (b : LatticeBond) : ℝ :=
  match b.axis with
  | .horizontal => rectangleExtendedPotential a w h φ (b.faceBase true) -
      rectangleExtendedPotential a w h φ (b.faceBase false)
  | .vertical => rectangleExtendedPotential a w h φ (b.faceBase false) -
      rectangleExtendedPotential a w h φ (b.faceBase true)

/-- The four normalized bonds incident to a vertex, in right/left/up/down order. -/
def rectangleCurlIncidentCandidate (v : LatticeVertex) : Fin 4 → LatticeBond
  | 0 => ⟨v, .horizontal⟩
  | 1 => ⟨(v.1 - 1, v.2), .horizontal⟩
  | 2 => ⟨v, .vertical⟩
  | 3 => ⟨(v.1, v.2 - 1), .vertical⟩

def rectangleCurlCandidateInside (a : LatticeVertex) (w h : ℕ)
    (v : LatticeVertex) (i : Fin 4) : Prop :=
  (rectangleCurlIncidentCandidate v i).source ∈ latticeRectangle a w h ∧
    (rectangleCurlIncidentCandidate v i).target ∈ latticeRectangle a w h

private theorem rectangleCurlIncidentCandidate_injective (v : LatticeVertex) :
    Function.Injective (rectangleCurlIncidentCandidate v) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals solve
    | rfl
    | (simp [rectangleCurlIncidentCandidate, LatticeBond.mk.injEq] at hij)
    | (simp [rectangleCurlIncidentCandidate, LatticeBond.mk.injEq] at hij
       ; have hx := congrArg Prod.fst hij
       ; have hy := congrArg Prod.snd hij
       ; omega)

 theorem rectangleCurlIncidentBond_exists_unique (v : LatticeVertex)
    (b : LatticeBond) (h : b.source = v ∨ b.target = v) :
    ∃! i : Fin 4, rectangleCurlIncidentCandidate v i = b := by
  let v0 := v
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax
  · change (x,y) = v ∨ (x+1,y) = v at h
    rcases h with hs | ht
    · subst v
      refine ⟨0, rfl, ?_⟩
      intro i hi
      have h₀ : rectangleCurlIncidentCandidate v0 0 = ⟨(x,y), .horizontal⟩ := rfl
      exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₀.symm)
    · subst v
      refine ⟨1, ?_, ?_⟩
      · simp [rectangleCurlIncidentCandidate]
      · intro i hi
        have h₁ : rectangleCurlIncidentCandidate v0 1 = ⟨(x,y), .horizontal⟩ := by
          simp [rectangleCurlIncidentCandidate, v0]
        exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₁.symm)
  · change (x,y) = v ∨ (x,y+1) = v at h
    rcases h with hs | ht
    · subst v
      refine ⟨2, rfl, ?_⟩
      intro i hi
      have h₂ : rectangleCurlIncidentCandidate v0 2 = ⟨(x,y), .vertical⟩ := rfl
      exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₂.symm)
    · subst v
      refine ⟨3, ?_, ?_⟩
      · simp [rectangleCurlIncidentCandidate]
      · intro i hi
        have h₃ : rectangleCurlIncidentCandidate v0 3 = ⟨(x,y), .vertical⟩ := by
          simp [rectangleCurlIncidentCandidate, v0]
        exact rectangleCurlIncidentCandidate_injective v0 (hi.trans h₃.symm)

private theorem rectangleCurlCandidate_faces_boundary
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) (i : Fin 4)
    (hv : v ∈ latticeRectangle a w h)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false ∈ rectangleDualBoundary a w h ∧
      LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true ∈ rectangleDualBoundary a w h := by
  fin_cases i <;>
    simp [rectangleCurlCandidateInside, rectangleCurlIncidentCandidate,
      rectangleDualBoundary, rectangleDualInterior, rectangleDualExpanded,
      mem_latticeRectangle, LatticeBond.source, LatticeBond.target,
      LatticeBond.faceBase] at * <;> omega

private theorem rectangleCurlCandidate_flow_zero_of_not_inside
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (i : Fin 4)
    (hv : v ∈ latticeRectangle a w h)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    rectangleCurlFlow a w h φ (rectangleCurlIncidentCandidate v i) = 0 := by
  obtain ⟨hfalse, htrue⟩ :=
    rectangleCurlCandidate_faces_boundary a w h v i hv hout
  have hexpFalse : LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false ∈
      rectangleDualExpanded a w h := (Finset.mem_filter.mp hfalse).1
  have hexpTrue : LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true ∈
      rectangleDualExpanded a w h := (Finset.mem_filter.mp htrue).1
  have hzeroFalse : rectangleExtendedPotential a w h φ
      (LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) false) = 0 := by
    rw [rectangleExtendedPotential_of_mem _ _ _ _ _ hexpFalse]
    exact φ.2 _ hfalse
  have hzeroTrue : rectangleExtendedPotential a w h φ
      (LatticeBond.faceBase (rectangleCurlIncidentCandidate v i) true) = 0 := by
    rw [rectangleExtendedPotential_of_mem _ _ _ _ _ hexpTrue]
    exact φ.2 _ htrue
  cases hi : (rectangleCurlIncidentCandidate v i).axis <;>
    simp [rectangleCurlFlow, hi, hzeroFalse, hzeroTrue]

/-- The true finite set of normalized original bonds incident to `v`. -/
def rectangleActualIncidentBonds (a : LatticeVertex) (w h : ℕ)
    (v : LatticeVertex) :=
  {b : RectanglePrimalBond a w h // b.1.source = v ∨ b.1.target = v}

noncomputable def rectangleActualIncidentCandidateEquiv
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    rectangleActualIncidentBonds a w h v ≃
      {i : Fin 4 // rectangleCurlCandidateInside a w h v i} where
  toFun b := by
    let i := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)
    have hi := (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)).1
    refine ⟨i, ?_⟩
    change (rectangleCurlIncidentCandidate v i).source ∈ latticeRectangle a w h ∧
      (rectangleCurlIncidentCandidate v i).target ∈ latticeRectangle a w h
    rw [hi]
    exact b.1.2
  invFun i := by
    rcases i with ⟨ix, hix⟩
    refine ⟨⟨rectangleCurlIncidentCandidate v ix, hix.1, hix.2⟩, ?_⟩
    fin_cases ix <;> simp [rectangleCurlIncidentCandidate, LatticeBond.source,
      LatticeBond.target]
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    let i := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)
    exact (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)).1
  right_inv i := by
    rcases i with ⟨ix, hix⟩
    apply Subtype.ext
    apply rectangleCurlIncidentCandidate_injective v
    let j := Classical.choose
      (rectangleCurlIncidentBond_exists_unique v
        (rectangleCurlIncidentCandidate v ix)
        (by fin_cases ix <;> simp [rectangleCurlIncidentCandidate,
          LatticeBond.source, LatticeBond.target]))
    have hj := (Classical.choose_spec
      (rectangleCurlIncidentBond_exists_unique v
        (rectangleCurlIncidentCandidate v ix)
        (by fin_cases ix <;> simp [rectangleCurlIncidentCandidate,
          LatticeBond.source, LatticeBond.target]))).1
    exact hj

private theorem rectangleActualIncidentCandidateEquiv_apply
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex)
    (b : rectangleActualIncidentBonds a w h v) :
    rectangleCurlIncidentCandidate v
      (rectangleActualIncidentCandidateEquiv a w h v b).1 = b.1.1 := by
  let i := Classical.choose
    (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)
  have hi := (Classical.choose_spec
    (rectangleCurlIncidentBond_exists_unique v b.1.1 b.2)).1
  change rectangleCurlIncidentCandidate v i = b.1.1
  exact hi

noncomputable instance rectangleActualIncidentBondsFintype
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    Fintype (rectangleActualIncidentBonds a w h v) := by
  classical
  letI : Fintype {i : Fin 4 // rectangleCurlCandidateInside a w h v i} := inferInstance
  exact Fintype.ofEquiv _ (Equiv.symm (rectangleActualIncidentCandidateEquiv a w h v))

noncomputable instance rectangleCurlCandidateFintype
    (a : LatticeVertex) (w h : ℕ) (v : LatticeVertex) :
    Fintype {i : Fin 4 // rectangleCurlCandidateInside a w h v i} :=
  by classical exact Fintype.ofFinite _

/-- Actual incidence divergence over all and only rectangle edges incident to
`v`, with the normalized bond orientation source-to-target. -/
noncomputable def rectanglePrimalCurlDivergence (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (v : LatticeVertex) : ℝ :=
  ∑ b : rectangleActualIncidentBonds a w h v,
    if b.1.1.source = v then rectangleCurlFlow a w h φ b.1.1
    else -rectangleCurlFlow a w h φ b.1.1

/-- Four-neighbor discrete divergence stencil, for comparison with actual
finite-edge incidence. -/
def rectangleCurlStencil (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (v : LatticeVertex) : ℝ :=
  rectangleCurlFlow a w h φ ⟨(v.1, v.2), LatticeAxis.horizontal⟩ -
    rectangleCurlFlow a w h φ ⟨(v.1 - 1, v.2), LatticeAxis.horizontal⟩ +
    rectangleCurlFlow a w h φ ⟨(v.1, v.2), LatticeAxis.vertical⟩ -
    rectangleCurlFlow a w h φ ⟨(v.1, v.2 - 1), LatticeAxis.vertical⟩

theorem rectangleCurlStencil_eq_zero (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (v : LatticeVertex) :
    rectangleCurlStencil a w h φ v = 0 := by
  simp [rectangleCurlStencil, rectangleCurlFlow, LatticeBond.faceBase]
  ring

def rectangleCurlSignedCandidate (a : LatticeVertex) (w h : ℕ)
    (φ : RectangleExteriorPotential a w h) (v : LatticeVertex) (i : Fin 4) : ℝ :=
  if (rectangleCurlIncidentCandidate v i).source = v then
    rectangleCurlFlow a w h φ (rectangleCurlIncidentCandidate v i)
  else -rectangleCurlFlow a w h φ (rectangleCurlIncidentCandidate v i)

private theorem rectangleCurlSignedCandidate_eq_term
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (i : Fin 4)
    (hi : rectangleCurlCandidateInside a w h v i) :
    rectangleCurlSignedCandidate a w h φ v i =
      match i.val with
      | 0 => rectangleCurlFlow a w h φ ⟨v, .horizontal⟩
      | 1 => -rectangleCurlFlow a w h φ ⟨(v.1 - 1, v.2), .horizontal⟩
      | 2 => rectangleCurlFlow a w h φ ⟨v, .vertical⟩
      | _ => -rectangleCurlFlow a w h φ ⟨(v.1, v.2 - 1), .vertical⟩ := by
  rcases v with ⟨x, y⟩
  fin_cases i
  · simp [rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
      LatticeBond.source]
  · have hn : (x - 1, y) ≠ (x, y) := by
      intro hh
      have hx := congrArg Prod.fst hh
      omega
    simp [rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
      LatticeBond.source, hn]
  · simp [rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
      LatticeBond.source]
  · have hn : (x, y - 1) ≠ (x, y) := by
      intro hh
      have hy := congrArg Prod.snd hh
      omega
    simp [rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
      LatticeBond.source, hn]

private theorem rectangleCurlFilteredSum_eq_stencil
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (hv : v ∈ latticeRectangle a w h) :
    (∑ i : {i : Fin 4 // rectangleCurlCandidateInside a w h v i},
      rectangleCurlSignedCandidate a w h φ v i.1) = rectangleCurlStencil a w h φ v := by
  classical
  let p : Fin 4 → Prop := rectangleCurlCandidateInside a w h v
  let : DecidablePred p := Classical.decPred p
  have hsub :
      (∑ i ∈ Finset.univ.filter p,
        rectangleCurlSignedCandidate a w h φ v i) =
      (∑ i : {i : Fin 4 // p i},
        rectangleCurlSignedCandidate a w h φ v i.1) := by
    exact Finset.sum_subtype (p := p) (Finset.univ.filter p)
      (by intro i; simp [p])
      (fun i => rectangleCurlSignedCandidate a w h φ v i)
  rw [← hsub]
  have hterm (i : Fin 4) :
      (if p i then rectangleCurlSignedCandidate a w h φ v i else 0) =
        match i.val with
        | 0 => rectangleCurlFlow a w h φ ⟨v, .horizontal⟩
        | 1 => -rectangleCurlFlow a w h φ ⟨(v.1 - 1, v.2), .horizontal⟩
        | 2 => rectangleCurlFlow a w h φ ⟨v, .vertical⟩
        | _ => -rectangleCurlFlow a w h φ ⟨(v.1, v.2 - 1), .vertical⟩ := by
    fin_cases i
    · by_cases hp : p 0
      · have ht := rectangleCurlSignedCandidate_eq_term a w h φ v 0 hp
        simpa [hp] using ht
      · have hz := rectangleCurlCandidate_flow_zero_of_not_inside a w h φ v 0 hv hp
        simpa [hp, rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
          LatticeBond.source] using hz.symm
    · by_cases hp : p 1
      · have ht := rectangleCurlSignedCandidate_eq_term a w h φ v 1 hp
        simpa [hp] using ht
      · have hz := rectangleCurlCandidate_flow_zero_of_not_inside a w h φ v 1 hv hp
        simpa [hp, rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
          LatticeBond.source] using hz
    · by_cases hp : p 2
      · have ht := rectangleCurlSignedCandidate_eq_term a w h φ v 2 hp
        simpa [hp] using ht
      · have hz := rectangleCurlCandidate_flow_zero_of_not_inside a w h φ v 2 hv hp
        simpa [hp, rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
          LatticeBond.source] using hz.symm
    · by_cases hp : p 3
      · have ht := rectangleCurlSignedCandidate_eq_term a w h φ v 3 hp
        simpa [hp] using ht
      · have hz := rectangleCurlCandidate_flow_zero_of_not_inside a w h φ v 3 hv hp
        have hn := congrArg Neg.neg hz
        simpa [hp, rectangleCurlSignedCandidate, rectangleCurlIncidentCandidate,
          LatticeBond.source] using hn
  rw [Finset.sum_filter]
  change (∑ i : Fin 4, if p i then rectangleCurlSignedCandidate a w h φ v i else 0) = _
  simp_rw [hterm]
  simp [Fin.sum_univ_succ, rectangleCurlStencil]
  ring

theorem rectanglePrimalCurlDivergence_eq_stencil
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (hv : v ∈ latticeRectangle a w h) :
    rectanglePrimalCurlDivergence a w h φ v = rectangleCurlStencil a w h φ v := by
  classical
  let e := rectangleActualIncidentCandidateEquiv a w h v
  calc
    rectanglePrimalCurlDivergence a w h φ v =
        ∑ b : rectangleActualIncidentBonds a w h v,
          rectangleCurlSignedCandidate a w h φ v (e b).1 := by
      change (∑ b : rectangleActualIncidentBonds a w h v,
        if b.1.1.source = v then rectangleCurlFlow a w h φ b.1.1
        else -rectangleCurlFlow a w h φ b.1.1) = _
      apply Finset.sum_congr rfl
      intro b hb
      have hmap := rectangleActualIncidentCandidateEquiv_apply a w h v b
      change rectangleCurlIncidentCandidate v (e b).1 = b.1.1 at hmap
      simp [rectangleCurlSignedCandidate, hmap]
    _ = ∑ i : {i : Fin 4 // rectangleCurlCandidateInside a w h v i},
          rectangleCurlSignedCandidate a w h φ v i.1 :=
            Equiv.sum_comp e (fun i => rectangleCurlSignedCandidate a w h φ v i.1)
    _ = rectangleCurlStencil a w h φ v :=
      rectangleCurlFilteredSum_eq_stencil a w h φ v hv

theorem rectanglePrimalCurlDivergence_eq_zero
    (a : LatticeVertex) (w h : ℕ) (φ : RectangleExteriorPotential a w h)
    (v : LatticeVertex) (hv : v ∈ latticeRectangle a w h) :
    rectanglePrimalCurlDivergence a w h φ v = 0 := by
  rw [rectanglePrimalCurlDivergence_eq_stencil a w h φ v hv]
  exact rectangleCurlStencil_eq_zero a w h φ v

end PottsDiscontinuity.FK
