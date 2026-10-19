/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceEdgeIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open scoped symmDiff

noncomputable def parafermionicCoverFacePositiveDartCount {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) : ℕ :=
  (S.filter fun i => (u.1, v.1) ∈ parafermionicCoverFiniteFaceDarts i.1).card

noncomputable def parafermionicCoverFaceBoundaryCoefficient {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) : ℤ :=
  (parafermionicCoverFacePositiveDartCount S u v : ℤ) -
    (parafermionicCoverFacePositiveDartCount S v u : ℤ)

private theorem coverFaceDarts_no_opposite {f : ParafermionicCoverVertex}
    {u v : ParafermionicCoverVertex}
    (huv : (u,v) ∈ parafermionicCoverFiniteFaceDarts f)
    (hvu : (v,u) ∈ parafermionicCoverFiniteFaceDarts f) : False := by
  rcases f with ⟨⟨x,y⟩,k⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at huv hvu
  rcases huv with h1 | h2 | h3 | h4 <;>
    rcases hvu with h1' | h2' | h3' | h4' <;>
    simp_all

private theorem list_countP_xor_mod {α : Type*} (L : List α)
    (p q : α → Bool)
    (h : ∀ a, ¬ (p a = true ∧ q a = true)) :
    (L.countP (fun a => p a != q a)) % 2 =
      (L.countP p + L.countP q) % 2 := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.countP_cons]
      have hcase := h a
      cases hp : p a <;> cases hq : q a
      · simpa [hp, hq] using ih
      · simp at ih ⊢; omega
      · simp at ih ⊢; omega
      · exact (hcase ⟨hp, hq⟩).elim

private theorem coverFacePositiveDartCount_le_one {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hdi : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
    (Finset.mem_filter.mp hi).2
  have hdj : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts j.1 :=
    (Finset.mem_filter.mp hj).2
  have hfaces := parafermionicCoverFiniteFaceDart_unique n i.2 j.2 hdi hdj
  exact Subtype.ext hfaces

theorem parafermionicCoverFaceBoundaryCoefficient_antisymm {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v =
      - parafermionicCoverFaceBoundaryCoefficient S v u := by
  simp [parafermionicCoverFaceBoundaryCoefficient, sub_eq_add_neg, add_comm]

theorem parafermionicCoverFaceBoundaryCoefficient_mem {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ∈ ({-1, 0, 1} : Set ℤ) := by
  have hp := coverFacePositiveDartCount_le_one S u v
  have hm := coverFacePositiveDartCount_le_one S v u
  have hpa : (parafermionicCoverFacePositiveDartCount S u v : ℤ) ≤ 1 := by
    exact_mod_cast hp
  have hma : (parafermionicCoverFacePositiveDartCount S v u : ℤ) ≤ 1 := by
    exact_mod_cast hm
  change parafermionicCoverFaceBoundaryCoefficient S u v = -1 ∨
    parafermionicCoverFaceBoundaryCoefficient S u v = 0 ∨
    parafermionicCoverFaceBoundaryCoefficient S u v = 1
  unfold parafermionicCoverFaceBoundaryCoefficient
  omega

private theorem coverFaceBoundaryEdge_countP_mod {n : ℕ}
    (L : List (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    [DecidablePred (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
      s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)]
    :
    (L.countP fun i => decide
      (s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)) % 2 =
    ((L.countP fun i => decide
      ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) +
      (L.countP fun i => decide
      ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1))) % 2 := by
  classical
  have horient (i : ParafermionicCoverFiniteFaceTopIndex n) :
      decide (s(u,v) ∈
        (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) =
      (decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) !=
        decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) := by
    have hmem := parafermionicCoverFiniteFaceBoundaryEdge_iff_darts i.1 i.2 u v
    by_cases hp : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1
    · have hn : ¬ (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
        intro h
        exact coverFaceDarts_no_opposite hp h
      simp [hmem, hp, hn]
    · by_cases hq : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1
      · simp [hmem, hp, hq]
      · simp [hmem, hp, hq]
  have hcount : L.countP (fun i => decide
      (s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)) =
      L.countP (fun i => decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) !=
        decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) := by
    induction L with
    | nil => rfl
    | cons i L ih => simp only [List.countP_cons, horient i, ih]
  have hno : ∀ i : ParafermionicCoverFiniteFaceTopIndex n,
      ¬ (decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1) = true ∧
      decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1) = true) := by
    intro (i : ParafermionicCoverFiniteFaceTopIndex n) ⟨hp, hq⟩
    exact coverFaceDarts_no_opposite (of_decide_eq_true hp) (of_decide_eq_true hq)
  have hxor := list_countP_xor_mod L
    (fun i => decide ((u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1))
    (fun i => decide ((v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1)) hno
  rw [hcount]
  exact hxor

theorem parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (L : List (ParafermionicCoverFiniteFaceTopIndex n))
    (hL : L.Nodup) (hS : L.toFinset = S)
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ (faceSymmDiffList
        (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L).edgeSet := by
  classical
  let P : ParafermionicCoverFiniteFaceTopIndex n → Prop := fun i =>
    (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1
  let Q : ParafermionicCoverFiniteFaceTopIndex n → Prop := fun i =>
    (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1
  let R : ParafermionicCoverFiniteFaceTopIndex n → Prop := fun i =>
    s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet
  have hcountP : L.countP P = parafermionicCoverFacePositiveDartCount S u v := by
    rw [← hS]
    exact (List.Nodup.card_eq_countP hL).symm
  have hcountQ : L.countP Q = parafermionicCoverFacePositiveDartCount S v u := by
    rw [← hS]
    exact (List.Nodup.card_eq_countP hL).symm
  let : DecidablePred (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
      s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) :=
    Classical.decPred _
  have hpar := coverFaceBoundaryEdge_countP_mod L u v
  have hedgepar := faceSymmDiffList_edge_iff_countP_mod
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L (s(u,v))
  have hcoeff :
      parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
        (L.countP P + L.countP Q) % 2 = 1 := by
    rw [hcountP, hcountQ]
    have hp := coverFacePositiveDartCount_le_one S u v
    have hq := coverFacePositiveDartCount_le_one S v u
    unfold parafermionicCoverFaceBoundaryCoefficient
    omega
  rw [hcoeff]
  rw [← hpar]
  exact hedgepar.symm

end PottsDiscontinuity.TorusTopology.Planar.Medial
