/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

theorem parafermionicCoverFiniteOrdinaryFace_has_cycle
    (n : ℕ) (v : ParafermionicCoverVertex)
    (hbox : v ∈ parafermionicCoverBoxFinset n)
    (hv : v ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∃ w : (parafermionicCoverBoxGraph n).Walk
        ⟨v, by change v ∈ parafermionicCoverBoxVertices n; exact hbox⟩
        ⟨v, by change v ∈ parafermionicCoverBoxVertices n; exact hbox⟩,
      w.IsCycle ∧ w.length = 4 ∧
        w.support.map Subtype.val = [v, parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2, v] := by
  classical
  rcases v with ⟨⟨x,y⟩,k⟩
  have hcrit := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hv
  rcases hcrit with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
  have hface := (parafermionicCoverFaceIntermediateBounds_iff n ((x,y),k)).mpr
    ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
  have hloop : parafermionicCoverFaceLiftEndpoint x y k = ((x,y),k) :=
    parafermionicCoverFaceLiftEndpoint_eq_start_of_not_branch x y k hnot
  let s : ParafermionicCoverBoxVertex n := ⟨((x,y),k), by
    change ((x,y),k) ∈ parafermionicCoverBoxVertices n
    exact hbox⟩
  let r : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightLift x y k, by simpa using hface.2.2.1⟩
  let u : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLift x y k, by simpa using hface.2.2.2.1⟩
  let l : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLeftLift x y k, by simpa using hface.2.2.2.2⟩
  have hsval : s.1 = ((x,y),k) := rfl
  have hrval : r.1 = ((x+1,y), k + if x = 0 ∧ y < 0 then 1 else 0) := by simp [r]
  have huval : u.1 = ((x+1,y+1), k + if x = 0 ∧ y < 0 then 1 else 0) := by simp [u]
  have hsum : (if x = 0 ∧ y < 0 then 1 else 0) +
      (if x = 0 ∧ y+1 < 0 then -1 else 0) = 0 := by
      by_cases hx : x = 0
      · by_cases hy : y < 0
        · have hy' : y < -1 := by
            by_contra h
            have : y = -1 := by omega
            exact hnot (Prod.ext hx this)
          have hnext : y+1 < 0 := by omega
          simp [hx,hy,hnext]
        · simp [hx,hy]
          omega
      · simp [hx]
  have hlval : l.1 = ((x,y+1), k) := by
    change parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1), k)
    rw [parafermionicCoverFaceRightUpLeftLift_formula]
    simp
    omega
  have hsheet : (k + (if x = 0 ∧ y < 0 then 1 else 0)) +
      (if x = 0 ∧ y + 1 < 0 then -1 else 0) = k := by omega
  have hsteps := parafermionicCoverFaceLift_steps_adj x y k
  have h1 : (parafermionicCoverBoxGraph n).Adj s r := by
    change parafermionicCoverGraph.Adj s.1 r.1
    simpa [hsval, hrval] using hsteps.1
  have h2 : (parafermionicCoverBoxGraph n).Adj r u := by
    change parafermionicCoverGraph.Adj r.1 u.1
    simpa [hrval, huval] using hsteps.2.1
  have h3 : (parafermionicCoverBoxGraph n).Adj u l := by
    change parafermionicCoverGraph.Adj u.1 l.1
    simpa [huval, hlval, hsheet] using hsteps.2.2.1
  have h4 : (parafermionicCoverBoxGraph n).Adj l s := by
    change parafermionicCoverGraph.Adj l.1 s.1
    simpa [hlval, hsval, hloop, hsheet] using hsteps.2.2.2
  let tail : (parafermionicCoverBoxGraph n).Walk s l :=
    SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 .nil))
  have hsr : s ≠ r := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1) h
    simp [hsval,hrval] at hh

  have hsu : s ≠ u := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1) h
    simp [hsval,huval] at hh

  have hsl : s ≠ l := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.2) h
    simp [hsval,hlval] at hh

  have hru : r ≠ u := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.2) h
    simp [hrval,huval] at hh

  have hrl : r ≠ l := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h
    simp [hrval,hlval] at hh

  have hul : u ≠ l := by
    intro h
    have hh := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h
    simp [huval,hlval] at hh

  have hpath : tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [tail, hsr, hsu, hsl, hru, hrl, hul]
  let p : (parafermionicCoverBoxGraph n).Path s l := ⟨tail, hpath⟩
  have hclose : s(s,l) ∉ (p.reverse : (parafermionicCoverBoxGraph n).Walk l s).edges := by
    change s(s,l) ∉ (SimpleGraph.Walk.reverse (p : (parafermionicCoverBoxGraph n).Walk s l)).edges
    rw [SimpleGraph.Walk.edges_reverse]
    simp [p, tail, SimpleGraph.Walk.edges_cons, Sym2.eq, hsr,hsu,hsl]; aesop
  let cyc := SimpleGraph.Walk.cons h4.symm (p.reverse : (parafermionicCoverBoxGraph n).Walk l s)
  have hcyc : cyc.IsCycle := by
    dsimp [cyc]
    exact p.reverse.cons_isCycle h4.symm hclose
  refine ⟨cyc.reverse, hcyc.reverse, ?_, ?_⟩
  · simp [cyc, SimpleGraph.Walk.length_cons, p, tail]
  · simp [cyc, SimpleGraph.Walk.support_cons, p, tail, s, r, u, l,
      parafermionicCoverFaceRightUpLeftLift_formula]

end PottsDiscontinuity.TorusTopology.Planar.Medial
