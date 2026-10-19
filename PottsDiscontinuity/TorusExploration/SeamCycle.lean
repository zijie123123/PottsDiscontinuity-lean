module

public import PottsDiscontinuity.SixVertex.InfinityEndpointOrder
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-! The seam band is one connected cycle through the bottom and top rows.
It supplies a return chain outside the seam-closed cylinder's interior. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus
open PottsDiscontinuity.SixVertex
variable {N M : ℕ}

/-- Precisely the indexed seam edges, with every other edge closed. -/
def seamOnlyConfig (N M : ℕ) : RCConfig N M := fun e => decide (e.2.val=0)

/-- The seam boundary vertex in column i; bottom and top alternate. -/
def seamCycleVertex (hN : Even N) (hM : Even M) (hMp : 0 < M) (i : Fin N) :
    FaceVertex N M true :=
  if checker (i,(⟨0,hMp⟩ : Fin M)) then
    faceEndpoint hN hM true (i,⟨0,hMp⟩) false
  else faceEndpoint hN hM true (i,⟨0,hMp⟩) true

lemma seamCycleVertex_reachable_prv (hN : Even N) (hM : Even M) (hMp : 0 < M) (i : Fin N) :
    (diamondOpenGraph hN hM true (seamOnlyConfig N M)).Reachable
      (seamCycleVertex hN hM hMp i) (seamCycleVertex hN hM hMp (prv i)) := by
  have hh := diamond_endpoints_reachable hN hM (seamOnlyConfig N M) (i,⟨0,hMp⟩)
    (by simp [seamOnlyConfig])
  have hpc := checker_prv_x hN i (⟨0,hMp⟩ : Fin M)
  cases hc : checker (i,(⟨0,hMp⟩ : Fin M))
  · have hp : checker (prv i,(⟨0,hMp⟩ : Fin M))=true := by simpa [hc] using hpc
    simpa only [seamCycleVertex,hc,hp,faceEndpoint,faceEndpointRaw,Bool.false_eq_true,ite_true,ite_false] using hh.symm
  · have hp : checker (prv i,(⟨0,hMp⟩ : Fin M))=false := by simpa [hc] using hpc
    simpa only [seamCycleVertex,hc,hp,faceEndpoint,faceEndpointRaw,Bool.false_eq_true,ite_true,ite_false] using hh

lemma seamCycleVertex_reachable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (i j : Fin N) :
    (diamondOpenGraph hN hM true (seamOnlyConfig N M)).Reachable
      (seamCycleVertex hN hM hMp i) (seamCycleVertex hN hM hMp j) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNp.ne'
  have hroot (i : Fin (n+1)) :
      (diamondOpenGraph hN hM true (seamOnlyConfig (n+1) M)).Reachable
        (seamCycleVertex hN hM hMp i) (seamCycleVertex hN hM hMp 0) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih =>
      have hp : prv i.succ=i.castSucc := by
        apply Fin.ext
        rw [prv_val_of_pos i.succ (by simp)]
        simp
      have hs := seamCycleVertex_reachable_prv hN hM hMp i.succ
      rw [hp] at hs
      exact hs.trans ih
  exact (hroot i).trans (hroot j).symm

lemma seamCycleVertex_eq_bottom (hN : Even N) (hM : Even M) (hMp : 0 < M)
    (u : FaceVertex N M true) (hu : u.val.2.val=0) :
    seamCycleVertex hN hM hMp u.val.1=u := by
  have hy : u.val.2=(⟨0,hMp⟩ : Fin M) := Fin.ext hu
  have hc : checker (u.val.1,(⟨0,hMp⟩ : Fin M))=true := by simpa [←hy] using u.property
  apply Subtype.ext
  simp only [seamCycleVertex,hc,ite_true,faceEndpoint,faceEndpointRaw,Subtype.coe_mk]
  exact Prod.ext rfl hy.symm

lemma seamCycleVertex_eq_top (hN : Even N) (hM : Even M) (hMp : 0 < M)
    (u : FaceVertex N M true) (hu : u.val.2.val+1=M) :
    seamCycleVertex hN hM hMp u.val.1=u := by
  have hy : u.val.2=prv (⟨0,hMp⟩ : Fin M) := by
    apply Fin.ext
    have hh := prv_val_zero (⟨0,hMp⟩ : Fin M) rfl
    omega
  have hp := checker_prv_y hM u.val.1 (⟨0,hMp⟩ : Fin M)
  have ht : checker (u.val.1,prv (⟨0,hMp⟩ : Fin M))=true := by simpa [←hy] using u.property
  have hc : checker (u.val.1,(⟨0,hMp⟩ : Fin M))=false := by
    rw [ht] at hp
    cases h : checker (u.val.1,(⟨0,hMp⟩ : Fin M)) <;> simp_all
  apply Subtype.ext
  simp only [seamCycleVertex,hc,ite_true,faceEndpoint,faceEndpointRaw]
  exact Prod.ext rfl hy.symm

/-- Every top vertex can return to any bottom vertex using only seam edges. -/
theorem top_bottom_seam_reachable (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (u v : FaceVertex N M true)
    (hu : u.val.2.val=0) (hv : v.val.2.val+1=M) :
    (diamondOpenGraph hN hM true (seamOnlyConfig N M)).Reachable v u := by
  simpa only [seamCycleVertex_eq_bottom hN hM hMp u hu,
    seamCycleVertex_eq_top hN hM hMp v hv] using
      seamCycleVertex_reachable hN hM hNp hMp v.val.1 u.val.1

end PottsDiscontinuity.TorusExploration
