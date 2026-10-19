module

public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! Explicit integer lifts of indexed diamond endpoints and vertical deck
translations. These retain the actual open-edge indices, including small periods. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC CorrLength
variable {N M : ℕ}

lemma periodicCoordinate_nat (hN : 0 < N) (i : Fin N) :
    periodicCoordinate hN (i.val : ℤ) = i := by
  apply Fin.ext
  change ((i.val : ℤ) % (N : ℤ)).toNat = i.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast i.isLt), Int.toNat_natCast]

lemma periodicCoordinate_sub_one (hN : 0 < N) (z : ℤ) :
    periodicCoordinate hN (z-1) = prv (periodicCoordinate hN z) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hN (z-1)).val : ℤ) = ((prv (periodicCoordinate hN z)).val : ℤ)
  rw [periodicCoordinate_val]
  change (z-1) % (N : ℤ) = (((finRotate N).symm (periodicCoordinate hN z)).val : ℤ)
  rw [finRotate_symm_apply, Fin.coe_int_sub_eq_mod, periodicCoordinate_val]
  norm_num

lemma periodicCoordinate_add_period_mul (hN : 0 < N) (z k : ℤ) :
    periodicCoordinate hN (z + (N : ℤ)*k) = periodicCoordinate hN z := by
  apply Fin.ext
  simp [periodicCoordinate,Int.add_emod]

/-- Canonical integer endpoint coordinates of an indexed primal diamond edge. -/
def edgeLiftRaw (e : Fin N × Fin M) (b : Bool) : ℤ × ℤ :=
  if b then
    (if checker e then (e.1.val : ℤ)-1 else e.1.val, (e.2.val : ℤ)-1)
  else (if checker e then e.1.val else (e.1.val : ℤ)-1, e.2.val)

lemma edgeLiftRaw_even (e : Fin N × Fin M) (b : Bool) :
    Even ((edgeLiftRaw e b).1 + (edgeLiftRaw e b).2) := by
  have hmod : (e.1.val + e.2.val) % 2 = 0 ∨ (e.1.val + e.2.val) % 2 = 1 := by omega
  rcases hmod with hc | hc
  · have hb : checker e = true := by simp [checker,hc]
    have he : Even (e.1.val+e.2.val) := Nat.even_iff.2 hc
    have hz : Even ((e.1.val : ℤ)+(e.2.val : ℤ)) := by exact_mod_cast he
    rcases hz with ⟨k,hk⟩
    cases b <;> simp only [edgeLiftRaw,hb,Bool.false_eq_true,ite_true,ite_false]
    · exact ⟨k,hk⟩
    · exact ⟨k-1,by omega⟩
  · have hb : checker e = false := by simp [checker,hc]
    have hz : ((e.1.val : ℤ)+(e.2.val : ℤ)) % 2 = 1 := by exact_mod_cast hc
    cases b <;> simp only [edgeLiftRaw,hb,Bool.false_eq_true,ite_true,ite_false] <;>
      exact ⟨((e.1.val : ℤ)+(e.2.val : ℤ))/2,by omega⟩

/-- A canonical lift of one endpoint, with no choice of path or representative. -/
def edgeLift (e : Fin N × Fin M) (b : Bool) : RotatedVertex :=
  ⟨edgeLiftRaw e b,edgeLiftRaw_even e b⟩

theorem edgeLift_adj (e : Fin N × Fin M) :
    rotatedLattice.Adj (edgeLift e false) (edgeLift e true) := by
  cases hc : checker e <;> simp [rotatedLattice,edgeLift,edgeLiftRaw,hc]

theorem edgeLift_index (hNp : 0 < N) (hMp : 0 < M) (e : Fin N × Fin M) :
    liftedEdgeIndex hNp hMp (edgeLift e false) (edgeLift e true) = e := by
  have hx : max (e.1.val : ℤ) ((e.1.val : ℤ)-1) = e.1.val := max_eq_left (by omega)
  have hy : max (e.2.val : ℤ) ((e.2.val : ℤ)-1) = e.2.val := max_eq_left (by omega)
  cases hc : checker e <;>
    simp [liftedEdgeIndex,edgeLift,edgeLiftRaw,hc,periodicCoordinate_nat]

theorem edgeLift_projects (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (e : Fin N × Fin M) (b : Bool) :
    liftedFaceVertex hN hM hNp hMp (edgeLift e b) = faceEndpoint hN hM true e b := by
  apply Subtype.ext
  cases b <;> cases hc : checker e <;>
    simp [liftedFaceVertex,edgeLift,edgeLiftRaw,faceEndpoint,faceEndpointRaw,hc,
      periodicCoordinate_sub_one,periodicCoordinate_nat]

/-- Vertical deck translation by an integral number of full periods. -/
def verticalDeck (hM : Even M) (k : ℤ) (u : RotatedVertex) : RotatedVertex :=
  ⟨(u.val.1,u.val.2+(M : ℤ)*k), by
    have he : Even ((M : ℤ)*k) := (show Even (M : ℤ) by exact_mod_cast hM).mul_right k
    simpa only [add_assoc] using u.property.add he⟩

lemma verticalDeck_projects (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (k : ℤ) (u : RotatedVertex) :
    liftedFaceVertex hN hM hNp hMp (verticalDeck hM k u) =
      liftedFaceVertex hN hM hNp hMp u := by
  apply Subtype.ext
  exact Prod.ext rfl (periodicCoordinate_add_period_mul hMp u.val.2 k)

lemma verticalDeck_index (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (k : ℤ) (u v : RotatedVertex) :
    liftedEdgeIndex hNp hMp (verticalDeck hM k u) (verticalDeck hM k v) =
      liftedEdgeIndex hNp hMp u v := by
  apply Prod.ext
  · rfl
  · change periodicCoordinate hMp (max (u.val.2+(M : ℤ)*k) (v.val.2+(M : ℤ)*k)) = _
    rw [max_add_add_right,periodicCoordinate_add_period_mul]
    rfl

lemma verticalDeck_adj (hM : Even M) (k : ℤ) {u v : RotatedVertex}
    (huv : rotatedLattice.Adj u v) :
    rotatedLattice.Adj (verticalDeck hM k u) (verticalDeck hM k v) := by
  simpa [rotatedLattice,verticalDeck] using huv

lemma edgeLift_x (e : Fin N × Fin M) (hx : e.1.val ≠ 0) (b : Bool)
    (hN : Even N) (hM : Even M) :
    (edgeLift e b).val.1 = ((faceEndpoint hN hM true e b).val.1.val : ℤ) := by
  have hp := prv_val_of_pos e.1 (Nat.pos_of_ne_zero hx)
  have hp' : ((prv e.1).val : ℤ) = (e.1.val : ℤ)-1 := by omega
  cases b <;> cases hc : checker e <;>
    simp only [edgeLift,edgeLiftRaw,faceEndpoint,faceEndpointRaw,hc,Bool.false_eq_true,
      ite_true,ite_false] <;> first | rfl | exact hp'.symm

/-- Every lift with the finite endpoint's canonical horizontal coordinate is a
unique vertical deck translate of the explicit indexed-edge endpoint. -/
theorem exists_deck_edgeLift_of_projection
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (e : Fin N × Fin M) (hx : e.1.val ≠ 0) (b : Bool) (u : RotatedVertex)
    (hproj : liftedFaceVertex hN hM hNp hMp u = faceEndpoint hN hM true e b)
    (hux : u.val.1 = ((faceEndpoint hN hM true e b).val.1.val : ℤ)) :
    ∃ k : ℤ, verticalDeck hM k (edgeLift e b) = u := by
  have hy := congrArg (fun v : FaceVertex N M true => (v.val.2.val : ℤ))
    (hproj.trans (edgeLift_projects hN hM hNp hMp e b).symm)
  change ((periodicCoordinate hMp u.val.2).val : ℤ) =
    ((periodicCoordinate hMp (edgeLift e b).val.2).val : ℤ) at hy
  rw [periodicCoordinate_val,periodicCoordinate_val] at hy
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.1 hy.symm
  refine ⟨k,Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact (edgeLift_x e hx b hN hM).trans hux.symm
  · change (edgeLift e b).val.2+(M : ℤ)*k = u.val.2
    omega

end PottsDiscontinuity.TorusTopology
