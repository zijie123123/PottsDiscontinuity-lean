module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Aggregate
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellationSum

/-!
# The finite index set of the zero-root T₁ residues

A surviving word has a unique ML edge, and the perturbed root occupies one of
its two endpoints. The two choices of endpoint are the two summands of a
canonical `T1PairIndex` pair.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A fixed-amplitude word term with a unique ML edge incident to the slot
occupied by the distinguished root. `side = false` places the root at the
right endpoint; `side = true` places it at the left endpoint. -/
structure RootIncidentTermIndex (n : ℕ) (l : Fin (n + 1)) where
  edge : Option (Fin n)
  side : Bool
  σ : RootSlotPerm l (if side then t1EdgeLeft edge else t1EdgeRight edge)
  w : Fin (n + 1) → Bool
  hleft : w (t1EdgeLeft edge) = false
  hright : w (t1EdgeRight edge) = true
  hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
    k = t1EdgeLeft edge

@[ext]
theorem RootIncidentTermIndex.ext {n : ℕ} {l : Fin (n + 1)}
    {i j : RootIncidentTermIndex n l}
    (hedge : i.edge = j.edge) (hside : i.side = j.side)
    (hσ : i.σ.1 = j.σ.1) (hw : i.w = j.w) : i = j := by
  cases i with
  | mk edge side σ w hleft hright hunique =>
    cases j with
    | mk edge' side' σ' w' hleft' hright' hunique' =>
      change edge = edge' at hedge
      change side = side' at hside
      change σ.1 = σ'.1 at hσ
      change w = w' at hw
      subst edge'
      subst side'
      subst w'
      have hσ' : σ = σ' := by
        apply Subtype.ext
        exact hσ
      subst σ'
      rfl

noncomputable instance rootIncidentTermIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (RootIncidentTermIndex n l) := by
  classical
  apply Fintype.ofInjective
    (fun i : RootIncidentTermIndex n l => (i.edge, i.side, i.σ.1, i.w))
  intro i j hij
  simp only [Prod.mk.injEq] at hij
  rcases hij with ⟨hedge, hside, hσ, hw⟩
  exact RootIncidentTermIndex.ext hedge hside hσ hw

/-- Put the zero label at the right (false) or left (true) end of a pair's ML edge. -/
noncomputable def t1PairSideForward {n : ℕ} {l : Fin (n + 1)}
    (v : T1PairIndex n l × Bool) : RootIncidentTermIndex n l := by
  rcases v with ⟨i, side⟩
  cases side
  · exact ⟨i.edge, false, ⟨i.σ, i.hσ⟩, i.w, i.hleft, i.hright, i.hunique⟩
  · refine ⟨i.edge, true, ⟨i.σ * Equiv.swap (t1EdgeLeft i.edge)
      (t1EdgeRight i.edge), ?_⟩, i.w, i.hleft, i.hright, i.hunique⟩
    change i.σ (Equiv.swap (t1EdgeLeft i.edge) (t1EdgeRight i.edge)
      (t1EdgeLeft i.edge)) = l
    rw [Equiv.swap_apply_left]
    exact i.hσ

/-- Recover the canonical orientation, undoing the endpoint swap on the
member whose root is at the left endpoint. -/
noncomputable def rootIncidentToPair {n : ℕ} {l : Fin (n + 1)}
    (j : RootIncidentTermIndex n l) : T1PairIndex n l × Bool := by
  cases j with
  | mk edge side σ w hleft hright hunique =>
    cases side
    · exact ⟨⟨σ.1, w, edge, σ.2, hleft, hright, hunique⟩, false⟩
    · have hroot : (σ.1 * Equiv.swap (t1EdgeLeft edge) (t1EdgeRight edge))
          (t1EdgeRight edge) = l := by
        change σ.1 (Equiv.swap (t1EdgeLeft edge) (t1EdgeRight edge)
          (t1EdgeRight edge)) = l
        rw [Equiv.swap_apply_right]
        exact σ.2
      exact ⟨⟨σ.1 * Equiv.swap (t1EdgeLeft edge) (t1EdgeRight edge),
        w, edge, hroot, hleft, hright, hunique⟩, true⟩

/-- The canonical pair and a choice of which member carries the zero root. -/
noncomputable def t1PairSideEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1PairIndex n l × Bool ≃ RootIncidentTermIndex n l where
  toFun := t1PairSideForward
  invFun := rootIncidentToPair
  left_inv := by
    rintro ⟨i, side⟩
    cases side
    · rfl
    · apply Prod.ext
      · apply T1PairIndex.ext
        · ext k
          simp [t1PairSideForward, rootIncidentToPair]
        · rfl
        · rfl
      · rfl
  right_inv := by
    intro j
    cases j with
    | mk edge side σ w hleft hright hunique =>
      cases side <;> apply RootIncidentTermIndex.ext <;>
        simp [t1PairSideForward, rootIncidentToPair]

/-- The raw permutation and word underlying a root-incident index. -/
noncomputable def rootIncidentUnderlying {n : ℕ} {l : Fin (n + 1)}
    (i : RootIncidentTermIndex n l) :
    Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool) := (i.σ.1, i.w)

/-- The endpoints of a cyclic edge are distinct when the cycle has at least
two vertices. -/
theorem t1EdgeLeft_ne_right {n : ℕ} (hn : 0 < n) (e : Option (Fin n)) :
    t1EdgeLeft e ≠ t1EdgeRight e := by
  cases e with
  | none =>
      intro h
      have hv := congrArg Fin.val h
      simp [t1EdgeLeft, t1EdgeRight] at hv
      omega
  | some a =>
      intro h
      have hv := congrArg Fin.val h
      simp [t1EdgeLeft, t1EdgeRight] at hv

/-- Forgetting the unique-edge and orientation witnesses is injective: the
word determines its unique ML edge, and the permutation determines which
endpoint carries the distinguished label. -/
theorem rootIncidentUnderlying_injective {n : ℕ} {l : Fin (n + 1)}
    (hn : 0 < n) : Function.Injective (rootIncidentUnderlying (n := n) (l := l)) := by
  intro i j hij
  have hσ : i.σ.1 = j.σ.1 := congrArg Prod.fst hij
  have hw : i.w = j.w := congrArg Prod.snd hij
  have hleft : t1EdgeLeft i.edge = t1EdgeLeft j.edge := by
    symm
    apply i.hunique (t1EdgeLeft j.edge)
    · rw [hw]
      exact j.hleft
    · rw [hw, t1EdgeLeft_rotate]
      exact j.hright
  have hedge : i.edge = j.edge := t1EdgeLeftEquiv.injective hleft
  have hroot : (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) =
      (if j.side then t1EdgeLeft j.edge else t1EdgeRight j.edge) := by
    apply i.σ.1.injective
    calc
      i.σ.1 (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) = l := i.σ.2
      _ = j.σ.1 (if j.side then t1EdgeLeft j.edge else t1EdgeRight j.edge) := j.σ.2.symm
      _ = i.σ.1 (if j.side then t1EdgeLeft j.edge else t1EdgeRight j.edge) := by rw [← hσ]
  have hside : i.side = j.side := by
    have hne := t1EdgeLeft_ne_right hn j.edge
    cases hi : i.side <;> cases hj : j.side
    · rfl
    · have h := hroot
      simp [hi, hj, hedge] at h
      exact False.elim (hne h.symm)
    · have h := hroot
      simp [hi, hj, hedge] at h
      exact False.elim (hne h)
    · rfl
  exact RootIncidentTermIndex.ext hedge hside hσ hw

/-- Two ML edges both touching the same slot must be the same cyclic edge. -/
theorem mlEdge_incident_unique {n : ℕ} (w : Fin (n + 1) → Bool)
    (r a b : Fin (n + 1))
    (ha₀ : w a = false) (ha₁ : w (finRotate (n + 1) a) = true)
    (haI : r = a ∨ r = finRotate (n + 1) a)
    (hb₀ : w b = false) (hb₁ : w (finRotate (n + 1) b) = true)
    (hbI : r = b ∨ r = finRotate (n + 1) b) : a = b := by
  rcases haI with haL | haR <;> rcases hbI with hbL | hbR
  · exact haL.symm.trans hbL
  · have hEq : a = finRotate (n + 1) b := haL.symm.trans hbR
    have htrue : w a = true := by rw [hEq]; exact hb₁
    have hfalse : false = true := ha₀.symm.trans htrue
    cases hfalse
  · have hEq : b = finRotate (n + 1) a := hbL.symm.trans haR
    have htrue : w b = true := by rw [hEq]; exact ha₁
    have hfalse : false = true := hb₀.symm.trans htrue
    cases hfalse
  · exact (finRotate (n + 1)).injective (haR.symm.trans hbR)

/-- A nonconstant cyclic Boolean word has at least one ML edge. -/
theorem exists_cyclicML_of_nonconstant {n : ℕ} (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    ∃ a, w a = false ∧ w (finRotate (n + 1) a) = true := by
  rcases nonconstant_word_has_ML w hL hM with ⟨a, ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨a.castSucc, ha, ?_⟩
    have hr : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
    rw [hr]
    exact hb
  · refine ⟨Fin.last n, ha, ?_⟩
    rw [finRotate_last]
    exact hb

/-- If all ML edges touch the zero-root slot, a nonconstant word determines
one unique edge and therefore a canonical root-incident T₁ term. -/
theorem exists_rootIncidentTerm_of_allMLIncident {n : ℕ} {l : Fin (n + 1)}
    (r : Fin (n + 1)) (σ : RootSlotPerm l r) (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false)
    (hAll : ∀ a, w a = false → w (finRotate (n + 1) a) = true →
      r = a ∨ r = finRotate (n + 1) a) :
    ∃ i : RootIncidentTermIndex n l, i.σ.1 = σ.1 ∧ i.w = w := by
  obtain ⟨a, ha, hb⟩ := exists_cyclicML_of_nonconstant w hL hM
  have hInc := hAll a ha hb
  let edge := t1EdgeLeftEquiv.symm a
  have hleft : t1EdgeLeft edge = a := t1EdgeLeftEquiv.apply_symm_apply a
  have hright : t1EdgeRight edge = finRotate (n + 1) a := by
    rw [← t1EdgeLeft_rotate edge, hleft]
  have hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
      k = t1EdgeLeft edge := by
    intro k hk₀ hk₁
    have hkI := hAll k hk₀ hk₁
    have heq := mlEdge_incident_unique w r k a hk₀ hk₁ hkI ha hb hInc
    rw [hleft]
    exact heq
  rcases hInc with hrootL | hrootR
  · refine ⟨⟨edge, true, ⟨σ.1, ?_⟩, w, ?_, ?_, hunique⟩, rfl, rfl⟩
    · change σ.1 (t1EdgeLeft edge) = l
      rw [hleft, ← hrootL]
      exact σ.2
    · simpa [hleft] using ha
    · simpa [hright] using hb
  · refine ⟨⟨edge, false, ⟨σ.1, ?_⟩, w, ?_, ?_, hunique⟩, rfl, rfl⟩
    · change σ.1 (t1EdgeRight edge) = l
      rw [hright, ← hrootR]
      exact σ.2
    · simpa [hleft] using ha
    · simpa [hright] using hb

end PottsDiscontinuity.BetheAnsatz
