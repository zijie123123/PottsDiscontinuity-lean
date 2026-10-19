module

public import PottsDiscontinuity.Torus.RibbonEuler

/-!
# Monotonicity of the attachment handle count

Extend any order of the old open edges by the newly open edges. Handle events
cannot be lost. Order independence transfers this to the coordinate-defined count.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

@[simp] theorem mem_openEdgeList_iff (A : RCConfig N M) (v : Fin N × Fin M) :
    v ∈ openEdgeList A ↔ A v = true := by
  simp only [openEdgeList, List.mem_filter, mem_diamondEdgeOrder, true_and]

theorem attachmentHandleCount_le_cons (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) (L : List (Fin N × Fin M)) :
    attachmentHandleCount hN hM L ≤ attachmentHandleCount hN hM (v :: L) := by
  classical
  rw [attachmentHandleCount_cons]
  exact Nat.le_add_right _ _

theorem attachmentHandleCount_le_append (hN : Even N) (hM : Even M)
    (L K : List (Fin N × Fin M)) :
    attachmentHandleCount hN hM K ≤ attachmentHandleCount hN hM (L ++ K) := by
  induction L with
  | nil => exact le_rfl
  | cons v L ih => exact ih.trans (attachmentHandleCount_le_cons hN hM v (L ++ K))

theorem attachmentHandleCount_eq_ribbonHandleCount (hN : Even N) (hM : Even M)
    (L : List (Fin N × Fin M)) (hL : L.Nodup) :
    attachmentHandleCount hN hM L = ribbonHandleCount hN hM (configOfList L) := by
  apply attachmentHandleCount_order_independent hN hM L _ hL (openEdgeList_nodup _)
  rw [configOfList_openEdgeList]

/-- Opening additional indexed edges cannot decrease the number of handles. -/
theorem ribbonHandleCount_mono (hN : Even N) (hM : Even M) (A B : RCConfig N M)
    (hAB : ∀ v, A v = true → B v = true) :
    ribbonHandleCount hN hM A ≤ ribbonHandleCount hN hM B := by
  let E : RCConfig N M := fun v => B v && !A v
  let L := openEdgeList E
  let K := openEdgeList A
  have hdis : List.Disjoint L K := by
    apply List.disjoint_left.mpr
    intro v hv hk
    have he : (B v && Bool.not (A v)) = true := (mem_openEdgeList_iff E v).mp hv
    have ha := (mem_openEdgeList_iff A v).mp hk
    simp only [ha, Bool.not_true, Bool.and_false, Bool.false_eq_true] at he
  have hLK : (L ++ K).Nodup :=
    (openEdgeList_nodup E).append (openEdgeList_nodup A) hdis
  have hcfg : configOfList (L ++ K) = B := by
    funext v
    have hv := hAB v
    change decide (v ∈ openEdgeList E ++ openEdgeList A) = B v
    simp only [List.mem_append, mem_openEdgeList_iff]
    change decide ((B v && Bool.not (A v)) = true ∨ A v = true) = B v
    cases ha : A v <;> cases hb : B v <;>
      simp_all only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
        Bool.false_eq_true, or_true, or_false,
        decide_true, decide_false]
  have hm := attachmentHandleCount_le_append hN hM L K
  rw [attachmentHandleCount_eq_ribbonHandleCount hN hM (L ++ K) hLK, hcfg] at hm
  exact hm

end PottsDiscontinuity.Torus
