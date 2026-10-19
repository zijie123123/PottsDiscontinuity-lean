module

public import PottsDiscontinuity.Torus.DiamondCounts
public import PottsDiscontinuity.Torus.EdgeOrder
public import PottsDiscontinuity.Torus.RibbonClusterSurgery

/-!
# Euler counting by cellular ribbon attachment

A handle-creating attachment joins two different boundary cycles of the same
component. Count these events in an explicit edge order and prove the Euler
identity by the three possible attachment cases. This count is not yet identified
with the winding-based net statistic of the paper.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- A ribbon joins different boundaries of one component, thereby creating a handle. -/
def IsHandleAttachment (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (v : Fin N × Fin M) : Prop :=
  RibbonConnected hN hM A (ribbonEndEquiv hN hM (v, false))
    (ribbonEndEquiv hN hM (v, true)) ∧
  ¬(ribbonBoundary hN hM A).SameCycle (ribbonEndEquiv hN hM (v, false))
    (ribbonEndEquiv hN hM (v, true))

/-- Number of handle-creating attachments, reading the list from right to left.
Repeated indices do not attach an already present ribbon again. -/
noncomputable def attachmentHandleCount (hN : Even N) (hM : Even M)
    (L : List (Fin N × Fin M)) : ℕ := by
  classical
  exact L.rec 0 (fun v L g => g +
    if v ∈ L then 0 else if IsHandleAttachment hN hM (configOfList L) v then 1 else 0)

@[simp] theorem attachmentHandleCount_nil (hN : Even N) (hM : Even M) :
    attachmentHandleCount hN hM [] = 0 := rfl

open scoped Classical in
theorem attachmentHandleCount_cons (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) (L : List (Fin N × Fin M)) :
    attachmentHandleCount hN hM (v :: L) = attachmentHandleCount hN hM L +
      if v ∈ L then 0 else if IsHandleAttachment hN hM (configOfList L) v then 1 else 0 := by
  classical
  rfl

/-- The cellular Euler identity for any duplicate-free ribbon attachment order. -/
theorem euler_attachmentHandleCount (hN : Even N) (hM : Even M)
    (L : List (Fin N × Fin M)) (hL : L.Nodup) :
    2 * clusterCount hN hM true (configOfList L) + L.length =
      rcLoopCount hN hM (configOfList L) + Fintype.card (FaceVertex N M true) +
        2 * attachmentHandleCount hN hM L := by
  classical
  induction L with
  | nil =>
    rw [configOfList_nil, clusterCount_closed, rcLoopCount_closed, attachmentHandleCount_nil]
    simp only [List.length_nil]
    omega
  | cons v L ih =>
    obtain ⟨hv, ht⟩ := List.nodup_cons.mp hL
    have hi := ih ht
    have hc : configOfList L v = false := by simp only [configOfList, hv, decide_false]
    rw [configOfList_cons v L hv, List.length_cons]
    by_cases hconn : RibbonConnected hN hM (configOfList L)
        (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))
    · have hk := clusterCount_toggle_of_connected hN hM (configOfList L) v hc hconn
      by_cases hbound : (ribbonBoundary hN hM (configOfList L)).SameCycle
          (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))
      · have hl := rcLoopCount_toggle_split hN hM (configOfList L) v hbound
        have hh : ¬IsHandleAttachment hN hM (configOfList L) v := fun h => h.2 hbound
        rw [attachmentHandleCount_cons]
        simp only [hv, ite_false, hh, add_zero]
        omega
      · have hl := rcLoopCount_toggle_join hN hM (configOfList L) v hbound
        have hh : IsHandleAttachment hN hM (configOfList L) v := ⟨hconn, hbound⟩
        rw [attachmentHandleCount_cons]
        simp only [hv, ite_false, hh, ite_true]
        omega
    · have hk := clusterCount_toggle_of_not_connected hN hM (configOfList L) v hc hconn
      have hbound : ¬(ribbonBoundary hN hM (configOfList L)).SameCycle
          (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true)) :=
        fun h => hconn (ribbonConnected_of_boundary_sameCycle hN hM (configOfList L) h)
      have hl := rcLoopCount_toggle_join hN hM (configOfList L) v hbound
      have hh : ¬IsHandleAttachment hN hM (configOfList L) v := fun h => hconn h.1
      rw [attachmentHandleCount_cons]
      simp only [hv, ite_false, hh, add_zero]
      omega

/-- The handle count in the explicit coordinate order, rather than an Euler-defect definition. -/
noncomputable def ribbonHandleCount (hN : Even N) (hM : Even M) (A : RCConfig N M) : ℕ :=
  attachmentHandleCount hN hM (openEdgeList A)

/-- The genuine RC statistics satisfy Euler counting with the attachment handle count.
Identifying this count with the winding-defined net indicator is a separate obligation. -/
theorem euler_ribbonHandleCount (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    2 * clusterCount hN hM true A + openCount A =
      rcLoopCount hN hM A + N * M / 2 + 2 * ribbonHandleCount hN hM A := by
  have he := euler_attachmentHandleCount hN hM (openEdgeList A) (openEdgeList_nodup A)
  simpa only [configOfList_openEdgeList, length_openEdgeList, card_faceVertex hN,
    ribbonHandleCount] using he

/-- Handle counting is independent of the duplicate-free order of the same open edges. -/
theorem attachmentHandleCount_order_independent (hN : Even N) (hM : Even M)
    (L K : List (Fin N × Fin M)) (hL : L.Nodup) (hK : K.Nodup)
    (h : configOfList L = configOfList K) :
    attachmentHandleCount hN hM L = attachmentHandleCount hN hM K := by
  have hl := euler_attachmentHandleCount hN hM L hL
  have hk := euler_attachmentHandleCount hN hM K hK
  have hn : L.length = K.length := by
    rw [← openCount_configOfList_of_nodup L hL, h, openCount_configOfList_of_nodup K hK]
  rw [h, hn] at hl
  omega

end PottsDiscontinuity.Torus
