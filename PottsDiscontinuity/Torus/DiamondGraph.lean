module

public import PottsDiscontinuity.Torus.Checkerboard
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter

/-!
# Indexed primal and dual diamond graphs on the even medial torus

The face labelled `(i,j)` has centre `(i+1/2,j+1/2)`. At the medial vertex `(i,j)`
the four faces are NE `(i,j)`, NW `(i-1,j)`, SW `(i-1,j-1)`, SE `(i,j-1)`.
The diamond edge of colour `c` joins the two opposite faces of that colour.
Each medial vertex indexes one primal and one dual edge, even when endpoints coincide
for small periods. Only the connectivity graph forgets loops and edge multiplicities;
the configuration and its weight keep the complete indexed edge set.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Face centres of one checkerboard colour: `true` primal, `false` dual. -/
abbrev FaceVertex (N M : ℕ) (c : Bool) := {v : Fin N × Fin M // checker v = c}

/-- An independent open/closed state on every diamond edge, indexed by its medial midpoint. -/
abbrev RCConfig (N M : ℕ) := Fin N × Fin M → Bool

/-- The raw endpoints of the diamond edge at a medial vertex. -/
def faceEndpointRaw (c : Bool) (v : Fin N × Fin M) (b : Bool) : Fin N × Fin M :=
  if checker v = c then
    if b then (prv v.1, prv v.2) else v
  else if b then (v.1, prv v.2) else (prv v.1, v.2)

theorem checker_faceEndpointRaw (hN : Even N) (hM : Even M) (c : Bool)
    (v : Fin N × Fin M) (b : Bool) : checker (faceEndpointRaw c v b) = c := by
  rcases v with ⟨i, j⟩
  unfold faceEndpointRaw
  by_cases hc : checker (i, j) = c
  · simp only [hc, ite_true]
    cases b
    · exact hc
    · change checker (prv i, prv j) = c
      rw [checker_prv_x hN, checker_prv_y hM, Bool.not_not, hc]
  · simp only [hc, ite_false]
    cases b
    · change checker (prv i, j) = c
      rw [checker_prv_x hN]
      cases ha : checker (i, j) <;> cases c <;> simp_all
    · change checker (i, prv j) = c
      rw [checker_prv_y hM]
      cases ha : checker (i, j) <;> cases c <;> simp_all

/-- The two endpoints with their actual face-colour membership proved. -/
def faceEndpoint (hN : Even N) (hM : Even M) (c : Bool)
    (v : Fin N × Fin M) (b : Bool) : FaceVertex N M c :=
  ⟨faceEndpointRaw c v b, checker_faceEndpointRaw hN hM c v b⟩

/-- The open connectivity graph, on all vertices including isolated ones. -/
def diamondOpenGraph (hN : Even N) (hM : Even M) (c : Bool)
    (A : RCConfig N M) : SimpleGraph (FaceVertex N M c) :=
  SimpleGraph.fromEdgeSet {p | ∃ v, A v = true ∧
    p = s(faceEndpoint hN hM c v false, faceEndpoint hN hM c v true)}

/-- The finite cluster count; endpoint multiplicity has no effect on connectivity. -/
noncomputable def clusterCount (hN : Even N) (hM : Even M) (c : Bool)
    (A : RCConfig N M) : ℕ :=
  Nat.card (diamondOpenGraph hN hM c A).ConnectedComponent

/-- Number of open indexed edges. -/
def openCount (A : RCConfig N M) : ℕ := (univ.filter fun v => A v = true).card

/-- Number of closed indexed edges. -/
def closedCount (A : RCConfig N M) : ℕ := (univ.filter fun v => A v = false).card

theorem openCount_add_closedCount (A : RCConfig N M) :
    openCount A + closedCount A = N * M := by
  have hc := Finset.card_filter_add_card_filter_not (s := univ)
    (fun v : Fin N × Fin M => A v = true)
  simpa only [openCount, closedCount, Bool.not_eq_true, card_univ,
    Fintype.card_prod, Fintype.card_fin] using hc

/-- The closed dual edge is open exactly when the primal edge is closed. -/
def dualConfig (A : RCConfig N M) : RCConfig N M := fun v => !A v

@[simp] theorem dualConfig_dualConfig (A : RCConfig N M) : dualConfig (dualConfig A) = A := by
  funext v
  exact Bool.not_not _

/-- The open/closed-to-pairing dictionary at a primal/dual crossing. -/
def rcSmoothing (A : RCConfig N M) : Smoothing N M := fun v => Bool.xor (checker v) (A v)

/-- Recover the primal edge states from the pairing field. -/
def smoothingRC (s : Smoothing N M) : RCConfig N M := fun v => Bool.xor (checker v) (s v)

@[simp] theorem smoothingRC_rcSmoothing (A : RCConfig N M) : smoothingRC (rcSmoothing A) = A := by
  funext v
  change Bool.xor (checker v) (Bool.xor (checker v) (A v)) = A v
  cases checker v <;> cases A v <;> rfl

@[simp] theorem rcSmoothing_smoothingRC (s : Smoothing N M) : rcSmoothing (smoothingRC s) = s := by
  funext v
  change Bool.xor (checker v) (Bool.xor (checker v) (s v)) = s v
  cases checker v <;> cases s v <;> rfl

/-- The local crossing dictionary is a genuine bijection, without counting arguments. -/
def rcSmoothingEquiv (N M : ℕ) : RCConfig N M ≃ Smoothing N M where
  toFun := rcSmoothing
  invFun := smoothingRC
  left_inv := smoothingRC_rcSmoothing
  right_inv := rcSmoothing_smoothingRC

/-- The critical torus RC weight on the actual indexed diamond graph. -/
noncomputable def torusRCWeight (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) : ℝ :=
  (rcCriticalParameter q).val ^ openCount A *
    (1 - (rcCriticalParameter q).val) ^ closedCount A *
      q.val ^ clusterCount hN hM true A

end PottsDiscontinuity.Torus
