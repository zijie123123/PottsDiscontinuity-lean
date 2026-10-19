module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open scoped ENNReal

noncomputable section

/-- An iid field assigns independent coordinate values at any finite family
of distinct sites. -/
theorem iidFieldMeasure_injective_cylinder {A C : Type*} [Fintype A]
    [DecidableEq A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} =
      ∏ a : A, ν {ξ a} := by
  classical
  let S : Finset Vertex := Finset.univ.image v
  let rep (y : ↥S) : A := Classical.choose (Finset.mem_image.mp y.2)
  have hrep (y : ↥S) : v (rep y) = y.1 := (Finset.mem_image.mp y.2).choose_spec.2
  let t : Vertex → Set C := fun y => if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_pi]
    constructor
    · intro hu y hy
      have hyFin : y ∈ S := by simpa using hy
      have hy' : v (rep ⟨y, hyFin⟩) = y := hrep ⟨y, hyFin⟩
      change u y ∈ (if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ)
      rw [dite_eq_left hyFin]
      simp only [Set.mem_singleton_iff]
      calc
        u y = u (v (rep ⟨y, hyFin⟩)) := congrArg u hy'.symm
        _ = ξ (rep ⟨y, hyFin⟩) := hu _
    · intro hu a
      have ha : v a ∈ S := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      have hya : rep ⟨v a, ha⟩ = a := hv (hrep ⟨v a, ha⟩)
      have hu' := hu (v a) ha
      change u (v a) ∈ (if hy : v a ∈ S then {ξ (rep ⟨v a, hy⟩)} else Set.univ) at hu'
      rw [dite_eq_left ha] at hu'
      simpa [hya] using hu'
  rw [hevent]
  change Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) = _
  have hpi : Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) =
      ∏ y ∈ S, ν (t y) := by
    apply Measure.infinitePi_pi
    intro y hy
    simp [t, hy]
  rw [hpi]
  rw [Finset.prod_image hv.injOn]
  apply Finset.prod_congr rfl
  intro a ha
  have hmem : v a ∈ S := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hchoosea : rep ⟨v a, hmem⟩ = a := hv (hrep ⟨v a, hmem⟩)
  have ht : t (v a) = {ξ a} := by
    simp [t, hmem, hchoosea]
  rw [ht]

/-- Distinct iid coordinates attached to the classes of a finite observed
partition have the ordinary product law. -/
theorem iidFieldMeasure_quotient_cylinder {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)]
    (v : Quotient R → Vertex) (hv : Function.Injective v)
    (ξ : Quotient R → C) :
    iidFieldMeasure ν
        {u : Vertex → C | ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      ∏ c : Quotient R, ν {ξ c} := by
  classical
  let : DecidableEq (Quotient R) := Classical.decEq _
  have hset : {u : Vertex → C |
      ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      {u : Vertex → C | ∀ c : Quotient R, u (v c) = ξ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      exact h a
    · intro h a
      exact h (Quotient.mk R a)
  rw [hset]
  exact iidFieldMeasure_injective_cylinder ν v hv ξ

/-- Conditional cylinder probability for coordinates indexed by the classes of
a finite observed relation, represented by distinct lattice sites. -/
theorem iidFieldMeasure_observedColoring_of_compatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)] (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      ∏ c : Quotient R, ν {ξ (Classical.choose (Quotient.exists_rep c))} := by
  classical
  let repQ : Quotient R → Vertex := Quotient.lift rep (fun a b hab => (hrep a b).mp hab)
  have hrepQ (a : A) : repQ (Quotient.mk R a) = rep a := rfl
  have hinj : Function.Injective repQ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    apply (hrep a b).mpr
    simpa [hrepQ] using hxy
  let ξQ : Quotient R → C := Quotient.lift ξ (fun a b hab => hξ hab)
  have hξQ (a : A) : ξQ (Quotient.mk R a) = ξ a := rfl
  have hset : {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      {u : Vertex → C | ∀ c : Quotient R, u (repQ c) = ξQ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      simpa [hrepQ, hξQ] using h a
    · intro h a
      simpa [hrepQ, hξQ] using h (Quotient.mk R a)
  have hquotset : {u : Vertex → C |
      ∀ a, u (repQ (Quotient.mk R a)) = ξQ (Quotient.mk R a)} =
      {u : Vertex → C | ∀ c : Quotient R, u (repQ c) = ξQ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      exact h a
    · intro h a
      exact h (Quotient.mk R a)
  rw [hset]
  rw [← hquotset]
  have hprob := iidFieldMeasure_quotient_cylinder ν R repQ hinj ξQ
  apply hprob.trans
  apply Finset.prod_congr rfl
  intro c hc
  have hchoose : Quotient.mk R (Classical.choose (Quotient.exists_rep c)) = c :=
    Classical.choose_spec (Quotient.exists_rep c)
  have hbeta : ξQ (Quotient.mk R (Classical.choose (Quotient.exists_rep c))) =
      ξ (Classical.choose (Quotient.exists_rep c)) := by
    simpa only [ξQ] using hξQ (Classical.choose (Quotient.exists_rep c))
  have hcolor : ξQ c = ξ (Classical.choose (Quotient.exists_rep c)) := by
    exact (congrArg ξQ hchoose.symm).trans hbeta
  rw [hcolor]

/-- An incompatible observed pattern has zero iid coloring probability. -/
theorem iidFieldMeasure_observedColoring_of_incompatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : ¬ R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} = 0 := by
  classical
  obtain ⟨a, b, hab, hcolors⟩ : ∃ a b, R a b ∧ ξ a ≠ ξ b := by
    by_contra h
    apply hξ
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hab, hne⟩
  have hempty : {u : Vertex → C | ∀ a, u (rep a) = ξ a} = ∅ := by
    ext u
    constructor
    · intro hu
      have hrepab := (hrep a b).mp hab
      apply hcolors
      calc
        ξ a = u (rep a) := (hu a).symm
        _ = u (rep b) := congrArg u hrepab
        _ = ξ b := hu b
    · intro h
      cases h
  rw [hempty]
  simp

theorem pottsUniformColor_singleton (q : ℕ)
    (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
      (q : ℝ≥0∞)⁻¹ := by
  classical
  have h := ProbabilityTheory.uniformOn_apply_finset
    (s := (Finset.univ : Finset (Set.Icc 1 q))) (t := {c})
  have hcard : (Finset.univ : Finset (Set.Icc 1 q)).card = q := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      PottsDiscontinuity.Potts.card_pottsColors]
  rw [hcard] at h
  simpa using h

/-- For a fixed free bond configuration with finite clusters, the iid
representative coloring has the free Edwards--Sokal cylinder kernel. -/
theorem freeClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
        (fun a : ↥A => ξ a.val)) := by
  classical
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure
      (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))) := inferInstance
  have : MeasurableSingletonClass (Set.Icc 1 q) := inferInstance
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have hrepExists (a : ↥A) : ∃ y, clusterRepresentative ω a.val = some y := by
    have hne : clusterRepresentative ω a.val ≠ none := by
      simp [clusterRepresentative, hfinite a.val]
    cases h : clusterRepresentative ω a.val with
    | none => exact (hne h).elim
    | some y => exact ⟨y, rfl⟩
  let repA (a : ↥A) : Vertex := Classical.choose (hrepExists a)
  have hrepA (a : ↥A) : clusterRepresentative ω a.val = some (repA a) :=
    Classical.choose_spec (hrepExists a)
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b := by
    change (rcInfiniteOpenGraph ω).Reachable a.val b.val ↔ _
    exact (clusterRepresentative_eq_iff_reachable ω a.val b.val
      (hfinite a.val) (hfinite b.val)).symm.trans (by simp [hrepA])
  have hset : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, u (repA a) = ξ a.val} := by
    ext u
    simp [clusterColoring, hrepA]
  rw [hset]
  by_cases hcompat : R ≤ Setoid.ker (fun a : ↥A => ξ a.val)
  · rw [iidFieldMeasure_observedColoring_of_compatible
      (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))) R repA hrep
      (fun a : ↥A => ξ a.val) hcompat]
    have hatom (c : Set.Icc 1 q) :
        ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
          (q : ℝ≥0∞)⁻¹ := pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    have hcount : observedClassCount R id = Nat.card (Quotient R) := rfl
    have hcompatId : R.comap id ≤ Setoid.ker (fun a : ↥A => ξ a.val) := by
      simpa using hcompat
    unfold PottsDiscontinuity.Potts.clusterCylinderProbability
    rw [ite_eq_left hcompatId, hcount,
      PottsDiscontinuity.Potts.card_pottsColors]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _)]
    rw [ENNReal.ofReal_pow hqreal.le, ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · rw [iidFieldMeasure_observedColoring_of_incompatible
      (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))) R repA hrep
      (fun a : ↥A => ξ a.val) hcompat]
    simp [PottsDiscontinuity.Potts.clusterCylinderProbability,
      Setoid.comap_id, R, hcompat]

/-- A pinned quotient coloring has independent iid colors on every observed
class except the distinguished class represented by `none`. -/
theorem iidFieldMeasure_pinnedObservedColoring_of_compatible
    {A C : Type*} [Fintype A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid (Option A)) [Fintype (Quotient R)]
    [Fintype {c : Quotient R // c ≠ Quotient.mk R none}]
    (rep : Option A → Option Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b)
    (hrepGhost : rep none = none) (c₀ : C) (ξ : Option A → C)
    (hξGhost : ξ none = c₀) (hcompat : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a : Option A,
      (rep a).elim c₀ u = ξ a} =
      ∏ c : {c : Quotient R // c ≠ Quotient.mk R none},
        ν {ξ (Classical.choose (Quotient.exists_rep c.val))} := by
  classical
  let Q := Quotient R
  let ghost : Q := Quotient.mk R none
  let repQ : Q → Option Vertex := Quotient.lift rep
    (fun a b hab => (hrep a b).mp hab)
  have hrepQ (a : Option A) : repQ (Quotient.mk R a) = rep a := rfl
  have hrepQGhost : repQ ghost = none := by simp [ghost, hrepQ, hrepGhost]
  have hinj : Function.Injective repQ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    exact (hrep a b).mpr (by simpa [hrepQ] using hxy)
  let ξQ : Q → C := Quotient.lift ξ (fun a b hab => hcompat hab)
  have hξQ (a : Option A) : ξQ (Quotient.mk R a) = ξ a := rfl
  have hξQGhost : ξQ ghost = c₀ := by simp [ghost, hξQ, hξGhost]
  let Qnz := {c : Q // c ≠ ghost}
  have hrepExists (c : Qnz) : ∃ v, repQ c.val = some v := by
    cases h : repQ c.val with
    | none =>
      apply False.elim (c.property ?_)
      apply hinj
      rw [h, hrepQGhost]
    | some v => exact ⟨v, rfl⟩
  let repNz (c : Qnz) : Vertex := Classical.choose (hrepExists c)
  have hrepNz (c : Qnz) : repQ c.val = some (repNz c) :=
    Classical.choose_spec (hrepExists c)
  have hinjNz : Function.Injective repNz := by
    intro c d hcd
    apply Subtype.ext
    apply hinj
    rw [hrepNz c, hrepNz d, hcd]
  have heventQ : {u : Vertex → C | ∀ a : Option A,
      (rep a).elim c₀ u = ξ a} =
      {u : Vertex → C | ∀ c : Q, (repQ c).elim c₀ u = ξQ c} := by
    ext u
    constructor
    · intro hu c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      simpa [hrepQ, hξQ] using hu a
    · intro hu a
      exact hu (Quotient.mk R a)
  have heventNz : {u : Vertex → C | ∀ c : Q,
      (repQ c).elim c₀ u = ξQ c} =
      {u : Vertex → C | ∀ c : Qnz, u (repNz c) = ξQ c.val} := by
    ext u
    constructor
    · intro hu c
      simpa [hrepNz c] using hu c.val
    · intro hu c
      by_cases hc : c = ghost
      · subst c
        simp [hrepQGhost, hξQGhost]
      · simpa [hrepNz ⟨c, hc⟩] using hu ⟨c, hc⟩
  rw [heventQ, heventNz]
  rw [iidFieldMeasure_injective_cylinder ν repNz hinjNz
    (fun c : Qnz => ξQ c.val)]
  apply Finset.prod_congr rfl
  intro c hc
  have hchoose : Quotient.mk R (Classical.choose (Quotient.exists_rep c.val)) = c.val :=
    Classical.choose_spec (Quotient.exists_rep c.val)
  have hcolor : ξQ c.val = ξ (Classical.choose (Quotient.exists_rep c.val)) := by
    calc
      ξQ c.val = ξQ (Quotient.mk R (Classical.choose (Quotient.exists_rep c.val))) :=
        congrArg ξQ hchoose.symm
      _ = ξ (Classical.choose (Quotient.exists_rep c.val)) := hξQ _
  rw [hcolor]

/-- The representative of an observed wired class is the ghost point for the
distinguished class and the lexicographic representative otherwise. -/
def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A) : Option Vertex :=
  a.elim none (fun x => clusterRepresentative ω (v x))

private theorem rcCluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) :
    RCInfinite.cluster ω x = RCInfinite.cluster ω y := by
  ext z
  constructor
  · intro hz
    change (rcInfiniteOpenGraph ω).Reachable x z at hz
    change (rcInfiniteOpenGraph ω).Reachable y z
    exact hxy.symm.trans hz
  · intro hz
    change (rcInfiniteOpenGraph ω).Reachable y z at hz
    change (rcInfiniteOpenGraph ω).Reachable x z
    exact hxy.trans hz

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  classical
  let H := rcInfiniteOpenGraph ω
  cases a with
  | none =>
    cases b with
    | none => simp [wiredObservedRepresentative]
    | some b =>
      change infiniteMergedSetoid H none (some (v b)) ↔ _
      constructor
      · intro hab
        have hba := (infiniteMergedSetoid H).symm hab
        have hinf := (infiniteMergedSetoid_some_none H (v b)).mp hba
        have hnone : clusterRepresentative ω (v b) = none :=
          (clusterRepresentative_none_iff ω (v b)).2 (by
            simpa [clusterIsInfinite, H, RCInfinite.cluster] using hinf)
        simp [wiredObservedRepresentative, hnone]
      · intro hrep
        have hnone : clusterRepresentative ω (v b) = none := by
          simpa [wiredObservedRepresentative] using hrep.symm
        have hinf : clusterIsInfinite H (v b) := by
          simpa [clusterIsInfinite, H, RCInfinite.cluster] using
            (clusterRepresentative_none_iff ω (v b)).1 hnone
        exact (infiniteMergedSetoid H).symm
          ((infiniteMergedSetoid_some_none H (v b)).mpr hinf)
  | some a =>
    cases b with
    | none =>
      change infiniteMergedSetoid H (some (v a)) none ↔ _
      constructor
      · intro hab
        have hinf := (infiniteMergedSetoid_some_none H (v a)).mp hab
        have hnone : clusterRepresentative ω (v a) = none :=
          (clusterRepresentative_none_iff ω (v a)).2 (by
            simpa [clusterIsInfinite, H, RCInfinite.cluster] using hinf)
        simp [wiredObservedRepresentative, hnone]
      · intro hrep
        have hnone : clusterRepresentative ω (v a) = none := by
          simpa [wiredObservedRepresentative] using hrep
        have hinf : clusterIsInfinite H (v a) := by
          simpa [clusterIsInfinite, H, RCInfinite.cluster] using
            (clusterRepresentative_none_iff ω (v a)).1 hnone
        exact (infiniteMergedSetoid_some_none H (v a)).mpr hinf
    | some b =>
      change infiniteMergedSetoid H (some (v a)) (some (v b)) ↔ _
      have hia : clusterIsInfinite H (v a) ↔ (RCInfinite.cluster ω (v a)).Infinite := by
        simp [clusterIsInfinite, H, RCInfinite.cluster]
      have hib : clusterIsInfinite H (v b) ↔ (RCInfinite.cluster ω (v b)).Infinite := by
        simp [clusterIsInfinite, H, RCInfinite.cluster]
      by_cases hfa : (RCInfinite.cluster ω (v a)).Finite
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          have hrep := clusterRepresentative_eq_iff_reachable ω (v a) (v b) hfa hfb
          simpa [wiredObservedRepresentative, hia, hib, hfa, hfb] using hrep.symm
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            intro hxy
            have heq := rcCluster_eq_of_reachable ω hxy
            exact hfb (by simpa [heq] using hfa)
          have hxrep : clusterRepresentative ω (v a) ≠ none := by
            simp [clusterRepresentative, hfa]
          have hyrep : clusterRepresentative ω (v b) = none :=
            (clusterRepresentative_none_iff ω (v b)).2 hfb
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            intro heq
            apply hxrep
            rw [heq, hyrep]
          constructor
          · rintro (hxy | ⟨hinf, _⟩)
            · exact (hnotReach hxy).elim
            · exact False.elim ((show ¬ (RCInfinite.cluster ω (v a)).Finite from
                hia.mp hinf) hfa)
          · exact fun heq => (hrepNe heq).elim
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            intro hxy
            have heq := rcCluster_eq_of_reachable ω hxy
            exact hfa (by simpa [heq] using hfb)
          have hxrep : clusterRepresentative ω (v a) = none :=
            (clusterRepresentative_none_iff ω (v a)).2 hfa
          have hyrep : clusterRepresentative ω (v b) ≠ none := by
            simp [clusterRepresentative, hfb]
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            intro heq
            apply hyrep
            rw [← heq, hxrep]
          constructor
          · rintro (hxy | ⟨_, hinf⟩)
            · exact (hnotReach hxy).elim
            · exact False.elim ((show ¬ (RCInfinite.cluster ω (v b)).Finite from
                hib.mp hinf) hfb)
          · exact fun heq => (hrepNe heq).elim
        · rw [infiniteMergedSetoid_some_some]
          have hxrep : clusterRepresentative ω (v a) = none :=
            (clusterRepresentative_none_iff ω (v a)).2 hfa
          have hyrep : clusterRepresentative ω (v b) = none :=
            (clusterRepresentative_none_iff ω (v b)).2 hfb
          have hinfa : clusterIsInfinite H (v a) := by
            change (RCInfinite.cluster ω (v a)).Infinite
            exact hfa
          have hinfb : clusterIsInfinite H (v b) := by
            change (RCInfinite.cluster ω (v b)).Infinite
            exact hfb
          constructor
          · intro _
            exact hxrep.trans hyrep.symm
          · intro _
            exact Or.inr ⟨hinfa, hinfb⟩

/-- For a fixed wired configuration, canonical coloring by iid colors on
finite clusters and the boundary color on all infinite clusters has the
pinned Edwards--Sokal cylinder probability. -/
theorem wiredClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring (boundaryColor q i hi) (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (pinnedClusterCylinderProbability
        (infiniteWiredPartition (Option.map (fun a : ↥A => a.val)) ω)
        some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi)) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := boundaryColor q i hi
  let v : ↥A → Vertex := fun a => a.val
  let R : Setoid (Option ↥A) := infiniteWiredPartition (Option.map v) ω
  let rep : Option ↥A → Option Vertex := wiredObservedRepresentative ω v
  let ξ' : Option ↥A → Set.Icc 1 q := markedMap (fun a : ↥A => ξ a.val) c₀
  let Q := Quotient R
  let ghost : Q := Quotient.mk R none
  let Qnz := {c : Q // c ≠ ghost}
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have : MeasurableSingletonClass (Set.Icc 1 q) := inferInstance
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have : Fintype Q := Fintype.ofFinite _
  have : Fintype Qnz := Fintype.ofFinite _
  have hrep : ∀ a b, R a b ↔ rep a = rep b := by
    intro a b
    exact wiredObservedRepresentative_eq_iff ω v a b
  have hrepGhost : rep none = none := by
    simp [rep, wiredObservedRepresentative]
  have hcomap (a b : Option ↥A) :
      R.comap (markedMap some none) a b ↔ R a b := by
    cases a <;> cases b <;> rfl
  have hcompKernel :
      (R.comap (markedMap some none) ≤ Setoid.ker (markedMap (fun a : ↥A => ξ a.val) c₀)) ↔
        R ≤ Setoid.ker ξ' := by
    constructor
    · intro h a b hab
      have hh := h (x := a) (y := b) ((hcomap a b).2 hab)
      simpa [ξ', markedMap] using hh
    · intro h a b hab
      have hh := h (x := a) (y := b) ((hcomap a b).1 hab)
      simpa [ξ', markedMap] using hh
  let E : Set (Vertex → Set.Icc 1 q) :=
    {u | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a}
  have hE : E = {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring c₀ (ω, u) a.val = ξ a.val} := by
    ext u
    simp only [E, Set.mem_ofPred_eq]
    constructor
    · intro hu a
      simpa [rep, ξ', wiredObservedRepresentative, clusterColoring, v, markedMap] using
        hu (some a)
    · intro hu a
      cases a with
      | none => simp [rep, ξ', wiredObservedRepresentative, markedMap]
      | some a =>
        simpa [rep, ξ', wiredObservedRepresentative, clusterColoring, v, markedMap] using
          hu a
  rw [← hE]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · have hkernel := (hcompKernel).2 hcompat
    rw [iidFieldMeasure_pinnedObservedColoring_of_compatible ν R rep hrep
      hrepGhost c₀ ξ' (by rfl) hcompat]
    have hatom (c : Set.Icc 1 q) : ν {c} = (q : ℝ≥0∞)⁻¹ := by
      dsimp [ν]
      exact pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    have hcardNz : Nat.card Qnz = Nat.card Q - 1 := by
      calc
        Nat.card Qnz = Fintype.card Qnz := Nat.card_eq_fintype_card
        _ = Fintype.card Q - Fintype.card {c : Q // c = ghost} :=
          Fintype.card_subtype_compl (fun c : Q => c = ghost)
        _ = Nat.card Q - 1 := by simp [ghost, Nat.card_eq_fintype_card]
    have hcardF : Fintype.card Qnz = Nat.card Q - 1 :=
      Nat.card_eq_fintype_card.symm.trans hcardNz
    have hcount : observedClassCount R (markedMap some none) = Nat.card Q := by
      rw [observedClassCount_eq_range]
      have hrange : Set.range (Quotient.mk R ∘ markedMap some none) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro c
        obtain ⟨a, rfl⟩ := Quotient.exists_rep c
        exact ⟨a, by
          change Quotient.mk R (a.elim none some) = Quotient.mk R a
          cases a <;> rfl⟩
      rw [hrange]
      simp [Q]
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left hkernel, hcount]
    rw [PottsDiscontinuity.Potts.card_pottsColors]
    rw [Finset.card_univ, hcardF]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le,
      ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · have hkernel :
        ¬ R.comap (markedMap some none) ≤
          Setoid.ker (markedMap (fun a : ↥A => ξ a.val) c₀) :=
      fun hk => hcompat ((hcompKernel).1 hk)
    have hEmpty : E = ∅ := by
      ext u
      simp only [E, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hu
      apply hcompat
      intro a b hab
      calc
        ξ' a = (rep a).elim c₀ u := (hu a).symm
        _ = (rep b).elim c₀ u := congrArg (fun x : Option Vertex => x.elim c₀ u)
          ((hrep a b).mp hab)
        _ = ξ' b := hu b
    rw [hEmpty]
    rw [MeasureTheory.measure_empty]
    change 0 = ENNReal.ofReal (pinnedClusterCylinderProbability R some
      (fun a : ↥A => ξ a.val) none c₀)
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right hkernel]
    simp

/-- Integrating a finite partition kernel over the first factor gives its
finite weighted sum. -/
theorem lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R : Setoid A, K R * μ {ω | r ω = R} := by
  classical
  let f : Setoid A → Ω → ℝ≥0∞ := fun R =>
    {ω | r ω = R}.indicator (fun _ => K R)
  have hf : (fun ω => K (r ω)) = fun ω => ∑ R : Setoid A, f R ω := by
    funext ω
    dsimp [f]
    rw [Finset.sum_eq_single (r ω)]
    · simp
    · intro R _ hR
      simp [hR.symm]
    · simp
  rw [hf, lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro R hR
    rw [lintegral_indicator_const (hr R)]
  · intro R hR
    exact measurable_const.indicator (hr R)

theorem toReal_lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (Setoid A) := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr]
  unfold PottsDiscontinuity.Potts.partitionExpectation
  rw [ENNReal.toReal_sum (fun R hR =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    (ENNReal.ofReal (K R) * μ {ω | r ω = R}).toReal =
        K R * (μ {ω | r ω = R}).toReal := by simp [ENNReal.toReal_mul, hK R]
    _ = (μ {ω | r ω = R}).toReal * K R := mul_comm _ _

end
end PottsDiscontinuity.PottsThm
