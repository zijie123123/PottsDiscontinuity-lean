module

public import PottsDiscontinuity.SixVertex.InfinityDefectMotion
public import PottsDiscontinuity.SixVertex.InfinityMoves

/-! # Admissible labelled defect choices and their upper row -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- Defects indexed by their actual cyclic sites. -/
abbrev DefectSite (x : Finset (Fin N)) := {i : Fin N // i ∈ defects x}

/-- `true` chooses a left unit move and `false` a right unit move. -/
abbrev DefectChoice (x : Finset (Fin N)) := DefectSite x → Bool

/-- A right-then-left choice at adjacent defects would exchange them and is forbidden. -/
def AdmissibleDefectChoice (x : Finset (Fin N)) (d : DefectChoice x) : Prop :=
  ∀ i : DefectSite x, ∀ hj : nxt i.1 ∈ defects x,
    d i = false → d ⟨nxt i.1, hj⟩ = false

instance (x : Finset (Fin N)) (d : DefectChoice x) : Decidable (AdmissibleDefectChoice x d) := by
  unfold AdmissibleDefectChoice
  infer_instance

/-- Horizontal arrows are reconstructed from the defect choices and the forced up switches. -/
def horizontalOfDefectChoice (x : Finset (Fin N)) (d : DefectChoice x) : Fin N → Bool :=
  fun i => if hd : nxt i ∈ defects x then d ⟨nxt i, hd⟩ else decide (i ∈ x)

/-- The upper up arrows are exactly the down switches of the horizontal arrows. -/
def upperOfHorizontal (h : Fin N → Bool) : Finset (Fin N) :=
  univ.filter fun i => h (prv i) = true ∧ h i = false

@[simp] theorem mem_upperOfHorizontal (h : Fin N → Bool) (i : Fin N) :
    i ∈ upperOfHorizontal h ↔ h (prv i) = true ∧ h i = false := by
  simp only [upperOfHorizontal, mem_filter, mem_univ, true_and]

/-- A choice is recovered exactly at the predecessor of its defect. -/
theorem horizontalOfDefectChoice_prv (x : Finset (Fin N)) (d : DefectChoice x)
    (i : DefectSite x) : horizontalOfDefectChoice x d (prv i.1) = d i := by
  unfold horizontalOfDefectChoice
  simp only [nxt, prv, Equiv.apply_symm_apply, dite_eq_left i.2]

theorem horizontalOfDefectChoice_up {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : DefectChoice x) {i : Fin N} (hi : i ∈ x) :
    horizontalOfDefectChoice x d (prv i) = false ∧ horizontalOfDefectChoice x d i = true := by
  have hn : nxt i ∉ defects x := by
    rw [mem_defects_iff]
    simp only [prv, nxt, Equiv.symm_apply_apply]
    tauto
  have hd : i ∉ defects x := by simp only [mem_defects_iff]; tauto
  have hp : prv i ∉ x := by
    intro hp
    exact hx (prv i) hp (by simpa only [nxt, prv, Equiv.apply_symm_apply] using hi)
  simp only [horizontalOfDefectChoice, nxt, prv, Equiv.apply_symm_apply,
    dite_eq_right hd, dite_eq_right hn, decide_eq_false hp, decide_eq_true hi, and_self]

/-- Admissibility excludes every additional up switch. -/
theorem horizontalOfDefectChoice_up_iff {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : DefectChoice x) (ha : AdmissibleDefectChoice x d) (i : Fin N) :
    i ∈ x ↔ horizontalOfDefectChoice x d (prv i) = false ∧
      horizontalOfDefectChoice x d i = true := by
  constructor
  · exact horizontalOfDefectChoice_up hx d
  · rintro ⟨hp, hi⟩
    by_contra hix
    by_cases hdi : i ∈ defects x
    · have hp' : d ⟨i, hdi⟩ = false := by
        exact (horizontalOfDefectChoice_prv x d ⟨i, hdi⟩).symm.trans hp
      by_cases hdn : nxt i ∈ defects x
      · have hdnext := ha ⟨i, hdi⟩ hdn hp'
        simp only [horizontalOfDefectChoice, dite_eq_left hdn, hdnext] at hi
        contradiction
      · simp only [horizontalOfDefectChoice, dite_eq_right hdn, decide_eq_false hix] at hi
        contradiction
    · have hprev : prv i ∈ x := by
        rw [mem_defects_iff] at hdi
        tauto
      have hp' := (horizontalOfDefectChoice_up hx d hprev).2
      rw [hp] at hp'
      contradiction

/-- Every admissible choice realizes an ice-rule row. -/
theorem flux_horizontalOfDefectChoice {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : DefectChoice x) (ha : AdmissibleDefectChoice x d) :
    Flux x (upperOfHorizontal (horizontalOfDefectChoice x d)) (horizontalOfDefectChoice x d) := by
  intro i
  have hu := horizontalOfDefectChoice_up_iff hx d ha i
  simp only [mem_upperOfHorizontal, hu]
  cases hp : horizontalOfDefectChoice x d (prv i) <;>
    cases hi : horizontalOfDefectChoice x d i <;> norm_num [toInt]

theorem disjoint_upperOfDefectChoice {x : Finset (Fin N)} (hx : NoConsecutiveUp x)
    (d : DefectChoice x) : Disjoint x (upperOfHorizontal (horizontalOfDefectChoice x d)) := by
  apply disjoint_left.mpr
  intro i hi hy
  have hh := horizontalOfDefectChoice_up hx d hi
  exact Bool.noConfusion (hh.1.symm.trans ((mem_upperOfHorizontal _ _).mp hy).1)

/-- Cardinality conservation for the generic cyclic flux equation. -/
theorem Flux.card_eq_generic {x y : Finset (Fin N)} {h : Fin N → Bool} (hf : Flux x y h) :
    x.card = y.card := by
  cases N with
  | zero => exact congrArg Finset.card (Subsingleton.elim _ _)
  | succ k => exact hf.card_eq

/-- The actual independent upper state associated to an admissible choice. -/
def defectChoiceUpperState (x : IndependentState N n)
    (d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}) : IndependentState N n :=
  let y := upperOfHorizontal (horizontalOfDefectChoice x.1.1 d.1)
  have hf := flux_horizontalOfDefectChoice x.2 d.1 d.2
  have hd := disjoint_upperOfDefectChoice x.2 d.1
  ⟨⟨y, hf.card_eq_generic.symm.trans x.1.2⟩,
    noConsecutiveUp_of_interlaced_disjoint (interlaced_of_flux hf).symm hd.symm⟩

/-- Admissible choices produce genuine limiting-matrix edges. -/
theorem infinityRestriction_defectChoiceUpperState (hn : 0 < n) (x : IndependentState N n)
    (d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}) :
    infinityRestriction N n x (defectChoiceUpperState x d) = 1 := by
  apply (infinityBlock_eq_one_iff hn _ _).mpr
  exact ⟨interlaced_of_flux (flux_horizontalOfDefectChoice x.2 d.1 d.2),
    disjoint_upperOfDefectChoice x.2 d.1⟩

/-- The labelled choice read from an ice-rule row. -/
def defectChoiceOfHorizontal (x : Finset (Fin N)) (h : Fin N → Bool) : DefectChoice x :=
  fun i => h (prv i.1)

/-- Every disjoint transfer row is recovered from its choices at the defects. -/
theorem Flux.horizontalOfDefectChoice_inverse {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) (hd : Disjoint x y) :
    horizontalOfDefectChoice x (defectChoiceOfHorizontal x h) = h := by
  funext i
  by_cases hi : nxt i ∈ defects x
  · simp only [horizontalOfDefectChoice, dite_eq_left hi, defectChoiceOfHorizontal,
      prv, nxt, Equiv.symm_apply_apply]
  · have hdi : i ∈ x ∨ nxt i ∈ x := by
      rw [mem_defects_iff] at hi
      simp only [prv, nxt, Equiv.symm_apply_apply] at hi
      tauto
    simp only [horizontalOfDefectChoice, dite_eq_right hi]
    rcases hdi with hx | hx
    · have hh := (hf.local_disjoint hd i).1.mp hx
      simp only [decide_eq_true hx, hh.2]
    · have hh := (hf.local_disjoint hd (nxt i)).1.mp hx |>.1
      simp only [prv, nxt, Equiv.symm_apply_apply] at hh
      have hix : i ∉ x := by
        intro hix
        have hi' := (hf.local_disjoint hd i).1.mp hix |>.2
        rw [hh] at hi'
        contradiction
      simp only [decide_eq_false hix, hh]

/-- The choices of a disjoint transfer row cannot exchange adjacent defects. -/
theorem Flux.admissibleDefectChoice {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) (hd : Disjoint x y) :
    AdmissibleDefectChoice x (defectChoiceOfHorizontal x h) := by
  intro i hj hi
  change h (prv i.1) = false at hi
  change h (prv (nxt i.1)) = false
  rw [show prv (nxt i.1) = i.1 from (finRotate N).symm_apply_apply i.1]
  have hix := (mem_defects_iff x i.1).mp i.2 |>.1
  have hup := (hf.local_disjoint hd i.1).1
  cases hh : h i.1
  · rfl
  · exact (hix (hup.mpr ⟨hi, hh⟩)).elim

/-- The upper row of a disjoint flux configuration is its set of horizontal down switches. -/
theorem Flux.upperOfHorizontal_eq {x y : Finset (Fin N)} {h : Fin N → Bool}
    (hf : Flux x y h) (hd : Disjoint x y) : upperOfHorizontal h = y := by
  ext i
  exact (mem_upperOfHorizontal h i).trans (hf.local_disjoint hd i).2.symm

/-- Nonempty disjoint vertical states admit at most one horizontal flux solution. -/
theorem Flux.unique_of_disjoint {x y : Finset (Fin N)} {h g : Fin N → Bool}
    (hf : Flux x y h) (hg : Flux x y g) (hd : Disjoint x y) (hx : x.Nonempty) : h = g := by
  classical
  have hxy : x ≠ y := by
    rintro rfl
    have he := disjoint_self.mp hd
    exact hx.ne_empty he
  cases N with
  | zero =>
    obtain ⟨i, _⟩ := hx
    exact Fin.elim0 i
  | succ k =>
    have hc := card_flux x y
    rw [ite_eq_right hxy, ite_eq_left (interlaced_of_flux hf)] at hc
    obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have hh : h ∈ (univ.filter fun h : Fin (k + 1) → Bool => Flux x y h) := mem_filter.mpr ⟨mem_univ _, hf⟩
    have hh' : g ∈ (univ.filter fun h : Fin (k + 1) → Bool => Flux x y h) := mem_filter.mpr ⟨mem_univ _, hg⟩
    rw [ha, mem_singleton] at hh hh'
    exact hh.trans hh'.symm

/-- Distinct admissible labelled choices give distinct neighboring row states. -/
theorem defectChoiceUpperState_injective (hn : 0 < n) (x : IndependentState N n) :
    Function.Injective (defectChoiceUpperState x) := by
  intro d e he
  have hd := flux_horizontalOfDefectChoice x.2 d.1 d.2
  have he' := flux_horizontalOfDefectChoice x.2 e.1 e.2
  have hval := congrArg (fun y : IndependentState N n => y.1.1) he
  change upperOfHorizontal (horizontalOfDefectChoice x.1.1 d.1) =
    upperOfHorizontal (horizontalOfDefectChoice x.1.1 e.1) at hval
  rw [← hval] at he'
  have hx : x.1.1.Nonempty := card_pos.mp (by rw [x.1.2]; exact hn)
  have hh := hd.unique_of_disjoint he' (disjoint_upperOfDefectChoice x.2 d.1) hx
  apply Subtype.ext
  funext i
  have hh' := congrFun hh (prv i.1)
  simpa only [horizontalOfDefectChoice_prv x.1.1 d.1 i,
    horizontalOfDefectChoice_prv x.1.1 e.1 i] using hh'

/-- Every genuine neighbor comes from an admissible labelled choice. -/
theorem exists_defectChoiceUpperState (hn : 0 < n) (x y : IndependentState N n)
    (hxy : infinityRestriction N n x y = 1) :
    ∃ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d},
      defectChoiceUpperState x d = y := by
  obtain ⟨hi, hd⟩ := (infinityBlock_eq_one_iff hn x.1 y.1).mp hxy
  obtain ⟨h, hf⟩ := exists_flux_of_interlaced hi
  let d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d} :=
    ⟨defectChoiceOfHorizontal x.1.1 h, hf.admissibleDefectChoice hd⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change upperOfHorizontal (horizontalOfDefectChoice x.1.1 (defectChoiceOfHorizontal x.1.1 h)) = y.1.1
  rw [hf.horizontalOfDefectChoice_inverse hd, hf.upperOfHorizontal_eq hd]

/-- Exact finite-state row summation over the admissible labelled choices. -/
theorem infinityRestriction_mulVec_eq_sum_choices (hn : 0 < n) (x : IndependentState N n)
    (v : IndependentState N n → ℝ) :
    (infinityRestriction N n *ᵥ v) x =
      ∑ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d}, v (defectChoiceUpperState x d) := by
  classical
  have hs : (∑ d : {d : DefectChoice x.1.1 // AdmissibleDefectChoice x.1.1 d},
      v (defectChoiceUpperState x d)) =
      ∑ y ∈ univ.filter (fun y => infinityRestriction N n x y = 1), v y := by
    apply sum_bij (fun d _ => defectChoiceUpperState x d)
    · intro d _
      exact mem_filter.mpr ⟨mem_univ _, infinityRestriction_defectChoiceUpperState hn x d⟩
    · intro d _ e _ he
      exact defectChoiceUpperState_injective hn x he
    · intro y hy
      obtain ⟨d, hd⟩ := exists_defectChoiceUpperState hn x y (mem_filter.mp hy).2
      exact ⟨d, mem_univ _, hd⟩
    · intro d _
      rfl
  rw [hs, Matrix.mulVec, dotProduct, sum_filter]
  apply sum_congr rfl
  intro y _
  change infinityBlock N n x.1 y.1 * v y =
    if infinityBlock N n x.1 y.1 = 1 then v y else 0
  unfold infinityBlock
  split_ifs <;> simp_all [Nat.ne_of_gt hn]

end PottsDiscontinuity.SixVertex
