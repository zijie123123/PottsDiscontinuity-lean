module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology Set MeasurableSpace
open scoped symmDiff

noncomputable section

def measurableRectangles {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    Set (Set (X × Y)) :=
  {R | ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ R = A ×ˢ B}

theorem measurableRectangles_isSetSemiring {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] : IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  classical
  constructor
  · refine ⟨∅, univ, MeasurableSet.empty, MeasurableSet.univ, ?_⟩
    simp
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    refine ⟨A ∩ C, B ∩ D, hA.inter hC, hB.inter hD, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod]
    tauto
  · rintro R ⟨A, B, hA, hB, rfl⟩ S ⟨C, D, hC, hD, rfl⟩
    let R₁ : Set (X × Y) := (A \ C) ×ˢ B
    let R₂ : Set (X × Y) := (A ∩ C) ×ˢ (B \ D)
    let K : Finset (Set (X × Y)) := insert R₁ {R₂}
    have hmemR₁ : R₁ ∈ K := Finset.mem_insert_self _ _
    have hmemR₂ : R₂ ∈ K := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have memK_iff (T : Set (X × Y)) : T ∈ K ↔ T = R₁ ∨ T = R₂ := by
      change T ∈ insert R₁ {R₂} ↔ _
      rw [Finset.mem_insert, Finset.mem_singleton]
    have hK : (K : Set (Set (X × Y))) ⊆
        measurableRectangles (X := X) (Y := Y) := by
      intro T hT
      have hT' : T = R₁ ∨ T = R₂ := (memK_iff T).mp hT
      rcases hT' with hT' | hT'
      · subst T
        exact ⟨A \ C, B, hA.inter hC.compl, hB, rfl⟩
      · subst T
        exact ⟨A ∩ C, B \ D, hA.inter hC, hB.inter hD.compl, rfl⟩
    have hdisj : PairwiseDisjoint (K : Set (Set (X × Y))) id := by
      intro T hT U hU hne
      have hT' : T = R₁ ∨ T = R₂ := (memK_iff T).mp hT
      have hU' : U = R₁ ∨ U = R₂ := (memK_iff U).mp hU
      rcases hT' with hT' | hT' <;> rcases hU' with hU' | hU'
      · subst T
        subst U
        exact (hne rfl).elim
      · subst T
        subst U
        change Disjoint R₁ R₂
        exact Set.disjoint_left.mpr (fun z hz₁ hz₂ => hz₁.1.2 hz₂.1.2)
      · subst T
        subst U
        change Disjoint R₂ R₁
        exact Set.disjoint_left.mpr (fun z hz₁ hz₂ => hz₂.1.2 hz₁.1.2)
      · subst T
        subst U
        exact (hne rfl).elim
    have hdecomp : A ×ˢ B \ C ×ˢ D = ⋃₀ (K : Set (Set (X × Y))) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_prod, Set.mem_sUnion, K, R₁, R₂]
      constructor
      · rintro ⟨⟨hzA, hzB⟩, hnot⟩
        by_cases hzC : z.1 ∈ C
        · have hzD : z.2 ∉ D := fun hz => hnot ⟨hzC, hz⟩
          refine ⟨R₂, hmemR₂, ?_⟩
          exact ⟨⟨hzA, hzC⟩, ⟨hzB, hzD⟩⟩
        · refine ⟨R₁, ?_, ?_⟩
          · exact hmemR₁
          · exact ⟨⟨hzA, hzC⟩, hzB⟩
      · rintro ⟨T, hT, hzT⟩
        have hT' : T = R₁ ∨ T = R₂ := (memK_iff T).mp hT
        rcases hT' with hT' | hT'
        · subst T
          change z.1 ∈ A \ C ∧ z.2 ∈ B at hzT
          rcases hzT with ⟨⟨hzA, hnotC⟩, hzB⟩
          exact ⟨⟨hzA, hzB⟩, fun h => hnotC h.1⟩
        · subst T
          change z.1 ∈ A ∩ C ∧ z.2 ∈ B \ D at hzT
          rcases hzT with ⟨⟨hzA, hzC⟩, ⟨hzB, hnotD⟩⟩
          exact ⟨⟨hzA, hzB⟩, fun h => hnotD h.2⟩
    exact ⟨K, hK, hdisj, hdecomp⟩

theorem measurableRectangles_generateFrom {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom (measurableRectangles (X := X) (Y := Y)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  have hrect : measurableRectangles (X := X) (Y := Y) =
      image2 (· ×ˢ ·) {A : Set X | MeasurableSet A}
        {B : Set Y | MeasurableSet B} := by
    ext R
    simp only [measurableRectangles, Set.mem_ofPred_eq, Set.mem_image2]
    constructor
    · rintro ⟨A, B, hA, hB, rfl⟩
      exact ⟨A, hA, B, hB, rfl⟩
    · rintro ⟨A, hA, B, hB, rfl⟩
      exact ⟨A, B, hA, hB, rfl⟩
  rw [hrect]
  exact generateFrom_prod

theorem measurableRectangleRing_generateFrom {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] :
    MeasurableSpace.generateFrom
        (supClosure (measurableRectangles (X := X) (Y := Y))) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  rw [← measurableRectangles_generateFrom (X := X) (Y := Y)]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro R hR
    exact measurableSet_generateFrom_of_mem_supClosure hR
  · apply MeasurableSpace.generateFrom_le
    intro R hR
    exact measurableSet_generateFrom (subset_supClosure hR)

def productShift {Γ X Y : Type*} (T : Γ → X → X) (S : Γ → Y → Y)
    (a : Γ) : X × Y → X × Y := fun z => (T a z.1, S a z.2)

private theorem prodMeasure_real_rectangle {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y} :
    (μ.prod ν).real (A ×ˢ B) = μ.real A * ν.real B := by
  simp only [Measure.real_def, Measure.prod_prod, ENNReal.toReal_mul]

/-- The product of two translation mixing systems has no nontrivial invariant
events. The proof uses rectangles as a generating set ring, so it does not
require either factor to have a finite dimensional state space. -/
theorem mixingProduct_invariant_event {Γ X Y : Type*} [Infinite Γ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Γ → X → X) (S : Γ → Y → Y)
    (hTpres : ∀ a, MeasurePreserving (T a) μ μ)
    (hSpres : ∀ a, MeasurePreserving (S a) ν ν)
    (hTmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => μ.real (A ∩ (T a) ⁻¹' B)) cofinite (𝓝 (μ.real A * μ.real B)))
    (hSmix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun a => ν.real (A ∩ (S a) ⁻¹' B)) cofinite (𝓝 (ν.real A * ν.real B)))
    {E : Set (X × Y)} (hE : MeasurableSet E)
    (hEinv : ∀ a, (productShift T S a) ⁻¹' E = E) :
    (μ.prod ν) E = 0 ∨ (μ.prod ν) Eᶜ = 0 := by
  classical
  let ρ : Measure (X × Y) := μ.prod ν
  have : IsProbabilityMeasure ρ := by
    change IsProbabilityMeasure (μ.prod ν)
    infer_instance
  have hprodPres (a : Γ) : MeasurePreserving (productShift T S a) ρ ρ := by
    change MeasurePreserving (Prod.map (T a) (S a)) (μ.prod ν) (μ.prod ν)
    exact (hTpres a).prod (hSpres a)
  let R : Set (Set (X × Y)) := supClosure
    (measurableRectangles (X := X) (Y := Y))
  have hRring : IsSetRing R :=
    (measurableRectangles_isSetSemiring (X := X) (Y := Y)).isSetRing_supClosure
  have hRcover : ∃ D : Set (Set (X × Y)), D.Countable ∧ D ⊆ R ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, by simp [ρ]⟩
    intro U hU
    subst U
    apply subset_supClosure
    exact ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by simp⟩
  have hfiniteApproxIndep (E' : Set (X × Y)) (P : Finpartition E')
      (hPrect : (P.parts : Set (Set (X × Y))) ⊆ measurableRectangles (X := X) (Y := Y))
      (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| ≤ ρ.real (E' ∆ E) := by
    let Q : Γ → X × Y → X × Y := productShift T S
    have hshiftMeas (a : Γ) : Measurable (Q a) := by
      dsimp [Q, productShift]
      exact ((hTpres a).measurable.comp measurable_fst).prodMk
        ((hSpres a).measurable.comp measurable_snd)
    have htargetMeas : MeasurableSet (A ×ˢ B) := hA.prod hB
    have hEparts : E' = ⋃ U ∈ P.parts, U := by
      calc
        E' = P.parts.sup id := P.sup_parts.symm
        _ = ⋃₀ (P.parts : Set (Set (X × Y))) := Finset.sup_id_set_eq_sUnion P.parts
        _ = ⋃ U ∈ P.parts, U := by ext z; simp
    have hEpartsSub : E' = ⋃ U : {U : Set (X × Y) // U ∈ P.parts}, (U : Set (X × Y)) := by
      calc
        E' = ⋃ U ∈ P.parts, U := hEparts
        _ = Set.iUnion (fun U : {U : Set (X × Y) // U ∈ P.parts} =>
              (U : Set (X × Y))) := by
          ext z
          simp only [Set.mem_iUnion]
          constructor
          · rintro ⟨U, hU, hzU⟩
            exact ⟨⟨U, hU⟩, hzU⟩
          · rintro ⟨⟨U, hU⟩, hzU⟩
            exact ⟨U, hU, hzU⟩
    have hRmeas (U : Set (X × Y)) (hU : U ∈ P.parts) : MeasurableSet U := by
      obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
      exact hC.prod hD
    have hE'meas : MeasurableSet E' := by
      rw [hEparts]
      exact P.parts.measurableSet_biUnion (fun U hU => hRmeas U hU)
    have hE'measure : ρ.real E' = ∑ U ∈ P.parts, ρ.real U := by
      calc
        ρ.real E' = ρ.real (⋃ U ∈ P.parts, U) := congrArg ρ.real hEparts
        _ = ∑ U ∈ P.parts, ρ.real U :=
          measureReal_biUnion_finset (s := P.parts) (f := id) P.disjoint
            (fun U hU => hRmeas U hU)
    have hpieceTerm (U : Set (X × Y)) (hU : U ∈ P.parts) :
        Tendsto (fun a => ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B))) cofinite
          (𝓝 (ρ.real U * ρ.real (A ×ˢ B))) := by
      obtain ⟨C, D, hC, hD, hUeq⟩ := hPrect hU
      have hset (a : Γ) : U ∩ (Q a) ⁻¹' (A ×ˢ B) =
          (C ∩ (T a) ⁻¹' A) ×ˢ (D ∩ (S a) ⁻¹' B) := by
        rw [hUeq]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Q, productShift]
        tauto
      have hterm (a : Γ) : ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B)) =
          μ.real (C ∩ (T a) ⁻¹' A) * ν.real (D ∩ (S a) ⁻¹' B) := by
        rw [hset, prodMeasure_real_rectangle]
      have hmix := (hTmix C A hC hA).mul (hSmix D B hD hB)
      have hlimit : (μ.real C * μ.real A) * (ν.real D * ν.real B) =
          ρ.real U * ρ.real (A ×ˢ B) := by
        rw [hUeq, prodMeasure_real_rectangle, prodMeasure_real_rectangle]
        ring
      convert hmix using 1
      · funext a
        exact hterm a
      · exact congrArg 𝓝 hlimit.symm
    have hjointSum (a : Γ) : ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B)) =
        ∑ U ∈ P.parts, ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B)) := by
      have hunion : E' ∩ (Q a) ⁻¹' (A ×ˢ B) =
          Set.iUnion (fun U : {U : Set (X × Y) // U ∈ P.parts} =>
            (U : Set (X × Y)) ∩ (Q a) ⁻¹' (A ×ˢ B)) := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨hzE', hzpre⟩
          have hzparts : z ∈ Set.iUnion (fun U : {U : Set (X × Y) // U ∈ P.parts} =>
              (U : Set (X × Y))) :=
            hEpartsSub ▸ hzE'
          rcases Set.mem_iUnion.mp hzparts with ⟨U, hzU⟩
          exact Set.mem_iUnion.mpr ⟨U, ⟨hzU, hzpre⟩⟩
        · intro hz
          rcases Set.mem_iUnion.mp hz with ⟨U, hzUpre⟩
          rcases hzUpre with ⟨hzU, hzpre⟩
          refine ⟨hEpartsSub.symm ▸ ?_, hzpre⟩
          exact Set.mem_iUnion.mpr ⟨U, hzU⟩
      have hpair : Pairwise (fun U V : {U : Set (X × Y) // U ∈ P.parts} =>
          Disjoint ((U : Set (X × Y)) ∩ (Q a) ⁻¹' (A ×ˢ B))
            ((V : Set (X × Y)) ∩ (Q a) ⁻¹' (A ×ˢ B))) := by
        intro U V hne
        have hUV : (U : Set (X × Y)) ≠ (V : Set (X × Y)) := by
          intro heq
          apply hne
          exact Subtype.ext heq
        exact (P.disjoint U.property V.property hUV).mono inter_subset_left inter_subset_left
      have hsumSubtype :
          ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B)) =
            ∑ U : {U : Set (X × Y) // U ∈ P.parts},
              ρ.real ((U : Set (X × Y)) ∩ (Q a) ⁻¹' (A ×ˢ B)) := by
        rw [hunion]
        exact measureReal_iUnion_fintype hpair
          (fun U => (hRmeas U.val U.property).inter ((hshiftMeas a) htargetMeas))
      have hsumConvert :
          (∑ U : {U : Set (X × Y) // U ∈ P.parts},
            ρ.real (U.val ∩ (Q a) ⁻¹' (A ×ˢ B))) =
            ∑ U ∈ P.parts, ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B)) := by
        symm
        exact Finset.sum_subtype P.parts (fun U => Iff.rfl)
          (fun U => ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B)))
      exact hsumSubtype.trans hsumConvert
    have hsumLimit : Tendsto (fun a : Γ =>
        ∑ U ∈ P.parts, ρ.real (U ∩ (Q a) ⁻¹' (A ×ˢ B))) cofinite
        (𝓝 (∑ U ∈ P.parts, ρ.real U * ρ.real (A ×ˢ B))) := by
      exact tendsto_finsetSum _ (fun U hU => hpieceTerm U hU)
    have hjointLimit : Tendsto (fun a : Γ =>
        ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))) cofinite
        (𝓝 (ρ.real E' * ρ.real (A ×ˢ B))) := by
      have hsumLimit' := hsumLimit
      rw [← Finset.sum_mul, ← hE'measure] at hsumLimit'
      exact hsumLimit'.congr' (Eventually.of_forall fun a => (hjointSum a).symm)
    have hconst (a : Γ) : ρ.real (E ∩ (Q a) ⁻¹' (A ×ˢ B)) =
        ρ.real (E ∩ (A ×ˢ B)) := by
      have hpre : (Q a) ⁻¹' (E ∩ (A ×ˢ B)) = E ∩ (Q a) ⁻¹' (A ×ˢ B) := by
        rw [Set.preimage_inter, hEinv a]
      have hm : ρ.real ((Q a) ⁻¹' (E ∩ (A ×ˢ B))) = ρ.real (E ∩ (A ×ˢ B)) := by
        simp only [Measure.real_def]
        rw [← Measure.map_apply (hprodPres a).measurable (hE.inter htargetMeas),
          (hprodPres a).map_eq]
      rw [← hpre]
      exact hm
    have hchangeLe (a : Γ) : |ρ.real (E ∩ (Q a) ⁻¹' (A ×ˢ B)) -
        ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))| ≤ ρ.real (E' ∆ E) := by
      have hsubset : (E ∩ (Q a) ⁻¹' (A ×ˢ B)) ∆
          (E' ∩ (Q a) ⁻¹' (A ×ˢ B)) ⊆ E ∆ E' := by
        intro z hz
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage] at hz ⊢
        tauto
      have hle := abs_measureReal_sub_le_symmDiff ρ
        (hE.inter (hshiftMeas a htargetMeas)) (hE'meas.inter (hshiftMeas a htargetMeas))
      calc
        _ ≤ ρ.real ((E ∩ (Q a) ⁻¹' (A ×ˢ B)) ∆ (E' ∩ (Q a) ⁻¹' (A ×ˢ B))) := hle
        _ ≤ ρ.real (E ∆ E') := measureReal_mono hsubset
        _ = ρ.real (E' ∆ E) := by rw [symmDiff_comm]
    by_contra hnot
    have hgap : ρ.real (E' ∆ E) <
        |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| := lt_of_not_ge hnot
    let η : ℝ := (|ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| -
      ρ.real (E' ∆ E)) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨a, ha⟩ := (Metric.tendsto_nhds.mp hjointLimit _ hη).exists
    rw [Real.dist_eq] at ha
    have hchangeRect : |ρ.real (E ∩ (A ×ˢ B)) -
        ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))| ≤ ρ.real (E' ∆ E) := by
      rw [← hconst a]
      exact hchangeLe a
    have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B)))
      (ρ.real (E' ∩ (Q a) ⁻¹' (A ×ˢ B))) (ρ.real E' * ρ.real (A ×ˢ B))
    dsimp [η] at ha
    nlinarith [hchangeRect, ha, hgap, htri]
  have hrectIndependent (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      ρ.real (E ∩ (A ×ˢ B)) = ρ.real E * ρ.real (A ×ˢ B) := by
    by_contra hne
    have hdpos : 0 < |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E * ρ.real (A ×ˢ B)| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    let η : ℝ := |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E * ρ.real (A ×ˢ B)| / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨E', hE'R, hE'err⟩ :=
      exists_measure_symmDiff_lt_of_generateFrom_isSetRing hRring hRcover
        (measurableRectangleRing_generateFrom (X := X) (Y := Y)).symm hE
        (ENNReal.ofReal_pos.mpr hη)
    have hE'errR : ρ.real (E' ∆ E) < η := by
      have ht := (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE'err
      simpa [ρ, Measure.real_def, ENNReal.toReal_ofReal hη.le] using ht
    obtain ⟨P, hPrect⟩ :=
      (measurableRectangles_isSetSemiring (X := X) (Y := Y)).mem_supClosure_iff.mp hE'R
    have hbound := hfiniteApproxIndep E' P hPrect A B hA hB
    have hE'meas : MeasurableSet E' := by
      have hparts : E' = ⋃ U ∈ P.parts, U := by
        calc
          E' = P.parts.sup id := P.sup_parts.symm
          _ = ⋃₀ (P.parts : Set (Set (X × Y))) := Finset.sup_id_set_eq_sUnion P.parts
          _ = ⋃ U ∈ P.parts, U := by ext z; simp
      rw [hparts]
      exact P.parts.measurableSet_biUnion (fun U hU => by
        obtain ⟨C, D, hC, hD, rfl⟩ := hPrect hU
        exact hC.prod hD)
    have hmass : |ρ.real E' - ρ.real E| ≤ ρ.real (E' ∆ E) :=
      abs_measureReal_sub_le_symmDiff ρ hE'meas hE
    have hrectNonneg : 0 ≤ ρ.real (A ×ˢ B) := measureReal_nonneg
    have hrectLeOne : ρ.real (A ×ˢ B) ≤ 1 := measureReal_le_one
    have hprodDiff :
        |ρ.real E' * ρ.real (A ×ˢ B) - ρ.real E * ρ.real (A ×ˢ B)| ≤
          ρ.real (E' ∆ E) := by
      calc
        _ = |ρ.real E' - ρ.real E| * |ρ.real (A ×ˢ B)| := by
          rw [← sub_mul, abs_mul]
        _ ≤ ρ.real (E' ∆ E) * 1 := by
          rw [abs_of_nonneg hrectNonneg]
          exact mul_le_mul hmass hrectLeOne hrectNonneg (measureReal_nonneg)
        _ = ρ.real (E' ∆ E) := mul_one _
    have hdev₁ :
        |ρ.real (E ∩ (A ×ˢ B)) - ρ.real E' * ρ.real (A ×ˢ B)| < η :=
      lt_of_le_of_lt hbound hE'errR
    have hdev₂ :
        |ρ.real E' * ρ.real (A ×ˢ B) - ρ.real E * ρ.real (A ×ˢ B)| < η :=
      lt_of_le_of_lt hprodDiff hE'errR
    have htri := abs_sub_le (ρ.real (E ∩ (A ×ˢ B)))
      (ρ.real E' * ρ.real (A ×ˢ B)) (ρ.real E * ρ.real (A ×ˢ B))
    dsimp [η] at hdev₁ hdev₂
    nlinarith [hdpos, htri]
  let p : ℝ := ρ.real E
  have hp0 : 0 ≤ p := by exact measureReal_nonneg
  have hp1 : p ≤ 1 := by exact measureReal_le_one
  by_cases hp : p = 0
  · left
    exact (ENNReal.toReal_eq_zero_iff (ρ E)).mp (by simpa [p, Measure.real_def] using hp)
      |>.resolve_right (measure_ne_top ρ E)
  · by_cases hp' : p = 1
    · right
      have hcompl : ρ.real Eᶜ = 0 := by
        have hadd := measureReal_add_measureReal_compl (μ := ρ) hE
        have hEreal : ρ.real E = 1 := by simpa [p] using hp'
        rw [hEreal] at hadd
        have huniv : ρ.real univ = 1 := by simp
        rw [huniv] at hadd
        linarith
      exact (ENNReal.toReal_eq_zero_iff (ρ Eᶜ)).mp (by simpa [Measure.real_def] using hcompl)
        |>.resolve_right (measure_ne_top ρ Eᶜ)
    · have hpLt : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
      have hpLt1 : p < 1 := lt_of_le_of_ne hp1 hp'
      let gap : ℝ := p * (1 - p)
      have hgap : 0 < gap := mul_pos hpLt (by linarith)
      let δ₀ : ℝ := gap / 4
      have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
      obtain ⟨E₀, hE₀R, hE₀err⟩ :=
        exists_measure_symmDiff_lt_of_generateFrom_isSetRing hRring hRcover
          (measurableRectangleRing_generateFrom (X := X) (Y := Y)).symm hE
          (ENNReal.ofReal_pos.mpr hδ₀)
      have hE₀errR : ρ.real (E₀ ∆ E) < δ₀ := by
        have ht := (ENNReal.toReal_lt_toReal (measure_ne_top ρ _) ENNReal.ofReal_ne_top).mpr hE₀err
        simpa [Measure.real_def, ENNReal.toReal_ofReal hδ₀.le] using ht
      obtain ⟨P₀, hP₀rect⟩ :=
        (measurableRectangles_isSetSemiring (X := X) (Y := Y)).mem_supClosure_iff.mp hE₀R
      have hE₀parts : E₀ = ⋃ U ∈ P₀.parts, U := by
        calc
          E₀ = P₀.parts.sup id := P₀.sup_parts.symm
          _ = ⋃₀ (P₀.parts : Set (Set (X × Y))) := Finset.sup_id_set_eq_sUnion P₀.parts
          _ = ⋃ U ∈ P₀.parts, U := by ext z; simp
      have hE₀partsSub :
          E₀ = ⋃ U : {U : Set (X × Y) // U ∈ P₀.parts}, (U : Set (X × Y)) := by
        calc
          E₀ = ⋃ U ∈ P₀.parts, U := hE₀parts
          _ = Set.iUnion (fun U : {U : Set (X × Y) // U ∈ P₀.parts} =>
                (U : Set (X × Y))) := by
            ext z
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨U, hU, hzU⟩
              exact ⟨⟨U, hU⟩, hzU⟩
            · rintro ⟨⟨U, hU⟩, hzU⟩
              exact ⟨U, hU, hzU⟩
      have hE₀meas (U : Set (X × Y)) (hU : U ∈ P₀.parts) : MeasurableSet U := by
        obtain ⟨A, B, hA, hB, rfl⟩ := hP₀rect hU
        exact hA.prod hB
      have hE₀measSet : MeasurableSet E₀ := by
        rw [hE₀partsSub]
        exact MeasurableSet.iUnion fun U => hE₀meas U.val U.property
      have hE₀sum : ρ.real E₀ = ∑ U ∈ P₀.parts, ρ.real U := by
        calc
          ρ.real E₀ = ρ.real (⋃ U ∈ P₀.parts, U) := congrArg ρ.real hE₀parts
          _ = ∑ U ∈ P₀.parts, ρ.real U :=
            measureReal_biUnion_finset (s := P₀.parts) (f := id) P₀.disjoint hE₀meas
      have hindsum : ρ.real (E ∩ E₀) = p * ρ.real E₀ := by
        have hunion : E ∩ E₀ = Set.iUnion
            (fun U : {U : Set (X × Y) // U ∈ P₀.parts} => E ∩ (U : Set (X × Y))) := by
          ext z
          constructor
          · intro hz
            rcases hz with ⟨hzE, hzE₀⟩
            have hzparts : z ∈ Set.iUnion (fun U : {U : Set (X × Y) // U ∈ P₀.parts} =>
                (U : Set (X × Y))) :=
              hE₀partsSub ▸ hzE₀
            rcases Set.mem_iUnion.mp hzparts with ⟨U, hzU⟩
            exact Set.mem_iUnion.mpr ⟨U, ⟨hzE, hzU⟩⟩
          · intro hz
            rcases Set.mem_iUnion.mp hz with ⟨U, hzEU⟩
            rcases hzEU with ⟨hzE, hzU⟩
            refine ⟨hzE, hE₀partsSub.symm ▸ ?_⟩
            exact Set.mem_iUnion.mpr ⟨U, hzU⟩
        have hpair : Pairwise (fun U V : {U : Set (X × Y) // U ∈ P₀.parts} =>
            Disjoint (E ∩ (U : Set (X × Y))) (E ∩ (V : Set (X × Y)))) := by
          intro U V hne
          have hUV : (U : Set (X × Y)) ≠ (V : Set (X × Y)) := by
            intro heq
            apply hne
            exact Subtype.ext heq
          exact (P₀.disjoint U.property V.property hUV).mono
            inter_subset_right inter_subset_right
        have hsumSubtype : ρ.real (E ∩ E₀) =
            ∑ U : {U : Set (X × Y) // U ∈ P₀.parts},
              ρ.real (E ∩ (U : Set (X × Y))) := by
          rw [hunion]
          exact measureReal_iUnion_fintype hpair
            (fun U => hE.inter (hE₀meas U.val U.property))
        have hsumConvert :
            (∑ U : {U : Set (X × Y) // U ∈ P₀.parts}, ρ.real (E ∩ U.val)) =
              ∑ U ∈ P₀.parts, ρ.real (E ∩ U) := by
          symm
          exact Finset.sum_subtype P₀.parts (fun U => Iff.rfl)
            (fun U => ρ.real (E ∩ U))
        calc
          ρ.real (E ∩ E₀) = ∑ U : {U : Set (X × Y) // U ∈ P₀.parts},
              ρ.real (E ∩ U.val) := hsumSubtype
          _ = ∑ U ∈ P₀.parts, ρ.real (E ∩ U) := hsumConvert
          _ = ∑ U ∈ P₀.parts, p * ρ.real U := by
            apply Finset.sum_congr rfl
            intro U hU
            obtain ⟨A, B, hA, hB, rfl⟩ := hP₀rect hU
            simpa [p] using hrectIndependent A B hA hB
          _ = p * ρ.real E₀ := by rw [← Finset.mul_sum, ← hE₀sum]
      have hsubset : (E ∩ E₀) ∆ E ⊆ E₀ ∆ E := by
        intro z hz
        simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hz ⊢
        tauto
      have hfirst : |p - ρ.real (E ∩ E₀)| ≤ ρ.real (E ∆ E₀) := by
        have hmeas : MeasurableSet (E ∩ E₀) := hE.inter hE₀measSet
        have hle := abs_measureReal_sub_le_symmDiff ρ hmeas hE
        rw [abs_sub_comm] at hle
        calc
          _ = |ρ.real E - ρ.real (E ∩ E₀)| := by simp [p]
          _ ≤ ρ.real ((E ∩ E₀) ∆ E) := hle
          _ ≤ ρ.real (E₀ ∆ E) := measureReal_mono hsubset
          _ = ρ.real (E ∆ E₀) := by rw [symmDiff_comm]
      have hfirst' : |p - ρ.real (E ∩ E₀)| < δ₀ := by
        have hsym : ρ.real (E ∆ E₀) = ρ.real (E₀ ∆ E) := by rw [symmDiff_comm]
        rw [hsym] at hfirst
        exact lt_of_le_of_lt hfirst hE₀errR
      have hsecond : |p * ρ.real E₀ - p * p| < δ₀ := by
        have hmass : |ρ.real E₀ - p| ≤ ρ.real (E₀ ∆ E) :=
          abs_measureReal_sub_le_symmDiff ρ hE₀measSet hE
        have hpMul : |p| ≤ 1 := by rw [abs_of_nonneg hp0]; exact hp1
        calc
          _ = |p| * |ρ.real E₀ - p| := by rw [← mul_sub, abs_mul]
          _ ≤ 1 * ρ.real (E₀ ∆ E) :=
            mul_le_mul hpMul hmass (abs_nonneg _) (by norm_num)
          _ = ρ.real (E₀ ∆ E) := one_mul _
          _ < δ₀ := hE₀errR
      have hgapBound : gap < 2 * δ₀ := by
        have htri := abs_sub_le p (ρ.real (E ∩ E₀)) (p * p)
        rw [hindsum] at htri
        rw [hindsum] at hfirst'
        have hgapAbs : |p - p * p| = gap := by
          rw [abs_of_nonneg]
          · dsimp [gap]
            ring
          · dsimp [gap] at hgap
            nlinarith
        calc
          gap = |p - p * p| := hgapAbs.symm
          _ ≤ |p - p * ρ.real E₀| + |p * ρ.real E₀ - p * p| := htri
          _ < δ₀ + δ₀ := add_lt_add hfirst' hsecond
          _ = 2 * δ₀ := by ring
      dsimp [δ₀] at hgapBound
      nlinarith [hgap]

end
end PottsDiscontinuity.PottsThm
