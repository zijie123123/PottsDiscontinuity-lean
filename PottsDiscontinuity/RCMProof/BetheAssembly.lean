module

public import FixedPointTheorems.brouwer
public import PottsDiscontinuity.Bethe.RatioAnySign
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

/-!
# Theorem 1.3 ratio limit at the critical six-vertex parameter

The assembly uses Theorem 2.3 to select the two symmetric Bethe families,
the Fourier eigenvalue-ratio limit for both parities (`Bethe/Ratio*`), and the
proved Corollary 3.4 analytic-family identifications.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

structure EndpointBetheState (N n r : ℕ) (Δ c : ℝ)
    (hΔ : Δ < -1) (K : ℝ) where
  hn : 0 < n
  hsize : 2 * n ≤ N
  roots : Fin n → ℝ
  roots_mem : roots ∈ Bethe.S_n n
  roots_bethe : Bethe.DiscreteBetheEquation Δ N n roots
  density_bound : Bethe.densityNorm Δ hΔ
      (fun x => Bethe.rootStepDensity N n roots roots_mem hn hsize x -
        Bethe.rho Δ x)
      (Bethe.rootStepDensity_error_bddAbove hΔ roots roots_mem hn hsize) ≤ K / N
  lambda_eq : SixVertex.cor34BetheLambda N n c roots = Lambda c N r

/-- Theorem 1.3, equation (1.7), along the tail of the subsequence `N ∈ 4ℕ`.
The finite-size Bethe/Perron-root identification uses the proved Corollary 3.4
endpoint-family theorem. -/
theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : ℕ, ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q / 2))) atTop
        (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) *
          (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  let Δcrit : ℝ := -Real.sqrt q / 2
  let c : ℝ := Real.sqrt (2 + Real.sqrt q)
  have hqpos : 0 < q := by linarith
  have hsqrtq : 2 < Real.sqrt q := by
    have hsquare := Real.sq_sqrt (show 0 ≤ q by linarith)
    have hsqrt_nonneg := Real.sqrt_nonneg q
    nlinarith [hq, hsquare, hsqrt_nonneg]
  have hΔcrit : Δcrit < -1 := by
    dsimp [Δcrit]
    linarith
  have hlam : 0 < Real.arcosh (Real.sqrt q / 2) := by
    exact Real.arcosh_pos (by nlinarith [hsqrtq])
  have hcosh : Real.cosh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt q / 2 :=
    Real.cosh_arcosh (by nlinarith)
  have hminus : -Δcrit = Real.sqrt q / 2 := by
    dsimp [Δcrit]
    ring
  have hlamEq : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) := by
    have hcoshDelta : Real.cosh (Real.arcosh (Real.sqrt q / 2)) = -Δcrit := by
      rw [hminus]
      exact hcosh
    exact (Bethe.eq_lamOf hlam hcoshDelta).symm
  have hcΔ : BetheAnsatz.anisotropy c = Δcrit := by
    have hc2 : (Real.sqrt (2 + Real.sqrt q)) ^ 2 = 2 + Real.sqrt q :=
      Real.sq_sqrt (by positivity)
    dsimp [BetheAnsatz.anisotropy, c, Δcrit]
    nlinarith
  have hcPhysical : Real.sqrt (2 - 2 * Δcrit) = c := by
    dsimp [Δcrit, c]
    have heq : 2 - 2 * (-Real.sqrt q / 2) = 2 + Real.sqrt q := by ring
    rw [heq]

  obtain ⟨Kq, hKq, Nq, hNq, hEndpointQ⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint r hΔcrit
  obtain ⟨Kp, hKp, Np, hNp, hEndpointP⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint 0 hΔcrit
  let B : ℕ := max (max Nq Np) (r + 2)
  let N : ℕ → ℕ := fun i => 4 * (i + B)
  have hB : 0 < B := by dsimp [B]; omega
  have hBq : Nq ≤ B := by dsimp [B]; omega
  have hBp : Np ≤ B := by dsimp [B]; omega
  have hBr : r + 2 ≤ B := by dsimp [B]; omega
  have hhalf (i : ℕ) : N i / 2 = 2 * (i + B) := by
    dsimp [N]
    rw [show 4 * (i + B) = 2 * (2 * (i + B)) by omega]
    exact Nat.mul_div_right _ (by norm_num)
  have hNpos (i : ℕ) : 0 < N i := by
    dsimp [N]
    omega
  have hNeven (i : ℕ) : Even (N i) := by
    refine ⟨N i / 2, ?_⟩
    rw [hhalf]
    dsimp [N]
    omega
  have hNlargeQ (i : ℕ) : Nq ≤ N i := by
    have hle : B ≤ N i := by dsimp [N]; omega
    exact hBq.trans hle
  have hNlargeP (i : ℕ) : Np ≤ N i := by
    have hle : B ≤ N i := by dsimp [N]; omega
    exact hBp.trans hle
  have h4 (i : ℕ) : 4 ∣ N i := by
    refine ⟨i + B, ?_⟩
    simp [N]
  have hNlim : Tendsto (fun i : ℕ => (N i : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro x
    let k := Nat.ceil x
    filter_upwards [Filter.eventually_ge_atTop k] with i hi
    have hki : k ≤ N i := by
      have hki' : k ≤ i + B := by omega
      dsimp [N]
      omega
    have hxk : x ≤ (k : ℝ) := Nat.le_ceil x
    have hkn : (k : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hki
    exact hxk.trans hkn
  have hrBound (i : ℕ) : r ≤ N i / 2 := by
    rw [hhalf]
    omega
  have hsizeQ (i : ℕ) : 2 * (N i / 2 - r) ≤ N i := by
    rw [hhalf]
    have hN4 : N i = 4 * (i + B) := by rfl
    rw [hN4]
    omega
  have hnQ (i : ℕ) : 0 < N i / 2 - r := by
    rw [hhalf]
    omega
  have hsizeP (i : ℕ) : 2 * (N i / 2) ≤ N i := by omega
  have hnP (i : ℕ) : 0 < N i / 2 := by rw [hhalf]; omega
  have hNdouble (i : ℕ) : N i = 2 * (N i / 2) := by
    rw [hhalf]
    dsimp [N]
    omega
  have hcountQ (i : ℕ) : N i = 2 * (N i / 2 - r + r) := by
    rw [hNdouble]
    rw [hhalf]
    congr 1
    omega
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by
    rw [hNdouble]
    rw [hhalf]
    congr 1
    omega

  have hdataQ : ∀ i : ℕ,
      Nonempty (EndpointBetheState (N i) (N i / 2 - r) r Δcrit c hΔcrit Kq) := by
    intro i
    obtain ⟨hn, hs, p, hp, hBE, hDensity, hLambda⟩ :=
      hEndpointQ (N i) (hNlargeQ i) (hNeven i)
    let data : EndpointBetheState (N i) (N i / 2 - r) r Δcrit c hΔcrit Kq :=
      { hn := hn
        hsize := hs
        roots := p
        roots_mem := hp
        roots_bethe := hBE
        density_bound := hDensity
        lambda_eq := by simpa [hcPhysical] using hLambda }
    exact ⟨data⟩
  have hdataP : ∀ i : ℕ,
      Nonempty (EndpointBetheState (N i) (N i / 2) 0 Δcrit c hΔcrit Kp) := by
    intro i
    obtain ⟨hn, hs, p, hp, hBE, hDensity, hLambda⟩ :=
      hEndpointP (N i) (hNlargeP i) (hNeven i)
    let data : EndpointBetheState (N i) (N i / 2) 0 Δcrit c hΔcrit Kp :=
      { hn := hn
        hsize := hs
        roots := p
        roots_mem := hp
        roots_bethe := hBE
        density_bound := hDensity
        lambda_eq := by simpa [hcPhysical] using hLambda }
    exact ⟨data⟩
  let Dq : ∀ i : ℕ, EndpointBetheState (N i) (N i / 2 - r) r Δcrit c hΔcrit Kq :=
    fun i => Classical.choice (hdataQ i)
  let Dp : ∀ i : ℕ, EndpointBetheState (N i) (N i / 2) 0 Δcrit c hΔcrit Kp :=
    fun i => Classical.choice (hdataP i)
  let rootsQ : ∀ i : ℕ, Fin (N i / 2 - r) → ℝ := fun i => (Dq i).roots
  let rootsP : ∀ i : ℕ, Fin (N i / 2) → ℝ := fun i => (Dp i).roots
  have hrootsQmem (i : ℕ) : rootsQ i ∈ Bethe.S_n (N i / 2 - r) :=
    (Dq i).roots_mem
  have hrootsPmem (i : ℕ) : rootsP i ∈ Bethe.S_n (N i / 2) :=
    (Dp i).roots_mem
  have hrootsQBE (i : ℕ) : Bethe.DiscreteBetheEquation Δcrit (N i)
      (N i / 2 - r) (rootsQ i) := (Dq i).roots_bethe
  have hrootsPBE (i : ℕ) : Bethe.DiscreteBetheEquation Δcrit (N i)
      (N i / 2) (rootsP i) := (Dp i).roots_bethe
  have hbp (i : ℕ) : BddAbove (Set.range fun α : Set.Icc (-Real.pi) Real.pi =>
      |Bethe.Xi (Bethe.lamOf Δcrit) α *
        (Bethe.rootStepDensity (N i) (N i / 2) (rootsP i) (hrootsPmem i)
          (hnP i) (hsizeP i) (Bethe.kMap (Bethe.lamOf Δcrit) α) -
          Bethe.rho Δcrit (Bethe.kMap (Bethe.lamOf Δcrit) α))|) :=
    Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsP i) (hrootsPmem i)
      (hnP i) (hsizeP i)
  have hbq (i : ℕ) : BddAbove (Set.range fun α : Set.Icc (-Real.pi) Real.pi =>
      |Bethe.Xi (Bethe.lamOf Δcrit) α *
        (Bethe.rootStepDensity (N i) (N i / 2 - r) (rootsQ i) (hrootsQmem i)
          (hnQ i) (hsizeQ i) (Bethe.kMap (Bethe.lamOf Δcrit) α) -
          Bethe.rho Δcrit (Bethe.kMap (Bethe.lamOf Δcrit) α))|) :=
    Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsQ i) (hrootsQmem i)
      (hnQ i) (hsizeQ i)
  have hnormP (i : ℕ) : Bethe.densityNorm Δcrit hΔcrit
      (fun x => Bethe.rootStepDensity (N i) (N i / 2) (rootsP i) (hrootsPmem i)
        (hnP i) (hsizeP i) x - Bethe.rho Δcrit x) (hbp i) ≤ Kp / N i :=
    (Dp i).density_bound
  have hnormQ (i : ℕ) : Bethe.densityNorm Δcrit hΔcrit
      (fun x => Bethe.rootStepDensity (N i) (N i / 2 - r) (rootsQ i) (hrootsQmem i)
        (hnQ i) (hsizeQ i) x - Bethe.rho Δcrit x) (hbq i) ≤ Kq / N i :=
    (Dq i).density_bound
  let K : ℝ := max Kp Kq
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hrate : ∀ᶠ i : ℕ in atTop,
      Bethe.densityNorm Δcrit hΔcrit
        (fun x => Bethe.rootStepDensity (N i) (N i / 2) (rootsP i) (hrootsPmem i)
          (hnP i) (hsizeP i) x - Bethe.rho Δcrit x) (hbp i) ≤ K / N i ∧
      Bethe.densityNorm Δcrit hΔcrit
        (fun x => Bethe.rootStepDensity (N i) (N i / 2 - r) (rootsQ i) (hrootsQmem i)
          (hnQ i) (hsizeQ i) x - Bethe.rho Δcrit x) (hbq i) ≤ K / N i := by
    filter_upwards with i
    constructor
    · exact hnormP i |>.trans (div_le_div_of_nonneg_right
        (le_max_left Kp Kq) (by positivity))
    · exact hnormQ i |>.trans (div_le_div_of_nonneg_right
        (le_max_right Kp Kq) (by positivity))

  have hSdata : ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Bethe.lamOf Δcrit)) atTop (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
         else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
           ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) /
          BetheAnsatz.eigenvalueRegular c (rootsP i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) *
          (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) := by
    by_cases hrEven : r % 2 = 0
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_even_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate
        hrEven hr hcΔ
      refine ⟨S, hS, ?_⟩
      simpa [hrEven] using hratio
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_odd_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK hrate
        hrEven hr hcΔ
      refine ⟨S, hS, ?_⟩
      simpa [hrEven] using hratio
  obtain ⟨S, hS, hratio⟩ := hSdata
  have hIdentity := PottsDiscontinuity.identity44
    (Real.arcosh (Real.sqrt q / 2)) hlam
  obtain ⟨S₀, T₀, hS₀, hT₀, hpositive, hvalue⟩ := hIdentity
  have hS₀' : Tendsto (PottsDiscontinuity.altTanhPartial
      (Real.arcosh (Real.sqrt q / 2)))
      atTop (𝓝 S₀) := by
    change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * Real.arcosh (Real.sqrt q / 2)))
      atTop (𝓝 S₀)
    exact hS₀
  have hS' : Tendsto (PottsDiscontinuity.altTanhPartial
      (Real.arcosh (Real.sqrt q / 2)))
      atTop (𝓝 S) := by
    simpa [hlamEq] using hS
  have hSS : S = S₀ := tendsto_nhds_unique hS' hS₀'

  have hPFtop (i : ℕ) : BetheAnsatz.eigenvalueRegular c (rootsP i) =
      ((PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c (N i / 2)) : ℝ) : ℂ) := by
    have hparity : Even (N i / 2) := by
      refine ⟨i + B, ?_⟩
      rw [hhalf]
      omega
    have hc : 2 < c := by
      change 2 < Real.sqrt (2 + Real.sqrt q)
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hsqrtq]
    have hratio := Bethe.ratio_eigenvalueRegular hc (hrootsPmem i)
    have hreal : BetheAnsatz.eigenvalueRegular c (rootsP i) =
        ((SixVertex.cor34BetheLambda (N i) (N i / 2) c (rootsP i) : ℝ) : ℂ) := by
      simpa [SixVertex.cor34BetheLambda, hparity] using hratio
    have hindex : Lambda c (N i) 0 =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c (N i / 2)) := by
      unfold Lambda
      simp
    calc
      _ = ((SixVertex.cor34BetheLambda (N i) (N i / 2) c (rootsP i) : ℝ) : ℂ) := hreal
      _ = ((Lambda c (N i) 0 : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) (Dp i).lambda_eq
      _ = ((PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2)) : ℝ) : ℂ) := by rw [hindex]
  have hPFbottomEven (i : ℕ) (hrEven : r % 2 = 0) :
      BetheAnsatz.eigenvalueRegular c (rootsQ i) =
        ((PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)) : ℝ) : ℂ) := by
    have hparity : Even (N i / 2 - r) := by
      refine ⟨(N i / 2 - r) / 2, ?_⟩
      rw [hhalf]
      omega
    have hc : 2 < c := by
      change 2 < Real.sqrt (2 + Real.sqrt q)
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hsqrtq]
    have hratio := Bethe.ratio_eigenvalueRegular hc (hrootsQmem i)
    have hreal : BetheAnsatz.eigenvalueRegular c (rootsQ i) =
        ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := by
      simpa [SixVertex.cor34BetheLambda, hparity] using hratio
    have hindex : Lambda c (N i) r =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)) := by
      unfold Lambda
      rfl
    calc
      _ = ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := hreal
      _ = ((Lambda c (N i) r : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) (Dq i).lambda_eq
      _ = ((PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2 - r)) : ℝ) : ℂ) := by rw [hindex]
  have hPFbottomOdd (i : ℕ) (hrOdd : r % 2 ≠ 0) :
      BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩ =
        ((PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)) : ℝ) : ℂ) := by
    have hparity : ¬ Even (N i / 2 - r) := by
      intro heven
      rcases heven with ⟨k, hk⟩
      have hpar : (N i / 2 - r) % 2 = r % 2 := by rw [hhalf]; omega
      have hzero : (N i / 2 - r) % 2 = 0 := by omega
      exact hrOdd (hpar.symm.trans hzero)
    let qcenter : ℕ := (N i / 2 - r) / 2 + 1
    have hnq : N i / 2 - r + 1 = 2 * qcenter := by
      dsimp [qcenter]
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hparity
      omega
    have hindex : qcenter - 1 = (N i / 2 - r) / 2 := by
      dsimp [qcenter]
    let l : Fin (N i / 2 - r) :=
      ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩
    have hcenter : rootsQ i l = 0 := by
      simpa [l, hindex] using
        (cor34_odd_S_n_center_zero (hrootsQmem i) hnq)
    have hc : 2 < c := by
      change 2 < Real.sqrt (2 + Real.sqrt q)
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hsqrtq]
    have hratio := Bethe.ratio_eigenvalueZero (N := N i) hc (hrootsQmem i) l hcenter
    have hreal : BetheAnsatz.eigenvalueZero (N i) c (rootsQ i) l =
        ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := by
      simpa [SixVertex.cor34BetheLambda, hparity, qcenter, l, hindex] using hratio
    have hindexLambda : Lambda c (N i) r =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)) := by
      unfold Lambda
      rfl
    calc
      _ = ((SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i) : ℝ) : ℂ) := hreal
      _ = ((Lambda c (N i) r : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) (Dq i).lambda_eq
      _ = ((PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2 - r)) : ℝ) : ℂ) := by rw [hindexLambda]
  have hPFnum (i : ℕ) :
      (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
       else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
         ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) =
        ((PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)) : ℝ) : ℂ) := by
    by_cases hrEven : r % 2 = 0
    · simp only [hrEven, ite_eq_left]
      exact hPFbottomEven i hrEven
    · simp only [hrEven]
      exact hPFbottomOdd i hrEven
  have hquot (i : ℕ) :
      (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
       else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
         ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) /
        BetheAnsatz.eigenvalueRegular c (rootsP i) =
      (((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) := by
    rw [hPFnum i, hPFtop i]
    simp only [Lambda]
    push_cast
    rfl
  have hcomplex : Tendsto (fun i : ℕ =>
      ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) *
        (Bethe.lamOf Δcrit + 2 * S₀)) : ℝ) : ℂ)) := by
    have htarget : Tendsto (fun i : ℕ =>
        ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) *
          (Bethe.lamOf Δcrit + 2 * S)) : ℝ) : ℂ)) := by
      apply hratio.congr
      intro i
      exact hquot i
    simpa [hSS] using htarget
  have hcomplexExp : Tendsto (fun i : ℕ =>
      ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 (Complex.exp (-(r : ℂ) *
        ((Bethe.lamOf Δcrit : ℂ) + 2 * (S₀ : ℂ))))) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hcomplex
  have hrealComplex : Tendsto (fun i : ℕ =>
      Complex.re (↑(Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 (Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S₀)))) := by
    have ht := Complex.continuous_re.continuousAt.tendsto.comp hcomplexExp
    change Tendsto (fun i : ℕ =>
      Complex.re (↑(Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝 ((Complex.exp (-(r : ℂ) *
        ((Bethe.lamOf Δcrit : ℂ) + 2 * (S₀ : ℂ)))).re)) at ht
    have hexp : (Complex.exp (-(r : ℂ) *
        ((Bethe.lamOf Δcrit : ℂ) + 2 * (S₀ : ℂ)))).re =
        Real.exp (-(r : ℝ) * (Bethe.lamOf Δcrit + 2 * S₀)) := by
      simp [Complex.exp_re]
    rw [hexp] at ht
    exact ht
  have hRe : (fun i : ℕ =>
      Complex.re (↑(Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) =
      (fun i : ℕ => Lambda c (N i) r / Lambda c (N i) 0) := by
    funext i
    simp
  rw [hRe] at hrealComplex
  have hreal : Tendsto (fun i : ℕ => Lambda c (N i) r / Lambda c (N i) 0)
      atTop (𝓝 (Real.exp (-(r : ℝ) *
        (Bethe.lamOf Δcrit + 2 * S₀)))) := hrealComplex
  have hlamValue : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) := hlamEq
  refine ⟨B, S₀, ?_, ?_⟩
  · change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / k * Real.tanh (k * Real.arcosh (Real.sqrt q / 2)))
      atTop (𝓝 S₀)
    exact hS₀
  · simpa [N, c, hlamValue] using hreal

end PottsDiscontinuity.RCMProof
