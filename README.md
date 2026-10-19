# PottsDiscontinuity-lean

[![Build and axiom audit](https://github.com/zijie123123/PottsDiscontinuity-lean/actions/workflows/build.yml/badge.svg)](https://github.com/zijie123123/PottsDiscontinuity-lean/actions/workflows/build.yml)
[![Comparator](https://github.com/zijie123123/PottsDiscontinuity-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/zijie123123/PottsDiscontinuity-lean/actions/workflows/comparator.yml)

A complete Lean 4 / Mathlib formalization of the two main theorems of

> H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu and V. Tassion,
> **Discontinuity of the phase transition for the planar random-cluster and Potts models with q > 4**,
> [arXiv:1611.09877v2](https://arxiv.org/abs/1611.09877v2); published in
> Ann. Sci. Éc. Norm. Supér. (4) **54** (2021), no. 6, 1363–1413.

Theorem 1.1 (the q-state Potts model, q > 4) and Theorem 1.2 (the random-cluster model, q > 4) are
proved in Lean with no `sorry` and no axioms beyond Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). The external results that the paper cites and the
proof uses (Edwards–Sokal coupling, FKG and comparison inequalities, finite energy, ergodicity and
the 0–1 law for infinite clusters, planar self-duality, the coordinate Bethe ansatz of the companion
paper [8], Perron–Frobenius, the analytic implicit function theorem, …) are proved here or taken from
Mathlib; nothing is assumed. Uniqueness of the infinite cluster (Burton–Keane), which the paper cites,
is not needed. Brouwer's fixed-point theorem, used once to make two crossing paths of a rectangle
intersect, comes from the vendored library `vendor/fixed-point-theorems`.

Formalized by Zijie Zhuang ([GitHub: zijie123123](https://github.com/zijie123123),
[homepage](https://zijie123123.github.io/)), with AI agents; see [Provenance](#provenance-and-use-of-ai).

## The results

Throughout, `x_n` is the site of ℤ² with both coordinates equal to ⌊n/2⌋, `β_c(q) = log(1 + √q)` and
`p_c(q) = √q / (1 + √q)`.

**Theorem 1.1 (paper, p. 2).** For the q-state Potts model on ℤ² with q > 4:
1. all the measures `μ^i_{β_c}`, i = 0,…,q, are distinct and ergodic (in particular `μ^0_{β_c}` is not
   the average of the `μ^i_{β_c}`, i ≥ 1);
2. for every i ∈ {1,…,q}, `μ^i_{β_c}[σ_0 = i] > 1/q`;
3. if λ > 0 satisfies cosh λ = √q / 2, then
   `lim_n −(1/n) log(μ^0_{β_c}[σ_0 = σ_{x_n}] − 1/q) = λ + 2 Σ_{k≥1} (−1)^k tanh(kλ)/k`,
   and this quantity is strictly positive.

**Theorem 1.2 (paper, p. 4).** For the random-cluster model on ℤ² with q > 4:
1. `φ^1_{p_c,q} ≠ φ^0_{p_c,q}`;
2. `φ^1_{p_c,q}[there exists an infinite cluster] = 1`;
3. if λ > 0 satisfies cosh λ = √q / 2, then
   `lim_n −(1/n) log φ^0_{p_c,q}[0 ↔ x_n] = λ + 2 Σ_{k≥1} (−1)^k tanh(kλ)/k`   (1.2);
   furthermore the right-hand side is positive and, as q ↘ 4,
   `λ + 2 Σ_{k≥1} (−1)^k tanh(kλ)/k = Σ_{k≥0} 4 / ((2k+1) sinh(π²(2k+1)/(2λ))) ∼ 8 exp(−π²/√(q−4))`   (1.3).

### The Lean statements

The trusted statement surface is [`Challenge.lean`](Challenge.lean) (284 lines, Mathlib only): it
contains the three theorems below and the 17 definitions they use, each with a docstring. The same
declarations are proved in [`PottsDiscontinuity/`](PottsDiscontinuity/) and exposed by
[`Solution.lean`](Solution.lean); Comparator checks that names, types and definitions agree.

```lean
/-- Theorem 1.1 (arXiv:1611.09877v2, p. 2). -/
theorem potts_theorem_1_1 (q : ℕ) (hq : 4 < q) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S)

/-- Theorem 1.2, items 1–3 including (1.2) (arXiv:1611.09877v2, p. 4). -/
theorem rc_theorem_1_2 (q : ℝ) (hq : 4 < q) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S)))

/-- Theorem 1.2, the final assertions: positivity of the right side of (1.2) and (1.3)
(arXiv:1611.09877v2, p. 4). Here `λ = arcosh(√q / 2)`. -/
theorem rc_theorem_1_2_positivity_eq_1_3 :
    (∀ q : ℝ, 4 < q → ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∃ S T : ℝ,
        Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
        HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
        0 < lam + 2 * S ∧ lam + 2 * S = T) ∧
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4))))
```

All three live in the namespace `PottsDiscontinuity`.

### How the paper's objects are represented

These choices were fixed and reviewed before any proof was written (rulings R1–R10 of the project);
several of them are also recorded in the docstrings of `Challenge.lean`.

- **R1 – infinite-volume measures along boxes.** `μ^i_β` and `φ^i_{p,q}` are limits along the boxes
  `Λ_n = [−n, n]²` (induced subgraphs of ℤ²), rather than along an arbitrary exhaustion "as G tends to
  ℤ²". The Potts Hamiltonian is the paper's literal one, with one boundary term per vertex of `∂Λ_n`.
- **R2 – weak convergence** is expressed as convergence of all finite-dimensional cylinder
  probabilities (equivalent on these compact product spaces).
- **R3 – existence packaging.** The theorems assert the existence of probability measures that are
  such cylinder limits and satisfy the conclusions. Existence of the box limits (stated but not proved
  in the paper, in particular for the literal Potts boundary term) is therefore part of what is
  proved; uniqueness of cylinder limits is also proved
  (`PottsDiscontinuity/Infra/CylinderUniqueness.lean`), so the existential packaging leaves no
  freedom in the choice of the measures.
- **R4 – explicit critical values.** `β_c = log(1+√q)` and `p_c = √q/(1+√q)` are used as explicit
  values (the paper takes them from [BefDum12]); the statement that they *are* the critical points is
  not part of the formalized theorems.
- **R5 – carriers.** Potts spins take values in `Set.Icc 1 q ⊆ ℕ`; Potts boundary conditions
  `i ∈ {0,…,q}` are `Fin (q+1)` (0 = free); random-cluster boundary conditions are `Fin 2`.
- **R6 – ergodicity** means invariance under all translations of ℤ² and that every
  translation-invariant measurable event is null or conull.
- **R7 – the alternating series** `Σ_{k≥1} (−1)^k tanh(kλ)/k` is encoded by the limit `S` of its
  ordered partial sums; the positive series in (1.3) uses `HasSum`/`tsum`.
- **R8 – (1.3)** is the exact identity `λ + 2S = Σ_{k≥0} 4/((2k+1) sinh(π²(2k+1)/(2λ)))` for every
  q > 4, together with `Asymptotics.IsEquivalent` along `𝓝[>] 4`, where `λ(q) = arcosh(√q/2)`.
- **R9 – splitting.** Theorem 1.1 is one Lean theorem; Theorem 1.2 is split into
  `rc_theorem_1_2` (items 1–3 and (1.2)) and `rc_theorem_1_2_positivity_eq_1_3` (positivity and
  (1.3)). The two parts share no witness (λ and S are determined by q).
- **R10 – finite volumes** are induced subgraphs on finite vertex sets V, with `∂V` the vertices of
  V having a neighbour of ℤ² outside V.
- **Logarithms.** Lean's `Real.log x` is `log |x|` (and `log 0 = 0`). The limit statements in
  Theorem 1.1(3) and Theorem 1.2(3) therefore do not by themselves assert that
  `μ^0_{β_c}[σ_0 = σ_{x_n}] − 1/q` and `φ^0_{p_c,q}[0 ↔ x_n]` are positive, which the paper's notation
  presupposes; they assert the stated limit of `−(1/n) log` of these quantities.

### Corrections to the paper's arguments

The formalization proves the stated theorems; along the way several steps of the published argument
had to be repaired. None affects the statements of Theorems 1.1 and 1.2. The repairs include:

- **Lemma 3.15:** the event C in the proof does not force U = 1 as claimed (it fails for
  N = M = 8, n = 1); the proof uses a corrected local connection event C′ instead.
- **Lemma 3.14** is proved in a corrected `limsup` form, with one additional input: the free one-arm
  probability on the rotated lattice tends to 0. This input is proved separately, from the positive
  lower bound on the inverse correlation length ((3.24) and identity (4.4)).
- **Section 3.3:** the dominance of Λ₀ over all sectors, which the argument uses without proof, is
  proved separately from (3.16), Corollary 3.13(iii) and the corrected Lemma 3.14.
- **Lemma 3.2:** the identity `Z(M) = Tr((V^[n]_∞)^M)` fails for r ≥ 2 (e.g. N = 8, r = 2, M = 4); the
  lemma's conclusion holds and is proved by a different count.
- **Corollary 3.4:** analyticity is available only on `[−∞, Δ₀)` while the conclusion is used at
  `Δ₀`; the endpoint is handled separately.
- **(3.8):** `ℓ′` has a logarithmic singularity at 0, so the weak-convergence step needs an extra
  truncation estimate.
- The absence of percolation for `φ^0_{p_c}` (q > 4) is derived from the finite correlation length
  rather than from Zhang's argument.
- Misprints are corrected where the proof uses them (e.g. the relation between `p_c` and `β_c` in
  the coupling section, and the factor `1 − 1/q` in the consequences of the Edwards–Sokal coupling),
  as are some steps of the companion paper [8] that are formalized in `BetheAnsatz/`.

## Repository layout

| Path | Contents |
|---|---|
| [`Challenge.lean`](Challenge.lean) | statement surface: 17 definitions and the 3 theorems, proofs `sorry` (Mathlib only) |
| [`Solution.lean`](Solution.lean) | imports the proof development; provides the proved declarations |
| [`comparator.json`](comparator.json) | Comparator configuration: the 3 theorems; the 17 definitions their statements use are compared in full (there are no definition holes) |
| [`PottsDiscontinuity/`](PottsDiscontinuity/) | the proof development, 873 modules — see [`PottsDiscontinuity/OVERVIEW.md`](PottsDiscontinuity/OVERVIEW.md) |
| [`PottsDiscontinuity.lean`](PottsDiscontinuity.lean) | entry point: imports exactly the three main theorems |
| [`Axioms.lean`](Axioms.lean) | axiom audit of the three main theorems |
| [`vendor/fixed-point-theorems/`](vendor/fixed-point-theorems/) | Brouwer's fixed-point theorem (MIT, vendored; see its `PROVENANCE.md`) |
| [`formalization.yaml`](formalization.yaml) | Palomar / formalization.yaml v0.4 metadata |
| [`paper/`](paper/) | link to the paper and the SHA-256 of the PDF used (the PDF itself is not redistributed) |
| [`scripts/`](scripts/) | source checks, Comparator run, metadata validation, paper download |

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` (**Lean v4.35.0**) and Mathlib is pinned to tag **v4.35.0** in `lake-manifest.json`.

```bash
lake exe cache get          # download compiled Mathlib
lake build                  # build PottsDiscontinuity, Challenge and Solution
lake env lean Axioms.lean   # axiom audit
```

Expected output of the axiom audit:

```
'PottsDiscontinuity.potts_theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PottsDiscontinuity.rc_theorem_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PottsDiscontinuity.rc_theorem_1_2_positivity_eq_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Further checks:

```bash
python3 scripts/check-lean-sources.py        # every .lean file is a module and has ≤ 10,000 lines
ruby scripts/validate-formalization.rb       # formalization.yaml has no template values
./scripts/verify-comparator.sh               # Comparator, with the toolchain's NanoDa and con-ron
                                             # kernels (Linux; needs bubblewrap)
```

`Challenge.lean` is expected to report three `declaration uses 'sorry'` warnings; nothing else in
the repository uses `sorry`.

## Provenance and use of AI

The formalization was produced on 2026-10-18/19 by an agent workflow directed by the author: Claude
Code (Claude Opus 5.5) as orchestrator, OpenAI Codex agents (gpt-6-luna, gpt-6.1-sol, gpt-6-astra) as
proof workers, and Claude Sonnet agents as independent reviewers. The statements of the main theorems
and their 17 definitions were transcribed from the paper, reviewed independently by two reviewer
agents against the paper, approved by the author, and then frozen; only proofs were developed
afterwards. The status is **agent-reviewed**: the Lean proofs are checked by Lean (and, via
Comparator, by independent kernels), but no human mathematician has refereed the formal development.

About 170 modules (finite FK-model foundations, planar duality and discrete topology) are adapted
from an earlier, unpublished formalization of the planar FK model by the same author; each such file
says so in its header. The development was carried out on Lean v4.34.1 and ported for this release
to Lean v4.35.0 / Mathlib v4.35.0 and the Lean module system. The port changed no statement of the
main theorems or of their 17 definitions (their text is identical up to the namespace prefix
`Research.PottsDiscontinuity` → `PottsDiscontinuity`); it made helper declarations public where
the module system requires it, renamed a few internal helper declarations, and adapted a handful of
proofs to the new Lean and Mathlib versions.

## Licence and citation

The Lean code in this repository is released under the [Apache License 2.0](LICENSE). The vendored
`vendor/fixed-point-theorems` keeps its MIT licence. The paper is © its authors and is not included.

If you use this formalization, please cite the paper above and this repository. The companion paper
[8] is H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu and V. Tassion, *The Bethe ansatz for
the six-vertex and XXZ models: an exposition*, [arXiv:1611.09909](https://arxiv.org/abs/1611.09909).

This repository is prepared for submission to [Palomar](https://palomar-registry.org/), a registry of
Lean-verified mathematics (submission form: https://submit.palomar-registry.org/).
