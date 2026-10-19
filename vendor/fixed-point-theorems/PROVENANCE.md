# Vendored: fixed-point-theorems (Brouwer's fixed-point theorem)

The proof of Theorems 1.1 and 1.2 uses Brouwer's fixed-point theorem
(`brouwer_fixed_point`, applied once in
`PottsDiscontinuity/Duality/RectanglePathIntersection.lean` to show that two crossing paths of a
rectangle intersect). Mathlib v4.35.0 does not contain this theorem, so the five modules of
<https://github.com/harfe/fixed-point-theorems-lean4> that prove it are vendored here.

- Upstream repository: https://github.com/harfe/fixed-point-theorems-lean4
- Upstream commit: `770940ddf9878cf61952ed53d910b92bca841838`
- Licence: MIT, copyright (c) 2026 harfe — see `LICENSE` in this directory. The licence of this
  repository (Apache-2.0) does not apply to these files.
- Files: `FixedPointTheorems/{brouwer,apply_cubical_sperner,convex_homeos,cubical_sperner,cubical_sperner_prep}.lean`
  (the upstream `kakutani.lean` is not used and not included).

Changes relative to the upstream commit (no change to any statement):

1. compatibility edits for recent Lean and Mathlib (deprecated names, `import Mathlib`, proof
   repairs), first made for Lean v4.34.1 and then for Lean v4.35.0 / Mathlib v4.35.0;
2. a mechanical port to the Lean module system (`module`, `public import`,
   `@[expose] public section`), required because every Lean file in a Palomar submission must be a
   module.
