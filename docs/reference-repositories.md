# Reference repository audit

Read-only review on 2026-10-22 through the GitHub connector. This is a review of
source/configuration and available CI evidence, not a fresh local rebuild.

## BCSI

- Repository: https://github.com/congma1028/bcsi-lean-verification
- Inspected commit: `e5e0cc33db70300520e3d1f93675869780ddeb55`.
- Lean: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib manifest commit: `79d0395a1825a6264ad5d269e35e60537518955e`.
- `UpperBound.lean` and `LowerBound.lean` are explicit public roots and are also
  the Lake default targets. They use both `#check` and `#print axioms` on the
  paper-facing conclusions.
- The source explicitly documents quantifier order and normalization, including
  constants chosen before dimensions and model parameters.
- The actual GitHub Actions workflow uses `leanprover/lean-action@v1`.
- Run https://github.com/congma1028/bcsi-lean-verification/actions/runs/33897240260
  succeeded at the inspected commit. Job `101102641496` logs were retrieved.
  They report the final upper and lower bound axiom dependencies as
  `[propext, Classical.choice, Quot.sound]` and end with
  `Build completed successfully (9553 jobs)`. No `sorryAx` or `error:` occurred
  in the retrieved log.

## PassK

- Repository: https://github.com/chandramaulichak108/passk-lean
- Inspected commit: `2c4142984969762526bb28d3be35361314be647a`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib manifest commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `PassK.lean` imports the foundational and staged development modules and
  explicitly says the full manuscript is not yet formalized.
- `PROOF_STATUS.md` is unusually clear about conditional reductions, missing
  algorithm-specific hypotheses, and unexecuted new source. Its dated scope
  statement says the expanded modules were authored and statically inspected
  but not executed by Lean.
- README links `.github/workflows/lean.yml` and claims a workflow runs builds;
  the linked file returns 404 and the Actions API reports zero workflow runs.
  Therefore the README CI statement should not be treated as verified evidence.
- The recommended `lake update` may alter dependency revisions and is not the
  strongest reproducibility command when a manifest already exists.

## Conventions to adopt for the Gaussian-mixture project

1. Pin Lean and the full Lake manifest; record source-PDF SHA256 and manuscript
   version/date so theorem correspondence cannot silently drift.
2. Give each paper theorem/lemma an exact public declaration and an audit root
   that imports its entire transitive project closure.
3. Distinguish theorem proved from model hypotheses, conditional reduction,
   statement only, and uncompiled draft. A proof of `A -> B` does not establish
   paper result B until the model supplies A.
4. Run `#check` and `#print axioms` on all public results. Permit only the standard
   Lean foundational axioms `propext`, `Classical.choice`, `Quot.sound`; reject
   `sorryAx` and project-specific axioms in the dependency closure.
5. Use source scans only as supplementary checks. They do not detect all hidden
   assumptions and do not prove that the theorem states the paper claim.
6. Keep a theorem-by-theorem coverage table including exact hypotheses,
   constants, quantifier order, definitions, formal source names, build status,
   and undischarged analytic obligations.
7. Preserve full build/audit logs. A green CI result alone can conceal an
   omitted target; verify the exact endpoint declarations are actually built.
8. Separate complete imported code from experimental or unfinished modules.
   Do not use an abstract hypothesis bundle to conceal a missing analytic proof.
