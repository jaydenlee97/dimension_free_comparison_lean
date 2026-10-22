# Proof status

**Theorem 1 and Lemmas 1–6 are machine checked. Verification of every argument
in the manuscript's chosen proof route remains incomplete.**

This project formalizes Jeonghwan Lee and Cong Ma, *Dimension-free comparison
inequalities between f-divergences for Gaussian location mixtures*, supplied
as `version_final.pdf`, dated October 22, 2026. The detailed
[coverage table](docs/coverage.md) records the mathematical scope and remaining
proof-route distinctions. The [theorem map](docs/theorem-map.md) gives direct
links to the principal Lean declarations.

## What is proved

| Part of the paper | Checked scope |
|---|---|
| Theorem 1 | Both exact comparison constants, finiteness, both directed chi-square inequalities, every natural dimension, and arbitrary probability priors supported in a closed ball of radius M ≥ 0. |
| Lemmas 1–6 and Appendix A | Actual divergence derivatives and global C¹ regularity; Gaussian integration by parts; exact Gaussian envelope constants; dominated differentiation; density and likelihood-ratio regularity. The literal cubic-cutoff argument and its Fubini assembly are also checked. |
| Remark 1 | Gaussian example, positive ratio denominators, optimal-constant suprema, numerical bounds and stated asymptotics, with M > 0 for the ratio claims. |
| Observation and posterior | The law of tΘ+Z under an independent probability product model, an explicit posterior Markov kernel, and its mean as an actual conditional expectation. |
| Section 3 | The density PDE, generalized Fisher matrix, a directly proved general-generator identity under explicit regularity/growth assumptions, and all three concrete generator instances. Spatial boundary decay and local integrable first/second time-derivative bounds are proved. |

The main comparison theorem assumes supported probability priors, not analytic
certificates containing the desired derivative identities. The Gaussian
densities, derivatives, integrability and posterior formulas are constructed
and proved in the imported development. Squared Hellinger distance uses the
paper's unhalved convention.

## What is not claimed

The broad external Proposition 6 cited in Section 3 has not been formalized
for arbitrary PDE families and linear operators. The applicable Gaussian
identity is proved directly instead. Spatial boundary decay is stated as a
limit at infinity; it is not a separate theorem about surface-flux integrals
over expanding spheres. These are distinctions between checking a conclusion
and checking every step of the paper's alternative proof route.

Two manuscript qualifications are explicit in the formalization:

- Remark 1's distinct-prior ratios require M > 0. Theorem 1 also covers M = 0.
- The KL and Hellinger generators are C² on (0,∞), with continuous extensions
  at zero; they are not differentiable at zero. The mixture density ratios
  used in the proofs are strictly positive.

No admitted proposition or project-specific axiom represents outstanding work.
The machine-readable status deliberately records `whole_paper_complete: false`.
See the [mathematical audit](docs/mathematical-audit.md) for statement-level
qualifications and the [coverage table](docs/coverage.md) for exact scope.

## Verification evidence

The retained [local verification snapshot](verification/latest/status.json)
completed on **2026-10-22 at 13:55 UTC**, with a fresh project build:

| Check | Recorded result |
|---|---|
| Build and axiom audit | Both exited successfully |
| Public import closure | All 42 project source modules |
| Declarations inspected | 1,105, including 953 theorem declarations |
| Required manuscript endpoints | All 73 present and audited |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound` only |

The declaration counts include generated auxiliary declarations and do not
count manuscript theorems. The audit checks transitive axiom dependencies of
every loaded project declaration, including private generated declarations.
The verifier also rejects omitted project modules, missing required endpoints,
admissions and prohibited proof mechanisms. A text search alone is not proof
evidence, and successful compilation does not itself establish correspondence
with the manuscript.

The evidence includes [build output](verification/latest/build.log),
[displayed statements and axiom output](verification/latest/axioms-and-statements.log),
[per-theorem axiom dependencies](verification/latest/theorem-axioms.json), and
[Lean-source SHA256 values](verification/latest/source-sha256.json).
This is local verification evidence; GitHub Actions results are separate runs.

## Reproduce

Use Lean **v4.33.0-rc1** from [lean-toolchain](lean-toolchain) and the committed
[Lake manifest](lake-manifest.json). Mathlib is pinned to
`79d0395a1825a6264ad5d269e35e60537518955e`.

```bash
lake exe cache get
bash verify.sh --fresh
```

Run these commands from the repository root. `--fresh` removes only this
project's generated build outputs before rebuilding the public root and
running [Audit.lean](Audit.lean). It reuses pinned dependency artifacts;
it does not rebuild Lean or Mathlib from source. Do not run `lake update`
when reproducing this revision. The verifier writes a new local snapshot
under `verification/latest/`.

The [required endpoint list](verification/required-theorems.json) prevents
paper-facing theorems from silently disappearing from verification. The
[runtime note](docs/runtime.md) documents the compatibility shim used on the
original execution host; ordinary installations use the commands above.
