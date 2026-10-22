# Local verification environment

The installed official runtime was Lean 4.33.0-rc1, with Mathlib pinned at
79d0395a1825a6264ad5d269e35e60537518955e. The exact version string and the
successful final build/audit logs are under `verification/latest/`.

All project modules were compiled from source in a fresh project build.
Pinned dependency artifacts were reused; this is not a claim that Mathlib
and Lean themselves were rebuilt from source in this run.

This execution host exposes `/proc/self/exe` but not the equivalent numeric
`/proc/<getpid()>/exe` lookup used by Lean's runtime path discovery. A narrowly
scoped libc `readlink` compatibility shim redirects only that current-process
lookup. Its source is `runtime/proc_self_compat.c`. It does not modify theorem
elaboration, the kernel, proof terms, or the original runtime binary/library.
Normal Linux installations do not require this shim.

The inherited runtime also uses two shell launchers: the outer scheduling gate
was inactive, and the inner launcher invokes the unmodified official binary
with Lean's `-j2` option. The actual compiler is `bin/lean.official`; the file
named `bin/lean` is the outer shell launcher. The launchers were inspected
before packaging, and the original compiler and shared-library hashes were
verified. These launchers are not part of the distributable project.

Original runtime SHA256 values:

| Component | SHA256 |
|---|---|
| Official compiler, locally `bin/lean.official` | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
| `lib/lean/libleanshared.so` | `f0826691c9f73b43dc640b90994b3939af33fb877d8f95105516ac1d2a27340d` |

The optional `LEAN_LAUNCHER` environment variable in `scripts/verify.py`
supports such host-specific command wrappers. It is unnecessary for the
ordinary reproduction commands in the README. Runtime binaries, dependency
caches, absolute-path launchers and build artifacts are excluded from the
deliverable.
