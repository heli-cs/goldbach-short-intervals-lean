# Goldbach short intervals in Lean

This project verifies three results in Lean 4 under the Riemann hypothesis (RH).

| Lean theorem | Statement |
| --- | --- |
| `goldbach_short_interval_explicit` | For every real $x\ge 5$, two odd primes have a sum in $(x,x+(\log x)^2]$. |
| `goldbach_short_interval_max` | For every real $x\ge 4$, the width $\max\{2,(\log x)^2\}$ suffices. |
| `goldbach_log_sq_optimal` | For all real $x\ge 4$, the least uniform coefficient of $(\log x)^2$ is $2/(\log 4)^2$. |

See the exact statements in [RemainingCoverage.lean](Goldbach/Explicit/RemainingCoverage.lean).

## Proof and certificates

The analytic argument uses weighted reflection and explicit-formula variance estimates for $x\ge e^{28}$. The finite proof checks prime certificates and combines two sequences of prime intervals to cover $[5,1.5\times10^{12})$. Lean verifies the overlap and assembles the final theorems. [Analytic theorem](Goldbach/Explicit/LargeRange.lean) · [Finite coverage](Goldbach/Explicit/IntervalCutoff.lean)

The recorded build passed 8,911 jobs. The recorded fresh kernel replay checked 478,270 declarations in the combined dependency closure and reported only `propext`, `Classical.choice` and `Quot.sound`. [Build log](notes/explicit-verification.log) · [Replay log](notes/explicit-kernel-replay.log) · [Certificate generation and build measurements](notes/cutoff28-certificates.log)

## Build and replay

Install Git and [elan](https://github.com/leanprover/elan). The project pins the Lean toolchain and the Mathlib and Zeta23 dependencies. Run these commands from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.33.0-rc2
lake exe cache get Mathlib
lake build +Goldbach +Goldbach.Check +Goldbach.Explicit.Check
lake env lean --run Goldbach/Replay.lean Goldbach.Explicit.RemainingCoverage remainingGoldbachIntervalCoverage goldbach_short_interval_explicit goldbach_short_interval_max goldbach_log_sq_optimal goldbach_short_interval_certified_prefix_to_cutoff goldbach_short_interval_explicit_of_exp28 goldbach_log_sq_real_cover_iff_even
```

The verified certificate sources are included. To regenerate the sixteen cutoff blocks in a separate checkout, run `python scripts/generate_cutoff_cover.py` with Python 3.10 or later. The certificate generation log records the source hashes and timing.

## Attribution

The analytic argument builds on Anton Vynohradov's compact-kernel approach and He Li's independent first-moment refinement. Vynohradov credits the refinement in §1.1 and reference [10] of v2. The project was developed with AI assistance. [Vynohradov v2](https://hexagonmath.org/2611.00885v2) · [He Li's first-moment refinement](https://github.com/anser-software/goldbach-numbers-in-short-intervals/issues/1)
