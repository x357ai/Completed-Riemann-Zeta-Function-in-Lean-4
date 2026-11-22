# Completed Riemann Zeta Function in Lean 4

Machine-checked Lean 4 formalization of explicit zero-free bounds and transverse Cauchy-Riemann seam coupling for the completed Riemann zeta function $\xi(s)$ and Mathlib's `riemannZeta`, paired with independent Arb interval arithmetic verification.

## Author & Scope

* **Author:** Barry Lee Guevremont (X357-AI, Goldsboro, North Carolina)
* **Research Timeline:** Independent research notes initiated March 2025; Lean 4 formalization certified November 2026.
* **Epistemic Scope:** This repository formally verifies **local zero-free regions** and **local transverse off-axis exclusion around simple critical-line zeros**. It does not claim a global proof of the Riemann Hypothesis.

## Verified Theorems (Zero `sorryAx`)

All theorems compile cleanly under `lake build` and depend strictly on `[propext, Classical.choice, Quot.sound]`:

1. **Critical-Strip Zero-Free Box (`MyMathProject.lean`):**
   `Guevremont.riemannZeta_ne_zero_on_criticalStripBox_five` proves $\zeta(s) \neq 0$ for all $s \in (0, 1) + i[-5, 5]$.
2. **Completed Zeta Lower Bound (`XiRectangleBound.lean`):**
   * `norm_completedRiemannZeta₀_le_two_div_57`: $\|\Lambda_0(s)\| \le \frac{2}{57}$ on $-1 \le \operatorname{Re}(s) \le 2$.
   * `riemannXi_ge_one_div_19_on_criticalStripBox_five`: $|\xi(s)| \ge \frac{1}{19}$ on $[0, 1] + i[-5, 5]$.
   * `riemannXi_ge_two_fifths_on_targetRect`: $|\xi(s)| \ge \frac{2}{5}$ on $[3/5, 4/5] + i[9/10, 11/10]$.
3. **Transverse Seam Coupling (`SeamCoupling.lean`):**
   * `riemannXi_mirror`: $\xi(1 - \bar{s}) = \overline{\xi(s)}$.
   * `riemannXi_orthogonal_gradient_transfer`: Along $\sigma = 1/2$, $\partial_\sigma \operatorname{Re}(\xi) = 0$ and $\partial_\sigma \operatorname{Im}(\xi) = -\partial_t \operatorname{Re}(\xi)$.
   * `riemannZeta_local_off_axis_zero_exclusion`: Local off-axis zero exclusion in a horizontal neighborhood of any $t_0$ where $\partial_t \Xi(t_0) \neq 0$.

## How to Verify Locally

    git clone https://github.com/x357ai/Completed-Riemann-Zeta-Function-in-Lean-4.git
    cd Completed-Riemann-Zeta-Function-in-Lean-4
    lake exe cache get
    lake build

The published project pins Lean `v4.33.1` and Mathlib `v4.33.1`; the exact Mathlib commit is recorded in `lake-manifest.json`. To display the theorem-level axiom reports explicitly, run:

```bash
lake env lean SeamCoupling.lean
lake env lean XiRectangleBound.lean
lake env lean MyMathProject.lean
```

The source at commit `4329cab81b9c67514dc52fe7099da22eac92c1cc` has a successful [GitHub Actions build](https://github.com/x357ai/Completed-Riemann-Zeta-Function-in-Lean-4/actions/runs/45019477968). This records a build using the repository's pinned environment; it does not report a separate independent-kernel replay.

## Reproduce the Arb Certificate

Use a C compiler and a FLINT installation providing `flint/acb_dirichlet.h`, together with the required GMP and MPFR development libraries. With those libraries available on the compiler's standard search paths:

```bash
cc -O2 -std=c11 -Wall -Wextra certify_xi_arb.c \
  -o certify_xi_arb -lflint -lmpfr -lgmp
./certify_xi_arb
```

The program evaluates **4,096 whole complex boxes**, rather than only their centers, at 128-bit working precision. The input balls enclose rational grid cells whose union is `[3/5, 4/5] + i[9/10, 11/10]`; endpoint rounding is enclosed by the balls. Every box must pass the rigorous comparison against `2/5`.

Exit status `0` means all boxes certified the strict lower bound. Exit status `1` and `NOT CERTIFIED` mean at least one evaluation was invalid or insufficiently sharp; this is not by itself a counterexample to the mathematical bound. The reported minimum is an **interval enclosure**, not an exact minimum or a lower bound given by its midpoint.

For a reproducible numerical record, retain the source commit, compiler and FLINT versions, complete output, and exit status from the actual run. The C certificate is separate from the Lean proof; `lake build` does not run this C program.

## Key Files

* `MyMathProject.lean` — Top-level entry point proving `riemannZeta s ≠ 0` on $(0, 1) + i[-5, 5]$.
* `XiRectangleBound.lean` — Mellin integral folding over $(0, 1)$ and $(1, \infty)$ via `HurwitzZeta.hurwitzEvenFEPair 0`.
* `SeamCoupling.lean` — Mirror law, orthogonal gradient transfer, and local off-axis zero exclusion.
* `certify_xi_arb.c` — Independent Arb ball-arithmetic verification source.
* `CITATION.cff` — Citation metadata.

## Licensing

Copyright 2026 Barry Lee Guevremont, for original copyrightable contributions.

* Original Lean and C source code, build configuration, and software code snippets are licensed under the **Apache License 2.0**; see [`LICENSE`](LICENSE).
* The manuscript's LaTeX source and PDF, original figures, this README, and other original explanatory documentation are licensed under **Creative Commons Attribution 4.0 International (CC BY 4.0)**, excluding software code snippets covered above; see [`paper/LICENSE`](paper/LICENSE) and the [license summary](https://creativecommons.org/licenses/by/4.0/).
* Third-party material and dependencies retain their own licenses and applicable notices. These grants apply only to rights held by the author.

The licenses apply to the identified materials separately. Both permit commercial reuse subject to their respective terms. Attribution and citation details are provided in [`CITATION.cff`](CITATION.cff).
