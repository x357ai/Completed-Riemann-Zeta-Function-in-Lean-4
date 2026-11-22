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

## Key Files

* `MyMathProject.lean` — Top-level entry point proving `riemannZeta s ≠ 0` on $(0, 1) + i[-5, 5]$.
* `XiRectangleBound.lean` — Mellin integral folding over $(0, 1)$ and $(1, \infty)$ via `HurwitzZeta.hurwitzEvenFEPair 0`.
* `SeamCoupling.lean` — Mirror law, orthogonal gradient transfer, and local off-axis zero exclusion.
* `certify_xi_arb.c` — Independent Arb ball-arithmetic verification source.
* `CITATION.cff` — Citation metadata.
