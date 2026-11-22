# Completed Riemann Zeta Function in Lean 4

Machine-checked Lean 4 verification of an explicit zero-free lower bound for the completed Riemann zeta function $\xi(s)$ on a compact rectangle in the critical strip, paired with independent Arb interval arithmetic verification.

## Verified Theorem

In `XiRectangleBound.lean`, the theorem `Guevremont.XiRectangleBound.riemannXi_ge_two_fifths_on_targetRect` formally certifies:

$$|\xi(s)| \ge \frac{2}{5} \quad \text{for all } s \in \left[\frac{3}{5}, \frac{4}{5}\right] + i\left[\frac{9}{10}, \frac{11}{10}\right].$$

### Proof Architecture & Axiom Audit
* **Track B (Lean 4 / Mathlib):** Built directly on Mathlib's `completedRiemannZeta₀` and `HurwitzZeta.hurwitzEvenFEPair 0`, folding the Mellin integral over $(0, 1)$ and $(1, \infty)$ and bounding the tail via `Real.exp` analysis.
* **Axiom Check:** Zero `sorryAx` and no custom axioms. `#print axioms` confirms dependence only on `[propext, Classical.choice, Quot.sound]`.
* **Track A (Arb Interval Verification):** Independent rigorous ball-arithmetic verification in `certify_xi_arb.c`.

## How to Verify Locally

    git clone https://github.com/x357ai/Completed-Riemann-Zeta-Function-in-Lean-4.git
    cd Completed-Riemann-Zeta-Function-in-Lean-4
    lake exe cache get
    lake env lean XiRectangleBound.lean

## Key Files

* `XiRectangleBound.lean` — Main formal proof and axiom check (`v1.0-track-b-verified`).
* `certify_xi_arb.c` — Track A Arb interval verification source.
* `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` — Pinned Lean 4 and Mathlib build configuration.

## Author

Barry Lee Guevremont (`x357ai`)
