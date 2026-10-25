# Lean 4 Formalization of Deterministic Zeroth-Order Nonconvex Lower Bounds

**Authors**: Yuxing Peng, Zhiqing Tang, Weijia Jia  
**Paper**: [arXiv:2610.27550](https://arxiv.org/abs/2610.27550)  
**License**: Apache-2.0 (see `LICENSE`)  
**Lean Version**: `leanprover/lean4:v4.19.0`  
**Mathlib Revision**: `c44e0c8ee63ca166450922a373c7409c5d26b00b`  

This directory contains the machine-checked formalization of the deterministic lower and upper bounds in Lean 4 accompanying the paper.

---

## 1. Overview and Formalized Statements

Let $d \ge 1$, $L, \Delta, \varepsilon > 0$, $1 \le E \le d$, and $T = L\Delta/\varepsilon^2 \ge 1$. For both the exact-value oracle and the rank-priced linear query oracle, the deterministic complexity $N_{\mathrm{det}}(\mathcal{B}^d_{L,\Delta,E})$ is finite and satisfies:

```math
d \le N_{\mathrm{det}} \le \min\bigl\{10dT,\; 100\sqrt{dET(d+T)}\bigr\},
```

```math
ET \le d \implies \frac{d}{2250}\min\Bigl\{T, \sqrt{\frac{ET}{\log(e+T)}}\Bigr\} \le N_{\mathrm{det}} \le 100\sqrt{2}\,d\sqrt{ET},
```

```math
E \ge T\log(e+T) \implies N_{\mathrm{det}} \ge \frac{dT}{2359296},
```

```math
T\log(e+T) \le E \le \frac{d}{T} \implies N_{\mathrm{det}} \ge \frac{dT}{2250}.
```

In addition, the randomized three-point method (Theorem B.8, `b:thm:stp`) achieves:

```math
N_{\mathrm{rand}}(\mathcal{B}^d_{L,\Delta,E}) \le 23ET.
```

These statements imply Theorem 3.2 (`thm:main-det`), the deterministic part of Corollary 3.3 (`cor:main-window`), and the upper bound of Theorem 3.1 (`thm:main-random`).

### Relation to Constants in the Paper
The formal proofs have the modular structure of Appendices B–E of the paper and use more conservative constants:
- The selection lemma (Lemma C.2, `a:lem:selection`) has constant $9$, where the paper has $13/3$.
- The main lower bound constant in the primary regime $ET \le d$ is $1/2250$, where the paper has $1/672$.
- The matched window lower bound constant is $1/2250$, and the trace-only window constant is $1/2359296$.

---

## 2. Model and Problem Formulation

- **Oracles and Costs**:
  - A query $(x, V)$ returns $(f(x), V^\top \nabla f(x))$ at cost $1 + \operatorname{rank}(V)$.
  - Exact-value queries correspond to $V = 0$ (cost $1$).
- **Algorithm Execution**:
  - A deterministic algorithm maps each finite query-response transcript to its next query point and subspace, or to an output point.
  - The final output point is uncharged and unrestricted.
  - $N_{\mathrm{det}}$ is the worst-case total cost incurred before outputting an $\varepsilon$-stationary point ($\Vert \nabla f(\hat{x})\Vert  \le \varepsilon$).
- **Function Class $\mathcal{B}^d_{L,\Delta,E}$**:
  - Functions $f$ on $\mathbb{R}^d$ with $L$-Lipschitz gradient, initial gap $f(0) - \inf f \le \Delta$, such that a single fixed positive semidefinite matrix $H \succeq 0$ with $\Vert H\Vert _{\mathrm{op}} \le L$ and $\operatorname{tr}(H) \le LE$ controls the derivative of $\nabla f$ almost everywhere on the sublevel set $\lbrace x : f(x) \lt f(0)\rbrace $.
  - **Segment Equivalence**: Lemma B.2 (`a:lem:hessian-segment`) establishes that this almost-everywhere Hessian condition is equivalent to the segment upper model used in the resistance proofs.

---

## 3. Axiomatic Foundation

The formalization relies strictly on the three standard foundational axioms of Lean 4 and Mathlib:
1. `propext` (Propositional extensionality)
2. `Classical.choice` (Axiom of choice)
3. `Quot.sound` (Soundness of quotient types)

The formal proofs contain **zero `sorry`**, **zero `admit`**, **zero non-standard `axiom` declarations**, and no use of `native_decide`.

---

## 4. Statements Not Formalized

As detailed in Appendix J of the paper, the following results are not formalized:
- The randomized lower bound of Corollary F.4 (`cor:quadratic-baseline`);
- The lower bound of Theorem E.8 (`thm:linear-lower`);
- The variant without $E$ or $H$;
- The three-point upper bound on the broader class $\mathcal{A}^d_{L,\Delta,E}$;
- The coercivity, nonconvexity, and global Lipschitz properties of the hard function constructions;
- The results of Appendices G and H, including lower bounds on the unconstrained global class $\mathcal{F}^d_{L,\Delta,E}$.

---

## 5. Paper Statements Coverage

| Paper Label | Lean Declaration | Scope and Status |
|---|---|---|
| `lem:transfer` | `ExactZO.scaling_lemma_fixedClass`, `ExactZO.normalized_gradient_barrier`, `ExactZO.linearReply_embedObjective` | Rescaling and embedding lemmas preserving smoothness, barrier properties, and query costs. |
| `lem:dimension-floor` | `ExactZO.dimension_floor_fixed`, `ExactZO.dimension_floor_sublevel`, `ExactZO.dimension_floor_value_fixed`, `ExactZO.dimension_floor_value_sublevel` | Dimension floor lower bound $N_{\mathrm{det}} \ge d$ for both value and rank-priced oracles. |
| `u:thm:main` ($10dT$ term) | `ExactZO.coordinate_value_upper`, `ExactZO.coordinate_value_upper_ten` | Coordinate difference upper bound $N_{\mathrm{det}} \le 10dT$ for value queries (labeled `prop:upper` in the Lean comments). |
| `lem:stage` | `ExactZO.Stage.stage_failure`, `ExactZO.Stage.stage_lower_bound` | General stage resistance theorem for hard function families with strip selection. |
| `a:lem:hessian-segment` | `ExactZO.aeHessianUpper_iff_segment_model`, `ExactZO.sublevelClass_iff_hessianSublevelClass` | Equivalence between almost-everywhere Hessian dominance and the segment upper-model condition. |
| `a:lem:selection` | `ExactZO.FiniteEntropySelection.direction_selection`, `ExactZO.unconditionalStripSelector` | Direction selection via finite entropy and quantized signs, establishing strip existence with constant 9. |
| `a:thm:stages` | `ExactZO.S4Selection.deterministic_stage_lower`, `ExactZO.S4Selection.deterministic_stage_lower_value` | Assembly of stage lower bounds with concrete matrix wrappers for both oracles. |
| `a:cor:smooth-rate` | `ExactZO.S4Selection.deterministic_rounded_lower`, `ExactZO.S4Selection.deterministic_rounded_lower_value`, `ExactZO.S4Selection.deterministic_window_lower`, `ExactZO.S4Selection.deterministic_window_lower_value` | Rounded smooth rates ($d/2250$) and trace window lower bounds ($dT/2359296$). |
| `u:lem:residual` / `line` / `blocks` | `ExactZO.SubspaceEstimate`, `ExactZO.SubspaceResidual`, `ExactZO.LineSearch`, `ExactZO.SubspaceInvariant` | Invariants and finite-difference estimators for deterministic subspace search. |
| `u:thm:capacity` / `u:eq:main` | `ExactZO.SubspaceUpper.capacity_value_upper`, `ExactZO.SubspaceUpper.deterministic_value_upper`, `ExactZO.SubspaceUpper.deterministic_linear_upper`, `ExactZO.SubspaceUpper.subspace_value_upper_small_time` | Capacity bound $\min\lbrace 10dT, 100\sqrt{dET(d+T)}\rbrace $ and small-time bound $100\sqrt{2}d\sqrt{ET}$. |
| `thm:main-det` | `ExactZO.MainResults.main_det_verified`, `ExactZO.MainResults.main_det_hessian_finite` | Verified deterministic complexity bounds for value and linear query oracles on class $\mathcal{B}$. |
| `a:lem:sphere-split` | `ExactZO.Gaussian.sphereGaussian_succ_split`, `ExactZO.Gaussian.sphereFirstCoordinateLaw_second_moment`, `ExactZO.Gaussian.sphereGaussian_succ_split_linearIsometryEquiv` | Spherical Gaussian decomposition and first-coordinate distribution lemmas. |
| `thm:main-random` | `ExactZO.MainResults.main_random_upper_twenty_three`, `ExactZO.MainResults.main_random_hessian_upper` | Unconditional $23ET$ upper bound for the randomized three-point method with finite Gaussian seeds. |
| `cor:main-window` | `ExactZO.MainResults.main_det_window_lower`, `ExactZO.MainResults.main_det_hessian_window_lower` | Deterministic lower bound $dT/2250$ in the matching window $T\log(e+T) \le E \le d/T$. |
| `thm:unrestricted` | `ExactZO.MainResults.reader_unrestricted_upper` | $10dT$ upper bound on general smooth classes. |

---

## 6. Building and Auditing the Formalization

### Prerequisites
- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Python 3 and Git

Install the required Lean toolchain:
```sh
elan toolchain install leanprover/lean4:v4.19.0
```

### Build Steps
From this directory:

```sh
# Fetch precompiled Mathlib cache artifacts
lake exe cache get

# Build the project library and targets
lake build

# Run mechanical dependency and axiom audit
python3 check.py
```

Or run the shell wrapper:
```sh
bash check.sh
```

### Expected Output
The verification script:
1. Verifies that all dependencies match the revisions locked in `lake-manifest.json`;
2. Scans all Lean source files (including comments) for forbidden tokens (`sorry`, `admit`, `axiom`);
3. Builds the project via `lake build`;
4. Iterates over all 692 registered targets in `TARGETS.md` (691 paper declarations + 1 environment control) to verify `#check` and recursively inspect `#print axioms`;
5. Asserts that all declarations depend strictly on `propext`, `Classical.choice`, and `Quot.sound`.

Upon success, it writes a detailed report to `CHECK_REPORT.md` and displays:
```text
Mechanical result: **PASS**.
```
