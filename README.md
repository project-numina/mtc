# Property F implies weak integrality

[![arXiv](https://img.shields.io/badge/arXiv-2611.12836-b31b1b.svg)](https://arxiv.org/abs/2611.12836)
[![Blog](https://img.shields.io/badge/Blog-Agentic%20Loops%20and%20Braids-blue.svg)](https://projectnumina.ai/article?slug=academic-loops)

A Lean 4 formalization of our preprint,
[Property F implies weak integrality for non-degenerate pivotal braided fusion categories](https://arxiv.org/abs/2611.12836).

**Theorem.** Every non-degenerate pivotal braided fusion category with
property F is weakly integral.

The formalization also includes the degenerate extension under its positivity
hypothesis and the supporting results of the proof.

- [Main theorems](MTC/PropertyF/Pivotal/MainTheorems.lean)
- [Exact statements](MTC/PropertyF/Pivotal/Statement.lean)
- [Closure and objectwise consequences](MTC/PropertyF/Pivotal/ClosureTheorems.lean)

The [earlier theorem](MTC/PropertyF/Theorem.lean), assuming a pseudo-unitary
Galois conjugate, is also included.

For background on the research, see [Agentic Loops and Braids](https://projectnumina.ai/article?slug=academic-loops).
