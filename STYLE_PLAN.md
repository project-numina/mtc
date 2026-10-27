# Parallel Mathlib-style cleanup plan

This plan starts from the survey baseline. The objective is a readable, reusable library with the same final theorem, not a score obtained by compressing mathematical arguments. An agent should keep a long proof when the decomposition makes the mathematics clearer, and should explain exceptions against the targets below.

## Non-negotiable verification and coordination

`PropertyF/Ground/Target.lean`, every definition in it, and the statement of `PropertyF.Ground.target` are frozen. Do not change the meaning of definitions on which that statement depends. The proof of `target` may be reorganized in later work, but its type must remain exactly `PropertyF.Ground.TargetStatement`. The present survey changes no proof.

After **every change**, run `LEAN_NUM_THREADS=4 taskset -c 28-31 lake build PropertyF` and `PROPERTYF_AUDIT_CORES=28-31 LEAN_NUM_THREADS=4 scripts/audit-target.sh`; both must pass. Verify the audit reports exactly `[propext, Classical.choice, Quot.sound]` (the current audit rejects additional axioms but does not itself require all three to appear). If a cached run does not display the list, rebuild or query the target axioms in a separate temporary Lean file. A passing audit is necessary, not proof that exported API and instance behavior are unchanged. For API and instance changes, compile the affected downstream modules and representative examples as well.

Use one branch and one separate worktree per owner. Do not work in another owner's files, even for imports. Each owner can make self-contained commits; integrate through the coordinator in dependency order. Request shared-file changes from the coordinator as patches. Queue builds on CPUs 28–31 to avoid running several full builds at once. Preserve any unrelated uncommitted work. No force-pushes or history rewriting. Do not push unless separately requested.

## Seven disjoint workstreams

Ownership covers every existing source file, including tests and compatibility modules. New files under each listed directory belong to the same owner. Shared files remain the coordinator's responsibility throughout. Frozen files are read-only for all owners.

| Owner | Exclusive paths | Precise brief |
|---|---|---|
| 1. Integration coordinator | `PropertyF.lean`, `PropertyF/Ground/Final.lean`, `PropertyF/Ground/Integrate/**`, `scripts/check-audit-imports.py`, `scripts/audit-target.sh`, and `scripts/style/**`; `PropertyF/Ground/Target.lean` is read-only | Inventory and simplify the `target_of_*` chain, legacy adapters, both project audits, root imports, and final integration. Own cross-directory import changes and audit coverage. Retain a reduction when it expresses a useful mathematical boundary or remains in the cone. |
| 2. Centre core | `PropertyF/Ground/Centre/**`, `PropertyF/Ground/CentreBundle/**`, `PropertyF/Ground/CentreRigid/**` | Consolidate centre construction, category structure, duals, and product machinery. Compare parallel centre constructions and state which is canonical before replacing anything. |
| 3. Centre calculus | `PropertyF/Ground/CentreCalculus/**`, `PropertyF/Ground/CentreCabling/**` | Deduplicate crossing, partial trace, monodromy, centralizer, and cabling lemmas; identify reusable lemmas rather than repeating local calculations. |
| 4. Centre induction | `PropertyF/Ground/CentreInduction/**` | Consolidate induction, forgetful functors, adjunctions, duals, pivotal structure, and the Drinfeld argument. Review long coherence arguments against Mathlib category-theory lemmas. |
| 5. Centre modularity | `PropertyF/Ground/CentreModular/**`, `PropertyF/Ground/CentreDimensions/**`, `PropertyF/Ground/CentreIntegrate/**`, `PropertyF/Ground/Modular/**` | Consolidate modularity, S-matrix, trace, and Vafa results. Check old and new centre pathways for equivalent statements and move reusable results to a single canonical home. |
| 6. Fusion and dimensions | `PropertyF/Ground/Dimensions/**`, `PropertyF/Ground/Fusion/**` | Consolidate fusion, Frobenius–Perron dimension, traces, duals, pivotal and spherical dimension machinery. Review the largest dimension and coherence proofs first. |
| 7. Cabling and foundational layer | `PropertyF/Ground/Cabling/**`, `PropertyF/Ground/Calculus/**`, and `PropertyF/*.lean` | Consolidate braid representations, generated subcategories, cabling, trace bounds, and older root-level numerical interfaces. Separate reusable results from legacy bridges; preserve exports until their users are migrated. |

For the target layout, reserve `Centre/Induction/**` for owner 4, `Centre/Calculus/**` for owner 3, `Centre/Modular/**` for owner 5, and `Braid/**` and `Trace/**` for owner 7; these reservations take precedence over the existing `Centre/**` ownership. The coordinator maintains an ownership map for any other new cross-cutting directory. A proposal to move a declaration across owners is implemented as a coordinated pair of changes: the destination owner adds a canonical declaration or temporary re-export, the source owner migrates users, and only then does the coordinator remove compatibility imports. Never leave an intermediate commit that fails the verification rule. Changes to audits, the umbrella import, and shared names are serialized through owner 1.

## Ordered phases and measurable gates

1. **Dead code and deduplication.** Each owner classifies every declaration in their ownership using `STYLE_DECLARATIONS.tsv`, the file scorecard, and the lint outputs: target-cone, externally useful API, elaboration/instance or audit dependency, duplicate, or removal candidate. Classify all no-cone modules and every same-type or near-duplicate candidate in the report; record a replacement and its imports for each proposed deletion. Check exact types and universes with Lean, search Mathlib by type and applicable domain vocabulary, and try `exact?` locally where practical. A hash match is not evidence of equivalence. Retain theorem aliases when needed for downstream compatibility; remove a legacy file only after auditing imports, instances, attributes, public consumers, and audit fixtures. Gate: every removal has a recorded reason and successful verification; zero unreviewed candidate deletions; reduce redundant declarations without changing the frozen statement.
2. **Restructure.** Consolidate short, closely related modules toward the layout below. The full Mathlib file median is 182 lines and p90 is 631. Aim for 150–350 lines for ordinary mathematical modules, allowing shorter genuinely independent modules and longer coherent files. Avoid files over 631 lines except generated audit/import aggregators, with a written reason. Target a project median of at least 130 lines after consolidation; measure again because removal changes the denominator. Gate: no import cycles, documented namespace and import changes, no unnecessary compatibility layer remaining after its consumers move, and unchanged frozen target. Review the longest import chains, not just line counts.
3. **Golf and mathematical reuse.** Within each ownership area, review every proof over the baseline Mathlib p90 and the longest ten proofs in that area; seek existing Mathlib lemmas, `simp only` where useful for stable local rewrites, meaningful helper lemmas, and simpler term proofs. The source survey's proof and tactic-step counts are estimates, not quality metrics. Aim to reduce the project median proof line count to at most twice the sampled Mathlib median and p90 to at most twice the sampled Mathlib p90, while preserving explanatory structure. Do not introduce fragile automation merely to meet a number. Re-run the survey after this phase and record exceptions for irreducible domain-specific arguments.
4. **Docstrings and lint.** Add module docs with purpose, main results, and references where they help; add declaration docs for public definitions and non-obvious theorems. Replace stale claims that work is unproved where the proof now exists, without editing the frozen file. Resolve the full-build style warnings and `#lint` findings in owned files, with narrowly justified suppressions only where appropriate. Gate: no new warnings, each pre-existing finding fixed or documented, all public definitions documented, and a final project-wide lint report. Run the complete verification rule after every change.

Each owner submits a before/after scorecard: file count and median/p90 lines; theorem count and median/p90 proof lines and estimated tactic steps; number of cone and no-cone declarations classified, exact and near duplicates reviewed, and lint findings fixed or excepted. Owner 1 aggregates these results and checks all phases in order. Do not merge a later-phase change into an area before its earlier-phase review is complete.

## Target module layout

These are destination families, not a demand to create empty files or to rename the frozen target. Exact module boundaries are chosen around coherent mathematical dependencies and reviewed in small verified steps.

```text
PropertyF/
  Definitions.lean                -- stable shared foundational API
  Ground/
    Target.lean                  -- frozen statement and definitions
    Fusion/                      -- fusion categories, representatives, FP dimension
    Dimensions/                  -- duals, traces, pivotal/spherical dimensions
    Braid/                       -- braid representations and cabling (owner 7)
    Trace/                       -- overlap and categorical trace bounds (owner 7)
    Centre/                      -- canonical centre, rigidity, induction, calculus
      Basic.lean
      Rigid.lean
      Induction/                 -- owner 4
      Calculus/                  -- owner 3
      Modular/                   -- owner 5
    Modular/                     -- general S-matrix and modular category results
    Integrate/                   -- minimal chain of named reductions and audits
    Final.lean                   -- proof of the frozen target statement
```

The existing `Centre*` trees are mathematical subsystems, not automatically duplicates. Owners 2–5 first map each declaration and namespace to the canonical `Centre/` destination; owner 1 coordinates imports. A temporary compatibility module may preserve users during migration, but each such module needs a named owner and removal condition. The legacy numerical layer may remain separately named if the classification finds a real supported use. Keep audit files and their private imports sufficient to cover every remaining project module; update the coverage checker and both audit imports atomically with any module deletion or move.
