# Pivotal cleanup review notes

The fixed-cohort measurements and unmatched declaration list are in the
[survey](README.md). These notes record review decisions; source proof lengths
are heuristics, not a measure of proof difficulty or mathematical strength.

The objectwise reduction now uses the independently useful fact that weak
integrality of the generated category forces the squared FP dimension of its
simple ambient generator to be integral. It replaces the same calculation in
three obstruction proofs. The categorical adjoint-closure equivalence, the
actual tensor-inverse result for the FP object, and conditional centre and
scalar-twist criteria remain supported APIs even where a particular target's
constant-reference cone does not include them. The centre-square descent,
squared-FP integrality, semilinear transport, finite semisimplicity of the
actual generated subcategory, and positivity and centrality reductions retain
longer arguments because their sums, nonvanishing facts, actual isomorphisms,
label choices, or distinct hypotheses carry the mathematical content. Explicit
arguments in the centre criteria name independent structures and premises; no
hypotheses were hidden to improve binder statistics.

The centre area retains the general positive fusion-subring proof and the
integer-dimensions/centre-orthogonality argument: the available total-matrix
results do not directly cover the former's arbitrary subring, and replacing
the latter with a higher-level result would enlarge its dependencies and
obscure its general hypotheses. Four support lemmas with nine explicit binders
remain because those labels and their infrastructure consumers are deliberate
API choices. The cabling area retains detailed heterogeneous associator,
strand-index and zero/positive-width transport proofs when a shorter checked
mathematical argument was not found. The trace area retains its spherical and
monodromy-bound APIs as independently useful results. The Haar restricted slide
retains the numerical test, support, naturality and nonvanishing hypotheses
needed for actual centrality.

## Deleted construction boundaries

Every module listed here was deleted after moving its declarations to the
named coherent destination and migrating source and audit imports; no temporary
reexports remain. These deletions consolidate APIs, not theorems.

- `MTC.Center.Normalization.SymmetricRising` → `SymmetricBinomial`: the
  rising-factorial and generalized-binomial arguments form one calculation.
- `MTC.Algebra.ComplexTraceReciprocity` → `ComplexBlockTrace`: weighted trace
  and its star/reciprocity results use the same setup.
- `MTC.PropertyF.Pivotal.MonoidalTrace` and `MonoidalDualComparison` →
  `MonoidalDual`: monoidal functor dual and trace comparisons belong together.
- `MTC.Braided.Cabling.ClosureSweepContext` → `ClosureSweep`;
  `ClosureBlockInduction` → `ClosureTwoRow`; `ClosureFlattenUnit` and
  `ClosureAdjacentCoherence` → `ClosureCommonInterface`; `ClosureFourTail` →
  `ClosureFour`; `ClosureBlockFinite` → `ClosureBlockProof`.
- `MTC.Braided.Cabling.PureSumPositive` → `ColorBiproductPositive`;
  `BlockFiniteBraid` → `BlockFinite`; `BlockFiniteGroups` → `BlockFiniteSum`;
  `PureSumPositiveCabling` → `PureSumPositiveState`. These pair the finite
  block criteria, crossing coherence, or positive-word results they support.

Ten public construction-stage Haar lemmas were removed after inspecting source
consumers, attributes, instances and tactic registrations. The six
`pivotalLeftPairing_snake_{right,left}`, `_id`, and `_whisker` stages specialize
the general exact-pairing snake identities and only called one another. The
four `pivotalComponent_whisker_exchange`, `haar_evaluation_exchange`,
`haar_pivotal_box_exchange`, and `haar_pivotal_cup_exchange` stages specialize
whisker exchange and coherence and had no source consumers. The general
exact-pairing and exchange APIs, as well as the actual boxed snake, mate and
closed slide proofs, remain. Their removal changes these construction-stage
public names; no cone-only deletion is inferred from the survey.

## Verification and comparison

The final survey pairs 690 surviving baseline new-layer theorems by qualified
name. Their lexical proof-line median/p90 is 6/20 before and 6/19 after;
Lean elaborated explicit binders are 3/7 before and 3/6 after. Hypothesis
median/p90 remains 1/3. Ten deleted baseline declarations and four newly
introduced source theorems are listed separately in
[cohort-unmatched.tsv](cohort-unmatched.tsv). The new-layer file snapshot
changes from 178 files with median 67 lines to 164 surviving baseline paths
with median 71; file populations are not paired. The fixed Mathlib sample has
18,060 source theorems and 15,606 unique Lean matches, so its source and
elaborated statistics use different populations.

With `LEAN_NUM_THREADS=4`, `scripts/check.sh` passed its 12 Python tests,
full build and audits of 5,250 integrated and 5,251 total project declarations.
`scripts/audit-target.sh` passed the original statement equivalence, new
source invariants and target dependency audit. A fresh survey followed by
`python3 scripts/print_public_axioms.py` printed and checked axioms for 1,590
public source theorems, with no unmatched source theorems and no axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. The complete original frozen
files, pivotal target file and generated-category file also matched their
`fb6ec518` SHA-256 hashes.

A comparison of cached baseline Lean warning traces with final traces found
197 versus 168 warning records, zero missing traces and no new or changed
warning messages after removing source locations. Baseline traces are saved in
the run directory; they are cached build evidence, not a newly rebuilt baseline.
Three retained theorem type hashes differ between environment dumps: the two
moved monoidal duality lemmas and the generated equation theorem
`transformedDualIso.eq_1`. Their fully printed types, including universes and
instance order, were compared with baseline and are identical. A prior moved
cabling lemma's instance ordering was restored after the same comparison.
Type hashes and printed types are review aids, not proofs of semantic equivalence.

The checked mathematical head is `de467610`. The report and final documentation
are committed afterwards; `git log -1 --format=%H -- docs/style/cleanup-notes.md`
identifies the commit containing this record. The final integrated commit and
complete command logs are also recorded in the run directory's `lead-status.md`.
