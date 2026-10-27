# Dependencies

- **Fusion:** supplied the genuine semisimple category, simple decompositions, multiplicities, and FP dimensions; these are used by the constructed block/trace theorems. No further fusion interface is needed for the local results currently proved.
- **Dimensions:** supplied pivotal structures, traces and iterated trace compatibility. The canonical positive spherical structure for a pseudo-unitary category remains needed to obtain positive transported block weights from the final target hypotheses.
- **Modular:** supplied the actual categorical S matrix; `two_braid_square_trace_categoricalS` and `three_braid_trace_categoricalS` prove the diagonal braid trace identities. Full Galois action on the categorical S matrix still depends on modular nondegeneracy and centre results.
- **Fusion / dimensions / modular:** an actual Galois-conjugate category and scalar-transport equivalence preserving the spherical structure and simple decompositions remain needed for realization transport. Merely applying an automorphism to a trace equality does not construct the transported representation.
- **Centre:** a genuine braided fusion structure and modular nondegeneracy for the Drinfeld centre are needed to apply the final realization to the centre.

The internal outstanding calculus step for Lemma 3.1 is the categorical coherence relating the actual repeated strand maps to the local partial-trace overlap recurrence, then iteration and the strengthened bound. Three-strand rigidity and the full transported realization are also not complete.
