# Papers

Informal manuscripts whose results are formalized in this library. Each manuscript has its own
folder, named after its main result, with:

- `manuscript.pdf`: the manuscript;
- `manuscript.txt`: a plain-text copy for search and review (optional);
- source files such as `manuscript.tex` and its bibliography, when available;
- `README.md`: the citation, status, and a table that maps each numbered result to its Lean
  declaration.

A manuscript is added in the same change that adds its formalization, or that states its results
as targets in `MTC/Conjectures/`.

| Folder | Main result | Lean | Status |
|---|---|---|---|
| [property-f-weak-integrality](property-f-weak-integrality/) | Property F implies weak integrality for braided fusion categories with a pseudo-unitary Galois conjugate | `MTC.target` | Formalized |
