# Papers

Informal manuscripts whose results are formalized in this library. Each manuscript has its own
folder, named after its main result, with:

- the LaTeX source (`.tex`, with its bibliography and figures) and the compiled `.pdf`;
- `README.md`: the citation, status, and a table that maps each numbered result to its Lean
  declaration.

A manuscript is added in the same change that adds its formalization, or that states its results
as targets in `Conjectures/`.

| Folder | Main result | Lean | Status |
|---|---|---|---|
| [property-f-weak-integrality](property-f-weak-integrality/) | Property F implies weak integrality for braided fusion categories with a pseudo-unitary Galois conjugate | `PropertyF.Ground.target` | Formalized |
