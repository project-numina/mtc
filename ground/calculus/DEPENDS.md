# Dependencies

- **Fusion / integrate:** a genuine finite semisimple category interface with simple representatives, finite-dimensional Hom spaces, biproduct decompositions, and tensor-power multiplicities. Needed for End-algebra blocks and the FP mass identity.
- **Dimensions:** a spherical structure with linear categorical and partial traces, cyclicity, tensor/partial-trace compatibility, and the simple-object scalar identity. Needed to construct the trace and partial-trace fields.
- **Modular:** construction of the S matrix as the categorical trace of double braiding and semilinear transport of traces. Needed for `ThreeStrandRealization.trace_formula`.
- **Fusion / dimensions / modular:** an actual Galois-conjugate category and a scalar-transport equivalence preserving the spherical structure and simple decompositions. Needed for `ThreeStrandRealization.transport` and `CenterInputs.realize`.
