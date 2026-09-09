# Verification and provenance

## Frozen source boundary

The 35 mathematical modules, literal-function probe, audit files, pinned Lake setup, and replay scripts are copied unchanged from the frozen 9 September 2026 proof packet. The three original manifests are checked by `formal/verify_full_t2.sh`.

- Final source `FullCovenMeyerowitz.lean`: SHA256 `6907123aadbeb81b5002a2ae9e2492018eaac53d843661cc6cf36218c0d263b6`.
- `SHA256SUMS.completion`: SHA256 `ac9663be74eb927664e9623d6e13dfa7740fd6bc8ddb9e85afc048e375c0b38f`.
- Lean: `leanprover/lean4:v4.23.0`.
- Mathlib: `37df177aaa770670452312393d4e84aaad56e7b6`.

The paper and public documentation were newly prepared on 10 September 2026. Historical unpublished draft status paragraphs are not reused as current verification claims. The public bundle excludes dependency caches, compiled Lean artifacts, private conversation history, credentials, and unrelated projects.

## What the verifier checks

A fresh local macOS/arm64 source replay on 10 September 2026 completed with exit code 0, rebuilding all 35 mathematical modules and the semantic probe and passing all 22 guards. The Mathlib checkout matched the pinned commit and had no tracked modifications. The original source hashes remained unchanged. The public Linux CI replay is an additional fresh-environment check, not inferred from this local result.

`verify_bridges.sh` recompiles 20 mathematical modules and runs 14 guarded axiom checks. `verify_full_t2.sh` checks the completion manifest, invokes that bridge verifier, recompiles 15 further mathematical modules, recompiles `CMFinalCyclicColdProbe.lean`, and runs 8 further guarded axiom checks. A failure in any step fails the script. CI preserves the shell pipeline's failure status.

The final declarations' only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`. A changed axiom list, including `sorryAx` or an added oracle, fails the guards. Source hashes also bind the original scripts and audit sources. Hashes identify exact content; they do not prove mathematical correctness by themselves.

The CI run linked by the repository badge is the public fresh-runner replay record. A passing run is a source rebuild of all project proof modules using pinned upstream dependencies; it is not an independent kernel implementation or a from-source reconstruction of all Mathlib.

## Release-day internal semantic review

A separate automated read-only scope audit checked the expanded final theorem and the actual integer-to-cyclic passage. It found no extra period, prime-count, cardinality, or auxiliary closure hypothesis in the final type. A fresh imported-artifact probe also verified that the starting tiling premise is inhabited by the singleton tile with constant-one complement.

The audit checked that the polynomial is the literal mask polynomial, that `constantMask 1` means the all-ones coefficient function, and that the smaller-period T2 premises are discharged by strong induction. It found no authored `sorry`, added axiom, unsafe declaration, native oracle, or notation substitution in its source scan.

A second automated architectural review compared the full prose route with character, stripe, phase, and induction interfaces. It found no mismatch in those inspected sections. These bounded internal automated reviews are not complete independent human line-by-line verification and do not replace source replay.

## Remaining assessment boundary

External specialist review, publication acceptance, and exclusive discovery priority remain unconfirmed. No specialist endorsement or referee correspondence is implied by this repository. Formal replay, semantic scope, attribution, novelty, and mathematical significance are separate questions.
