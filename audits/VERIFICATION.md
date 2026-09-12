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

## Full characterization extension — 13 September 2026

The three new mathematical modules `CMCharacterizationDefinitions`, `CMCharacterizationT1`, and `CMCharacterizationSufficiency` add period-independent classical predicates, T1 necessity, constructive T1+T2 sufficiency, and the full equivalence for arbitrary `Finset ℤ`. `CMCharacterizationSemanticsAudit` exposes the literal set-indicator covering equation and polynomial conditions. The new files do not alter the frozen 35-module T2 core or its original manifests.

The exact final theorem is `CMCharacterization.finite_integer_tiling_iff_T1_T2`. It derives nonemptiness on the forward implication and imposes no prime-count, exponent, period, or unique-complement hypothesis. The finite primary-divisor cutoff is proved exhaustive for nonzero polynomials. The sufficiency construction does not invoke T2 necessity: missing-primary digit factors provide mass and root coverage, Fourier inversion proves exact convolution, and inverse normalization restores arbitrary signed integer sets. The known T1 and sufficiency mathematics is credited to Coven and Meyerowitz, not claimed as a new result.

A complete macOS/arm64 replay finished at **2026-09-12 21:49:27 UTC** (13 September in India), with exit code 0. It recompiled the original 35 mathematical modules and cyclic semantic probe, then all three new mathematical modules and the signed-set semantic probe. All **42 exact axiom guards** passed: 22 existing and 20 additional. The only permitted final axioms are `propext`, `Classical.choice`, and `Quot.sound`.

This local replay used the matching pinned Mathlib dependency cache; it rebuilt every authored proof module in this checkout. It was not a cold reconstruction of Mathlib or Lean. The updated public workflow independently runs the same extended verifier on a fresh runner and preserves its receipt, source identities, and individual logs. The workflow result must be checked at the exact commit; configuring it is not a claim that a future run has passed.

| Added source | SHA256 |
|---|---|
| `CMCharacterizationDefinitions.lean` | `44ee67af55698ccba9fece656a03695ac78bef880c830bf85f13f5adb33397a5` |
| `CMCharacterizationT1.lean` | `0fbbffd79884ae09f1fbce1b4ec25cf6687a546adbd976c498da1031a202f8e2` |
| `CMCharacterizationSufficiency.lean` | `3d3d46318a1efa5d677e1158c4a65628ed6e6c2f613c2d6b2c0d0727cb5961d6` |
| `CMCharacterizationSemanticsAudit.lean` | `0303952e994d74097e8003c99a1ae9290aad51eb5299854c92a0232c5bae2ed9` |
| `verify_characterization.sh` | `11c1769a66487c665c7f8e2e780cd1d6c94aad10f1047dc200763010836ccf15` |

Separate automated read-only reviews compared the new definitions and bridge arguments with the original CM statement and found no fatal scope mismatch in those inspected components. These reviews did not independently re-audit the entire earlier T2 core and are not human specialist reports. The development has not been accepted or merged by Mathlib.

## Remaining assessment boundary

External specialist review, publication acceptance, and exclusive discovery priority remain unconfirmed. No specialist endorsement or referee correspondence is implied by this repository. Formal replay, semantic scope, attribution, novelty, and mathematical significance are separate questions.
