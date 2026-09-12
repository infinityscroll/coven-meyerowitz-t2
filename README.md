# Coven–Meyerowitz T2 necessity: proof and Lean verification

[![Full proof replay](https://github.com/infinityscroll/coven-meyerowitz-t2/actions/workflows/verify.yml/badge.svg)](https://github.com/infinityscroll/coven-meyerowitz-t2/actions/workflows/verify.yml)

This repository presents a proof of full **T2 necessity for finite integer tiles**, together with its Lean 4 formalization and an explicit all-module verification workflow.

The 13 September extension also formalizes the classical T1 necessity and T1+T2 sufficiency implications, yielding a single **full characterization theorem** for arbitrary finite subsets of the integers. The older T2 proof packet and its manifests are preserved unchanged.

**Jitendra Prajapati · Independent**

[23f1001521@ds.study.iitm.ac.in](mailto:23f1001521@ds.study.iitm.ac.in) · [ORCID 0009-0008-7493-0311](https://orcid.org/0009-0008-7493-0311)

**Status: formally checked statement; public research release for external review.** External specialist acceptance and exclusive discovery priority are not established. Automated reviews are internal checks, not independent human refereeing. See [verification and provenance](audits/VERIFICATION.md).

- [Paper (PDF)](output/pdf/coven-meyerowitz-t2.pdf) · [editable LaTeX source](paper/coven-meyerowitz-t2.tex)
- [Minimal arXiv source archive](output/arxiv/coven-meyerowitz-t2-source.tar.gz) (the single self-contained manuscript source; no arXiv posting is implied).
- [Unrestricted T2 necessity](formal/FullCovenMeyerowitz.lean) · [full characterization](formal/CMCharacterizationSufficiency.lean) · [literal signed-set interface](formal/CMCharacterizationSemanticsAudit.lean)
- [Verification workflow](.github/workflows/verify.yml) · [complete characterization verifier](formal/verify_characterization.sh) · [preserved T2 verifier](formal/verify_full_t2.sh)
- [Literature and attribution](audits/LITERATURE.md) · [citation guidance](CITATION.md)

## Statement

Let a finite set $A\subseteq\mathbb Z$ tile the integers by translations. This means there exists a set $C\subseteq\mathbb Z$ such that every integer has exactly one representation as $a+c$ with $a\in A$ and $c\in C$; the complement $C$ is **not** required to be unique. Translate $A$ to have nonnegative entries and put $A(X)=\sum_{a\in A}X^a$. If $p_1,\ldots,p_k$ are distinct primes, $e_i>0$, and every $\Phi_{p_i^{e_i}}$ divides $A(X)$, then

$$
\Phi_{\prod_{i=1}^k p_i^{e_i}}(X)\mid A(X).
$$

The formal theorem covers every nonempty finite prime family, all positive levels, and arbitrary periods. Its starting hypothesis is literally

$$
\sum_{a\in A}c(t-a)=1\qquad(t\in\mathbb Z),\qquad c:\mathbb Z\to\mathbb N.
$$

Periodicity is derived, not assumed. `FullCovenMeyerowitz.arbitrary_integer_tile_T2` also handles negative entries by minimum normalization. These are universal theorems, not bounded enumeration results.

### Full characterization extension

`CMCharacterization.finite_integer_tiling_iff_T1_T2` states that an arbitrary `F : Finset ℤ` tiles ℤ exactly when it is nonempty and its minimum-normalized mask satisfies T1 and unrestricted T2. T1 uses the complete set of primary cyclotomic divisors: the finite degree cutoff in its implementation is proved exhaustive, not imposed as an additional assumption.

The reverse implication constructs the complement from missing primary digit factors, proves its mass and coverage of every nontrivial root, and recovers an exact tiling by Fourier inversion. It does not invoke T2 necessity. The [literal semantic interface](formal/CMCharacterizationSemanticsAudit.lean) exposes the set-indicator covering equation and both polynomial conditions without the `TilesZ`, `T1`, or `T2` abbreviations. Empty sets and arbitrary integer singletons are checked separately.

These two additional implications formalize established results of Coven and Meyerowitz; no new priority is claimed for them. The original PDF and arXiv source preserve the earlier T2-only formalization snapshot. See [verification and provenance](audits/VERIFICATION.md) for the extension's boundary.

## Reproduce

Install [Elan](https://github.com/leanprover/elan), clone this repository, then:

```sh
cd formal
lake exe cache get
sh ./verify_characterization.sh
```

The pins are Lean **4.23.0** and Mathlib commit **37df177aaa770670452312393d4e84aaad56e7b6**. Dependency download/cache extraction needs several GB of disk; the repository itself excludes those caches.

The complete verifier first runs the preserved T2 verifier: three source manifests, **35 mathematical modules**, a literal-function cyclic semantics probe, and **22 guarded axiom checks**. It then compiles three characterization modules and the literal signed-set semantics probe, including **20 further guards**. In total it rebuilds **38 mathematical modules and two semantic probes, with 42 guarded axiom checks**. The permitted final dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. Unexpected axiom lists fail the audit. Old unused-section-variable warnings are harmless and preserved.

Each complete run records the toolchain, source hashes, individual logs, and a unique fail-closed receipt. It rechecks source identities before emitting `PASS`. The script clears an inherited `LEAN_PATH`; it does not search for another checkout. The older T2-only command remains `sh ./verify_full_t2.sh`.

**Plain `lake build` is not the verification command.** The frozen original default target includes only `StripeCollapse`; the explicit script covers the whole proof. The CI job starts without a project build cache, downloads pinned Mathlib dependencies, runs that script with pipe-failure propagation, and uploads its log.

To rebuild the paper with a conventional TeX installation:

```sh
sh paper/build.sh
```

## Scope and trust

The final theorem uses standard integer polynomials and cyclotomic divisibility. The proof proceeds through character analysis of actual cyclic tilings, periodic product stripes, integral quotient descent followed by characteristic-prime Frobenius, all-phase lower-period tilings, and strong induction for both original factors.

The original frozen formalization certifies T2 necessity. The additive characterization extension formalizes the known T1 necessity and T1+T2 sufficiency of Coven and Meyerowitz as well. The abstract ingredients have substantial antecedents; the paper does not assert priority for each ingredient or claim that a bounded literature search establishes a first proof. The development has not been merged into Mathlib.

The source rebuild relies on the pinned Lean toolchain and upstream dependency artifacts. It is not a from-source rebuild of every Mathlib theorem or an independent implementation of Lean's kernel. Public CI replay, semantic correspondence, specialist review, and novelty are separate checks.

## Review and provenance

Please report a proposed gap with the precise paper statement or Lean declaration and a reproducible explanation. Public issues are welcome. This repository was prepared with AI assistance; the included automated scope and architectural reviews are not external referee reports. No specialist endorsement is implied.

This repository preserves the frozen Lean sources and their original hash manifests. The manuscript, including its LaTeX source and PDF, is licensed under [CC BY 4.0](LICENSE.md). AI assistance was used in proof development, manuscript preparation, and Lean formalization; no AI system is listed as an author. See [CITATION.md](CITATION.md) for the human author metadata and version-specific citation guidance. No arXiv identifier or journal acceptance is asserted until one has actually been obtained.
