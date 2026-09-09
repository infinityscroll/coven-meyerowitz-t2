# Coven–Meyerowitz T2 necessity: proof and Lean verification

[![Full proof replay](https://github.com/infinityscroll/coven-meyerowitz-t2/actions/workflows/verify.yml/badge.svg)](https://github.com/infinityscroll/coven-meyerowitz-t2/actions/workflows/verify.yml)

This repository presents a proof of full **T2 necessity for finite integer tiles**, together with its Lean 4 formalization and an explicit all-module verification workflow.

**Status: formally checked statement; public research release for external review.** External specialist acceptance and exclusive discovery priority are not established. Automated reviews are internal checks, not independent human refereeing. See [verification and provenance](audits/VERIFICATION.md).

- [Paper (PDF)](output/pdf/coven-meyerowitz-t2.pdf) · [editable LaTeX source](paper/coven-meyerowitz-t2.tex)
- [Final, fully exposed Lean theorem](formal/FullCovenMeyerowitz.lean)
- [Verification workflow](.github/workflows/verify.yml) · [all-module verifier](formal/verify_full_t2.sh)
- [Literature and attribution](audits/LITERATURE.md) · [citation guidance](CITATION.md)

## Statement

Let a finite set $A\subseteq\mathbb Z$ tile the integers uniquely by translations. Translate it to have nonnegative entries and put $A(X)=\sum_{a\in A}X^a$. If $p_1,\ldots,p_k$ are distinct primes, $e_i>0$, and every $\Phi_{p_i^{e_i}}$ divides $A(X)$, then

$$
\Phi_{\prod_{i=1}^k p_i^{e_i}}(X)\mid A(X).
$$

The formal theorem covers every nonempty finite prime family, all positive levels, and arbitrary periods. Its starting hypothesis is literally

$$
\sum_{a\in A}c(t-a)=1\qquad(t\in\mathbb Z),\qquad c:\mathbb Z\to\mathbb N.
$$

Periodicity is derived, not assumed. `FullCovenMeyerowitz.arbitrary_integer_tile_T2` also handles negative entries by minimum normalization. These are universal theorems, not bounded enumeration results.

## Reproduce

Install [Elan](https://github.com/leanprover/elan), clone this repository, then:

```sh
cd formal
lake exe cache get
sh ./verify_full_t2.sh
```

The pins are Lean **4.23.0** and Mathlib commit **37df177aaa770670452312393d4e84aaad56e7b6**. Dependency download/cache extraction needs several GB of disk; the repository itself excludes those caches.

The verifier checks three source manifests, recompiles **35 mathematical modules** in dependency order, recompiles the literal-function cyclic semantics probe, and runs **22 guarded axiom checks**. The permitted final dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. Unexpected axiom lists fail the audit. Old unused-section-variable warnings are harmless and preserved.

**Plain `lake build` is not the verification command.** The frozen original default target includes only `StripeCollapse`; the explicit script covers the whole proof. The CI job starts without a project build cache, downloads pinned Mathlib dependencies, runs that script with pipe-failure propagation, and uploads its log.

To rebuild the paper with a conventional TeX installation:

```sh
sh paper/build.sh
```

## Scope and trust

The final theorem uses standard integer polynomials and cyclotomic divisibility. The proof proceeds through character analysis of actual cyclic tilings, periodic product stripes, integral quotient descent followed by characteristic-prime Frobenius, all-phase lower-period tilings, and strong induction for both original factors.

The formalization certifies T2 necessity. The known T1 necessity and T1+T2 sufficiency of Coven and Meyerowitz are cited, not newly formalized here. The abstract ingredients have substantial antecedents; the paper does not assert priority for each ingredient or claim that a bounded literature search establishes a first proof.

The source rebuild relies on the pinned Lean toolchain and upstream dependency artifacts. It is not a from-source rebuild of every Mathlib theorem or an independent implementation of Lean's kernel. Public CI replay, semantic correspondence, specialist review, and novelty are separate checks.

## Review and provenance

Please report a proposed gap with the precise paper statement or Lean declaration and a reproducible explanation. Public issues are welcome. This repository was prepared with AI assistance; the included automated scope and architectural reviews are not external referee reports. No specialist endorsement is implied.

This public release preserves the frozen Lean sources and their original hash manifests. The paper and publication documentation are newly prepared for this release. No personal author name or additional reuse license is assigned by the automated publication process; see [CITATION.md](CITATION.md).
