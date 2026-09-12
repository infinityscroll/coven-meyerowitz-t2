# Literature and attribution boundary

10 September 2026. This is a bounded source comparison, not exhaustive priority clearance.

The original [Coven–Meyerowitz paper](https://arxiv.org/abs/math/9802122), submitted in February 1998 and published in *Journal of Algebra* 212 (1999), establishes T1 necessity and T1+T2 sufficiency, as well as T2 necessity in the at-most-two-distinct-prime-factor cardinality case. These established results are not new contributions of this repository.

Section 1.3 of [Kadir–Fan, version 2](https://arxiv.org/html/2607.02149v2), read again for this release, explicitly describes unrestricted T2 necessity as open. Their stated main theorem is about positive-definite weak tiles in a two-prime cyclic group, not the unrestricted theorem here. This is dated evidence of the problem's status in that text, not proof that no subsequent or unpublished resolution exists.

The targeted release-day search returned existing partial results and related work, but no full resolution. A broader initial query returned irrelevant results and is not used as negative evidence. Search absence does not certify originality, priority, or acceptance.

## Antecedents that must be credited

- CM Lemma 2.1: primary cyclotomic allocation by cardinality/valuation exhaustion.
- CM Lemma 3.1: characteristic-prime Frobenius in tiling dilation, with positivity used to upgrade coefficient information.
- CM Lemma 2.5: common-complement fiber inheritance and lifting.
- [Tao, *Some notes on the Coven–Meyerowitz conjecture*](https://terrytao.wordpress.com/2011/11/19/some-notes-on-the-coven-meyerowitz-conjecture/), Proposition 17: stripe partitions in the square-free CRT setting. The subsequent corrections in the comments must be distinguished from the original post.
- [Łaba–Londner, *Splitting for Integer Tilings*](https://doi.org/10.1093/imrn/rnaf090), Definition 3.3 and Lemma 3.4: divisor-isometry freedom. Fiber coalescence in the present proof is not itself a divisor isometry.

The comparison target for a possible new contribution is the combined argument: descend periodic convolution minors over the integers, cancel the lift multiplicity before reduction modulo the chosen prime, force a single stripe orientation by coprime Frobenius, obtain coalesced lower-period tilings for every independent phase, and recover mixed zeros of both original factors. The individual ingredients are not advertised as newly invented.

## Different statements are not counterexamples to this theorem

[Kiss–Londner–Matolcsi–Somlai, *Functional tilings and the Coven–Meyerowitz tiling conditions*](https://arxiv.org/abs/2411.03854) gives counterexamples for a nonnegative-function relaxation. The present argument uses Boolean sets and integral descent essentially; it is not a theorem about arbitrary fractional functional tiles.

The theorem here is T2 necessity. Calling the entire historical T1–T2 characterization newly formalized would overstate the artifact. Calling the public release externally accepted or priority-cleared would likewise be unsupported.

## Citation revision: 13 September 2026

The paper now contains 17 cited references, with historical and related-work discussion in the introduction and citations at the allocation, common-complement, and periodicity steps. This is a dependency and attribution review, not a claim of exhaustive bibliographic coverage or exclusive priority.

The coverage is:

- **Statement and classical implications:** Coven–Meyerowitz, Theorems A/B1/B2; Konyagin–Łaba, Conjecture 1.3, *J. Number Theory* 103 (2003), 267–280, [publisher record](https://doi.org/10.1016/j.jnt.2003.06.006).
- **Periodicity and prime-power tiles:** Newman, *J. Number Theory* 9 (1977), 107–111. The paper also credits Hajós, de Bruijn, and Swenson through CM's explicit historical account in Lemma 1.2. Newman's publisher metadata was checked; the attribution of his finite-window proof was corroborated through CM, not a newly obtained full-text copy of Newman.
- **Dilation and subgroup reductions:** Tijdeman's Theorem 1 and CM's Frobenius reproof; Sands's normalized two-prime subgroup theorem; Szabó's construction and Lagarias–Szabó's order-900 counterexample. Sands's publication year is **1979**, not its received year 1977. Original Sands and Lagarias–Szabó texts were checked; Tijdeman and Szabó metadata and their statements as recorded in CM/Lagarias–Szabó were checked.
- **Modern T2 developments:** Łaba–Londner's 2022 methods paper, 2023 odd-prime paper, 2025 even-prime paper, and 2025 splitting paper. The square-three-prime and shared-prime hypotheses are kept explicit. Publisher metadata and relevant theorem statements were checked.
- **Spectral consequence:** Łaba's 2002 Theorem 1.5(i) and Proposition 1.3. The statement used concerns finite sets and their unit-interval unions, not arbitrary measurable subsets of the line.
- **Algorithmic consequence:** Kolountzakis–Matolcsi's 2009 Theorem 2.1, checked in the [author manuscript](http://math.bme.hu/~matolcsi/talgbekuld.pdf). The parameter is the diameter, not the bit length of a sparse list.
- **Mechanism and boundary:** Tao's stripe discussion; Łaba–Londner's divisor isometries; Kiss–Londner–Matolcsi–Somlai's functional counterexamples. These do not license a claim about arbitrary functional tiles.
- **Formal infrastructure:** de Moura–Ullrich's Lean 4 paper and the mathlib Community's library paper, with the actual toolchain and library revision still pinned separately.

A recent abstract on unsupported mixed cyclotomic divisors (arXiv:2609.06677) was screened for relevance. Its extra-zero phenomenon runs in the converse direction to T2 and was not added merely to enlarge the bibliography. No human review or endorsement is inferred from this citation revision.
