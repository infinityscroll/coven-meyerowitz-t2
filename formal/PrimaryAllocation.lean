import CanonicalMaskPolynomial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import CyclicFiberEvaluation
import Mathlib.Algebra.Polynomial.Div

/-!
# Exact primary allocation derived from actual integral cyclic tiling

This file starts from actual A,B : Z[ZMod N] and A*B=constantMask 1, with N>0.
The canonical polynomials are the literal integer mask polynomials from the
imported module. No T1, exact allocation, or cardinality exhaustion is assumed.

For a prime q, `ownedLevels f q a` is the concrete finite set of k<a for which
Phi_(q^(k+1)) divides maskPolynomial f in Z[X]. The zero-based index k represents
the positive primary exponent k+1. Taking a = N.factorization q, the file proves:

* the two actual owner sets have union range a and are disjoint;
* their cardinalities equal the q-valuations of the absolute integral masses;
* every positive q-primary factor of either mask polynomial divides N;
* in particular there are no extra primary factors outside N, also when q∤N.

The proof includes integral cyclotomic relative primality, simultaneous product
divisibility for any finite set of distinct primary levels, evaluation at one
giving q^card divisibility of the actual mass, coverage from a genuine primitive
root and actual convolution, and mass-product valuation exhaustion. The absence
of extra factors is proved by inserting an additional level into the finite
valuation budget, not by assuming a period restriction on primary factors.

These conclusions hold for integral masks generally. Boolean/nonnegative set
tilings are included; for them the positive mass is the usual cardinality.

The final ordinary-fiber interface is also proved, not assumed: Phi_p divides
the canonical mask polynomial iff all literal base-p fiber masses are equal.
For positive total mass these equal masses are positive. In an actual tiling,
if B owns Phi_p, B has equal fiber masses and A has a pair of unequal masses.
The fiber sums use `CyclicFiberEvaluation.fiberIndex` directly and need no new
fiber decomposition premise. This is not a T2 or full CM formalization.

Replay: `lake env lean PrimaryAllocation.lean` in the pinned Lean 4.23.0 project.
No sorry, added axiom, or native decision oracle is used.
-/

open scoped BigOperators
open Polynomial CanonicalMaskPolynomial

noncomputable section

namespace PrimaryAllocation

theorem cyclotomic_isRelPrime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hne : m ≠ n) :
    IsRelPrime (cyclotomic m ℤ) (cyclotomic n ℤ) := by
  apply (cyclotomic.irreducible hm).isRelPrime_iff_not_dvd.mpr
  intro hdiv
  apply hne
  apply cyclotomic_injective (R := ℤ)
  exact eq_of_monic_of_associated (cyclotomic.monic m ℤ) (cyclotomic.monic n ℤ)
    (Irreducible.associated_of_dvd (cyclotomic.irreducible hm)
      (cyclotomic.irreducible hn) hdiv)

variable {N : ℕ} [NeZero N]

theorem primary_product_dvd (f : AddMonoidAlgebra ℤ (ZMod N))
    {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial f) :
    (∏ k ∈ s, cyclotomic (q ^ (k + 1)) ℤ) ∣ maskPolynomial f := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro i hi j hj hij
    apply cyclotomic_isRelPrime (pow_pos hq.pos _) (pow_pos hq.pos _)
    intro heq
    have h := Nat.pow_right_injective hq.two_le heq
    omega
  · exact hs

theorem primary_mass_dvd (f : AddMonoidAlgebra ℤ (ZMod N))
    {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial f) :
    q ^ s.card ∣ (FiberMass.mass f).natAbs := by
  letI : Fact q.Prime := ⟨hq⟩
  have h := map_dvd (Polynomial.evalRingHom (1 : ℤ)) (primary_product_dvd f hq s hs)
  have hi : (q : ℤ) ^ s.card ∣ FiberMass.mass f := by
    simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_prod,
      Polynomial.eval_one_cyclotomic_prime_pow, Finset.prod_const, eval_one_eq_mass] using h
  have hn := Int.natAbs_dvd_natAbs.mpr hi
  simpa only [Int.natAbs_pow, Int.natAbs_natCast] using hn

theorem primary_card_le_valuation (f : AddMonoidAlgebra ℤ (ZMod N))
    (hf : FiberMass.mass f ≠ 0) {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial f) :
    s.card ≤ (FiberMass.mass f).natAbs.factorization q := by
  apply (hq.pow_dvd_iff_le_factorization (fun h => hf (Int.natAbs_eq_zero.mp h))).mp
  exact primary_mass_dvd f hq s hs

theorem cyclotomic_coverage (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {n : ℕ} (hn : 1 < n) (hnN : n ∣ N) :
    cyclotomic n ℤ ∣ maskPolynomial A ∨ cyclotomic n ℤ ∣ maskPolynomial B := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n (by omega)
  have hzN : z ^ N = 1 := (hz.pow_eq_one_iff_dvd N).mpr hnN
  have h := CyclicEvaluation.tiling_evaluation_product_zero A B htile hzN (hz.ne_one hn)
  rw [mul_eq_zero] at h
  exact h.imp ((cyclotomic_dvd_iff_evaluate_eq_zero A (by omega) hz).mpr)
    ((cyclotomic_dvd_iff_evaluate_eq_zero B (by omega) hz).mpr)

def ownedLevels (f : AddMonoidAlgebra ℤ (ZMod N)) (q a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter (fun k => cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial f)

@[simp] theorem mem_ownedLevels (f : AddMonoidAlgebra ℤ (ZMod N)) (q a k : ℕ) :
    k ∈ ownedLevels f q a ↔ k < a ∧ cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial f := by
  classical
  simp [ownedLevels]

theorem ownedLevels_union (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime) :
    ownedLevels A q (N.factorization q) ∪ ownedLevels B q (N.factorization q) =
      Finset.range (N.factorization q) := by
  classical
  ext k
  simp only [Finset.mem_union, mem_ownedLevels, Finset.mem_range]
  constructor
  · intro h
    exact h.elim And.left And.left
  · intro hk
    have hdvd : q ^ (k + 1) ∣ N :=
      (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mpr (by omega)
    have hbig : 1 < q ^ (k + 1) := Nat.one_lt_pow (by omega) hq.one_lt
    exact (cyclotomic_coverage A B htile hbig hdvd).imp (And.intro hk) (And.intro hk)

theorem exact_primary_allocation (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime) :
    Disjoint (ownedLevels A q (N.factorization q)) (ownedLevels B q (N.factorization q)) ∧
    (ownedLevels A q (N.factorization q)).card = (FiberMass.mass A).natAbs.factorization q ∧
    (ownedLevels B q (N.factorization q)).card = (FiberMass.mass B).natAbs.factorization q := by
  classical
  have hn := tiling_mass_ne_zero A B htile
  have hA := primary_card_le_valuation A hn.1 hq (ownedLevels A q (N.factorization q))
    (fun k hk => (mem_ownedLevels A q (N.factorization q) k).mp hk |>.2)
  have hB := primary_card_le_valuation B hn.2 hq (ownedLevels B q (N.factorization q))
    (fun k hk => (mem_ownedLevels B q (N.factorization q) k).mp hk |>.2)
  have hf := Nat.factorization_mul
    (a := (FiberMass.mass A).natAbs) (b := (FiberMass.mass B).natAbs)
    (fun h => hn.1 (Int.natAbs_eq_zero.mp h)) (fun h => hn.2 (Int.natAbs_eq_zero.mp h))
  rw [tiling_mass_natAbs_product A B htile] at hf
  have hfq := congrArg (fun f : ℕ →₀ ℕ => f q) hf
  simp only [Finsupp.add_apply] at hfq
  have hc := Finset.card_union_add_card_inter
    (ownedLevels A q (N.factorization q)) (ownedLevels B q (N.factorization q))
  rw [ownedLevels_union A B htile hq, Finset.card_range] at hc
  have hz : ((ownedLevels A q (N.factorization q)) ∩
      (ownedLevels B q (N.factorization q))).card = 0 := by omega
  refine ⟨Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz), ?_, ?_⟩
  · omega
  · omega

theorem primary_owner_iff_not (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime)
    {k : ℕ} (hk : q ^ (k + 1) ∣ N) :
    (cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial A) ↔
      ¬ (cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial B) := by
  have hka : k < N.factorization q := by
    have h := (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mp hk
    omega
  have hdis := (exact_primary_allocation A B htile hq).1
  have hcover := cyclotomic_coverage A B htile
    (Nat.one_lt_pow (by omega : k + 1 ≠ 0) hq.one_lt) hk
  constructor
  · intro hA hB
    exact Finset.disjoint_left.mp hdis
      ((mem_ownedLevels A q (N.factorization q) k).mpr ⟨hka, hA⟩)
      ((mem_ownedLevels B q (N.factorization q) k).mpr ⟨hka, hB⟩)
  · intro hB
    exact hcover.resolve_right hB

theorem primary_divisor_within_period (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime)
    {k : ℕ} (hk : cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial A) :
    q ^ (k + 1) ∣ N := by
  classical
  apply (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mpr
  by_contra hnot
  have hka : N.factorization q ≤ k := by omega
  have hmem : k ∉ ownedLevels A q (N.factorization q) := by
    simp only [mem_ownedLevels, not_and]
    intro hlt
    omega
  have hn := (tiling_mass_ne_zero A B htile).1
  have hb := primary_card_le_valuation A hn hq
    (insert k (ownedLevels A q (N.factorization q))) (by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hk
      · exact (mem_ownedLevels A q (N.factorization q) j).mp hj |>.2)
  rw [Finset.card_insert_of_notMem hmem,
    (exact_primary_allocation A B htile hq).2.1] at hb
  omega

theorem no_primary_outside_period (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime)
    {k : ℕ} (hk : ¬ q ^ (k + 1) ∣ N) :
    ¬ cyclotomic (q ^ (k + 1)) ℤ ∣ maskPolynomial A := by
  intro h
  exact hk (primary_divisor_within_period A B htile hq h)

theorem primary_divisor_within_period_pos (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) {q : ℕ} (hq : q.Prime)
    {k : ℕ} (hkpos : 0 < k) (hk : cyclotomic (q ^ k) ℤ ∣ maskPolynomial A) :
    q ^ k ∣ N := by
  cases k with
  | zero => omega
  | succ k => exact primary_divisor_within_period A B htile hq hk

theorem nonnegative_tiling_mass_positive (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) (hA : ∀ x, 0 ≤ A x) :
    0 < FiberMass.mass A := by
  have hn := (tiling_mass_ne_zero A B htile).1
  have hp : 0 ≤ FiberMass.mass A := Finset.sum_nonneg (fun x _ => hA x)
  omega

section BaseFibers

variable (p M : ℕ) [NeZero p] [NeZero M]

def baseFiberMass (f : AddMonoidAlgebra ℤ (ZMod (p * M))) (i : Fin p) : ℤ :=
  ∑ a : ZMod M, f (CyclicFiberEvaluation.fiberIndex p M i a)

def baseMassPolynomial (f : AddMonoidAlgebra ℤ (ZMod (p * M))) : ℤ[X] :=
  ∑ i : Fin p, C (baseFiberMass p M f i) * X ^ i.val

omit [NeZero p] in
theorem baseMassPolynomial_coeff (f : AddMonoidAlgebra ℤ (ZMod (p * M))) (i : Fin p) :
    (baseMassPolynomial p M f).coeff i.val = baseFiberMass p M f i := by
  classical
  simp only [baseMassPolynomial, finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
  simp

theorem baseMassPolynomial_natDegree_lt (f : AddMonoidAlgebra ℤ (ZMod (p * M))) :
    (baseMassPolynomial p M f).natDegree < p := by
  by_cases h : baseMassPolynomial p M f = 0
  · rw [h, natDegree_zero]
    exact NeZero.pos p
  · exact (natDegree_lt_iff_degree_lt h).mpr (degree_sum_fin_lt _)

theorem evaluate_eq_baseMassPolynomial (f : AddMonoidAlgebra ℤ (ZMod (p * M)))
    {z : ℂ} (hz : z ^ p = 1) :
    CyclicEvaluation.evaluate f z = aeval z (baseMassPolynomial p M f) := by
  change (∑ x : ZMod (p * M), (f x : ℂ) * z ^ x.val) = _
  rw [CyclicFiberEvaluation.integer_eval_regroup, hz]
  simp only [baseMassPolynomial, map_sum, map_mul, map_pow, aeval_C, aeval_X,
    one_pow, mul_one, baseFiberMass]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem prime_divisor_iff_equal_fiber_masses
    (f : AddMonoidAlgebra ℤ (ZMod (p * M))) (hp : p.Prime) :
    cyclotomic p ℤ ∣ maskPolynomial f ↔
      ∀ i j : Fin p, baseFiberMass p M f i = baseFiberMass p M f j := by
  letI : Fact p.Prime := ⟨hp⟩
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hz : IsPrimitiveRoot z p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hc : ∀ i : Fin p, (cyclotomic p ℤ).coeff i.val = 1 := by
    intro i
    rw [cyclotomic_prime]
    simp [finset_sum_coeff, coeff_X_pow, i.is_lt]
  have hroots : cyclotomic p ℤ ∣ maskPolynomial f ↔
      cyclotomic p ℤ ∣ baseMassPolynomial p M f := by
    rw [cyclotomic_dvd_iff_evaluate_eq_zero f hp.pos hz,
      evaluate_eq_baseMassPolynomial p M f hz.pow_eq_one]
    constructor
    · intro h
      rw [cyclotomic_eq_minpoly hz hp.pos]
      exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral hp.pos) h
    · rintro ⟨Q, hQ⟩
      have he : aeval z (cyclotomic p ℤ) = 0 := by
        rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
        exact hz.isRoot_cyclotomic hp.pos
      rw [hQ, map_mul, he, zero_mul]
  rw [hroots]
  constructor
  · intro hdiv i j
    have hdeg : (baseMassPolynomial p M f).natDegree ≤ (cyclotomic p ℤ).natDegree := by
      have h := baseMassPolynomial_natDegree_lt p M f
      rw [natDegree_cyclotomic, Nat.totient_prime hp]
      omega
    have he := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (cyclotomic.monic p ℤ) hdiv hdeg
    have hij : (baseMassPolynomial p M f).coeff i.val =
        (baseMassPolynomial p M f).coeff j.val := by
      rw [he, coeff_C_mul, coeff_C_mul, hc, hc]
    simpa only [baseMassPolynomial_coeff] using hij
  · intro h
    let i0 : Fin p := ⟨0, hp.pos⟩
    have he : baseMassPolynomial p M f = C (baseFiberMass p M f i0) * cyclotomic p ℤ := by
      unfold baseMassPolynomial
      simp_rw [h _ i0]
      rw [← Finset.mul_sum, cyclotomic_prime]
      congr 1
      exact Fin.sum_univ_eq_sum_range _ p
    exact ⟨C (baseFiberMass p M f i0), by simpa only [mul_comm] using he⟩

theorem uniform_mass_relation (f : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (h : ∀ i j : Fin p, baseFiberMass p M f i = baseFiberMass p M f j) (i : Fin p) :
    FiberMass.mass f = (p : ℤ) * baseFiberMass p M f i := by
  unfold FiberMass.mass
  rw [← (CyclicFiberEvaluation.fiberEquiv p M).sum_comp f, Fintype.sum_prod_type]
  change (∑ j : Fin p, baseFiberMass p M f j) = _
  simp_rw [h _ i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem prime_divisor_fiber_mass_positive
    (f : AddMonoidAlgebra ℤ (ZMod (p * M))) (hp : p.Prime)
    (hdiv : cyclotomic p ℤ ∣ maskPolynomial f) (hmass : 0 < FiberMass.mass f) :
    ∀ i : Fin p, 0 < baseFiberMass p M f i := by
  intro i
  have h := uniform_mass_relation p M f
    ((prime_divisor_iff_equal_fiber_masses p M f hp).mp hdiv) i
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  nlinarith

theorem tiling_prime_owner_uniformity
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1) (hp : p.Prime)
    (hB : cyclotomic p ℤ ∣ maskPolynomial B) :
    (∀ i j : Fin p, baseFiberMass p M B i = baseFiberMass p M B j) ∧
      (∃ i j : Fin p, baseFiberMass p M A i ≠ baseFiberMass p M A j) := by
  refine ⟨(prime_divisor_iff_equal_fiber_masses p M B hp).mp hB, ?_⟩
  by_contra h
  push_neg at h
  have hA := (prime_divisor_iff_equal_fiber_masses p M A hp).mpr h
  have hdiv : p ^ (0 + 1) ∣ p * M := by simp
  have hex := (primary_owner_iff_not A B htile hp hdiv).mp (by simpa using hA)
  exact hex (by simpa using hB)

end BaseFibers

end PrimaryAllocation

#print axioms PrimaryAllocation.cyclotomic_isRelPrime
#print axioms PrimaryAllocation.primary_product_dvd
#print axioms PrimaryAllocation.primary_card_le_valuation
#print axioms PrimaryAllocation.cyclotomic_coverage
#print axioms PrimaryAllocation.ownedLevels_union
#print axioms PrimaryAllocation.exact_primary_allocation
#print axioms PrimaryAllocation.primary_owner_iff_not
#print axioms PrimaryAllocation.primary_divisor_within_period
#print axioms PrimaryAllocation.primary_divisor_within_period_pos
#print axioms PrimaryAllocation.no_primary_outside_period
#print axioms PrimaryAllocation.prime_divisor_iff_equal_fiber_masses
#print axioms PrimaryAllocation.prime_divisor_fiber_mass_positive
#print axioms PrimaryAllocation.tiling_prime_owner_uniformity
