import PrimaryAllocation
import DephasedMasks

/-!
# An actual common fiber complement lifts upstairs and forces primary inheritance

For positive p,M, `embed p M C` is the literal integral mask on ZMod(p*M)
supported on residue zero modulo p: at the canonical index p*a.val its entry is
C a, and other residues have entry zero. The definition, coefficient theorem,
injectivity, and Boolean preservation are explicit; no abstract embedding or
common-complement predicate is assumed.

`evaluate_embed` proves eval(embed C,z)=eval(C,z^p) for every complex z.
`common_complement_lifts` starts from the actual p convolution identities
C * integerFiber B j = J_M and derives the actual identity
B * embed C = J_(p*M), using proved evaluation regrouping and Fourier separation.

`prime_power_inherits` is the requested original-complement allocation bridge.
For primes p,q with q!=p, e>0, and Phi_(q^e) dividing the actual upstairs B
polynomial, it proves q^e divides M and Phi_(q^e) divides every original B_j
polynomial. The period condition q^e|(p*M) is itself derived from exact primary
allocation of B and embed C. Coprimality gives q^e|M. Exact upstairs allocation
excludes that primary factor from embed C; evaluation and the fact that z->z^p
preserves primitive q^e roots excludes it from C. Actual lower tiling coverage
then forces it into each original fiber. No desired inheritance, T1, or abstract
specialized polynomial identity is an input.

All statements hold for integral masks, so actual Boolean set tilings are
included. This file does not prove either-factor T2 induction or full CM.
Replay: `lake env lean CommonComplementLift.lean` in the pinned Lean 4.23.0
workspace. No sorry, added axiom, or native decision oracle is used.
-/

open scoped BigOperators
open Polynomial CanonicalMaskPolynomial CyclicFiberEvaluation DephasedMasks

noncomputable section

namespace CommonComplementLift

variable (p M : ℕ) [NeZero p] [NeZero M]

def embed (C : AddMonoidAlgebra ℤ (ZMod M)) : AddMonoidAlgebra ℤ (ZMod (p * M)) :=
  Finsupp.equivFunOnFinite.symm (fun x =>
    if x.val % p = 0 then C (x.val / p : ZMod M) else 0)

@[simp] theorem embed_apply (C : AddMonoidAlgebra ℤ (ZMod M)) (x : ZMod (p * M)) :
    embed p M C x = if x.val % p = 0 then C (x.val / p : ZMod M) else 0 := rfl

@[simp] theorem embed_fiberIndex (C : AddMonoidAlgebra ℤ (ZMod M))
    (i : Fin p) (a : ZMod M) :
    embed p M C (fiberIndex p M i a) = if i = 0 then C a else 0 := by
  simp only [embed_apply, fiberIndex_val, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt i.is_lt, Nat.add_mul_div_left _ _ (NeZero.pos p),
    Nat.div_eq_of_lt i.is_lt, zero_add, ZMod.natCast_zmod_val]
  simp only [Fin.ext_iff, Fin.val_zero]

@[simp] theorem integerFiber_embed (C : AddMonoidAlgebra ℤ (ZMod M)) (i : Fin p) :
    integerFiber p M (embed p M C) i = if i = 0 then C else 0 := by
  ext a
  simp only [integerFiber_apply, embed_fiberIndex]
  split_ifs <;> rfl

theorem evaluate_regroup (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (z : ℂ) :
    CyclicEvaluation.evaluate B z =
      ∑ i : Fin p, z ^ i.val * CyclicEvaluation.evaluate (integerFiber p M B i) (z ^ p) :=
  integer_eval_regroup p M B z

theorem evaluate_embed (C : AddMonoidAlgebra ℤ (ZMod M)) (z : ℂ) :
    CyclicEvaluation.evaluate (embed p M C) z = CyclicEvaluation.evaluate C (z ^ p) := by
  rw [evaluate_regroup]
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp only [integerFiber_embed, ite_true, Fin.val_zero, pow_zero, one_mul]
  · intro i _ hi
    simp only [integerFiber_embed, hi, ite_false, CyclicEvaluation.evaluate,
      Finsupp.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
      mul_zero]
  · simp

theorem common_complement_lifts
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (C : AddMonoidAlgebra ℤ (ZMod M))
    (hcommon : ∀ j : Fin p, C * integerFiber p M B j = StripeCollapse.constantMask 1) :
    B * embed p M C = StripeCollapse.constantMask 1 := by
  apply SpectralIdentities.evaluations_determine_mask
  intro z hz
  have hzp : (z ^ p) ^ M = 1 := by rwa [← pow_mul]
  have heach : ∀ j : Fin p,
      CyclicEvaluation.evaluate (integerFiber p M B j) (z ^ p) *
        CyclicEvaluation.evaluate C (z ^ p) =
          CyclicEvaluation.evaluate (StripeCollapse.constantMask 1 :
            AddMonoidAlgebra ℤ (ZMod M)) (z ^ p) := by
    intro j
    rw [← CyclicEvaluation.evaluate_mul _ _ hzp, mul_comm, hcommon]
  rw [CyclicEvaluation.evaluate_mul _ _ hz, evaluate_embed,
    evaluate_regroup p M B z, Finset.sum_mul, evaluate_regroup]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, heach]
  congr 2

theorem cyclotomic_dvd_embed_iff (C : AddMonoidAlgebra ℤ (ZMod M))
    {n : ℕ} (hn : 0 < n) (hcop : p.Coprime n) :
    cyclotomic n ℤ ∣ maskPolynomial (embed p M C) ↔
      cyclotomic n ℤ ∣ maskPolynomial C := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  rw [cyclotomic_dvd_iff_evaluate_eq_zero (embed p M C) hn hz, evaluate_embed,
    ← cyclotomic_dvd_iff_evaluate_eq_zero C hn (hz.pow_of_coprime p hcop)]

theorem prime_power_inherits
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (C : AddMonoidAlgebra ℤ (ZMod M))
    (hcommon : ∀ j : Fin p, C * integerFiber p M B j = StripeCollapse.constantMask 1)
    (hp : p.Prime) {q e : ℕ} (hq : q.Prime) (hqp : q ≠ p) (he : 0 < e)
    (hB : cyclotomic (q ^ e) ℤ ∣ maskPolynomial B) :
    q ^ e ∣ M ∧ ∀ j : Fin p, cyclotomic (q ^ e) ℤ ∣ maskPolynomial (integerFiber p M B j) := by
  have hup := common_complement_lifts p M B C hcommon
  have hcop : (q ^ e).Coprime p := ((Nat.coprime_primes hq hp).mpr hqp).pow_left e
  have hnN := PrimaryAllocation.primary_divisor_within_period_pos B (embed p M C) hup hq he hB
  have hnM : q ^ e ∣ M := hcop.dvd_mul_left.mp hnN
  refine ⟨hnM, ?_⟩
  have hnotembed : ¬ cyclotomic (q ^ e) ℤ ∣ maskPolynomial (embed p M C) := by
    cases e with
    | zero => omega
    | succ k => exact (PrimaryAllocation.primary_owner_iff_not B (embed p M C) hup hq hnN).mp hB
  have hnotC : ¬ cyclotomic (q ^ e) ℤ ∣ maskPolynomial C := by
    intro hC
    exact hnotembed ((cyclotomic_dvd_embed_iff p M C (pow_pos hq.pos _) hcop.symm).mpr hC)
  intro j
  have hcover := PrimaryAllocation.cyclotomic_coverage C (integerFiber p M B j) (hcommon j)
    (Nat.one_lt_pow he.ne' hq.one_lt) hnM
  exact hcover.resolve_left hnotC

theorem embed_boolean (C : AddMonoidAlgebra ℤ (ZMod M))
    (hC : ∀ a, C a = 0 ∨ C a = 1) :
    ∀ x, embed p M C x = 0 ∨ embed p M C x = 1 := by
  intro x
  rw [embed_apply]
  split_ifs
  · exact hC _
  · exact Or.inl rfl

theorem embed_injective : Function.Injective (embed p M) := by
  intro C D h
  ext a
  have hx := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod (p * M)) =>
    f (fiberIndex p M (0 : Fin p) a)) h
  simpa only [embed_fiberIndex, ite_true] using hx

end CommonComplementLift

#print axioms CommonComplementLift.integerFiber_embed
#print axioms CommonComplementLift.evaluate_embed
#print axioms CommonComplementLift.common_complement_lifts
#print axioms CommonComplementLift.cyclotomic_dvd_embed_iff
#print axioms CommonComplementLift.prime_power_inherits
#print axioms CommonComplementLift.embed_boolean
#print axioms CommonComplementLift.embed_injective
