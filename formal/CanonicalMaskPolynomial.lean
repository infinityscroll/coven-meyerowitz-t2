import CyclicEvaluation
import FiberMass
import RelativeCyclotomic

/-!
# Canonical integer polynomial of an actual cyclic mask

`maskPolynomial f` is literally the sum of C(f x)*X^x.val over ZMod N.
The coefficients at canonical residues, arbitrary complex evaluation, value at
one, and primitive-root cyclotomic divisibility are proved from that definition.
For actual integral convolution A*B=1, the mass product and absolute-mass product
are N. Neither T1 nor primary allocation is assumed or asserted in this module.

Positive N is expressed by `NeZero N`. No Boolean assumption is needed: actual
set masks are included, and the identities hold for integral masks generally.
Replay: `lake env lean CanonicalMaskPolynomial.lean` (pinned Lean 4.23.0).
No sorry, added axiom, or native decision oracle is used.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace CanonicalMaskPolynomial

variable {N : ℕ} [NeZero N]

def maskPolynomial (f : AddMonoidAlgebra ℤ (ZMod N)) : ℤ[X] :=
  ∑ x : ZMod N, C (f x) * X ^ x.val

theorem aeval_eq_evaluate (f : AddMonoidAlgebra ℤ (ZMod N)) (z : ℂ) :
    Polynomial.aeval z (maskPolynomial f) = CyclicEvaluation.evaluate f z := by
  simp only [maskPolynomial, map_sum, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X, CyclicEvaluation.evaluate]
  rfl

theorem eval_one_eq_mass (f : AddMonoidAlgebra ℤ (ZMod N)) :
    (maskPolynomial f).eval 1 = FiberMass.mass f := by
  simp only [maskPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one,
    FiberMass.mass]

theorem coeff_val (f : AddMonoidAlgebra ℤ (ZMod N)) (x : ZMod N) :
    (maskPolynomial f).coeff x.val = f x := by
  classical
  simp only [maskPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    (ZMod.val_injective N).eq_iff]
  simp

theorem cyclotomic_dvd_iff_evaluate_eq_zero
    (f : AddMonoidAlgebra ℤ (ZMod N)) {n : ℕ} (hn : 0 < n)
    {z : ℂ} (hz : IsPrimitiveRoot z n) :
    Polynomial.cyclotomic n ℤ ∣ maskPolynomial f ↔ CyclicEvaluation.evaluate f z = 0 := by
  rw [← aeval_eq_evaluate]
  have hroot : Polynomial.aeval z (Polynomial.cyclotomic n ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hz.isRoot_cyclotomic hn
  constructor
  · rintro ⟨Q, hQ⟩
    rw [hQ, map_mul, hroot, zero_mul]
  · intro h
    rw [Polynomial.cyclotomic_eq_minpoly hz hn]
    exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral hn) h

theorem tiling_mass_product (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) :
    FiberMass.mass A * FiberMass.mass B = (N : ℤ) := by
  rw [← FiberMass.mass_mul, htile]
  simp [FiberMass.mass, StripeCollapse.constantMask_apply, ZMod.card]

theorem tiling_mass_natAbs_product (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) :
    (FiberMass.mass A).natAbs * (FiberMass.mass B).natAbs = N := by
  have h := congrArg Int.natAbs (tiling_mass_product A B htile)
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h

theorem tiling_mass_ne_zero (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) :
    FiberMass.mass A ≠ 0 ∧ FiberMass.mass B ≠ 0 := by
  have h := tiling_mass_product A B htile
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  exact mul_ne_zero_iff.mp (h ▸ hN)

end CanonicalMaskPolynomial

#print axioms CanonicalMaskPolynomial.coeff_val
#print axioms CanonicalMaskPolynomial.aeval_eq_evaluate
#print axioms CanonicalMaskPolynomial.eval_one_eq_mass
#print axioms CanonicalMaskPolynomial.cyclotomic_dvd_iff_evaluate_eq_zero
#print axioms CanonicalMaskPolynomial.tiling_mass_natAbs_product
