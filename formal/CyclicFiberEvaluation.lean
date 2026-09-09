import RelativeCyclotomic
import Mathlib.Data.ZMod.Basic
import CyclicEvaluation
import RamifiedCyclotomic

/-!
# Literal cyclic fibers, evaluation regrouping, and the ramified tiling case

For positive p and M (`NeZero` on natural numbers), `fiberIndex` is the literal
index i.val + p*a.val in ZMod(p*M). `fiberEquiv` proves that these indices are a
bijection from Fin p x ZMod M, and `fiberIndex_val` proves that the exponent is
already canonical. Thus `eval_regroup` holds for every complex z, with no root
of unity hypothesis and no assumed decomposition. The elementary regrouping
also permits p = 1 or M = 1; primality is imposed only in the ramified corollary.

For integer masks, `cyclotomicFiberPolynomial` is an actual polynomial over the
intermediate field Q(theta). Its coefficients are literal finite sums of the
integer fiber entries times powers of the actual generator. Its degree is less
than p, and its evaluation at z with z^p = theta is the original cyclic-mask
evaluation. `evaluate_eq_aeval` connects this with `CyclicEvaluation.evaluate`.

The final `ramified_tiling_fiber_zero` theorem starts from actual integral group
algebra convolution A*B = constantMask 1. For p prime, d>0, p|d, theta primitive
d, theta^M = 1, and z^p = theta, it derives that all ordinary fiber evaluations
of A vanish at theta or all those of B do. It proves z^(p*M)=1 and z!=1, obtains
the evaluation-product equation from actual tiling convolution, and applies the
derived relative-degree theorem. No specialized product-zero premise is used.
The theorem includes p=2. Positivity or Boolean masks are not needed for this
character case; actual set tilings are included among these integer masks.

Scope: these are exact index/evaluation statements and one ramified character
consequence. No coprime character case, Fourier inversion, periodic descent,
stripe decomposition, phase tiling, T2 induction, or full CM proof is asserted.
Replay: `lake env lean CyclicFiberEvaluation.lean`, in the pinned Lean 4.23.0
workspace. The axiom reports below are part of the replay. No added axiom or
sorry is used, and no native decision oracle is used.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace CyclicFiberEvaluation

variable (p M : ℕ) [NeZero p] [NeZero M]

def fiberIndex (i : Fin p) (a : ZMod M) : ZMod (p * M) :=
  ((i.val + p * a.val : ℕ) : ZMod (p * M))

theorem fiberIndex_bound (i : Fin p) (a : ZMod M) :
    i.val + p * a.val < p * M := by
  have hi := i.is_lt
  have ha := a.val_lt
  have hp : 0 < p := NeZero.pos p
  nlinarith

@[simp] theorem fiberIndex_val (i : Fin p) (a : ZMod M) :
    (fiberIndex p M i a).val = i.val + p * a.val :=
  ZMod.val_natCast_of_lt (fiberIndex_bound p M i a)

def fiberEquiv : (Fin p × ZMod M) ≃ ZMod (p * M) where
  toFun ia := fiberIndex p M ia.1 ia.2
  invFun x :=
    (⟨x.val % p, Nat.mod_lt _ (NeZero.pos p)⟩, (x.val / p : ZMod M))
  left_inv ia := by
    rcases ia with ⟨i, a⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [fiberIndex_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.is_lt]
    · change (((fiberIndex p M i a).val / p : ℕ) : ZMod M) = a
      rw [fiberIndex_val, Nat.add_mul_div_left _ _ (NeZero.pos p),
        Nat.div_eq_of_lt i.is_lt, zero_add, ZMod.natCast_zmod_val]
  right_inv x := by
    have hdiv : x.val / p < M := by
      apply (Nat.div_lt_iff_lt_mul (NeZero.pos p)).mpr
      simpa only [Nat.mul_comm] using x.val_lt
    change (((x.val % p + p * (x.val / p : ZMod M).val : ℕ)) : ZMod (p * M)) = x
    rw [ZMod.val_natCast_of_lt hdiv, Nat.mod_add_div, ZMod.natCast_zmod_val]

@[simp] theorem fiberEquiv_apply (i : Fin p) (a : ZMod M) :
    fiberEquiv p M (i, a) = fiberIndex p M i a := rfl

def fiber (f : ZMod (p * M) → ℂ) (i : Fin p) (a : ZMod M) : ℂ :=
  f (fiberIndex p M i a)

def maskEval {n : ℕ} [NeZero n] (f : ZMod n → ℂ) (z : ℂ) : ℂ :=
  ∑ x : ZMod n, f x * z ^ x.val

theorem sum_fibers (f : ZMod (p * M) → ℂ) :
    ∑ x, f x = ∑ i : Fin p, ∑ a : ZMod M, fiber p M f i a := by
  rw [← (fiberEquiv p M).sum_comp f, Fintype.sum_prod_type]
  rfl

theorem eval_regroup (f : ZMod (p * M) → ℂ) (z : ℂ) :
    maskEval f z = ∑ i : Fin p, z ^ i.val * maskEval (fiber p M f i) (z ^ p) := by
  unfold maskEval
  rw [← (fiberEquiv p M).sum_comp (fun x => f x * z ^ x.val),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberEquiv_apply, fiberIndex_val, fiber, pow_add, pow_mul]
  ring

def fiberPolynomial (f : ZMod (p * M) → ℂ) (t : ℂ) : ℂ[X] :=
  ∑ i : Fin p, C (maskEval (fiber p M f i) t) * X ^ i.val

omit [NeZero p] in
theorem fiberPolynomial_eval (f : ZMod (p * M) → ℂ) (t z : ℂ) :
    (fiberPolynomial p M f t).eval z =
      ∑ i : Fin p, z ^ i.val * maskEval (fiber p M f i) t := by
  simp only [fiberPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [NeZero p] in
theorem fiberPolynomial_degree_lt (f : ZMod (p * M) → ℂ) (t : ℂ) :
    (fiberPolynomial p M f t).degree < p :=
  Polynomial.degree_sum_fin_lt (fun i => maskEval (fiber p M f i) t)

theorem fiberPolynomial_natDegree_lt (f : ZMod (p * M) → ℂ) (t : ℂ) :
    (fiberPolynomial p M f t).natDegree < p := by
  by_cases h : fiberPolynomial p M f t = 0
  · rw [h, Polynomial.natDegree_zero]
    exact NeZero.pos p
  · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr
      (fiberPolynomial_degree_lt p M f t)

theorem eval_at_root (f : ZMod (p * M) → ℂ) {t z : ℂ} (hz : z ^ p = t) :
    maskEval f z = (fiberPolynomial p M f t).eval z := by
  rw [eval_regroup p M f z, hz, fiberPolynomial_eval]

theorem integer_eval_regroup (f : ZMod (p * M) → ℤ) (z : ℂ) :
    (∑ x : ZMod (p * M), (f x : ℂ) * z ^ x.val) =
      ∑ i : Fin p, z ^ i.val *
        ∑ a : ZMod M, (f (fiberIndex p M i a) : ℂ) * (z ^ p) ^ a.val :=
  eval_regroup p M (fun x => (f x : ℂ)) z

open IntermediateField
open scoped IntermediateField

def cyclotomicFiberPolynomial (f : ZMod (p * M) → ℤ) (θ : ℂ) : ℚ⟮θ⟯[X] :=
  ∑ i : Fin p,
    C (∑ a : ZMod M, (f (fiberIndex p M i a) : ℚ⟮θ⟯) *
      (IntermediateField.AdjoinSimple.gen ℚ θ) ^ a.val) * X ^ i.val

omit [NeZero p] in
theorem cyclotomicFiberPolynomial_coeff
    (f : ZMod (p * M) → ℤ) (θ : ℂ) (i : Fin p) :
    (cyclotomicFiberPolynomial p M f θ).coeff i.val =
      ∑ a : ZMod M, (f (fiberIndex p M i a) : ℚ⟮θ⟯) *
        (IntermediateField.AdjoinSimple.gen ℚ θ) ^ a.val := by
  classical
  simp only [cyclotomicFiberPolynomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
  simp

omit [NeZero p] in
theorem cyclotomicFiberPolynomial_coeff_map
    (f : ZMod (p * M) → ℤ) (θ : ℂ) (i : Fin p) :
    algebraMap ℚ⟮θ⟯ ℂ ((cyclotomicFiberPolynomial p M f θ).coeff i.val) =
      maskEval (fiber p M (fun x => (f x : ℂ)) i) θ := by
  rw [cyclotomicFiberPolynomial_coeff]
  simp only [map_sum, map_mul, map_pow, map_intCast]
  rfl

theorem cyclotomicFiberPolynomial_natDegree_lt
    (f : ZMod (p * M) → ℤ) (θ : ℂ) :
    (cyclotomicFiberPolynomial p M f θ).natDegree < p := by
  by_cases h : cyclotomicFiberPolynomial p M f θ = 0
  · rw [h, Polynomial.natDegree_zero]
    exact NeZero.pos p
  · apply (Polynomial.natDegree_lt_iff_degree_lt h).mpr
    exact Polynomial.degree_sum_fin_lt _

theorem integer_eval_at_root (f : ZMod (p * M) → ℤ) {θ z : ℂ}
    (hz : z ^ p = θ) :
    (∑ x : ZMod (p * M), (f x : ℂ) * z ^ x.val) =
      Polynomial.aeval z (cyclotomicFiberPolynomial p M f θ) := by
  rw [integer_eval_regroup p M f z, hz]
  simp only [cyclotomicFiberPolynomial, map_sum, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, map_intCast]
  apply Finset.sum_congr rfl
  intro i _
  have hgen : algebraMap ℚ⟮θ⟯ ℂ (IntermediateField.AdjoinSimple.gen ℚ θ) = θ := rfl
  rw [hgen]
  exact mul_comm _ _

theorem evaluate_eq_aeval (f : AddMonoidAlgebra ℤ (ZMod (p * M))) {θ z : ℂ}
    (hz : z ^ p = θ) :
    CyclicEvaluation.evaluate f z =
      Polynomial.aeval z (cyclotomicFiberPolynomial p M f θ) :=
  integer_eval_at_root p M f hz

theorem ramified_tiling_polynomial_zero
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 0 < d) (hpd : p ∣ d)
    {θ z : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1) (hz : z ^ p = θ) :
    cyclotomicFiberPolynomial p M A θ = 0 ∨
      cyclotomicFiberPolynomial p M B θ = 0 := by
  have hzN : z ^ (p * M) = 1 := by rw [pow_mul, hz, hθM]
  have hzne : z ≠ 1 := by
    intro heq
    have hdtwo : 2 ≤ d := hp.two_le.trans (Nat.le_of_dvd hd hpd)
    apply hθ.ne_one (by omega)
    rw [← hz, heq, one_pow]
  have heval := CyclicEvaluation.tiling_evaluation_product_zero A B htile hzN hzne
  rw [evaluate_eq_aeval p M A hz, evaluate_eq_aeval p M B hz] at heval
  apply RamifiedCyclotomic.low_degree_product_zero hp hd hpd hθ hz
    (cyclotomicFiberPolynomial p M A θ) (cyclotomicFiberPolynomial p M B θ)
    (cyclotomicFiberPolynomial_natDegree_lt p M A θ)
    (cyclotomicFiberPolynomial_natDegree_lt p M B θ)
  rw [map_mul]
  exact heval

theorem ramified_tiling_fiber_zero
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 0 < d) (hpd : p ∣ d)
    {θ z : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1) (hz : z ^ p = θ) :
    (∀ i : Fin p, maskEval (fiber p M (fun x => (A x : ℂ)) i) θ = 0) ∨
      (∀ i : Fin p, maskEval (fiber p M (fun x => (B x : ℂ)) i) θ = 0) := by
  have hzero : ∀ f : AddMonoidAlgebra ℤ (ZMod (p * M)),
      cyclotomicFiberPolynomial p M f θ = 0 →
        ∀ i : Fin p, maskEval (fiber p M (fun x => (f x : ℂ)) i) θ = 0 := by
    intro f hf i
    rw [← cyclotomicFiberPolynomial_coeff_map p M f θ i, hf,
      Polynomial.coeff_zero, map_zero]
  exact (ramified_tiling_polynomial_zero p M A B htile hp hd hpd hθ hθM hz).imp
    (hzero A) (hzero B)

end CyclicFiberEvaluation

#print axioms CyclicFiberEvaluation.fiberEquiv
#print axioms CyclicFiberEvaluation.fiberIndex_val
#print axioms CyclicFiberEvaluation.eval_regroup
#print axioms CyclicFiberEvaluation.cyclotomicFiberPolynomial_natDegree_lt
#print axioms CyclicFiberEvaluation.cyclotomicFiberPolynomial_coeff_map
#print axioms CyclicFiberEvaluation.evaluate_eq_aeval
#print axioms CyclicFiberEvaluation.ramified_tiling_polynomial_zero
#print axioms CyclicFiberEvaluation.ramified_tiling_fiber_zero
