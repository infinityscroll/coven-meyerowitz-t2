import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
Periodicity from root-evaluation vanishing on a finite cyclic group.
The proof uses Mathlib's proved discrete Fourier inversion equivalence;
character separation or Fourier injectivity is not an assumed hypothesis.
-/

open scoped BigOperators

noncomputable section

namespace FourierPeriod

variable {N : ℕ} [NeZero N]

/-- Literal evaluation of the canonical-residue mask at a complex number. -/
def rootEval (f : ZMod N → ℂ) (theta : ℂ) : ℂ :=
  ∑ n, f n * theta ^ n.val

theorem stdAddChar_is_root (k : ZMod N) :
    (ZMod.stdAddChar k) ^ N = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self,
    zero_mul, AddChar.map_zero_eq_one]

/-- Mathlib's negative-sign DFT is exactly the literal mask evaluation at
the corresponding Nth root, including the canonical exponent n.val. -/
theorem dft_eq_rootEval (f : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft f k = rootEval f (ZMod.stdAddChar (-k)) := by
  rw [ZMod.dft_apply, rootEval]
  apply Finset.sum_congr rfl
  intro n hn
  have hpow : (ZMod.stdAddChar (-k)) ^ n.val = ZMod.stdAddChar (-(n * k)) := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_neg]
  simp only [hpow, smul_eq_mul, mul_comm]

theorem dft_zero_of_root_vanishing (r : ℕ) (f : ZMod N → ℂ)
    (hvanish : ∀ theta : ℂ, theta ^ N = 1 → theta ^ r ≠ 1 → rootEval f theta = 0)
    (k : ZMod N) (hk : (r : ZMod N) * k ≠ 0) :
    ZMod.dft f k = 0 := by
  rw [dft_eq_rootEval]
  apply hvanish _ (stdAddChar_is_root (-k))
  intro h
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_neg] at h
  have hz : -((r : ZMod N) * k) = 0 :=
    ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
  exact hk (neg_eq_zero.mp hz)

/-- The annihilator condition forces period r for every complex mask on
ZMod N. No prime-power condition or divisibility relation on r is needed. -/
theorem complex_period_of_root_vanishing (r : ℕ) (f : ZMod N → ℂ)
    (hvanish : ∀ theta : ℂ, theta ^ N = 1 → theta ^ r ≠ 1 → rootEval f theta = 0) :
    ∀ x, f (x + (r : ZMod N)) = f x := by
  intro x
  have hinv (y : ZMod N) :
      f y = (N : ℂ)⁻¹ * ∑ k, ZMod.stdAddChar (y * k) * ZMod.dft f k := by
    have h := congrFun ((ZMod.dft (N := N) (E := ℂ)).symm_apply_apply f) y
    simpa only [ZMod.invDFT_apply, smul_eq_mul, mul_comm] using h.symm
  rw [hinv (x + (r : ZMod N)), hinv x]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkr : (r : ZMod N) * k = 0
  · simp only [add_mul, hkr, add_zero]
  · have hz := dft_zero_of_root_vanishing r f hvanish k hkr
    simp only [hz, mul_zero]

/-- Integral coefficients are recovered by injectivity of their complex cast. -/
theorem integer_period_of_root_vanishing (r : ℕ) (f : ZMod N → ℤ)
    (hvanish : ∀ theta : ℂ, theta ^ N = 1 → theta ^ r ≠ 1 →
      rootEval (fun n => (f n : ℂ)) theta = 0) :
    ∀ x, f (x + (r : ZMod N)) = f x := by
  intro x
  have h := complex_period_of_root_vanishing r (fun n => (f n : ℂ)) hvanish x
  exact Int.cast_injective h

/-- The same implication for an actual integral group-algebra mask. -/
theorem integral_mask_period_of_root_vanishing (r : ℕ)
    (f : AddMonoidAlgebra ℤ (ZMod N))
    (hvanish : ∀ theta : ℂ, theta ^ N = 1 → theta ^ r ≠ 1 →
      rootEval (fun n => (f n : ℂ)) theta = 0) :
    ∀ x, f (x + (r : ZMod N)) = f x :=
  integer_period_of_root_vanishing r f hvanish

/-- The manuscript's period-R implication for a mask on ZMod (K*R), with
positive K and R. The vanishing condition is the only spectral premise. -/
theorem integral_mask_period_mul {K R : ℕ} (hK : 0 < K) (hR : 0 < R) :
    letI : NeZero (K * R) := ⟨Nat.ne_of_gt (Nat.mul_pos hK hR)⟩
    ∀ f : AddMonoidAlgebra ℤ (ZMod (K * R)),
      (∀ theta : ℂ, theta ^ (K * R) = 1 → theta ^ R ≠ 1 →
        rootEval (fun n => (f n : ℂ)) theta = 0) →
      ∀ x, f (x + (R : ZMod (K * R))) = f x := by
  letI : NeZero (K * R) := ⟨Nat.ne_of_gt (Nat.mul_pos hK hR)⟩
  intro f hvanish
  exact integral_mask_period_of_root_vanishing R f hvanish

#print axioms dft_eq_rootEval
#print axioms complex_period_of_root_vanishing
#print axioms integral_mask_period_mul

end FourierPeriod
