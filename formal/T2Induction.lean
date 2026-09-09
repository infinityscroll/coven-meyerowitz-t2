import CanonicalMaskPolynomial
import DephasedMasks
import ResidueGrading
import PhaseIsolation
import PrimeDirectionArithmetic
import PrimaryAllocation
import CommonComplementLift

/-!
Full, unbounded T2 definitions and completed induction bridges.
The obligation ledger records which links to a full both-factor cyclic
induction remain open. No incomplete theorem or placeholder proof is declared.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace T2Induction

def selectedOrder (S : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ q ∈ S, q ^ e q

/-- Full T2: every nonempty finite family of distinct prime labels, with
arbitrary positive levels. There is no bound on the size of the family. -/
def PolynomialT2 (P : ℤ[X]) : Prop :=
  ∀ (S : Finset ℕ) (e : ℕ → ℕ), S.Nonempty →
    (∀ q ∈ S, q.Prime) → (∀ q ∈ S, 0 < e q) →
    (∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ P) →
    cyclotomic (selectedOrder S e) ℤ ∣ P

def RootT2 (P : ℤ[X]) : Prop :=
  ∀ (S : Finset ℕ) (e : ℕ → ℕ), S.Nonempty →
    (∀ q ∈ S, q.Prime) → (∀ q ∈ S, 0 < e q) →
    (∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ P) →
    ∀ z : ℂ, IsPrimitiveRoot z (selectedOrder S e) → aeval z P = 0

theorem selectedOrder_pos (S : Finset ℕ) (e : ℕ → ℕ)
    (hprime : ∀ q ∈ S, q.Prime) : 0 < selectedOrder S e := by
  exact Finset.prod_pos (fun q hq => pow_pos (hprime q hq).pos _)

theorem prime_pow_coprime_selectedOrder {p : ℕ} (hp : p.Prime)
    (S : Finset ℕ) (e : ℕ → ℕ) (k : ℕ) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) : (p ^ k).Coprime (selectedOrder S e) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  exact Nat.coprime_pow_primes k (e q) hp (hprime q hq)
    (by intro hh; subst q; exact hpS hq)

theorem selectedOrder_dvd {N : ℕ} (S : Finset ℕ) (e : ℕ → ℕ)
    (hprime : ∀ q ∈ S, q.Prime) (hdiv : ∀ q ∈ S, q ^ e q ∣ N) :
    selectedOrder S e ∣ N := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [selectedOrder]
  | @insert p S hpS ih =>
    rw [selectedOrder, Finset.prod_insert hpS]
    exact (prime_pow_coprime_selectedOrder (hprime p (Finset.mem_insert_self p S))
      S e (e p) hpS (fun q hq => hprime q (Finset.mem_insert_of_mem hq))).mul_dvd_of_dvd_of_dvd
      (hdiv p (Finset.mem_insert_self p S))
      (ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq => hdiv q (Finset.mem_insert_of_mem hq)))

theorem cyclotomic_dvd_iff_aeval_zero (P : ℤ[X]) {n : ℕ} (hn : 0 < n)
    {z : ℂ} (hz : IsPrimitiveRoot z n) :
    cyclotomic n ℤ ∣ P ↔ aeval z P = 0 := by
  have hroot : aeval z (cyclotomic n ℤ) = 0 := by
    rw [cyclotomic_eq_minpoly hz hn]
    exact minpoly.aeval ℤ z
  constructor
  · rintro ⟨Q, hQ⟩
    rw [hQ, map_mul, hroot, zero_mul]
  · intro h
    rw [cyclotomic_eq_minpoly hz hn]
    exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral hn) h

theorem polynomialT2_iff_rootT2 (P : ℤ[X]) : PolynomialT2 P ↔ RootT2 P := by
  constructor
  · intro h S e hS hprime he hprimary z hz
    exact (cyclotomic_dvd_iff_aeval_zero P (selectedOrder_pos S e hprime) hz).mp
      (h S e hS hprime he hprimary)
  · intro h S e hS hprime he hprimary
    let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / (selectedOrder S e : ℂ))
    have hz : IsPrimitiveRoot z (selectedOrder S e) :=
      Complex.isPrimitiveRoot_exp _ (selectedOrder_pos S e hprime).ne'
    exact (cyclotomic_dvd_iff_aeval_zero P (selectedOrder_pos S e hprime) hz).mpr
      (h S e hS hprime he hprimary z hz)

def CyclicT2 {N : ℕ} [NeZero N] (f : AddMonoidAlgebra ℤ (ZMod N)) : Prop :=
  PolynomialT2 (CanonicalMaskPolynomial.maskPolynomial f)

/-- Exact target for a single period; this is a definition, not a claimed proof. -/
def CyclicTilingT2 (N : ℕ) [NeZero N] : Prop :=
  ∀ A B : AddMonoidAlgebra ℤ (ZMod N),
    (∀ x, A x = 0 ∨ A x = 1) → (∀ x, B x = 0 ∨ B x = 1) →
    A * B = StripeCollapse.constantMask 1 → CyclicT2 A ∧ CyclicT2 B

section Fibers

open CanonicalMaskPolynomial CyclicFiberEvaluation DephasedMasks

variable (p M : ℕ) [NeZero p] [NeZero M]

/-- Exact ordinary-fiber polynomial decomposition, derived from the literal
canonical indexing bijection rather than assumed as an inheritance premise. -/
theorem maskPolynomial_eq_fiber_sum (A : AddMonoidAlgebra ℤ (ZMod (p * M))) :
    maskPolynomial A = ∑ i : Fin p,
      X ^ i.val * (maskPolynomial (integerFiber p M A i)).comp (X ^ p) := by
  unfold maskPolynomial
  rw [← (fiberEquiv p M).sum_comp (fun x => C (A x) * X ^ x.val),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [fiberEquiv_apply, fiberIndex_val, integerFiber_apply,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp,
    pow_add, pow_mul]
  ring

theorem higher_primary_dvd_every_fiber
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (hp : p.Prime) (k : ℕ)
    (hprimary : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial A) :
    ∀ i, cyclotomic (p ^ (k + 1)) ℤ ∣ maskPolynomial (integerFiber p M A i) := by
  rw [maskPolynomial_eq_fiber_sum p M A] at hprimary
  exact (ResidueGrading.cyclotomic_prime_power_dvd_residue_sum_iff hp k
    (fun i => maskPolynomial (integerFiber p M A i))).mp hprimary

/-- The literal integer phase mask, with independent signed phases. -/
def phaseMask (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (rho R : ℕ)
    (h : Fin p → ℤ) : AddMonoidAlgebra ℤ (ZMod M) :=
  ∑ i, AddMonoidAlgebra.single (((R : ℤ) * h i : ℤ) : ZMod M) 1 *
    dephased p M A rho i

theorem evaluate_single_int (n : ℤ) {theta : ℂ} (htheta : theta ^ M = 1) :
    CyclicEvaluation.evaluate
      (AddMonoidAlgebra.single (n : ZMod M) 1 : AddMonoidAlgebra ℤ (ZMod M)) theta =
      theta ^ n := by
  rw [← CyclicEvaluation.evaluationHom_apply htheta]
  rw [CyclicEvaluation.evaluationHom, AddMonoidAlgebra.liftNCRingHom_single]
  simp only [map_one, one_mul]
  change (AddChar.zmodChar M htheta) (n : ZMod M) = _
  have hc := (AddChar.zmodChar M htheta).map_zsmul_eq_zpow n (1 : ZMod M)
  have hc1 : (AddChar.zmodChar M htheta) 1 = theta := by
    simpa using AddChar.zmodChar_apply' htheta 1
  simpa [zsmul_eq_mul, hc1] using hc

omit [NeZero p] in
theorem evaluate_phaseMask (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (rho R : ℕ) (h : Fin p → ℤ) {theta : ℂ} (htheta : theta ^ M = 1) :
    CyclicEvaluation.evaluate (phaseMask p M A rho R h) theta =
      ∑ i, theta ^ (rho * i.val) * (theta ^ R) ^ (h i) *
        CyclicEvaluation.evaluate (integerFiber p M A i) theta := by
  unfold phaseMask
  rw [← CyclicEvaluation.evaluationHom_apply htheta, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [CyclicEvaluation.evaluationHom_apply, CyclicEvaluation.evaluate_mul _ _ htheta,
    evaluate_single_int M _ htheta]
  rw [dephased, CyclicEvaluation.evaluate_mul _ _ htheta,
    evaluate_single_nat M _ htheta, zpow_mul, zpow_natCast]
  ring

/-- At a root trivial on the phase direction, the actual phase mask is the
original mask evaluated at the inverse-exponent root. -/
theorem evaluate_phaseMask_coprime (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    {R rho : ℕ} (hR : 0 < R) (hRM : R ∣ M)
    (hinverse : p * rho ≡ 1 [MOD R]) (h : Fin p → ℤ)
    {theta : ℂ} (htheta : theta ^ R = 1) :
    CyclicEvaluation.evaluate (phaseMask p M A rho R h) theta =
      CyclicEvaluation.evaluate A (theta ^ rho) := by
  have hM : theta ^ M = 1 := by
    obtain ⟨v, rfl⟩ := hRM
    rw [pow_mul, htheta, one_pow]
  rw [evaluate_phaseMask p M A rho R h hM]
  rw [show CyclicEvaluation.evaluate A (theta ^ rho) =
      ∑ i : Fin p, (theta ^ rho) ^ i.val *
        maskEval (fiber p M (fun x => (A x : ℂ)) i) ((theta ^ rho) ^ p) from
      integer_eval_regroup p M A (theta ^ rho)]
  rw [PrimeDirectionArithmetic.inverse_exponent_root_of_modEq hR hinverse htheta]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [htheta, one_zpow, mul_one, ← pow_mul]
  rfl

theorem coprime_divisor_inherited_by_phaseMask
    (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    {R n : ℕ} (hR : 0 < R) (hRM : R ∣ M) (hcop : p.Coprime R)
    (hn : 0 < n) (hnR : n ∣ R)
    (hprimary : cyclotomic n ℤ ∣ maskPolynomial A) (h : Fin p → ℤ) :
    cyclotomic n ℤ ∣ maskPolynomial
      (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h) := by
  let theta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have ht : IsPrimitiveRoot theta n := Complex.isPrimitiveRoot_exp _ hn.ne'
  apply (cyclotomic_dvd_iff_evaluate_eq_zero _ hn ht).mpr
  rw [evaluate_phaseMask_coprime p M A hR hRM
    (PrimeDirectionArithmetic.rho_modEq hcop) h ((ht.pow_eq_one_iff_dvd R).mpr hnR)]
  exact (cyclotomic_dvd_iff_evaluate_eq_zero A hn
    (PrimeDirectionArithmetic.inverse_exponent_primitive hcop hnR ht)).mp hprimary

theorem higher_primary_inherited_by_phaseMask
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (hp : p.Prime) (k rho R : ℕ)
    (hdiv : p ^ (k + 1) ∣ M)
    (hprimary : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial A)
    (h : Fin p → ℤ) :
    cyclotomic (p ^ (k + 1)) ℤ ∣ maskPolynomial (phaseMask p M A rho R h) := by
  have hn : 0 < p ^ (k + 1) := pow_pos hp.pos _
  let theta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p ^ (k + 1) : ℕ))
  have ht : IsPrimitiveRoot theta (p ^ (k + 1)) :=
    Complex.isPrimitiveRoot_exp _ hn.ne'
  apply (cyclotomic_dvd_iff_evaluate_eq_zero _ hn ht).mpr
  rw [evaluate_phaseMask p M A rho R h ((ht.pow_eq_one_iff_dvd M).mpr hdiv)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [(cyclotomic_dvd_iff_evaluate_eq_zero _ hn ht).mp
    (higher_primary_dvd_every_fiber p M A hp k hprimary i), mul_zero]

omit [NeZero p] in
/-- No fiberwise vanishing premise: all actual phase-mask evaluations isolate
the literal ordinary fibers whenever the phase direction is nontrivial. -/
theorem phaseMask_zeros_isolate_fibers
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (rho R : ℕ)
    {theta : ℂ} (htheta : theta ^ M = 1) (hne : theta ≠ 0)
    (hphase : theta ^ R ≠ 1)
    (hall : ∀ h : Fin p → ℤ,
      CyclicEvaluation.evaluate (phaseMask p M A rho R h) theta = 0) :
    ∀ i, CyclicEvaluation.evaluate (integerFiber p M A i) theta = 0 := by
  apply PhaseIsolation.all_integer_phases_isolate
    (fun i : Fin p => theta ^ (rho * i.val))
    (fun i => CyclicEvaluation.evaluate (integerFiber p M A i) theta)
    (theta ^ R) (fun i => pow_ne_zero _ hne) hphase
  intro h
  rw [← evaluate_phaseMask p M A rho R h htheta]
  exact hall h

theorem original_zero_of_phaseMask_zeros
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (rho R : ℕ)
    {zeta : ℂ} (htheta : (zeta ^ p) ^ M = 1) (hne : zeta ^ p ≠ 0)
    (hphase : (zeta ^ p) ^ R ≠ 1)
    (hall : ∀ h : Fin p → ℤ,
      CyclicEvaluation.evaluate (phaseMask p M A rho R h) (zeta ^ p) = 0) :
    CyclicEvaluation.evaluate A zeta = 0 := by
  have hf := phaseMask_zeros_isolate_fibers p M A rho R htheta hne hphase hall
  rw [show CyclicEvaluation.evaluate A zeta =
      ∑ i : Fin p, zeta ^ i.val *
        CyclicEvaluation.evaluate (integerFiber p M A i) (zeta ^ p) from
      integer_eval_regroup p M A zeta]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hf i, mul_zero]

/-- All finite mixed families containing an upper p-level are recovered in
the original mask. The induction input is full T2 only for the literal
smaller phase masks; no mixed zero or fiber inheritance is assumed. -/
theorem upper_mixed_divisor_of_phase_T2
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (hp : p.Prime)
    {R : ℕ} (hR : 0 < R) (hRM : R ∣ M) (hcop : p.Coprime R)
    (S : Finset ℕ) (e : ℕ → ℕ) (k : ℕ) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) (he : ∀ q ∈ S, 0 < e q)
    (hotherR : ∀ q ∈ S, q ^ e q ∣ R)
    (hotherA : ∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ maskPolynomial A)
    (hpA : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial A)
    (hlowerM : p ^ (k + 1) * selectedOrder S e ∣ M)
    (hIH : ∀ h : Fin p → ℤ,
      CyclicT2 (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h)) :
    cyclotomic (p ^ (k + 2) * selectedOrder S e) ℤ ∣ maskPolynomial A := by
  classical
  let e' : ℕ → ℕ := Function.update e p (k + 1)
  have he'p : e' p = k + 1 := by simp [e']
  have he'q : ∀ q ∈ S, e' q = e q := by
    intro q hq
    exact Function.update_of_ne (by intro hh; subst q; exact hpS hq) _ _
  have horder : selectedOrder (insert p S) e' = p ^ (k + 1) * selectedOrder S e := by
    unfold selectedOrder
    rw [Finset.prod_insert hpS, he'p]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    rw [he'q q hq]
  have hlow : ∀ h : Fin p → ℤ,
      cyclotomic (p ^ (k + 1) * selectedOrder S e) ℤ ∣
        maskPolynomial (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h) := by
    intro h
    rw [← horder]
    apply hIH h (insert p S) e' (Finset.insert_nonempty p S)
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hprime q hq
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [he'p]; omega
      · rw [he'q q hq]; exact he q hq
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [he'p]
        exact higher_primary_inherited_by_phaseMask q M A hp k _ R
          ((dvd_mul_right _ _).trans hlowerM) hpA h
      · rw [he'q q hq]
        exact coprime_divisor_inherited_by_phaseMask p M A hR hRM hcop
          (pow_pos (hprime q hq).pos _) (hotherR q hq) (hotherA q hq) h
  have hd : 0 < selectedOrder S e := selectedOrder_pos S e hprime
  have hn : 0 < p ^ (k + 2) * selectedOrder S e := Nat.mul_pos (pow_pos hp.pos _) hd
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I /
    (p ^ (k + 2) * selectedOrder S e : ℕ))
  have hzeta : IsPrimitiveRoot zeta (p ^ (k + 2) * selectedOrder S e) :=
    Complex.isPrimitiveRoot_exp _ hn.ne'
  have htheta : IsPrimitiveRoot (zeta ^ p) (p ^ (k + 1) * selectedOrder S e) := by
    simpa using PrimeDirectionArithmetic.upper_level_power_primitive hp
      (by omega : 1 ≤ k + 2) hd hzeta
  apply (cyclotomic_dvd_iff_evaluate_eq_zero A hn hzeta).mpr
  apply original_zero_of_phaseMask_zeros p M A (PrimeDirectionArithmetic.rho p R) R
    ((htheta.pow_eq_one_iff_dvd M).mpr hlowerM)
    (htheta.ne_zero (Nat.mul_pos (pow_pos hp.pos _) hd).ne')
    (PrimeDirectionArithmetic.upper_level_power_not_coprimePart_root hp
      (by omega : 2 ≤ k + 2) hd hcop hzeta)
  intro h
  exact (cyclotomic_dvd_iff_evaluate_eq_zero _
    (Nat.mul_pos (pow_pos hp.pos _) hd) htheta).mp (hlow h)

theorem coprime_mixed_divisor_of_phase_T2
    (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    {R : ℕ} (hR : 0 < R) (hRM : R ∣ M) (hcop : p.Coprime R)
    (S : Finset ℕ) (e : ℕ → ℕ) (hS : S.Nonempty)
    (hprime : ∀ q ∈ S, q.Prime) (he : ∀ q ∈ S, 0 < e q)
    (hotherR : ∀ q ∈ S, q ^ e q ∣ R)
    (hotherA : ∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ maskPolynomial A)
    (horderR : selectedOrder S e ∣ R)
    (hIH : CyclicT2
      (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R (fun _ => 0))) :
    cyclotomic (selectedOrder S e) ℤ ∣ maskPolynomial A := by
  have hlow := hIH S e hS hprime he (fun q hq =>
    coprime_divisor_inherited_by_phaseMask p M A hR hRM hcop
      (pow_pos (hprime q hq).pos _) (hotherR q hq) (hotherA q hq) (fun _ => 0))
  have hn := selectedOrder_pos S e hprime
  let theta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (selectedOrder S e : ℂ))
  have ht : IsPrimitiveRoot theta (selectedOrder S e) :=
    Complex.isPrimitiveRoot_exp _ hn.ne'
  apply (cyclotomic_dvd_iff_evaluate_eq_zero A hn
    (PrimeDirectionArithmetic.inverse_exponent_primitive hcop horderR ht)).mpr
  rw [← evaluate_phaseMask_coprime p M A hR hRM
    (PrimeDirectionArithmetic.rho_modEq hcop) (fun _ => 0)
    ((ht.pow_eq_one_iff_dvd R).mpr horderR)]
  exact (cyclotomic_dvd_iff_evaluate_eq_zero _ hn ht).mp hlow

/-- Prime-power orders owned by the original tiling factor and distinct
from p lie in the actual coprime part, with no allocation premise. -/
theorem other_primary_order_dvd_coprimePart
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1) (hp : p.Prime)
    {a R q k : ℕ} (hM : M = p ^ a * R) (hq : q.Prime) (hqp : q ≠ p)
    (hk : 0 < k) (hprimary : cyclotomic (q ^ k) ℤ ∣ maskPolynomial A) : q ^ k ∣ R := by
  have hdiv := PrimaryAllocation.primary_divisor_within_period_pos A B htile hq hk hprimary
  have hperiod : p * M = p ^ (a + 1) * R := by rw [hM, pow_succ]; ring
  rw [hperiod] at hdiv
  apply PrimeDirectionArithmetic.order_dvd_coprimePart hp hdiv
  exact hp.coprime_iff_not_dvd.mp (((Nat.coprime_primes hp hq).mpr hqp.symm).pow_right k)

/-- Full original-A T2, for every finite distinct-prime family, from T2
of the literal smaller masks. The actual tiling supplies every order bound. -/
theorem original_A_T2_of_phase_T2
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1) (hp : p.Prime)
    {a R : ℕ} (hM : M = p ^ a * R) (hR : 0 < R) (hcop : p.Coprime R)
    (hbase : ¬ cyclotomic p ℤ ∣ maskPolynomial A)
    (hIH : ∀ h : Fin p → ℤ,
      CyclicT2 (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h)) :
    CyclicT2 A := by
  classical
  have hRM : R ∣ M := by rw [hM]; exact dvd_mul_left _ _
  intro S e hS hprime he hprimary
  have hotherR : ∀ q ∈ S, q ≠ p → q ^ e q ∣ R := by
    intro q hq hqp
    exact other_primary_order_dvd_coprimePart p M A B htile hp hM
      (hprime q hq) hqp (he q hq) (hprimary q hq)
  by_cases hpS : p ∈ S
  · have hep : 2 ≤ e p := by
      have hpPos := he p hpS
      by_contra hnot
      have heone : e p = 1 := by omega
      exact hbase (by simpa [heone] using hprimary p hpS)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, e p = k + 2 := ⟨e p - 2, by omega⟩
    have hprime' : ∀ q ∈ S.erase p, q.Prime :=
      fun q hq => hprime q (Finset.mem_of_mem_erase hq)
    have hR' : ∀ q ∈ S.erase p, q ^ e q ∣ R := fun q hq =>
      hotherR q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)
    have hpA : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial A := by
      simpa [hk] using hprimary p hpS
    have hpM : p ^ (k + 1) ∣ M := by
      have hup := PrimaryAllocation.primary_divisor_within_period_pos A B htile hp
        (by omega : 0 < k + 2) hpA
      apply Nat.dvd_of_mul_dvd_mul_left hp.pos
      convert hup using 1
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    have hlowM : p ^ (k + 1) * selectedOrder (S.erase p) e ∣ M :=
      (prime_pow_coprime_selectedOrder hp (S.erase p) e (k + 1)
        (Finset.notMem_erase p S) hprime').mul_dvd_of_dvd_of_dvd hpM
        ((selectedOrder_dvd _ e hprime' hR').trans hRM)
    have htarget := upper_mixed_divisor_of_phase_T2 p M A hp hR hRM hcop
      (S.erase p) e k (Finset.notMem_erase p S) hprime'
      (fun q hq => he q (Finset.mem_of_mem_erase hq)) hR'
      (fun q hq => hprimary q (Finset.mem_of_mem_erase hq)) hpA hlowM hIH
    have horder : selectedOrder S e = p ^ (k + 2) * selectedOrder (S.erase p) e := by
      rw [selectedOrder, ← Finset.mul_prod_erase S (fun q => q ^ e q) hpS, hk]
      rfl
    rwa [horder]
  · have hR' : ∀ q ∈ S, q ^ e q ∣ R := fun q hq =>
      hotherR q hq (by intro hh; subst q; exact hpS hq)
    exact coprime_mixed_divisor_of_phase_T2 p M A hR hRM hcop S e hS
      hprime he hR' hprimary (selectedOrder_dvd S e hprime hR') (hIH (fun _ => 0))

theorem original_zero_of_fiber_zeros
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (zeta : ℂ)
    (hf : ∀ i, CyclicEvaluation.evaluate (integerFiber p M B i) (zeta ^ p) = 0) :
    CyclicEvaluation.evaluate B zeta = 0 := by
  rw [CommonComplementLift.evaluate_regroup]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hf i, mul_zero]

theorem coprime_mixed_divisor_every_fiber
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (C : AddMonoidAlgebra ℤ (ZMod M))
    (hcommon : ∀ j : Fin p, C * integerFiber p M B j = StripeCollapse.constantMask 1)
    (hp : p.Prime) (S : Finset ℕ) (e : ℕ → ℕ) (hS : S.Nonempty) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) (he : ∀ q ∈ S, 0 < e q)
    (hprimary : ∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ maskPolynomial B)
    (hIH : ∀ i, CyclicT2 (integerFiber p M B i)) :
    ∀ i, cyclotomic (selectedOrder S e) ℤ ∣ maskPolynomial (integerFiber p M B i) := by
  intro i
  apply hIH i S e hS hprime he
  intro q hq
  exact (CommonComplementLift.prime_power_inherits p M B C hcommon hp (hprime q hq)
    (by intro hh; subst q; exact hpS hq) (he q hq) (hprimary q hq)).2 i

theorem upper_mixed_divisor_every_fiber
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (C : AddMonoidAlgebra ℤ (ZMod M))
    (hcommon : ∀ j : Fin p, C * integerFiber p M B j = StripeCollapse.constantMask 1)
    (hp : p.Prime) (S : Finset ℕ) (e : ℕ → ℕ) (k : ℕ) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, q.Prime) (he : ∀ q ∈ S, 0 < e q)
    (hprimary : ∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ maskPolynomial B)
    (hpB : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial B)
    (hIH : ∀ i, CyclicT2 (integerFiber p M B i)) :
    ∀ i, cyclotomic (p ^ (k + 1) * selectedOrder S e) ℤ ∣
      maskPolynomial (integerFiber p M B i) := by
  classical
  let e' : ℕ → ℕ := Function.update e p (k + 1)
  have he'p : e' p = k + 1 := by simp [e']
  have he'q : ∀ q ∈ S, e' q = e q := by
    intro q hq
    exact Function.update_of_ne (by intro hh; subst q; exact hpS hq) _ _
  have horder : selectedOrder (insert p S) e' = p ^ (k + 1) * selectedOrder S e := by
    unfold selectedOrder
    rw [Finset.prod_insert hpS, he'p]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    rw [he'q q hq]
  intro i
  rw [← horder]
  apply hIH i (insert p S) e' (Finset.insert_nonempty p S)
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hprime q hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [he'p]; omega
    · rw [he'q q hq]; exact he q hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [he'p]
      exact higher_primary_dvd_every_fiber q M B hp k hpB i
    · rw [he'q q hq]
      exact (CommonComplementLift.prime_power_inherits p M B C hcommon hp (hprime q hq)
        (by intro hh; subst q; exact hpS hq) (he q hq) (hprimary q hq)).2 i

/-- Full original-B T2 from the actual common complement and lower-fiber
T2. This includes the selected base p-level, not just higher p-levels. -/
theorem original_B_T2_of_common_complement
    (B : AddMonoidAlgebra ℤ (ZMod (p * M))) (C : AddMonoidAlgebra ℤ (ZMod M))
    (hcommon : ∀ j : Fin p, C * integerFiber p M B j = StripeCollapse.constantMask 1)
    (hp : p.Prime) (hIH : ∀ i, CyclicT2 (integerFiber p M B i)) : CyclicT2 B := by
  classical
  intro S e hS hprime he hprimary
  have hn : 0 < selectedOrder S e := selectedOrder_pos S e hprime
  let zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (selectedOrder S e : ℂ))
  have hzeta : IsPrimitiveRoot zeta (selectedOrder S e) :=
    Complex.isPrimitiveRoot_exp _ hn.ne'
  by_cases hpS : p ∈ S
  · have hprime' : ∀ q ∈ S.erase p, q.Prime :=
      fun q hq => hprime q (Finset.mem_of_mem_erase hq)
    have he' : ∀ q ∈ S.erase p, 0 < e q :=
      fun q hq => he q (Finset.mem_of_mem_erase hq)
    have hprimary' : ∀ q ∈ S.erase p,
        cyclotomic (q ^ e q) ℤ ∣ maskPolynomial B :=
      fun q hq => hprimary q (Finset.mem_of_mem_erase hq)
    have hd : 0 < selectedOrder (S.erase p) e := selectedOrder_pos _ _ hprime'
    have horder : selectedOrder S e = p ^ e p * selectedOrder (S.erase p) e := by
      exact (Finset.mul_prod_erase S (fun q => q ^ e q) hpS).symm
    have hzeta' : IsPrimitiveRoot zeta (p ^ e p * selectedOrder (S.erase p) e) := by
      rwa [← horder]
    by_cases hep : e p = 1
    · by_cases hrest : (S.erase p).Nonempty
      · have hf := coprime_mixed_divisor_every_fiber p M B C hcommon hp
          (S.erase p) e hrest (Finset.notMem_erase p S) hprime' he' hprimary' hIH
        have ht : IsPrimitiveRoot (zeta ^ p) (selectedOrder (S.erase p) e) := by
          simpa [hep] using PrimeDirectionArithmetic.upper_level_power_primitive hp
            (by omega : 1 ≤ e p) hd hzeta'
        apply (cyclotomic_dvd_iff_evaluate_eq_zero B hn hzeta).mpr
        apply original_zero_of_fiber_zeros p M B zeta
        intro i
        exact (cyclotomic_dvd_iff_evaluate_eq_zero _ hd ht).mp (hf i)
      · have hempty : S.erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
        rw [horder, hep, pow_one, selectedOrder, hempty, Finset.prod_empty, mul_one]
        simpa [hep] using hprimary p hpS
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, e p = k + 2 := by
        have hpPos := he p hpS
        exact ⟨e p - 2, by omega⟩
      have hpB : cyclotomic (p ^ (k + 2)) ℤ ∣ maskPolynomial B := by
        simpa [hk] using hprimary p hpS
      have hf := upper_mixed_divisor_every_fiber p M B C hcommon hp
        (S.erase p) e k (Finset.notMem_erase p S) hprime' he' hprimary' hpB hIH
      have ht : IsPrimitiveRoot (zeta ^ p) (p ^ (k + 1) * selectedOrder (S.erase p) e) := by
        simpa [hk] using PrimeDirectionArithmetic.upper_level_power_primitive hp
          (he p hpS) hd hzeta'
      apply (cyclotomic_dvd_iff_evaluate_eq_zero B hn hzeta).mpr
      apply original_zero_of_fiber_zeros p M B zeta
      intro i
      exact (cyclotomic_dvd_iff_evaluate_eq_zero _
        (Nat.mul_pos (pow_pos hp.pos _) hd) ht).mp (hf i)
  · have hf := coprime_mixed_divisor_every_fiber p M B C hcommon hp
      S e hS hpS hprime he hprimary hIH
    have hcop : p.Coprime (selectedOrder S e) := by
      simpa using prime_pow_coprime_selectedOrder hp S e 1 hpS hprime
    apply (cyclotomic_dvd_iff_evaluate_eq_zero B hn hzeta).mpr
    apply original_zero_of_fiber_zeros p M B zeta
    intro i
    exact (cyclotomic_dvd_iff_evaluate_eq_zero _ hn (hzeta.pow_of_coprime p hcop)).mp (hf i)

end Fibers

#print axioms polynomialT2_iff_rootT2
#print axioms maskPolynomial_eq_fiber_sum
#print axioms higher_primary_dvd_every_fiber
#print axioms evaluate_phaseMask
#print axioms evaluate_phaseMask_coprime
#print axioms phaseMask_zeros_isolate_fibers
#print axioms original_A_T2_of_phase_T2
#print axioms original_B_T2_of_common_complement

end T2Induction
