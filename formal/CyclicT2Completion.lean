import T2Induction
import ActualIntegerReduction

/-!
The all-period, both-factor cyclic T2 completion. The prime reduction is
derived from actual Boolean integral tilings. The strong induction has no
abstract inheritance, lower tiling, or original mixed-zero premise.

`actual_cyclic_tiling_T2` exposes the complete final assumptions: a positive
natural period N, integral masks A,B on ZMod N, Booleanity of both masks,
and their literal convolution equation A*B=J_N. It concludes the full
`PolynomialT2` of both canonical ordinary mask polynomials. That definition
quantifies over every nonempty finite set of distinct prime labels and all
positive levels; it is neither pairwise-only nor bounded in cardinality.

The proof uses strong induction on N, the exact N=1 base, a proved prime
direction factorization with strict smaller period, exact primary ownership
to orient the original factors, actual independent-phase tilings, and the
separately proved original-A and original-B lifting steps.

This source does not by itself formalize passage from a bi-infinite integer
tiling to a finite cyclic tiling or canonical-polynomial transfer under that
passage. Nor is machine checking a claim about novelty or external acceptance.
The author participated in earlier bridge formalizations, so this is not a
blind independent audit. Replay in pinned Lean 4.23.0 / Mathlib 4.23.0:
`lake env lean CyclicT2Completion.lean`.
-/

open scoped BigOperators
open Polynomial CanonicalMaskPolynomial DephasedMasks T2Induction

noncomputable section

namespace CyclicT2Completion

theorem period_one_T2 (A B : AddMonoidAlgebra ℤ (ZMod 1))
    (htile : A * B = StripeCollapse.constantMask 1) : CyclicT2 A := by
  intro S e hS hprime he hprimary
  obtain ⟨q, hq⟩ := hS
  have hd := PrimaryAllocation.primary_divisor_within_period_pos A B htile
    (hprime q hq) (he q hq) (hprimary q hq)
  have heq : q ^ e q = 1 := Nat.dvd_one.mp hd
  have hgt : 1 < q ^ e q := Nat.one_lt_pow (he q hq).ne' (hprime q hq).one_lt
  omega

theorem period_one_both_T2 : CyclicTilingT2 1 := by
  intro A B hA hB htile
  exact ⟨period_one_T2 A B htile, period_one_T2 B A (by rwa [mul_comm])⟩

/-- Positive-period arithmetic selects an actual prime direction and
its coprime part; the smaller period is strictly smaller. -/
theorem exists_prime_direction {N : ℕ} (hN : 0 < N) (hne : N ≠ 1) :
    ∃ p a R : ℕ, p.Prime ∧ 0 < R ∧ p.Coprime R ∧
      N = p * (p ^ a * R) ∧ p ^ a * R < N := by
  obtain ⟨p, hp, M, hNM⟩ := Nat.exists_prime_and_dvd hne
  have hM : 0 < M := by
    by_contra hh
    have hzero : M = 0 := by omega
    simp [hzero] at hNM
    omega
  obtain ⟨a, R, hnot, hMR⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one
  have hR : 0 < R := by
    by_contra hh
    have hzero : R = 0 := by omega
    simp [hzero] at hMR
    omega
  refine ⟨p, a, R, hp, hR, hp.coprime_iff_not_dvd.mpr hnot, ?_, ?_⟩
  · rwa [← hMR]
  · rw [← hMR, hNM]
    nlinarith [hp.two_le]

/-- The two lifting arguments consume genuine smaller tilings, so their
T2 hypotheses follow from the same smaller-period induction instance. -/
theorem both_T2_of_actual_phase_tilings
    (p M : ℕ) [NeZero p] [NeZero M]
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hBbool : ∀ x, B x = 0 ∨ B x = 1) (hp : p.Prime)
    {a R : ℕ} (hM : M = p ^ a * R) (hR : 0 < R) (hcop : p.Coprime R)
    (hBprime : cyclotomic p ℤ ∣ maskPolynomial B)
    (hphases : ∀ h : Fin p → ℤ, ∀ j : Fin p,
      phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h * integerFiber p M B j =
        StripeCollapse.constantMask 1)
    (hphasebool : ∀ h : Fin p → ℤ, ∀ x,
      phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h x = 0 ∨
      phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h x = 1)
    (hsmall : CyclicTilingT2 M) : CyclicT2 A ∧ CyclicT2 B := by
  have hbase : ¬ cyclotomic p ℤ ∣ maskPolynomial A := by
    have h := (PrimaryAllocation.primary_owner_iff_not B A
      (by rw [mul_comm B A]; exact htile) hp (k := 0) (by simp)).mp
        (by simpa using hBprime)
    simpa using h
  have hfbool : ∀ j : Fin p, ∀ x,
      integerFiber p M B j x = 0 ∨ integerFiber p M B j x = 1 := by
    intro j x
    exact hBbool (CyclicFiberEvaluation.fiberIndex p M j x)
  have hphaseT2 : ∀ h : Fin p → ℤ,
      CyclicT2 (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R h) := by
    intro h
    exact (hsmall _ (integerFiber p M B 0) (hphasebool h) (hfbool 0) (hphases h 0)).1
  have hfT2 : ∀ j : Fin p, CyclicT2 (integerFiber p M B j) := by
    intro j
    exact (hsmall (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R (fun _ => 0))
      _ (hphasebool (fun _ => 0)) (hfbool j) (hphases (fun _ => 0) j)).2
  exact ⟨original_A_T2_of_phase_T2 p M A B htile hp hM hR hcop hbase hphaseT2,
    original_B_T2_of_common_complement p M B
      (phaseMask p M A (PrimeDirectionArithmetic.rho p R) R (fun _ => 0))
      (hphases (fun _ => 0)) hp hfT2⟩

/-- A complete prime-direction induction step: its only T2 hypothesis is
the already proved smaller-period theorem. -/
theorem prime_direction_step (p a R : ℕ) [NeZero p] [NeZero R]
    (hp : p.Prime) (hcop : p.Coprime R)
    (hsmall : CyclicTilingT2 (p ^ a * R)) : CyclicTilingT2 (p * (p ^ a * R)) := by
  intro A B hA hB htile
  have oriented : ∀ U V : AddMonoidAlgebra ℤ (ZMod (p * (p ^ a * R))),
      U * V = StripeCollapse.constantMask 1 →
      (∀ x, U x = 0 ∨ U x = 1) → (∀ x, V x = 0 ∨ V x = 1) →
      cyclotomic p ℤ ∣ maskPolynomial V → CyclicT2 U ∧ CyclicT2 V := by
    intro U V hUV hU hV hVprime
    have hred := ActualIntegerReduction.actual_integer_ordinary_phase_tilings p a R
      U V hUV hp hcop hU hV hVprime
    exact both_T2_of_actual_phase_tilings p (p ^ a * R) U V hUV hV hp rfl
      (NeZero.pos R) hcop hVprime (fun h j => (hred h j).1)
      (fun h => (hred h 0).2) hsmall
  rcases PrimaryAllocation.cyclotomic_coverage A B htile hp.one_lt
      (dvd_mul_right p (p ^ a * R)) with hAprim | hBprim
  · exact (oriented B A (by rw [mul_comm B A]; exact htile) hB hA hAprim).symm
  · exact oriented A B htile hA hB hBprim

/-- Full finite cyclic T2 necessity, simultaneously for both Boolean
integral factors, at every positive period and all finite prime families. -/
theorem full_cyclic_T2 (N : ℕ) : ∀ [NeZero N], CyclicTilingT2 N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hNZ
    by_cases hN1 : N = 1
    · subst N
      exact period_one_both_T2
    · obtain ⟨p, a, R, hp, hR, hcop, hN, hlt⟩ :=
        exists_prime_direction (NeZero.pos N) hN1
      subst N
      letI : NeZero p := ⟨hp.ne_zero⟩
      letI : NeZero R := ⟨hR.ne'⟩
      exact prime_direction_step p a R hp hcop (ih (p ^ a * R) hlt)

/-- A statement with the actual masks exposed, rather than hidden behind
the period-wise target abbreviation. -/
theorem actual_cyclic_tiling_T2 {N : ℕ} [NeZero N]
    (A B : AddMonoidAlgebra ℤ (ZMod N))
    (hA : ∀ x, A x = 0 ∨ A x = 1) (hB : ∀ x, B x = 0 ∨ B x = 1)
    (htile : A * B = StripeCollapse.constantMask 1) :
    PolynomialT2 (maskPolynomial A) ∧ PolynomialT2 (maskPolynomial B) :=
  full_cyclic_T2 N A B hA hB htile

#print axioms period_one_both_T2
#print axioms exists_prime_direction
#print axioms both_T2_of_actual_phase_tilings
#print axioms prime_direction_step
#print axioms full_cyclic_T2
#print axioms actual_cyclic_tiling_T2

end CyclicT2Completion
