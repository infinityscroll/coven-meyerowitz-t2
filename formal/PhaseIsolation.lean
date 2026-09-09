import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring

/-!
Coefficient isolation from independent integer phases. The result is an
algebraic bridge only: it does not construct phase tilings or prove that
their polynomial evaluations vanish.
-/

open scoped BigOperators

namespace PhaseIsolation

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The zero phase and each individual one-coordinate phase already suffice. -/
theorem single_coordinate_phase_isolation
    (q a : ι → K) (w : K)
    (hq : ∀ i, q i ≠ 0) (hw : w ≠ 1)
    (hzero : (∑ i, q i * a i) = 0)
    (hsingle : ∀ i, (∑ j, q j * w ^ (if j = i then (1 : ℤ) else 0) * a j) = 0) :
    ∀ i, a i = 0 := by
  intro i
  have hterm (j : ι) :
      q j * w ^ (if j = i then (1 : ℤ) else 0) * a j =
        q j * a j + if j = i then q i * (w - 1) * a i else 0 := by
    by_cases hji : j = i
    · rw [if_pos hji, if_pos hji, zpow_one, hji]
      ring
    · simp [hji]
  have hsum :
      (∑ j, q j * w ^ (if j = i then (1 : ℤ) else 0) * a j) =
        (∑ j, q j * a j) + q i * (w - 1) * a i := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp
  have hprod : q i * (w - 1) * a i = 0 := by
    simpa only [hsum, hzero, zero_add] using hsingle i
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (hq i) (sub_ne_zero.mpr hw))

/-- Vanishing for every independent integer phase forces every coefficient
to vanish; no coefficientwise vanishing is assumed. -/
theorem all_integer_phases_isolate
    (q a : ι → K) (w : K)
    (hq : ∀ i, q i ≠ 0) (hw : w ≠ 1)
    (hphase : ∀ h : ι → ℤ, (∑ i, q i * w ^ (h i) * a i) = 0) :
    ∀ i, a i = 0 := by
  apply single_coordinate_phase_isolation q a w hq hw
  · simpa using hphase (fun _ => 0)
  · intro i
    exact hphase (fun j => if j = i then 1 else 0)

/-- The dephasing weights theta^(rho*i) are nonzero when theta is nonzero. -/
theorem theta_weighted_phase_isolation {p : ℕ}
    (theta : K) (rho : ℤ) (w : K) (a : Fin p → K)
    (htheta : theta ≠ 0) (hw : w ≠ 1)
    (hphase : ∀ h : Fin p → ℤ,
      (∑ i, theta ^ (rho * (i.val : ℤ)) * w ^ (h i) * a i) = 0) :
    ∀ i, a i = 0 := by
  apply all_integer_phases_isolate
    (fun i => theta ^ (rho * (i.val : ℤ))) a w _ hw hphase
  intro i
  exact zpow_ne_zero _ htheta

/-- The literal common multiplier theta^r used by independently shifted
fiber evaluations. Nontriviality of this multiplier is an explicit input. -/
theorem theta_power_phase_isolation {p : ℕ}
    (theta : K) (rho : ℤ) (r : ℕ) (a : Fin p → K)
    (htheta : theta ≠ 0) (hw : theta ^ r ≠ 1)
    (hphase : ∀ h : Fin p → ℤ,
      (∑ i, theta ^ (rho * (i.val : ℤ)) * (theta ^ r) ^ (h i) * a i) = 0) :
    ∀ i, a i = 0 :=
  theta_weighted_phase_isolation theta rho (theta ^ r) a htheta hw hphase

#print axioms all_integer_phases_isolate
#print axioms theta_power_phase_isolation

end PhaseIsolation
