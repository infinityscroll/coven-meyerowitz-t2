import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Ordinary residue grading for actual polynomials. This bridge formalizes
fiberwise divisibility under substitution X ↦ X^p. It does not formalize
cyclic carries, character arguments, tiling, or the full T2 induction.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace ResidueGrading

variable {R : Type*} [CommRing R]

theorem contract_sum {p : ℕ} (hp : p ≠ 0) {ι : Type*}
    (s : Finset ι) (f : ι → R[X]) :
    contract p (∑ i ∈ s, f i) = ∑ i ∈ s, contract p (f i) := by
  ext n
  simp only [coeff_contract hp, finset_sum_coeff]

theorem contract_residue_monomial {p : ℕ} (hp : 0 < p) (i j : Fin p) :
    contract p (X ^ (p - i.val + j.val) : R[X]) =
      if i = j then X else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
    ext n
    simp only [coeff_contract (Nat.ne_of_gt hp), coeff_X_pow, coeff_X]
    congr 1
    apply propext
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  · rw [if_neg hij]
    ext n
    rw [coeff_contract (Nat.ne_of_gt hp), coeff_X_pow, coeff_zero]
    apply if_neg
    intro heq
    have hs : p - i.val + i.val = p := Nat.sub_add_cancel (Nat.le_of_lt i.isLt)
    have hnpos : 0 < n := by nlinarith [i.isLt, j.isLt]
    have hnlt : n < 2 := by nlinarith [i.isLt, j.isLt]
    have hn : n = 1 := by omega
    have hvals : i.val = j.val := by simp [hn] at heq; omega
    exact hij (Fin.ext hvals)

theorem contract_residue_sum {p : ℕ} (hp : 0 < p)
    (F : Fin p → R[X]) (i : Fin p) :
    contract p (X ^ (p - i.val) *
      (∑ j, X ^ j.val * expand R p (F j))) = X * F i := by
  rw [Finset.mul_sum, contract_sum (Nat.ne_of_gt hp)]
  simp_rw [← mul_assoc, ← pow_add,
    contract_mul_expand (Nat.ne_of_gt hp), contract_residue_monomial hp]
  simp

/-- Substitution divisibility is equivalent to divisibility of every ordinary
residue fiber. No primality or nonzero-divisor assumption is needed here. -/
theorem expand_dvd_residue_sum_iff {p : ℕ} (hp : 0 < p)
    (Q : R[X]) (F : Fin p → R[X]) :
    expand R p Q ∣ (∑ i, X ^ i.val * expand R p (F i)) ↔
      ∀ i, Q ∣ F i := by
  constructor
  · rintro ⟨H, hH⟩ i
    have hi : 0 < p - i.val := Nat.sub_pos_of_lt i.isLt
    have hX : (X : R[X]) ∣ contract p (X ^ (p - i.val) * H) := by
      apply X_dvd_iff.mpr
      rw [coeff_contract (Nat.ne_of_gt hp), Nat.zero_mul, coeff_X_pow_mul']
      exact if_neg (by omega)
    obtain ⟨H_i, hHi⟩ := hX
    have heq : X * F i = X * (Q * H_i) := by
      calc
        X * F i = contract p (X ^ (p - i.val) *
            (∑ j, X ^ j.val * expand R p (F j))) :=
          (contract_residue_sum hp F i).symm
        _ = contract p (X ^ (p - i.val) * (expand R p Q * H)) := by rw [hH]
        _ = contract p ((X ^ (p - i.val) * H) * expand R p Q) := by
          congr 1
          ring
        _ = contract p (X ^ (p - i.val) * H) * Q :=
          contract_mul_expand (Nat.ne_of_gt hp) _ _
        _ = X * (Q * H_i) := by rw [hHi]; ring
    refine ⟨H_i, ?_⟩
    ext n
    have hc := congrArg (fun P : R[X] => P.coeff (n + 1)) heq
    simpa only [coeff_X_mul] using hc
  · intro h
    choose H hH using h
    refine ⟨∑ i, X ^ i.val * expand R p (H i), ?_⟩
    simp_rw [hH, map_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- The same theorem in literal polynomial-composition notation. -/
theorem comp_X_pow_dvd_residue_sum_iff {p : ℕ} (hp : 0 < p)
    (Q : R[X]) (F : Fin p → R[X]) :
    Q.comp (X ^ p) ∣ (∑ i, X ^ i.val * (F i).comp (X ^ p)) ↔
      ∀ i, Q ∣ F i := by
  simpa only [expand_eq_comp_X_pow] using expand_dvd_residue_sum_iff hp Q F

/-- The actual cyclotomic substitution identity when p divides d. -/
theorem cyclotomic_mul_eq_comp {p d : ℕ} (hp : p.Prime) (hpd : p ∣ d) :
    cyclotomic (p * d) R = (cyclotomic d R).comp (X ^ p) := by
  simpa only [expand_eq_comp_X_pow, Nat.mul_comm] using
    (cyclotomic_expand_eq_cyclotomic hp hpd R).symm

/-- The cyclotomic bridge needed for the ordinary p-fibers of a mask. -/
theorem cyclotomic_mul_dvd_residue_sum_iff {p d : ℕ}
    (hp : p.Prime) (hpd : p ∣ d) (F : Fin p → R[X]) :
    cyclotomic (p * d) R ∣ (∑ i, X ^ i.val * (F i).comp (X ^ p)) ↔
      ∀ i, cyclotomic d R ∣ F i := by
  rw [cyclotomic_mul_eq_comp hp hpd]
  exact comp_X_pow_dvd_residue_sum_iff hp.pos _ F

/-- For every upper prime-power level k+2, all ordinary p-fibers have
the lower prime-power factor k+1, and conversely. -/
theorem cyclotomic_prime_power_dvd_residue_sum_iff {p : ℕ}
    (hp : p.Prime) (k : ℕ) (F : Fin p → R[X]) :
    cyclotomic (p ^ (k + 2)) R ∣
        (∑ i, X ^ i.val * (F i).comp (X ^ p)) ↔
      ∀ i, cyclotomic (p ^ (k + 1)) R ∣ F i := by
  have hpd : p ∣ p ^ (k + 1) := dvd_pow_self p (by omega)
  have hpow : p * p ^ (k + 1) = p ^ (k + 2) := by
    exact (pow_succ' p (k + 1)).symm
  simpa only [hpow] using cyclotomic_mul_dvd_residue_sum_iff hp hpd F

#print axioms expand_dvd_residue_sum_iff
#print axioms cyclotomic_mul_dvd_residue_sum_iff
#print axioms cyclotomic_prime_power_dvd_residue_sum_iff

end ResidueGrading
