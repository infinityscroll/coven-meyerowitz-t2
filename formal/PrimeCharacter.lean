import RelativeCyclotomic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
The actual p-free character implication after the carry product is
specialized. Relative cyclotomic irreducibility is proved in the import,
not assumed here. The specialized divisibility remains an explicit input.
-/

open scoped BigOperators
open Polynomial IntermediateField
open scoped IntermediateField

noncomputable section

namespace PrimeCharacter

theorem prime_cyclotomic_coeff {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] (i : Fin p) :
    (cyclotomic p K).coeff i.val = 1 := by
  rw [cyclotomic_prime]
  simp [finset_sum_coeff, coeff_X_pow, i.isLt]

theorem small_cyclotomic_multiple_constant {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] (P : K[X])
    (hdeg : P.natDegree < p) (hdiv : cyclotomic p K ∣ P) :
    ∀ i j : Fin p, P.coeff i.val = P.coeff j.val := by
  have hd : P.natDegree ≤ (cyclotomic p K).natDegree := by
    rw [natDegree_cyclotomic, Nat.totient_prime (Fact.out : p.Prime)]
    omega
  have he := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (cyclotomic.monic p K) hdiv hd
  intro i j
  rw [he, coeff_C_mul, coeff_C_mul, prime_cyclotomic_coeff, prime_cyclotomic_coeff]

theorem coprime_character_constant_family
    {p d : ℕ} (hp : p.Prime) (hd : 0 < d) (hcop : p.Coprime d)
    {theta : ℂ} (htheta : IsPrimitiveRoot theta d)
    (P Q : Polynomial ℚ⟮theta⟯)
    (hP : P.natDegree < p) (hQ : Q.natDegree < p)
    (hcarry : X ^ p - 1 ∣ P * Q) :
    (∀ i k : Fin p, P.coeff i.val = P.coeff k.val) ∨
    (∀ j l : Fin p, Q.coeff j.val = Q.coeff l.val) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc : cyclotomic p ℚ⟮theta⟯ ∣ P * Q := by
    apply dvd_trans _ hcarry
    exact ⟨X - 1, (cyclotomic_prime_mul_X_sub_one ℚ⟮theta⟯ p).symm⟩
  have hi := RelativeCyclotomic.prime_coprime_irreducible hp hd hcop htheta
  rcases hi.prime.dvd_mul.mp hc with h | h
  · exact Or.inl (small_cyclotomic_multiple_constant P hP h)
  · exact Or.inr (small_cyclotomic_multiple_constant Q hQ h)

theorem coprime_character_rectangles
    {p d : ℕ} (hp : p.Prime) (hd : 0 < d) (hcop : p.Coprime d)
    {theta : ℂ} (htheta : IsPrimitiveRoot theta d)
    (P Q : Polynomial ℚ⟮theta⟯)
    (hP : P.natDegree < p) (hQ : Q.natDegree < p)
    (hcarry : X ^ p - 1 ∣ P * Q) :
    ∀ i k j l : Fin p,
      (P.coeff i.val - P.coeff k.val) *
        (Q.coeff j.val - Q.coeff l.val) = 0 := by
  rcases coprime_character_constant_family hp hd hcop htheta P Q hP hQ hcarry
    with h | h
  · intro i k j l
    simp [h i k]
  · intro i k j l
    simp [h j l]

theorem carry_evaluation_one {K : Type*} [Field K]
    (p : ℕ) (P Q : K[X]) (hcarry : X ^ p - 1 ∣ P * Q) :
    P.eval 1 * Q.eval 1 = 0 := by
  obtain ⟨H, hH⟩ := hcarry
  have he := congrArg (Polynomial.eval (1 : K)) hH
  simpa using he

theorem carry_coefficient_sum_product {K : Type*} [Field K]
    {p : ℕ} (P Q : K[X]) (hP : P.natDegree < p) (hQ : Q.natDegree < p)
    (hcarry : X ^ p - 1 ∣ P * Q) :
    (∑ i : Fin p, P.coeff i.val) * (∑ j : Fin p, Q.coeff j.val) = 0 := by
  have h := carry_evaluation_one p P Q hcarry
  rw [eval_eq_sum_range' hP, eval_eq_sum_range' hQ] at h
  simpa [Fin.sum_univ_eq_sum_range] using h

end PrimeCharacter

#print axioms PrimeCharacter.coprime_character_constant_family
#print axioms PrimeCharacter.coprime_character_rectangles
#print axioms PrimeCharacter.carry_coefficient_sum_product
