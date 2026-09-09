import CyclicFiberEvaluation
import PrimeCharacter

/-!
# Coprime character identities from actual integral cyclic tiling

For positive p,M, the coefficient `complexCoefficient f theta rho i` is exactly
theta^(rho*i.val) times the evaluation at theta of the literal ith base-p fiber
of f. Its field-valued counterpart and `dephasedPolynomial` are constructed in
the actual intermediate field Q(theta); the polynomial has degree below p.

The main conclusions assume actual integral cyclic convolution A*B = 1 on
ZMod(p*M), p prime, theta a primitive dth root with d>1 coprime to p,
theta^M=1, and the explicit dephasing equation (theta^rho)^p=theta, rho natural.
Evaluation regrouping proves that evaluating this polynomial at omega is the
original mask evaluation at theta^rho*omega whenever omega^p=1.

For a constructed primitive pth root omega, relative cyclotomic irreducibility
is imported as a proved theorem, used to identify the actual minpoly of omega,
and hence to show one whole coefficient family is constant. The only use of
PrimeCharacter is its small-degree cyclotomic-multiple coefficient lemma.
No divisibility by X^p-1 or specialized polynomial-product identity is assumed.

Evaluation at omega=1 independently gives the product of coefficient sums zero.
The explicit d>1 hypothesis makes theta^rho*omega nontrivial in both arguments:
its pth power is theta != 1. This file deliberately does not assert the sum
identity at d=1, where the trivial-character tiling value is nonzero.

The conclusions are for the actual complex coefficients: constant-family
alternative, vanishing rectangular difference products, additive rectangular
identities, and product of coefficient sums zero. p=2 is included. Integral
convolution suffices; no nonnegativity or Boolean-mask assumption is required.

Scope: this establishes the nontrivial coprime-character algebraic step from
actual tiling. It does not assert Fourier inversion, periods, Boolean stripes,
phase-family tiling, either-factor T2 induction, or a formal full CM proof.
Replay: `lake env lean CoprimeTilingFibers.lean` in the pinned Lean 4.23.0
workspace. No sorry, added axiom, or native decision oracle is used.
-/

open scoped BigOperators
open Polynomial IntermediateField CyclicFiberEvaluation
open scoped IntermediateField

noncomputable section

namespace CoprimeTilingFibers

variable (p M : ℕ) [NeZero p] [NeZero M]

def dephasedCoefficient (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) (i : Fin p) :
    ℚ⟮θ⟯ :=
  (IntermediateField.AdjoinSimple.gen ℚ θ) ^ (ρ * i.val) *
    (cyclotomicFiberPolynomial p M f θ).coeff i.val

def complexCoefficient (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) (i : Fin p) : ℂ :=
  θ ^ (ρ * i.val) * maskEval (fiber p M (fun x => (f x : ℂ)) i) θ

omit [NeZero p] in
theorem dephasedCoefficient_map (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) (i : Fin p) :
    algebraMap ℚ⟮θ⟯ ℂ (dephasedCoefficient p M f θ ρ i) =
      complexCoefficient p M f θ ρ i := by
  simp only [dephasedCoefficient, map_mul, map_pow, cyclotomicFiberPolynomial_coeff_map]
  rfl

def dephasedPolynomial (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) : ℚ⟮θ⟯[X] :=
  ∑ i : Fin p, C (dephasedCoefficient p M f θ ρ i) * X ^ i.val

omit [NeZero p] in
theorem dephasedPolynomial_coeff (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) (i : Fin p) :
    (dephasedPolynomial p M f θ ρ).coeff i.val = dephasedCoefficient p M f θ ρ i := by
  classical
  simp only [dephasedPolynomial, finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
  simp

theorem dephasedPolynomial_natDegree_lt (f : ZMod (p * M) → ℤ) (θ : ℂ) (ρ : ℕ) :
    (dephasedPolynomial p M f θ ρ).natDegree < p := by
  by_cases h : dephasedPolynomial p M f θ ρ = 0
  · rw [h, natDegree_zero]
    exact NeZero.pos p
  · apply (natDegree_lt_iff_degree_lt h).mpr
    exact degree_sum_fin_lt _

omit [NeZero p] in
theorem dephasedPolynomial_aeval (f : ZMod (p * M) → ℤ) (θ ω : ℂ) (ρ : ℕ) :
    aeval ω (dephasedPolynomial p M f θ ρ) =
      ∑ i : Fin p, complexCoefficient p M f θ ρ i * ω ^ i.val := by
  simp only [dephasedPolynomial, map_sum, map_mul, map_pow, aeval_C, aeval_X,
    dephasedCoefficient_map]

theorem evaluate_dephased (f : AddMonoidAlgebra ℤ (ZMod (p * M)))
    {θ ω : ℂ} (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) (hω : ω ^ p = 1) :
    CyclicEvaluation.evaluate f (θ ^ ρ * ω) =
      aeval ω (dephasedPolynomial p M f θ ρ) := by
  change (∑ x : ZMod (p * M), (f x : ℂ) * (θ ^ ρ * ω) ^ x.val) = _
  rw [integer_eval_regroup, dephasedPolynomial_aeval]
  simp only [mul_pow, hρ, hω, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  simp only [complexCoefficient, maskEval, fiber, pow_mul]
  ring

omit [NeZero p] in
theorem minpoly_primitive_coprime {d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hcop : p.Coprime d) {θ ω : ℂ} (hθ : IsPrimitiveRoot θ d)
    (hω : IsPrimitiveRoot ω p) :
    minpoly ℚ⟮θ⟯ ω = cyclotomic p ℚ⟮θ⟯ := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
    (RelativeCyclotomic.prime_coprime_irreducible hp hd hcop hθ)
  · rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hω.isRoot_cyclotomic hp.pos
  · exact cyclotomic.monic p ℚ⟮θ⟯

theorem tiling_dephased_product_zero
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    {d : ℕ} (hd : 1 < d) {θ ω : ℂ} (hθ : IsPrimitiveRoot θ d)
    (hθM : θ ^ M = 1) (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) (hω : ω ^ p = 1) :
    aeval ω (dephasedPolynomial p M A θ ρ) *
      aeval ω (dephasedPolynomial p M B θ ρ) = 0 := by
  have hz : (θ ^ ρ * ω) ^ p = θ := by rw [mul_pow, hρ, hω, mul_one]
  have hzN : (θ ^ ρ * ω) ^ (p * M) = 1 := by rw [pow_mul, hz, hθM]
  have hzne : θ ^ ρ * ω ≠ 1 := by
    intro heq
    apply hθ.ne_one hd
    rw [← hz, heq, one_pow]
  have h := CyclicEvaluation.tiling_evaluation_product_zero A B htile hzN hzne
  rwa [evaluate_dephased p M A ρ hρ hω, evaluate_dephased p M B ρ hρ hω] at h

theorem coprime_tiling_constant_family
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 1 < d) (hcop : p.Coprime d)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1)
    (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) :
    (∀ i k : Fin p, complexCoefficient p M A θ ρ i = complexCoefficient p M A θ ρ k) ∨
      (∀ j l : Fin p, complexCoefficient p M B θ ρ j = complexCoefficient p M B θ ρ l) := by
  letI : Fact p.Prime := ⟨hp⟩
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hω : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have heval := tiling_dephased_product_zero p M A B htile hd hθ hθM ρ hρ hω.pow_eq_one
  have hmin := minpoly_primitive_coprime p hp (by omega) hcop hθ hω
  have hconst : ∀ f : AddMonoidAlgebra ℤ (ZMod (p * M)),
      aeval ω (dephasedPolynomial p M f θ ρ) = 0 →
      ∀ i k : Fin p, complexCoefficient p M f θ ρ i = complexCoefficient p M f θ ρ k := by
    intro f hf i k
    have hdiv := minpoly.dvd ℚ⟮θ⟯ ω hf
    rw [hmin] at hdiv
    have hc := PrimeCharacter.small_cyclotomic_multiple_constant
      (dephasedPolynomial p M f θ ρ) (dephasedPolynomial_natDegree_lt p M f θ ρ) hdiv i k
    rw [dephasedPolynomial_coeff, dephasedPolynomial_coeff] at hc
    simpa only [dephasedCoefficient_map] using congrArg (algebraMap ℚ⟮θ⟯ ℂ) hc
  exact (mul_eq_zero.mp heval).imp (hconst A) (hconst B)

theorem coprime_tiling_rectangles
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 1 < d) (hcop : p.Coprime d)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1)
    (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) :
    ∀ i k j l : Fin p,
      (complexCoefficient p M A θ ρ i - complexCoefficient p M A θ ρ k) *
        (complexCoefficient p M B θ ρ j - complexCoefficient p M B θ ρ l) = 0 := by
  rcases coprime_tiling_constant_family p M A B htile hp hd hcop hθ hθM ρ hρ
    with h | h
  · intro i k j l
    simp only [h i k, sub_self, zero_mul]
  · intro i k j l
    simp only [h j l, sub_self, mul_zero]

theorem coprime_tiling_additive_rectangles
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 1 < d) (hcop : p.Coprime d)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1)
    (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) :
    ∀ i k j l : Fin p,
      complexCoefficient p M A θ ρ i * complexCoefficient p M B θ ρ j +
        complexCoefficient p M A θ ρ k * complexCoefficient p M B θ ρ l =
      complexCoefficient p M A θ ρ i * complexCoefficient p M B θ ρ l +
        complexCoefficient p M A θ ρ k * complexCoefficient p M B θ ρ j := by
  rcases coprime_tiling_constant_family p M A B htile hp hd hcop hθ hθM ρ hρ
    with h | h
  · intro i k j l
    rw [h i k]
    ring
  · intro i k j l
    rw [h j l]

theorem tiling_coefficient_sum_product_zero
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    {d : ℕ} (hd : 1 < d) {θ : ℂ} (hθ : IsPrimitiveRoot θ d)
    (hθM : θ ^ M = 1) (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) :
    (∑ i : Fin p, complexCoefficient p M A θ ρ i) *
      (∑ j : Fin p, complexCoefficient p M B θ ρ j) = 0 := by
  have h := tiling_dephased_product_zero p M A B htile hd hθ hθM ρ hρ
    (ω := 1) (one_pow p)
  simpa only [dephasedPolynomial_aeval, one_pow, mul_one] using h

theorem actual_coprime_character_identities
    (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = StripeCollapse.constantMask 1)
    (hp : p.Prime) {d : ℕ} (hd : 1 < d) (hcop : p.Coprime d)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ d) (hθM : θ ^ M = 1)
    (ρ : ℕ) (hρ : (θ ^ ρ) ^ p = θ) :
    (∀ i k j l : Fin p,
      (complexCoefficient p M A θ ρ i - complexCoefficient p M A θ ρ k) *
        (complexCoefficient p M B θ ρ j - complexCoefficient p M B θ ρ l) = 0) ∧
    ((∑ i : Fin p, complexCoefficient p M A θ ρ i) *
      (∑ j : Fin p, complexCoefficient p M B θ ρ j) = 0) :=
  ⟨coprime_tiling_rectangles p M A B htile hp hd hcop hθ hθM ρ hρ,
    tiling_coefficient_sum_product_zero p M A B htile hd hθ hθM ρ hρ⟩

end CoprimeTilingFibers

#print axioms CoprimeTilingFibers.dephasedCoefficient_map
#print axioms CoprimeTilingFibers.dephasedPolynomial_natDegree_lt
#print axioms CoprimeTilingFibers.evaluate_dephased
#print axioms CoprimeTilingFibers.minpoly_primitive_coprime
#print axioms CoprimeTilingFibers.coprime_tiling_constant_family
#print axioms CoprimeTilingFibers.coprime_tiling_rectangles
#print axioms CoprimeTilingFibers.coprime_tiling_additive_rectangles
#print axioms CoprimeTilingFibers.tiling_coefficient_sum_product_zero
#print axioms CoprimeTilingFibers.actual_coprime_character_identities
