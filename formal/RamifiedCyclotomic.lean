import RelativeCyclotomic

/-!
# The ramified character case over an actual cyclotomic subfield of C

Let p be prime, d > 0, p divide d, and theta be a primitive dth root in C.
This file proves that X^p - theta is irreducible over the actual intermediate
field Q(theta). The constant is `AdjoinSimple.gen Q theta`, not a free parameter.

No relative-degree or irreducibility conclusion is assumed. For every zeta
with zeta^p = theta we derive its order p*d, use the rational cyclotomic degree
and the tower law to obtain the relative degree lower bound p, and identify the
binomial with the minimal polynomial. Existence of a suitable zeta in the final
irreducibility theorem is constructed using a primitive (p*d)th root; no added
algebraic-closure assumption is needed. All arguments include p = 2.

The final factor-zero theorem is the degree-below-p implication needed in the
ramified Fourier character case. It does not formalize carry rings, Fourier
descent, cyclic tiling, induction, or the full Coven--Meyerowitz conjecture.

Replay: `lake env lean RamifiedCyclotomic.lean` in the pinned Lean 4.23.0 project.
The axiom reports below are part of the replay. No sorry or added axiom is used.
-/

open Polynomial IntermediateField
open scoped IntermediateField

noncomputable section

namespace RamifiedCyclotomic

/-- A pth root of a primitive dth root has order p*d when p divides d. -/
theorem primitive_of_prime_root {p d : ℕ} (hp : p.Prime) (hpd : p ∣ d)
    {θ ζ : ℂ} (hθ : IsPrimitiveRoot θ d) (hpow : ζ ^ p = θ) :
    IsPrimitiveRoot ζ (p * d) := by
  have hdord : d ∣ orderOf ζ := hθ.dvd_of_pow_eq_one _ (by
    rw [← hpow, ← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
  have hpord : p ∣ orderOf ζ := dvd_trans hpd hdord
  have horder : d = orderOf ζ / p := by
    rw [hθ.eq_orderOf, ← hpow, orderOf_pow_of_dvd hp.ne_zero hpord]
  have heq : p * d = orderOf ζ := by
    rw [horder, Nat.mul_div_cancel' hpord]
  rw [heq]
  exact IsPrimitiveRoot.orderOf ζ

/-- The actual binomial over Q(theta) is the minimal polynomial of every pth root. -/
theorem binomial_eq_minpoly {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) {θ ζ : ℂ} (hθ : IsPrimitiveRoot θ d) (hpow : ζ ^ p = θ) :
    (X : ℚ⟮θ⟯[X]) ^ p - C (IntermediateField.AdjoinSimple.gen ℚ θ) =
      minpoly ℚ⟮θ⟯ ζ := by
  let K : IntermediateField ℚ ℂ := ℚ⟮θ⟯
  let θK : K := IntermediateField.AdjoinSimple.gen ℚ θ
  have hζ : IsPrimitiveRoot ζ (p * d) := primitive_of_prime_root hp hpd hθ hpow
  have hθint : IsIntegral ℚ θ := (hθ.isIntegral hd).tower_top
  have hζint : IsIntegral K ζ := (hζ.isIntegral (Nat.mul_pos hp.pos hd)).tower_top
  let L : IntermediateField K ℂ := K⟮ζ⟯
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hθint
  letI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hζint
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  have hdimK : Module.finrank ℚ K = d.totient := by
    change Module.finrank ℚ ℚ⟮θ⟯ = d.totient
    rw [IntermediateField.adjoin.finrank hθint,
      ← Polynomial.cyclotomic_eq_minpoly_rat hθ hd, Polynomial.natDegree_cyclotomic]
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  have hζL : IsPrimitiveRoot ζL (p * d) :=
    hζ.of_map_of_injective (f := L.subtype) (fun _ _ h => Subtype.ext h)
  have hlower := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hζL hζL
    (Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos
      (Nat.mul_pos hp.pos hd) (Nat.mul_pos hp.pos hd)))
  rw [Nat.lcm_self, Nat.totient_mul_of_prime_of_dvd hp hpd,
    ← Module.finrank_mul_finrank ℚ K L, hdimK] at hlower
  have hdpos : 0 < d.totient := Nat.totient_pos.mpr hd
  have hdegree : p ≤ Module.finrank K L := by nlinarith
  have hroot : Polynomial.aeval ζ ((X : K[X]) ^ p - C θK) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change ζ ^ p - θ = 0
    exact sub_eq_zero.mpr hpow
  change (X : K[X]) ^ p - C θK = minpoly K ζ
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hζint) (Polynomial.monic_X_pow_sub_C θK hp.ne_zero)
    (minpoly.dvd K ζ hroot)
  rw [Polynomial.natDegree_X_pow_sub_C]
  simpa only [L, IntermediateField.adjoin.finrank hζint] using hdegree

/-- Relative degree p is a conclusion, not a hypothesis. -/
theorem relative_finrank {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) {θ ζ : ℂ} (hθ : IsPrimitiveRoot θ d) (hpow : ζ ^ p = θ) :
    Module.finrank ℚ⟮θ⟯ ℚ⟮θ⟯⟮ζ⟯ = p := by
  have hζint : IsIntegral ℚ⟮θ⟯ ζ :=
    ((primitive_of_prime_root hp hpd hθ hpow).isIntegral
      (Nat.mul_pos hp.pos hd)).tower_top
  rw [IntermediateField.adjoin.finrank hζint,
    ← binomial_eq_minpoly hp hd hpd hθ hpow, Polynomial.natDegree_X_pow_sub_C]

/-- Irreducibility in the actual cyclotomic intermediate field, including p = 2. -/
theorem ramified_irreducible {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) {θ : ℂ} (hθ : IsPrimitiveRoot θ d) :
    Irreducible ((X : ℚ⟮θ⟯[X]) ^ p -
      C (IntermediateField.AdjoinSimple.gen ℚ θ)) := by
  let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * d : ℕ) : ℂ))
  have hρ : IsPrimitiveRoot ρ (p * d) :=
    Complex.isPrimitiveRoot_exp (p * d) (Nat.mul_pos hp.pos hd).ne'
  have hρp : IsPrimitiveRoot (ρ ^ p) d := hρ.pow (Nat.mul_pos hp.pos hd) rfl
  letI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨i, _, hi⟩ := hρp.eq_pow_of_pow_eq_one hθ.pow_eq_one
  let ζ := ρ ^ i
  have hpow : ζ ^ p = θ := by
    change (ρ ^ i) ^ p = θ
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact hi
  rw [binomial_eq_minpoly hp hd hpd hθ hpow]
  exact minpoly.irreducible
    ((primitive_of_prime_root hp hpd hθ hpow).isIntegral
      (Nat.mul_pos hp.pos hd)).tower_top

/-- Evaluation at the root is injective on polynomials of degree below p. -/
theorem low_degree_aeval_eq_zero_iff {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) {θ ζ : ℂ} (hθ : IsPrimitiveRoot θ d) (hpow : ζ ^ p = θ)
    (P : ℚ⟮θ⟯[X]) (hP : P.natDegree < p) :
    Polynomial.aeval ζ P = 0 ↔ P = 0 := by
  constructor
  · intro hzero
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ⟮θ⟯ ζ hzero) hne
    rw [← binomial_eq_minpoly hp hd hpd hθ hpow,
      Polynomial.natDegree_X_pow_sub_C] at hle
    exact (Nat.not_le_of_gt hP) hle
  · rintro rfl
    exact map_zero _

/-- The actual degree-below-p factor-zero implication for the character argument. -/
theorem low_degree_product_zero {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hpd : p ∣ d) {θ ζ : ℂ} (hθ : IsPrimitiveRoot θ d) (hpow : ζ ^ p = θ)
    (P Q : ℚ⟮θ⟯[X]) (hP : P.natDegree < p) (hQ : Q.natDegree < p)
    (hzero : Polynomial.aeval ζ (P * Q) = 0) : P = 0 ∨ Q = 0 := by
  rw [map_mul, mul_eq_zero] at hzero
  exact hzero.imp
    (low_degree_aeval_eq_zero_iff hp hd hpd hθ hpow P hP).mp
    (low_degree_aeval_eq_zero_iff hp hd hpd hθ hpow Q hQ).mp

end RamifiedCyclotomic

#print axioms RamifiedCyclotomic.primitive_of_prime_root
#print axioms RamifiedCyclotomic.binomial_eq_minpoly
#print axioms RamifiedCyclotomic.relative_finrank
#print axioms RamifiedCyclotomic.ramified_irreducible
#print axioms RamifiedCyclotomic.low_degree_aeval_eq_zero_iff
#print axioms RamifiedCyclotomic.low_degree_product_zero
