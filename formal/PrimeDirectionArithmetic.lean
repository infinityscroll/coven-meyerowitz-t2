import RelativeCyclotomic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
Arithmetic of actual roots of unity in a prime direction. The positive order,
its prime-free reduction, natural inverse exponent, and existence of a pth
root are derived from the actual root equation. No character-separation,
relative-degree, or specialized carry-divisibility hypothesis is used.
-/

noncomputable section

namespace PrimeDirectionArithmetic

theorem root_order_data {N : ℕ} (hN : 0 < N) {theta : ℂ}
    (htheta : theta ^ N = 1) :
    0 < orderOf theta ∧ IsPrimitiveRoot theta (orderOf theta) ∧
      orderOf theta ∣ N := by
  have hf : IsOfFinOrder theta := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, htheta⟩
  exact ⟨hf.orderOf_pos, IsPrimitiveRoot.orderOf theta, orderOf_dvd_of_pow_eq_one htheta⟩

theorem positive_order_of_root {N : ℕ} (hN : 0 < N) {theta : ℂ}
    (htheta : theta ^ N = 1) : 0 < orderOf theta :=
  (root_order_data hN htheta).1

theorem primitive_ne_one_iff {d : ℕ} (hd : 0 < d) {theta : ℂ}
    (htheta : IsPrimitiveRoot theta d) : theta ≠ 1 ↔ 1 < d := by
  constructor
  · intro hne
    have hdne : d ≠ 1 := by
      intro heq
      subst d
      exact hne (IsPrimitiveRoot.one_right_iff.mp htheta)
    omega
  · exact htheta.ne_one

theorem exists_primitive_order {N : ℕ} (hN : 0 < N) {theta : ℂ}
    (htheta : theta ^ N = 1) :
    ∃ d : ℕ, 0 < d ∧ IsPrimitiveRoot theta d ∧ d ∣ N ∧
      (theta ≠ 1 ↔ 1 < d) := by
  obtain ⟨hd, hprim, hdiv⟩ := root_order_data hN htheta
  exact ⟨orderOf theta, hd, hprim, hdiv, primitive_ne_one_iff hd hprim⟩

/-- Removing the p-power part of a divisor prime to p is pure arithmetic. -/
theorem order_dvd_coprimePart {p a R d : ℕ} (hp : p.Prime)
    (hdiv : d ∣ p ^ a * R) (hnot : ¬ p ∣ d) : d ∣ R :=
  (hp.coprime_pow_of_not_dvd hnot).dvd_of_dvd_mul_left hdiv

theorem coprime_order_dvd_R {p a R : ℕ} (hp : p.Prime)
    {theta : ℂ} (htheta : theta ^ (p ^ a * R) = 1)
    (hnot : ¬ p ∣ orderOf theta) : orderOf theta ∣ R :=
  order_dvd_coprimePart hp (orderOf_dvd_of_pow_eq_one htheta) hnot

theorem coprimePart_power_eq_one {p a R : ℕ} (hp : p.Prime)
    {theta : ℂ} (htheta : theta ^ (p ^ a * R) = 1)
    (hnot : ¬ p ∣ orderOf theta) : theta ^ R = 1 := by
  exact orderOf_dvd_iff_pow_eq_one.mp
    (order_dvd_coprimePart hp (orderOf_dvd_of_pow_eq_one htheta) hnot)

theorem prime_dvd_order_of_not_coprimePart_root {p a R : ℕ} (hp : p.Prime)
    {theta : ℂ} (htheta : theta ^ (p ^ a * R) = 1)
    (hnot : theta ^ R ≠ 1) : p ∣ orderOf theta := by
  by_contra h
  exact hnot (coprimePart_power_eq_one hp htheta h)

/-- Both cases for an arbitrary actual period root, including its true order. -/
theorem prime_direction_order_cases {p a R : ℕ} (hp : p.Prime) (hR : 0 < R)
    (hcop : p.Coprime R) {theta : ℂ} (htheta : theta ^ (p ^ a * R) = 1) :
    ∃ d : ℕ, 0 < d ∧ IsPrimitiveRoot theta d ∧ d ∣ p ^ a * R ∧
      (theta ≠ 1 ↔ 1 < d) ∧
      ((¬ p ∣ d) ↔ d ∣ R) ∧
      ((¬ p ∣ d) ↔ theta ^ R = 1) ∧
      (theta ^ R ≠ 1 → p ∣ d) := by
  obtain ⟨d, hd, hprim, hdiv, hne⟩ :=
    exists_primitive_order (Nat.mul_pos (pow_pos hp.pos a) hR) htheta
  have hdR : (¬ p ∣ d) ↔ d ∣ R := by
    constructor
    · exact order_dvd_coprimePart hp hdiv
    · intro hdR hpd
      exact (hp.coprime_iff_not_dvd.mp hcop) (hpd.trans hdR)
  have hpow : (¬ p ∣ d) ↔ theta ^ R = 1 :=
    hdR.trans (hprim.pow_eq_one_iff_dvd R).symm
  refine ⟨d, hd, hprim, hdiv, hne, hdR, hpow, ?_⟩
  intro hnot
  by_contra hpd
  exact hnot (hpow.mp hpd)

/-- Canonical natural inverse exponent. At R=1 it is exactly zero. -/
def rho (p R : ℕ) : ℕ := ((p : ZMod R)⁻¹).val

@[simp] theorem rho_one (p : ℕ) : rho p 1 = 0 := by
  unfold rho
  rw [show (p : ZMod 1)⁻¹ = 0 from Subsingleton.elim _ _]
  rfl

theorem rho_lt (p R : ℕ) [NeZero R] : rho p R < R :=
  ZMod.val_lt _

theorem rho_modEq {p R : ℕ} (hcop : p.Coprime R) :
    p * rho p R ≡ 1 [MOD R] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ R).mp
  simpa only [rho, Nat.cast_mul, Nat.cast_one] using ZMod.mul_val_inv hcop

theorem inverse_exponent_root_of_modEq {p R r : ℕ} (hR : 0 < R)
    (hinverse : p * r ≡ 1 [MOD R]) {theta : ℂ} (htheta : theta ^ R = 1) :
    (theta ^ r) ^ p = theta := by
  have hf : IsOfFinOrder theta := isOfFinOrder_iff_pow_eq_one.mpr ⟨R, hR, htheta⟩
  have hm : p * r ≡ 1 [MOD orderOf theta] :=
    hinverse.of_dvd (orderOf_dvd_of_pow_eq_one htheta)
  calc
    (theta ^ r) ^ p = theta ^ (p * r) := by rw [← pow_mul, Nat.mul_comm]
    _ = theta ^ 1 := hf.pow_eq_pow_iff_modEq.mpr hm
    _ = theta := pow_one _

theorem inverse_exponent_root {p R : ℕ} (hR : 0 < R) (hcop : p.Coprime R)
    {theta : ℂ} (htheta : theta ^ R = 1) : (theta ^ rho p R) ^ p = theta :=
  inverse_exponent_root_of_modEq hR (rho_modEq hcop) htheta

theorem rho_coprime_divisor {p R d : ℕ} (hcop : p.Coprime R) (hdR : d ∣ R) :
    (rho p R).Coprime d := by
  have hm : rho p R * p ≡ 1 [MOD d] := by
    simpa only [Nat.mul_comm] using (rho_modEq hcop).of_dvd hdR
  exact Nat.coprime_of_mul_modEq_one p hm

theorem inverse_exponent_primitive {p R d : ℕ} (hcop : p.Coprime R) (hdR : d ∣ R)
    {theta : ℂ} (htheta : IsPrimitiveRoot theta d) :
    IsPrimitiveRoot (theta ^ rho p R) d :=
  htheta.pow_of_coprime (rho p R) (rho_coprime_divisor hcop hdR)

/-- A finite root has an actual pth root in C. The construction uses an
explicit primitive (p*N)th root and its powers, not an existence premise. -/
theorem exists_root_of_period {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {theta : ℂ} (htheta : theta ^ N = 1) :
    ∃ z : ℂ, z ^ p = theta ∧ z ^ (p * N) = 1 ∧ (theta ≠ 1 → z ≠ 1) := by
  let eta : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))
  have heta : IsPrimitiveRoot eta (p * N) :=
    Complex.isPrimitiveRoot_exp (p * N) (Nat.mul_pos hp hN).ne'
  have hetap : IsPrimitiveRoot (eta ^ p) N := heta.pow (Nat.mul_pos hp hN) rfl
  letI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, _, hi⟩ := hetap.eq_pow_of_pow_eq_one htheta
  have hz : (eta ^ i) ^ p = theta := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact hi
  refine ⟨eta ^ i, hz, ?_, ?_⟩
  · rw [pow_mul, hz, htheta]
  · intro hne heq
    apply hne
    rw [← hz, heq, one_pow]

theorem exists_pth_root {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {theta : ℂ} (htheta : theta ^ N = 1) : ∃ z : ℂ, z ^ p = theta := by
  obtain ⟨z, hz, _, _⟩ := exists_root_of_period hp.pos hN htheta
  exact ⟨z, hz⟩

/-- Direct ramified-case input package from theta^M=1 and theta^R != 1. -/
theorem ramified_root_data {p a R : ℕ} (hp : p.Prime) (hR : 0 < R)
    {theta : ℂ} (htheta : theta ^ (p ^ a * R) = 1) (hnot : theta ^ R ≠ 1) :
    ∃ d : ℕ, ∃ z : ℂ,
      0 < d ∧ p ∣ d ∧ IsPrimitiveRoot theta d ∧ d ∣ p ^ a * R ∧
      z ^ p = theta ∧ z ^ (p * (p ^ a * R)) = 1 ∧ z ≠ 1 := by
  have hM : 0 < p ^ a * R := Nat.mul_pos (pow_pos hp.pos a) hR
  obtain ⟨hd, hprim, hdiv⟩ := root_order_data hM htheta
  obtain ⟨z, hz, hzN, hznon⟩ := exists_root_of_period hp.pos hM htheta
  have hne : theta ≠ 1 := by
    intro heq
    exact hnot (by rw [heq, one_pow])
  exact ⟨orderOf theta, z, hd,
    prime_dvd_order_of_not_coprimePart_root hp htheta hnot,
    hprim, hdiv, hz, hzN, hznon hne⟩

/-- Raising a primitive upper-level mixed root to p lowers its p-level by
one while retaining the entire other-prime factor d. -/
theorem upper_level_power_primitive {p k d : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hd : 0 < d) {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta (p ^ k * d)) :
    IsPrimitiveRoot (zeta ^ p) (p ^ (k - 1) * d) := by
  apply hzeta.pow (Nat.mul_pos (pow_pos hp.pos k) hd)
  calc
    p ^ k * d = p ^ (k - 1 + 1) * d := by congr 2; omega
    _ = p * (p ^ (k - 1) * d) := by rw [pow_succ]; ring

theorem upper_level_power_not_coprimePart_root {p k d R : ℕ}
    (hp : p.Prime) (hk : 2 ≤ k) (hd : 0 < d) (hcop : p.Coprime R)
    {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta (p ^ k * d)) :
    (zeta ^ p) ^ R ≠ 1 := by
  have hprim := upper_level_power_primitive hp (by omega) hd hzeta
  have hpd : p ∣ p ^ (k - 1) * d :=
    dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) d
  intro heq
  exact (hp.coprime_iff_not_dvd.mp hcop)
    (hpd.trans (hprim.dvd_of_pow_eq_one R heq))

#print axioms exists_primitive_order
#print axioms positive_order_of_root
#print axioms coprime_order_dvd_R
#print axioms prime_direction_order_cases
#print axioms rho_one
#print axioms rho_modEq
#print axioms inverse_exponent_root
#print axioms inverse_exponent_root_of_modEq
#print axioms inverse_exponent_primitive
#print axioms exists_root_of_period
#print axioms exists_pth_root
#print axioms ramified_root_data
#print axioms upper_level_power_primitive
#print axioms upper_level_power_not_coprimePart_root

end PrimeDirectionArithmetic
