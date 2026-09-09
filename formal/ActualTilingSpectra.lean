import DephasedMasks
import CanonicalMaskPolynomial
import PrimeDirectionArithmetic

/-!
Assembly of character information for literal dephased ordinary fibers.
The trivial character is treated by actual masses, not by applying the
nontrivial-character vanishing theorem at one.
-/

open scoped BigOperators

noncomputable section

namespace ActualTilingSpectra

open DephasedMasks CyclicEvaluation StripeCollapse

variable (p M : ℕ) [NeZero p] [NeZero M]

omit [NeZero p] in
theorem dephased_evaluation_one (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (rho : ℕ) (i : Fin p) :
    evaluate (dephased p M A rho i) 1 =
      (FiberMass.mass (integerFiber p M A i) : ℂ) := by
  rw [DephasedMasks.evaluate_dephased p M A rho i (one_pow M)]
  simp [CoprimeTilingFibers.complexCoefficient, CyclicFiberEvaluation.maskEval,
    CyclicFiberEvaluation.fiber, FiberMass.mass]

theorem sum_dephased_evaluation_one (A : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (rho : ℕ) :
    (∑ i : Fin p, evaluate (dephased p M A rho i) 1) = (FiberMass.mass A : ℂ) := by
  simp_rw [dephased_evaluation_one]
  simpa [FiberMass.mass, CyclicFiberEvaluation.fiber] using
    (CyclicFiberEvaluation.sum_fibers p M (fun x => (A x : ℂ))).symm

theorem evaluate_sum {N : ℕ} [NeZero N] {ι : Type*} [Fintype ι]
    (f : ι → AddMonoidAlgebra ℤ (ZMod N)) {z : ℂ} (hz : z ^ N = 1) :
    evaluate (∑ i, f i) z = ∑ i, evaluate (f i) z := by
  simpa only [evaluationHom_apply] using map_sum (evaluationHom hz) f Finset.univ

theorem evaluate_constant {N : ℕ} [NeZero N] (c : ℤ) (z : ℂ) :
    evaluate (constantMask c : AddMonoidAlgebra ℤ (ZMod N)) z =
      (c : ℂ) * evaluate (constantMask 1 : AddMonoidAlgebra ℤ (ZMod N)) z := by
  simp [evaluate, Finset.mul_sum]

theorem evaluate_constant_one {N : ℕ} [NeZero N] (c : ℤ) :
    evaluate (constantMask c : AddMonoidAlgebra ℤ (ZMod N)) 1 = (N : ℂ) * c := by
  simp [evaluate, ZMod.card, mul_comm]

theorem trivial_total (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (rho : ℕ) :
    evaluate ((∑ i, dephased p M A rho i) * (∑ j, dephased p M B rho j)) 1 =
      evaluate (constantMask (p : ℤ) : AddMonoidAlgebra ℤ (ZMod M)) 1 := by
  rw [evaluate_mul _ _ (one_pow M), evaluate_sum _ (one_pow M),
    evaluate_sum _ (one_pow M), sum_dephased_evaluation_one,
    sum_dephased_evaluation_one, evaluate_constant_one]
  have h := congrArg (fun n : ℤ => (n : ℂ))
    (CanonicalMaskPolynomial.tiling_mass_product A B htile)
  simpa [mul_comm] using h

omit [NeZero p] in
theorem trivial_rectangles (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (rho : ℕ)
    (hB : ∀ j l : Fin p,
      FiberMass.mass (integerFiber p M B j) = FiberMass.mass (integerFiber p M B l)) :
    ∀ i j k l : Fin p,
      evaluate (dephased p M A rho i * dephased p M B rho j +
        dephased p M A rho k * dephased p M B rho l) 1 =
      evaluate (dephased p M A rho i * dephased p M B rho l +
        dephased p M A rho k * dephased p M B rho j) 1 := by
  intro i j k l
  simp only [evaluate_add _ _ (one_pow M), evaluate_mul _ _ (one_pow M),
    dephased_evaluation_one, hB j l]

theorem ramified_family_zero (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    {d : ℕ} (hd : 0 < d) (hpd : p ∣ d) {theta z : ℂ}
    (htheta : IsPrimitiveRoot theta d) (hthetaM : theta ^ M = 1)
    (hz : z ^ p = theta) (rho : ℕ) :
    (∀ i : Fin p, evaluate (dephased p M A rho i) theta = 0) ∨
      (∀ j : Fin p, evaluate (dephased p M B rho j) theta = 0) := by
  rcases CyclicFiberEvaluation.ramified_tiling_fiber_zero p M A B htile hp hd hpd
    htheta hthetaM hz with h | h
  · left
    intro i
    rw [DephasedMasks.evaluate_dephased p M A rho i hthetaM]
    simp only [CoprimeTilingFibers.complexCoefficient, h i, mul_zero]
  · right
    intro j
    rw [DephasedMasks.evaluate_dephased p M B rho j hthetaM]
    simp only [CoprimeTilingFibers.complexCoefficient, h j, mul_zero]

theorem ramified_product_zero (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    {d : ℕ} (hd : 0 < d) (hpd : p ∣ d) {theta z : ℂ}
    (htheta : IsPrimitiveRoot theta d) (hthetaM : theta ^ M = 1)
    (hz : z ^ p = theta) (rho : ℕ) :
    ∀ i j : Fin p,
      evaluate (dephased p M A rho i * dephased p M B rho j) theta = 0 := by
  rcases ramified_family_zero p M A B htile hp hd hpd htheta hthetaM hz rho with h | h
  · intro i j
    rw [evaluate_mul _ _ hthetaM, h i, zero_mul]
  · intro i j
    rw [evaluate_mul _ _ hthetaM, h j, mul_zero]

theorem coprime_rectangles (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    {d : ℕ} (hd : 1 < d) (hcop : p.Coprime d) {theta : ℂ}
    (htheta : IsPrimitiveRoot theta d) (hthetaM : theta ^ M = 1)
    (rho : ℕ) (hrho : (theta ^ rho) ^ p = theta) :
    ∀ i j k l : Fin p,
      evaluate (dephased p M A rho i * dephased p M B rho j +
        dephased p M A rho k * dephased p M B rho l) theta =
      evaluate (dephased p M A rho i * dephased p M B rho l +
        dephased p M A rho k * dephased p M B rho j) theta := by
  intro i j k l
  simpa only [evaluate_add _ _ hthetaM, evaluate_mul _ _ hthetaM,
    DephasedMasks.evaluate_dephased p M _ _ _ hthetaM] using
    CoprimeTilingFibers.coprime_tiling_additive_rectangles p M A B htile hp hd hcop
      htheta hthetaM rho hrho i k j l

theorem coprime_total_zero (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) {d : ℕ} (hd : 1 < d) {theta : ℂ}
    (htheta : IsPrimitiveRoot theta d) (hthetaM : theta ^ M = 1)
    (rho : ℕ) (hrho : (theta ^ rho) ^ p = theta) :
    evaluate ((∑ i, dephased p M A rho i) * (∑ j, dephased p M B rho j)) theta = 0 := by
  simpa only [evaluate_mul _ _ hthetaM, evaluate_sum _ hthetaM,
    DephasedMasks.evaluate_dephased p M _ _ _ hthetaM] using
    CoprimeTilingFibers.tiling_coefficient_sum_product_zero p M A B htile hd
      htheta hthetaM rho hrho

theorem actual_rectangles (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    (a R : ℕ) (hR : 0 < R) (hM : M = p ^ a * R) (hcop : p.Coprime R)
    (hB : ∀ j l : Fin p,
      FiberMass.mass (integerFiber p M B j) = FiberMass.mass (integerFiber p M B l)) :
    ∀ i j k l : Fin p,
      dephased p M A (PrimeDirectionArithmetic.rho p R) i *
          dephased p M B (PrimeDirectionArithmetic.rho p R) j +
        dephased p M A (PrimeDirectionArithmetic.rho p R) k *
          dephased p M B (PrimeDirectionArithmetic.rho p R) l =
      dephased p M A (PrimeDirectionArithmetic.rho p R) i *
          dephased p M B (PrimeDirectionArithmetic.rho p R) l +
        dephased p M A (PrimeDirectionArithmetic.rho p R) k *
          dephased p M B (PrimeDirectionArithmetic.rho p R) j := by
  intro i j k l
  apply SpectralIdentities.evaluations_determine_mask
  intro theta hthetaM
  by_cases htheta1 : theta = 1
  · subst theta
    exact trivial_rectangles p M A B _ hB i j k l
  · obtain ⟨hd, hprim, _⟩ :=
      PrimeDirectionArithmetic.root_order_data (NeZero.pos M) hthetaM
    have hdgt : 1 < orderOf theta :=
      (PrimeDirectionArithmetic.primitive_ne_one_iff hd hprim).mp htheta1
    by_cases hpd : p ∣ orderOf theta
    · obtain ⟨z, hz⟩ := PrimeDirectionArithmetic.exists_pth_root hp (NeZero.pos M) hthetaM
      have hzprod := ramified_product_zero p M A B htile hp hd hpd hprim hthetaM hz
        (PrimeDirectionArithmetic.rho p R)
      simp only [evaluate_add _ _ hthetaM, hzprod]
    · have hthetaR : theta ^ R = 1 :=
        PrimeDirectionArithmetic.coprimePart_power_eq_one hp (by simpa only [hM] using hthetaM) hpd
      exact coprime_rectangles p M A B htile hp hdgt (hp.coprime_iff_not_dvd.mpr hpd)
        hprim hthetaM _ (PrimeDirectionArithmetic.inverse_exponent_root hR hcop hthetaR)
        i j k l

theorem actual_total (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    (a R : ℕ) (hR : 0 < R) (hM : M = p ^ a * R) (hcop : p.Coprime R) :
    (∑ i, dephased p M A (PrimeDirectionArithmetic.rho p R) i) *
      (∑ j, dephased p M B (PrimeDirectionArithmetic.rho p R) j) =
        constantMask (p : ℤ) := by
  apply SpectralIdentities.evaluations_determine_mask
  intro theta hthetaM
  by_cases htheta1 : theta = 1
  · subst theta
    exact trivial_total p M A B htile _
  · rw [evaluate_constant, evaluate_all_ones hthetaM htheta1, mul_zero]
    obtain ⟨hd, hprim, _⟩ :=
      PrimeDirectionArithmetic.root_order_data (NeZero.pos M) hthetaM
    have hdgt : 1 < orderOf theta :=
      (PrimeDirectionArithmetic.primitive_ne_one_iff hd hprim).mp htheta1
    by_cases hpd : p ∣ orderOf theta
    · obtain ⟨z, hz⟩ := PrimeDirectionArithmetic.exists_pth_root hp (NeZero.pos M) hthetaM
      have h := ramified_family_zero p M A B htile hp hd hpd hprim hthetaM hz
        (PrimeDirectionArithmetic.rho p R)
      rw [evaluate_mul _ _ hthetaM, evaluate_sum _ hthetaM, evaluate_sum _ hthetaM]
      rcases h with h | h <;> simp only [h, Finset.sum_const_zero, zero_mul, mul_zero]
    · have hthetaR : theta ^ R = 1 :=
        PrimeDirectionArithmetic.coprimePart_power_eq_one hp (by simpa only [hM] using hthetaM) hpd
      exact coprime_total_zero p M A B htile hdgt hprim hthetaM _
        (PrimeDirectionArithmetic.inverse_exponent_root hR hcop hthetaR)

theorem actual_product_period (A B : AddMonoidAlgebra ℤ (ZMod (p * M)))
    (htile : A * B = constantMask 1) (hp : p.Prime)
    (a R : ℕ) (hR : 0 < R) (hM : M = p ^ a * R) (rho : ℕ) :
    ∀ i j : Fin p, ∀ x : ZMod M,
      (dephased p M A rho i * dephased p M B rho j) (x + (R : ZMod M)) =
        (dephased p M A rho i * dephased p M B rho j) x := by
  intro i j
  apply SpectralIdentities.spectral_period R
  intro theta hthetaM hnot
  obtain ⟨d, z, hd, hpd, hprim, _, hz, _, _⟩ :=
    PrimeDirectionArithmetic.ramified_root_data hp hR
      (by simpa only [hM] using hthetaM) hnot
  exact ramified_product_zero p M A B htile hp hd hpd hprim hthetaM hz rho i j

end ActualTilingSpectra

#print axioms ActualTilingSpectra.trivial_total
#print axioms ActualTilingSpectra.trivial_rectangles
#print axioms ActualTilingSpectra.actual_rectangles
#print axioms ActualTilingSpectra.actual_total
#print axioms ActualTilingSpectra.actual_product_period
