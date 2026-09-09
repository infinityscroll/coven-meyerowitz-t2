import ActualTilingSpectra
import PrimaryAllocation

/-!
Actual prime-direction reduction: every independent phase sum tiles each
dephased complement fiber. All matrix, period, and mass hypotheses are derived
from an actual nonnegative cyclic tiling and ownership of the base prime.
-/

open scoped BigOperators

noncomputable section

namespace ActualPrimeReduction

open DephasedMasks PeriodicPhaseReduction StripeCollapse

theorem mass_single_one {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (t : G) : FiberMass.mass (AddMonoidAlgebra.single t 1 : AddMonoidAlgebra ℤ G) = 1 := by
  simp [FiberMass.mass, AddMonoidAlgebra.single_apply]

theorem mass_dephased (p M : ℕ) [NeZero p] [NeZero M]
    (A : AddMonoidAlgebra ℤ (ZMod (p * M))) (rho : ℕ) (i : Fin p) :
    FiberMass.mass (dephased p M A rho i) = PrimaryAllocation.baseFiberMass p M A i := by
  rw [dephased, FiberMass.mass_mul, mass_single_one, one_mul]
  rfl

theorem natural_dephased_boolean (p M : ℕ) [NeZero p] [NeZero M]
    (A : AddMonoidAlgebra ℕ (ZMod (p * M)))
    (hA : ∀ x, A x = 0 ∨ A x = 1) (rho : ℕ) (i : Fin p) :
    ∀ x, naturalDephased p M A rho i x = 0 ∨ naturalDephased p M A rho i x = 1 := by
  intro x
  simpa only [naturalDephased, PhaseTilings.translate_apply,
    FiberProductBoolean.ordinaryFiber_apply] using hA
      (CyclicFiberEvaluation.fiberIndex p M i (-((rho * i.val : ℕ) : ZMod M) + x))

variable (p a R : ℕ) [NeZero p] [NeZero R]

theorem actual_prime_phase_tilings
    (A B : AddMonoidAlgebra ℕ (ZMod (p * (p ^ a * R))))
    (htile : A * B = constantMask 1) (hp : p.Prime) (hcop : p.Coprime R)
    (hBbool : ∀ x, B x = 0 ∨ B x = 1)
    (hBprime : Polynomial.cyclotomic p ℤ ∣ CanonicalMaskPolynomial.maskPolynomial (castMask B)) :
    ∀ j : Fin p, ∀ h : Fin p → ℤ,
      ((∑ i, PhaseTilings.translate (h i • (R : ZMod (p ^ a * R)))
        (naturalDephased p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) i)) *
        naturalDephased p (p ^ a * R) B (PrimeDirectionArithmetic.rho p R) j =
          constantMask 1) ∧
      (∀ x, (∑ i, PhaseTilings.translate (h i • (R : ZMod (p ^ a * R)))
        (naturalDephased p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) i)) x = 0 ∨
        (∑ i, PhaseTilings.translate (h i • (R : ZMod (p ^ a * R)))
        (naturalDephased p (p ^ a * R) A (PrimeDirectionArithmetic.rho p R) i)) x = 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let M := p ^ a * R
  let rho := PrimeDirectionArithmetic.rho p R
  let U := naturalDephased p M A rho
  let V := naturalDephased p M B rho
  have htileI : castMask A * castMask B = constantMask (1 : ℤ) := by
    simpa only [map_mul, castMask_constant, Nat.cast_one] using congrArg castMask htile
  obtain ⟨hB, hA⟩ := PrimaryAllocation.tiling_prime_owner_uniformity p M
    (castMask A) (castMask B) htileI hp hBprime
  have hBmass : ∀ j l : Fin p, FiberMass.mass (integerFiber p M (castMask B) j) =
      FiberMass.mass (integerFiber p M (castMask B) l) := hB
  have hrect : ∀ i j k l, U i * V j + U k * V l = U i * V l + U k * V j := by
    intro i j k l
    apply castMask_injective
    simpa only [U, V, rho, map_add, map_mul, cast_naturalDephased] using
      ActualTilingSpectra.actual_rectangles p M (castMask A) (castMask B) htileI hp
        a R (NeZero.pos R) rfl hcop hBmass i j k l
  have htotal : (∑ i, ∑ j, U i * V j) = constantMask (p : ℕ) := by
    apply castMask_injective
    have hz := ActualTilingSpectra.actual_total p M (castMask A) (castMask B) htileI hp
      a R (NeZero.pos R) rfl hcop
    rw [Finset.sum_mul] at hz
    simp_rw [Finset.mul_sum] at hz
    simpa only [U, V, rho, map_sum, map_mul, cast_naturalDephased, castMask_constant] using hz
  have hperiod : ∀ i j x, (U i * V j) (x + (R : ZMod M)) = (U i * V j) x := by
    intro i j x
    have hz := ActualTilingSpectra.actual_product_period p M (castMask A) (castMask B)
      htileI hp a R (NeZero.pos R) rfl rho i j x
    simpa only [← cast_naturalDephased, ← map_mul, castMask_apply, Nat.cast_inj] using hz
  have hUnequal : ∃ i k, FiberMass.mass (castMask (U i)) ≠ FiberMass.mass (castMask (U k)) := by
    simpa only [U, cast_naturalDephased, mass_dephased] using hA
  have hBpositive : 0 < FiberMass.mass (castMask B) :=
    PrimaryAllocation.nonnegative_tiling_mass_positive (castMask B) (castMask A)
      (by simpa only [mul_comm] using htileI) (fun x => by simp)
  have hVpositive : ∀ j, 0 < FiberMass.mass (castMask (V j)) := by
    intro j
    simpa only [V, cast_naturalDephased, mass_dephased] using
      PrimaryAllocation.prime_divisor_fiber_mass_positive p M (castMask B)
        hp hBprime hBpositive j
  intro j
  have hVbool : ∀ x, V j x = 0 ∨ V j x = 1 :=
    natural_dephased_boolean p M B hBbool rho j
  have hVnonempty : ∃ x, V j x = 1 := by
    by_contra h
    push_neg at h
    have hz : ∀ x, V j x = 0 := fun x => (hVbool x).resolve_right (h x)
    have hm : FiberMass.mass (castMask (V j)) = 0 := by
      simp [FiberMass.mass, hz]
    have := hVpositive j
    omega
  exact PeriodicPhaseReduction.periodic_product_phase_tilings (p ^ a) R hcop.symm U V
    (natural_products_boolean p M A B htile rho) hrect htotal hperiod hUnequal j
    hVbool hVnonempty

end ActualPrimeReduction

#print axioms ActualPrimeReduction.actual_prime_phase_tilings
