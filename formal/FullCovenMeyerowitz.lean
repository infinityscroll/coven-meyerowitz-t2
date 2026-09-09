import IntegerT2Completion
import IntegerSetNormalization

/-!
Exposed full integer-set T2 necessity, including translation of finite sets
with negative entries. The complement is defined on all integers and is not
assumed periodic. Prime families and positive levels are unrestricted.

This certifies the mathematical necessity statement. Prior T1 necessity and
T1+T2 sufficiency are existing results, not claimed as new theorems here.
Priority and external assessment are separate from kernel verification.
-/

open scoped BigOperators
open Polynomial T2Induction

noncomputable section

namespace FullCovenMeyerowitz

/-- Fully exposed original T2 necessity for every finite nonnegative
integer tile, with no mask or target abbreviation in the statement. -/
theorem integer_tile_cyclotomic_product
    (E : Finset ℕ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ a ∈ E, c (t - (a : ℤ))) = 1)
    (S : Finset ℕ) (e : ℕ → ℕ) (hS : S.Nonempty)
    (hprime : ∀ q ∈ S, Nat.Prime q) (hpositive : ∀ q ∈ S, 0 < e q)
    (hprimary : ∀ q ∈ S, cyclotomic (q ^ e q) ℤ ∣ ∑ a ∈ E, (X : ℤ[X]) ^ a) :
    cyclotomic (∏ q ∈ S, q ^ e q) ℤ ∣ ∑ a ∈ E, (X : ℤ[X]) ^ a :=
  IntegerT2Completion.integer_tiling_T2 E c htile S e hS hprime hpositive hprimary

/-- Arbitrary finite integer sets are translated by their minimum, so
negative exponents are removed without losing any tiling information. -/
theorem finite_integer_tiling_T2
    (F : Finset ℤ) (hF : F.Nonempty) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    PolynomialT2 (∑ f ∈ F, (X : ℤ[X]) ^ (f - F.min' hF).toNat) := by
  have hmin : ∀ f ∈ F, F.min' hF ≤ f := fun f hf => Finset.min'_le F f hf
  have hn := IntegerT2Completion.integer_tiling_T2
    (IntegerSetNormalization.normalizedSet F (F.min' hF))
    (IntegerSetNormalization.shiftedComplement c (F.min' hF))
    (IntegerSetNormalization.normalized_tiling_equation F c (F.min' hF) hmin htile)
  simpa only [IntegerSetNormalization.normalizedSet,
    Finset.sum_image (IntegerSetNormalization.normalized_index_injective_on F (F.min' hF) hmin)] using hn

/-- Nonemptiness is a derived conclusion of the actual integer tiling;
no auxiliary condition is needed for the arbitrary-integer-set result. -/
theorem arbitrary_integer_tile_T2 (F : Finset ℤ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    ∃ hF : F.Nonempty,
      PolynomialT2 (∑ f ∈ F, (X : ℤ[X]) ^ (f - F.min' hF).toNat) := by
  have hF := IntegerSetNormalization.tiling_set_nonempty F c htile
  exact ⟨hF, finite_integer_tiling_T2 F hF c htile⟩

end FullCovenMeyerowitz

#print axioms FullCovenMeyerowitz.integer_tile_cyclotomic_product
#print axioms FullCovenMeyerowitz.finite_integer_tiling_T2
#print axioms FullCovenMeyerowitz.arbitrary_integer_tile_T2
