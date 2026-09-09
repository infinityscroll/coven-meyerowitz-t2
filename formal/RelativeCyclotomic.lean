import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Tactic.Linarith

open Polynomial IntermediateField
open scoped IntermediateField

/-!
Coprime cyclotomic irreducibility over the actual field Q(theta).
No relative-irreducibility hypothesis is assumed. This does not
formalize the remaining carry or T2 induction arguments.

Checked with Lean 4.23.0 and pinned Mathlib v4.23.0. The principal
requested result is `prime_coprime_irreducible`. Its only mathematical
hypotheses are primality of p, d > 0, coprimality, and that theta is
a primitive d-th root in C. The main proof works for any positive
n coprime to d. In particular p = 2 and d = 1 require no exceptions.

Proof route: adjoin an actual primitive n-th root to K = Q(theta).
Both adjoin extensions are proved finite from integrality. The lower
bound for their rational degree comes from the two primitive roots and
the rational irreducibility of the lcm cyclotomic polynomial. The tower
law then bounds the relative minimal-polynomial degree below by phi(n).
That minimal polynomial divides the monic n-th cyclotomic polynomial,
so equality and irreducibility follow. Relative irreducibility is not
supplied as an instance or hypothesis at any stage.

This formalizes only the p-free relative cyclotomic step of the
candidate's Section 4.2. It does not prove the p-divisible binomial
case, the carry identities, Fourier inversion, or either-factor T2
induction. It makes no historical novelty or full-CM verification claim.

Replay: `lake env lean RelativeCyclotomic.lean`.
-/

noncomputable section

namespace RelativeCyclotomic

theorem coprime_irreducible {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hcop : n.Coprime d) {θ : ℂ} (hθ : IsPrimitiveRoot θ d) :
    Irreducible (Polynomial.cyclotomic n ℚ⟮θ⟯) := by
  let K : IntermediateField ℚ ℂ := ℚ⟮θ⟯
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hθint : IsIntegral ℚ θ := (hθ.isIntegral hd).tower_top
  have hζint : IsIntegral K ζ := (hζ.isIntegral hn).tower_top
  let L : IntermediateField K ℂ := K⟮ζ⟯
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hθint
  letI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hζint
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  have hdimK : Module.finrank ℚ K = d.totient := by
    change Module.finrank ℚ ℚ⟮θ⟯ = d.totient
    rw [IntermediateField.adjoin.finrank hθint,
      ← Polynomial.cyclotomic_eq_minpoly_rat hθ hd, Polynomial.natDegree_cyclotomic]
  let θK : K := ⟨θ, IntermediateField.mem_adjoin_simple_self ℚ θ⟩
  have hθK : IsPrimitiveRoot θK d :=
    hθ.of_map_of_injective (f := K.subtype) (fun _ _ h => Subtype.ext h)
  have hθL : IsPrimitiveRoot (algebraMap K L θK) d :=
    hθK.map_of_injective (f := algebraMap K L) (algebraMap K L).injective
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  have hζL : IsPrimitiveRoot ζL n :=
    hζ.of_map_of_injective (f := L.subtype) (fun _ _ h => Subtype.ext h)
  have hlower := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hζL hθL
    (Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos hn hd))
  rw [hcop.lcm_eq_mul, Nat.totient_mul hcop,
    ← Module.finrank_mul_finrank ℚ K L, hdimK] at hlower
  have hdpos : 0 < d.totient := Nat.totient_pos.mpr hd
  have hdegree : n.totient ≤ Module.finrank K L := by nlinarith
  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic n K) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  have heq : Polynomial.cyclotomic n K = minpoly K ζ := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hζint) (Polynomial.cyclotomic.monic n K) (minpoly.dvd K ζ hroot)
    rw [Polynomial.natDegree_cyclotomic]
    simpa only [L, IntermediateField.adjoin.finrank hζint] using hdegree
  change Irreducible (Polynomial.cyclotomic n K)
  rw [heq]
  exact minpoly.irreducible hζint

theorem prime_coprime_irreducible {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hcop : p.Coprime d) {θ : ℂ} (hθ : IsPrimitiveRoot θ d) :
    Irreducible (Polynomial.cyclotomic p ℚ⟮θ⟯) :=
  coprime_irreducible hp.pos hd hcop hθ

#print axioms prime_coprime_irreducible
#print axioms coprime_irreducible

end RelativeCyclotomic
