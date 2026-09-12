import CMCharacterizationDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
T1 necessity for finite integer tiles, with the complete primary divisor set
defined independently of the derived period. This supplies a formalization of
the classical necessity theorem, not a new originality claim.
-/

open scoped BigOperators
open Polynomial CanonicalMaskPolynomial PrimaryAllocation

noncomputable section

namespace CMCharacterization

def polynomialOwnedLevels (P : ℤ[X]) (q a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter (fun k => cyclotomic (q ^ (k + 1)) ℤ ∣ P)

def polynomialMissingLevels (P : ℤ[X]) (q a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter (fun k => ¬ cyclotomic (q ^ (k + 1)) ℤ ∣ P)

def missingLevels (P : ℤ[X]) (N : ℕ) : Finset ((_q : ℕ) × ℕ) :=
  N.primeFactors.sigma (fun q => polynomialMissingLevels P q (N.factorization q))

@[simp] theorem mem_polynomialOwnedLevels (P : ℤ[X]) (q a k : ℕ) :
    k ∈ polynomialOwnedLevels P q a ↔ k < a ∧ cyclotomic (q ^ (k + 1)) ℤ ∣ P := by
  classical
  simp [polynomialOwnedLevels]

@[simp] theorem mem_polynomialMissingLevels (P : ℤ[X]) (q a k : ℕ) :
    k ∈ polynomialMissingLevels P q a ↔ k < a ∧ ¬ cyclotomic (q ^ (k + 1)) ℤ ∣ P := by
  classical
  simp [polynomialMissingLevels]

@[simp] theorem mem_missingLevels_iff (P : ℤ[X]) (N : ℕ) (v : (_q : ℕ) × ℕ) :
    v ∈ missingLevels P N ↔ v.1 ∈ N.primeFactors ∧
      v.2 < N.factorization v.1 ∧ ¬ cyclotomic (v.1 ^ (v.2 + 1)) ℤ ∣ P := by
  simp [missingLevels]

def primaryPeriod (P : ℤ[X]) : ℕ := ∏ s ∈ primaryDivisors P, s

theorem primaryPeriod_pos (P : ℤ[X]) : 0 < primaryPeriod P := by
  classical
  apply Finset.prod_pos
  intro s hs
  have hs' := (Finset.mem_filter.mp hs).2.1
  obtain ⟨q, k, hq, _, rfl⟩ := hs'
  exact pow_pos hq.pos _

theorem primary_dvd_primaryPeriod (P : ℤ[X]) {s : ℕ} (hs : s ∈ primaryDivisors P) :
    s ∣ primaryPeriod P := Finset.dvd_prod_of_mem (fun s => s) hs

theorem primary_product_of_period (P : ℤ[X]) (hP : P ≠ 0) (N : ℕ) (hN : N ≠ 0)
    (hperiod : ∀ s ∈ primaryDivisors P, s ∣ N) :
    (∏ s ∈ primaryDivisors P, (cyclotomic s ℤ).eval 1) =
      ∏ q ∈ N.primeFactors, (q : ℤ) ^ (polynomialOwnedLevels P q (N.factorization q)).card := by
  classical
  let pairs := N.primeFactors.sigma (fun q => polynomialOwnedLevels P q (N.factorization q))
  have hpairs : (∏ v ∈ pairs, (cyclotomic (v.1 ^ (v.2 + 1)) ℤ).eval 1) =
      ∏ s ∈ primaryDivisors P, (cyclotomic s ℤ).eval 1 := by
    apply Finset.prod_bij (fun v _ => v.1 ^ (v.2 + 1))
    · intro v hv
      have hv' := Finset.mem_sigma.mp hv
      have hq := Nat.prime_of_mem_primeFactors hv'.1
      exact (mem_primaryDivisors_iff _ hP _).mpr
        ⟨⟨v.1, v.2 + 1, hq, by omega, rfl⟩,
          (mem_polynomialOwnedLevels P v.1 (N.factorization v.1) v.2).mp hv'.2 |>.2⟩
    · intro v hv w hw heq
      have hv' := Finset.mem_sigma.mp hv
      have hw' := Finset.mem_sigma.mp hw
      have h := (Nat.prime_of_mem_primeFactors hv'.1).pow_inj
        (Nat.prime_of_mem_primeFactors hw'.1) heq
      cases v
      cases w
      simp only [Sigma.mk.inj_iff]
      exact ⟨h.1, heq_of_eq h.2⟩
    · intro s hs
      have hs' := hs
      obtain ⟨⟨q, k, hq, hk, rfl⟩, hdiv⟩ := (mem_primaryDivisors_iff _ hP s).mp hs
      cases k with
      | zero => omega
      | succ k =>
        have hd := hperiod _ hs'
        have hqN : q ∣ N := (dvd_pow_self q (by omega : k + 1 ≠ 0)).trans hd
        have hlevel : k < N.factorization q := by
          have := (hq.pow_dvd_iff_le_factorization hN).mp hd
          omega
        refine ⟨⟨q, k⟩, ?_, rfl⟩
        exact Finset.mem_sigma.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hq, hqN, hN⟩,
            (mem_polynomialOwnedLevels P q (N.factorization q) k).mpr ⟨hlevel, hdiv⟩⟩
    · intro v hv
      rfl
  rw [← hpairs]
  change (∏ v ∈ N.primeFactors.sigma (fun q => polynomialOwnedLevels P q (N.factorization q)),
    (cyclotomic (v.1 ^ (v.2 + 1)) ℤ).eval 1) = _
  rw [Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro q hq
  letI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  simp only [Polynomial.eval_one_cyclotomic_prime_pow, Finset.prod_const]

theorem owned_missing_card (P : ℤ[X]) (q a : ℕ) :
    (polynomialOwnedLevels P q a).card + (polynomialMissingLevels P q a).card = a := by
  classical
  exact (Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.range a) (fun k => cyclotomic (q ^ (k + 1)) ℤ ∣ P)).trans
      (Finset.card_range a)

/-- The mass of the standard missing-level complement, before its root and
Boolean properties are proved. This uses T1 alone, not T2 necessity. -/
theorem T1_missing_level_mass (P : ℤ[X]) (hP : P ≠ 0) (hT1 : T1 P)
    (N : ℕ) (hN : N ≠ 0) (hperiod : ∀ s ∈ primaryDivisors P, s ∣ N) :
    P.eval 1 * (∏ v ∈ missingLevels P N, (v.1 : ℤ)) = (N : ℤ) := by
  change P.eval 1 = _ at hT1
  rw [hT1, primary_product_of_period P hP N hN hperiod]
  unfold missingLevels
  rw [Finset.prod_sigma]
  simp only [Finset.prod_const]
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ q ∈ N.primeFactors, (q : ℤ) ^ (polynomialOwnedLevels P q (N.factorization q)).card *
        (q : ℤ) ^ (polynomialMissingLevels P q (N.factorization q)).card) =
      ∏ q ∈ N.primeFactors, (q : ℤ) ^ N.factorization q := by
        apply Finset.prod_congr rfl
        intro q hq
        rw [← pow_add, owned_missing_card]
    _ = ((∏ q ∈ N.primeFactors, q ^ N.factorization q) : ℕ) := by
      simp only [Nat.cast_prod, Nat.cast_pow]
    _ = (N : ℤ) := by
      exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.factorization_prod_pow_eq_self hN)

variable {N : ℕ} [NeZero N]

theorem cyclic_primary_product (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) :
    (∏ s ∈ primaryDivisors (maskPolynomial A), (cyclotomic s ℤ).eval 1) =
      ∏ q ∈ N.primeFactors, (q : ℤ) ^
        (ownedLevels A q (N.factorization q)).card := by
  classical
  have hmass := (tiling_mass_ne_zero A B htile).1
  have hP : maskPolynomial A ≠ 0 := by
    intro h
    apply hmass
    rw [← eval_one_eq_mass, h, Polynomial.eval_zero]
  let pairs := N.primeFactors.sigma (fun q => ownedLevels A q (N.factorization q))
  have hpairs : (∏ v ∈ pairs, (cyclotomic (v.1 ^ (v.2 + 1)) ℤ).eval 1) =
      ∏ s ∈ primaryDivisors (maskPolynomial A), (cyclotomic s ℤ).eval 1 := by
    apply Finset.prod_bij (fun v _ => v.1 ^ (v.2 + 1))
    · intro v hv
      have hv' := Finset.mem_sigma.mp hv
      have hq := Nat.prime_of_mem_primeFactors hv'.1
      exact (mem_primaryDivisors_iff _ hP _).mpr
        ⟨⟨v.1, v.2 + 1, hq, by omega, rfl⟩,
          (mem_ownedLevels A v.1 (N.factorization v.1) v.2).mp hv'.2 |>.2⟩
    · intro v hv w hw heq
      have hv' := Finset.mem_sigma.mp hv
      have hw' := Finset.mem_sigma.mp hw
      have h := (Nat.prime_of_mem_primeFactors hv'.1).pow_inj
        (Nat.prime_of_mem_primeFactors hw'.1) heq
      cases v
      cases w
      simp only [Sigma.mk.inj_iff]
      exact ⟨h.1, heq_of_eq h.2⟩
    · intro s hs
      obtain ⟨⟨q, k, hq, hk, rfl⟩, hdiv⟩ := (mem_primaryDivisors_iff _ hP s).mp hs
      cases k with
      | zero => omega
      | succ k =>
        have hd := primary_divisor_within_period A B htile hq hdiv
        have hqN : q ∣ N := (dvd_pow_self q (by omega : k + 1 ≠ 0)).trans hd
        have hlevel : k < N.factorization q := by
          have := (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mp hd
          omega
        refine ⟨⟨q, k⟩, ?_, rfl⟩
        exact Finset.mem_sigma.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩,
            (mem_ownedLevels A q (N.factorization q) k).mpr ⟨hlevel, hdiv⟩⟩
    · intro v hv
      rfl
  rw [← hpairs]
  change (∏ v ∈ N.primeFactors.sigma (fun q => ownedLevels A q (N.factorization q)),
    (cyclotomic (v.1 ^ (v.2 + 1)) ℤ).eval 1) = _
  rw [Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro q hq
  letI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  simp only [Polynomial.eval_one_cyclotomic_prime_pow, Finset.prod_const]

theorem prime_factorization_product_over_multiple {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ∣ n) :
    (∏ q ∈ n.primeFactors, q ^ (m.factorization q)) = m := by
  calc
    (∏ q ∈ n.primeFactors, q ^ (m.factorization q)) =
        ∏ q ∈ m.primeFactors, q ^ (m.factorization q) := by
      symm
      apply Finset.prod_subset (Nat.primeFactors_mono hmn hn)
      intro q hqn hqm
      have hz : m.factorization q = 0 := by
        exact Finsupp.notMem_support_iff.mp hqm
      rw [hz, pow_zero]
    _ = m := Nat.factorization_prod_pow_eq_self hm

theorem cyclic_tiling_T1 (A B : AddMonoidAlgebra ℤ (ZMod N))
    (htile : A * B = StripeCollapse.constantMask 1) (hA : ∀ x, 0 ≤ A x) :
    T1 (maskPolynomial A) := by
  have hm := (tiling_mass_ne_zero A B htile).1
  have hmpos := nonnegative_tiling_mass_positive A B htile hA
  have hmN : (FiberMass.mass A).natAbs ∣ N :=
    Dvd.intro (FiberMass.mass B).natAbs (tiling_mass_natAbs_product A B htile)
  unfold T1
  rw [cyclic_primary_product A B htile]
  have hp : (∏ q ∈ N.primeFactors,
      (q : ℤ) ^ (ownedLevels A q (N.factorization q)).card) =
      ((FiberMass.mass A).natAbs : ℤ) := by
    calc
      _ = ∏ q ∈ N.primeFactors, (q : ℤ) ^ (FiberMass.mass A).natAbs.factorization q := by
        apply Finset.prod_congr rfl
        intro q hq
        rw [(exact_primary_allocation A B htile (Nat.prime_of_mem_primeFactors hq)).2.1]
      _ = ((∏ q ∈ N.primeFactors, q ^ (FiberMass.mass A).natAbs.factorization q) : ℕ) := by
        simp only [Nat.cast_prod, Nat.cast_pow]
      _ = ((FiberMass.mass A).natAbs : ℤ) := by
        rw [prime_factorization_product_over_multiple
          (fun h => hm (Int.natAbs_eq_zero.mp h)) (NeZero.ne N) hmN]
  rw [hp, eval_one_eq_mass, Int.natCast_natAbs, abs_of_pos hmpos]

theorem normalized_integer_tiling_T1 (E : Finset ℕ) (c : ℤ → ℕ)
    (hzero : 0 ∈ E)
    (htile : ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1) : T1 (mask E) := by
  have hE : E.Nonempty := ⟨0, hzero⟩
  obtain ⟨N, hN, _, _, A, B, hA, _, hAB, hpoly, _, _⟩ :=
    IntegerCyclicReduction.normalized_integer_tiling_to_cyclic E c (E.max' hE)
      hzero (Finset.max'_mem E hE) (fun e he => Finset.le_max' E e he) htile
  letI : NeZero N := ⟨hN.ne'⟩
  change T1 (∑ e ∈ E, (X : ℤ[X]) ^ e)
  rw [← hpoly]
  exact cyclic_tiling_T1 A B hAB (fun x => by rcases hA x with h | h <;> omega)

theorem finite_integer_tiling_T1 (F : Finset ℤ) (hF : F.Nonempty) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) : T1 (normalizedMask F hF) := by
  have hmin : ∀ f ∈ F, F.min' hF ≤ f := fun f hf => Finset.min'_le F f hf
  exact normalized_integer_tiling_T1
    (IntegerSetNormalization.normalizedSet F (F.min' hF))
    (IntegerSetNormalization.shiftedComplement c (F.min' hF))
    (IntegerSetNormalization.zero_mem_normalizedSet F (F.min' hF) (Finset.min'_mem F hF))
    (IntegerSetNormalization.normalized_tiling_equation F c (F.min' hF) hmin htile)

theorem arbitrary_integer_tile_T1 (F : Finset ℤ) (h : TilesZ F) :
    ∃ hF : F.Nonempty, T1 (normalizedMask F hF) := by
  obtain ⟨c, hc⟩ := h
  have hF := IntegerSetNormalization.tiling_set_nonempty F c hc
  exact ⟨hF, finite_integer_tiling_T1 F hF c hc⟩

theorem normalizedMask_eq_literal (F : Finset ℤ) (hF : F.Nonempty) :
    normalizedMask F hF = ∑ f ∈ F, (X : ℤ[X]) ^ (f - F.min' hF).toNat := by
  unfold normalizedMask mask IntegerSetNormalization.normalizedSet
  exact Finset.sum_image (IntegerSetNormalization.normalized_index_injective_on
    F (F.min' hF) (fun f hf => Finset.min'_le F f hf))

theorem finite_integer_tiling_conditions (F : Finset ℤ) (hF : F.Nonempty)
    (c : ℤ → ℕ) (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    T1 (normalizedMask F hF) ∧ T2 (normalizedMask F hF) := by
  refine ⟨finite_integer_tiling_T1 F hF c htile, ?_⟩
  rw [normalizedMask_eq_literal]
  exact FullCovenMeyerowitz.finite_integer_tiling_T2 F hF c htile

/-- Both classical necessary conditions for every finite integer tile.
Nonemptiness is derived; no normalization or periodicity is assumed. -/
theorem arbitrary_integer_tile_conditions (F : Finset ℤ) (h : TilesZ F) :
    ∃ hF : F.Nonempty, T1 (normalizedMask F hF) ∧ T2 (normalizedMask F hF) := by
  obtain ⟨c, hc⟩ := h
  have hF := IntegerSetNormalization.tiling_set_nonempty F c hc
  exact ⟨hF, finite_integer_tiling_conditions F hF c hc⟩

/-- A complement in the natural-valued tiling equation is necessarily
Boolean. The definition does not assume that the complement is unique. -/
theorem tilesZ_complement_boolean (F : Finset ℤ) (c : ℤ → ℕ)
    (htile : ∀ t : ℤ, (∑ f ∈ F, c (t - f)) = 1) :
    ∀ t : ℤ, c t = 0 ∨ c t = 1 := by
  have hF := IntegerSetNormalization.tiling_set_nonempty F c htile
  obtain ⟨f, hf⟩ := hF
  intro t
  have hle : c t ≤ 1 := by
    have hs := Finset.single_le_sum (fun a _ => Nat.zero_le (c (t + f - a))) hf
    rw [htile (t + f)] at hs
    simpa only [add_sub_cancel_right] using hs
  omega

open Classical in
theorem tilesZ_iff_boolean_complement (F : Finset ℤ) :
    TilesZ F ↔ ∃ C : Set ℤ, ∀ t : ℤ,
      (∑ f ∈ F, if t - f ∈ C then (1 : ℕ) else 0) = 1 := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨{t | c t = 1}, ?_⟩
    intro t
    convert hc t using 1
    apply Finset.sum_congr rfl
    intro f hf
    rcases tilesZ_complement_boolean F c hc (t - f) with h | h <;> simp [h]
  · rintro ⟨C, hC⟩
    exact ⟨fun t => if t ∈ C then 1 else 0, hC⟩

end CMCharacterization

/-- info: 'CMCharacterization.mem_primaryDivisors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.mem_primaryDivisors_iff

/-- info: 'CMCharacterization.cyclic_tiling_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.cyclic_tiling_T1

/-- info: 'CMCharacterization.finite_integer_tiling_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.finite_integer_tiling_T1

/-- info: 'CMCharacterization.arbitrary_integer_tile_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.arbitrary_integer_tile_T1

/-- info: 'CMCharacterization.arbitrary_integer_tile_conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.arbitrary_integer_tile_conditions

/-- info: 'CMCharacterization.tilesZ_iff_boolean_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.tilesZ_iff_boolean_complement

/-- info: 'CMCharacterization.T1_missing_level_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.T1_missing_level_mass
