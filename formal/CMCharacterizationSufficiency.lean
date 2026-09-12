import IntegerCyclicReduction
import IntegerSetNormalization
import FourierPeriod
import CMCharacterizationT1

/-!
The classical Coven--Meyerowitz sufficiency direction and full characterization.
The complement is explicitly constructed as the product of all missing
primary digit factors. T1 gives its mass, T2 gives complete root coverage,
and Fourier inversion proves exact cyclic convolution. Pullback to the
integers and inverse normalization handle every finite subset of Z.

The sufficiency proof does not use T2 necessity. Only the forward direction
of the final equivalence invokes the previously formalized necessity theorem.
These are formalizations of the classical implications, not new priority
claims for the known T1 necessity or T1+T2 sufficiency results.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace CMCharacterization

variable {N : ℕ} [NeZero N]

/-- All root evaluations determine an integral cyclic mask. -/
theorem cyclic_mask_eq_of_evaluations
    (A B : AddMonoidAlgebra ℤ (ZMod N))
    (h : ∀ z : ℂ, z ^ N = 1 →
      CyclicEvaluation.evaluate A z = CyclicEvaluation.evaluate B z) : A = B := by
  have hdft : ZMod.dft (fun x => (A x : ℂ)) =
      ZMod.dft (fun x => (B x : ℂ)) := by
    funext k
    rw [FourierPeriod.dft_eq_rootEval, FourierPeriod.dft_eq_rootEval]
    exact h _ (FourierPeriod.stdAddChar_is_root (-k))
  have hab : (fun x => (A x : ℂ)) = (fun x => (B x : ℂ)) :=
    ZMod.dft.injective hdft
  ext x
  exact Int.cast_injective (congrFun hab x)

theorem cyclic_evaluate_one (A : AddMonoidAlgebra ℤ (ZMod N)) :
    CyclicEvaluation.evaluate A 1 = (FiberMass.mass A : ℂ) := by
  simp [CyclicEvaluation.evaluate, FiberMass.mass]

/-- Mass and coverage of every nontrivial Nth root certify exact convolution,
without assuming positivity or Boolean coefficients. -/
theorem cyclic_tiling_of_mass_and_root_coverage
    (A B : AddMonoidAlgebra ℤ (ZMod N))
    (hmass : FiberMass.mass A * FiberMass.mass B = (N : ℤ))
    (hcover : ∀ z : ℂ, z ^ N = 1 → z ≠ 1 →
      CyclicEvaluation.evaluate A z = 0 ∨ CyclicEvaluation.evaluate B z = 0) :
    A * B = StripeCollapse.constantMask 1 := by
  apply cyclic_mask_eq_of_evaluations
  intro z hz
  by_cases hzone : z = 1
  · subst z
    rw [cyclic_evaluate_one, FiberMass.mass_mul, hmass, cyclic_evaluate_one]
    simp [FiberMass.mass, StripeCollapse.constantMask_apply, ZMod.card]
  · rw [CyclicEvaluation.evaluate_mul A B hz,
      CyclicEvaluation.evaluate_all_ones hz hzone]
    exact mul_eq_zero.mpr (hcover z hz hzone)

/-- Pull a nonnegative cyclic complement back along Z -> Z/NZ. -/
def integerComplementOfMask (B : AddMonoidAlgebra ℤ (ZMod N)) : ℤ → ℕ :=
  fun t => (B (t : ZMod N)).toNat

/-- Exact cyclic convolution gives a genuine tiling of all integers.
There is no bounded-support, collision-free, or Boolean premise. -/
theorem integer_tiling_of_cyclic_convolution
    (E : Finset ℕ) (B : AddMonoidAlgebra ℤ (ZMod N))
    (hB : ∀ x, 0 ≤ B x)
    (htile : IntegerCyclicReduction.tileMask E * B = StripeCollapse.constantMask 1) :
    ∀ t : ℤ, (∑ e ∈ E, integerComplementOfMask B (t - (e : ℤ))) = 1 := by
  classical
  intro t
  have ht := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod N) => f (t : ZMod N)) htile
  change (((∑ e ∈ E, AddMonoidAlgebra.single (e : ZMod N) (1 : ℤ)) * B)
    (t : ZMod N)) = 1 at ht
  rw [Finset.sum_mul] at ht
  simp only [StripeCollapse.sum_apply, AddMonoidAlgebra.single_mul_apply, one_mul] at ht
  have heval : ∀ e : ℕ,
      (integerComplementOfMask B (t - (e : ℤ)) : ℤ) = B (-(e : ZMod N) + (t : ZMod N)) := by
    intro e
    rw [integerComplementOfMask, Int.toNat_of_nonneg (hB _)]
    congr 1
    simp [sub_eq_add_neg, add_comm]
  have hcast : ((∑ e ∈ E, integerComplementOfMask B (t - (e : ℤ))) : ℤ) = 1 := by
    simpa only [Nat.cast_sum, heval] using ht
  exact_mod_cast hcast

/-- Translation restores an arbitrary finite set of integers, including
negative entries, from a tiling of its normalized natural exponents. -/
theorem integer_tiling_of_normalized_tiling
    (F : Finset ℤ) (m : ℤ) (hmin : ∀ f ∈ F, m ≤ f)
    (c : ℤ → ℕ)
    (htile : ∀ t : ℤ,
      (∑ e ∈ IntegerSetNormalization.normalizedSet F m, c (t - (e : ℤ))) = 1) :
    ∀ t : ℤ, (∑ f ∈ F, c (t - f + m)) = 1 := by
  classical
  intro t
  have ht := htile t
  unfold IntegerSetNormalization.normalizedSet at ht
  rw [Finset.sum_image (IntegerSetNormalization.normalized_index_injective_on F m hmin)] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  have he := IntegerSetNormalization.translate_normalized_index m f (hmin f hf)
  omega

/-- An ordinary digit factor, evaluated in the cyclic group algebra. -/
def digitMask (q step : ℕ) : AddMonoidAlgebra ℤ (ZMod N) :=
  ∑ i ∈ Finset.range q, AddMonoidAlgebra.single ((step * i : ℕ) : ZMod N) 1

theorem digitMask_nonnegative (q step : ℕ) (x : ZMod N) :
    0 ≤ digitMask q step x := by
  classical
  simp only [digitMask, StripeCollapse.sum_apply, AddMonoidAlgebra.single_apply]
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> omega

theorem digitMask_mass (q step : ℕ) : FiberMass.mass (digitMask (N := N) q step) = q := by
  classical
  rw [← FiberMass.massHom_apply]
  simp [digitMask, FiberMass.massHom_apply, FiberMass.mass, Finsupp.single_apply]

theorem cyclic_evaluate_single_nat (n : ℕ) {z : ℂ} (hz : z ^ N = 1) :
    CyclicEvaluation.evaluate
      (AddMonoidAlgebra.single (n : ZMod N) 1 : AddMonoidAlgebra ℤ (ZMod N)) z = z ^ n := by
  simp only [CyclicEvaluation.evaluate, AddMonoidAlgebra.single_apply,
    Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ZMod.val_natCast]
  exact (pow_eq_pow_mod n hz).symm

theorem digitMask_evaluate (q step : ℕ) {z : ℂ} (hz : z ^ N = 1) :
    CyclicEvaluation.evaluate (digitMask (N := N) q step) z = ∑ i ∈ Finset.range q, (z ^ step) ^ i := by
  rw [← CyclicEvaluation.evaluationHom_apply hz]
  simp only [digitMask, map_sum, CyclicEvaluation.evaluationHom_apply,
    cyclic_evaluate_single_nat _ hz, pow_mul]

theorem digitMask_evaluate_zero (q step : ℕ) {z : ℂ} (hz : z ^ N = 1)
    (hpow : (z ^ step) ^ q = 1) (hne : z ^ step ≠ 1) :
    CyclicEvaluation.evaluate (digitMask (N := N) q step) z = 0 := by
  rw [digitMask_evaluate q step hz]
  apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr hne.symm)
  rw [mul_neg_geom_sum, hpow, sub_self]

omit [NeZero N] in
theorem cyclic_mul_nonnegative (A B : AddMonoidAlgebra ℤ (ZMod N))
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (x : ZMod N) :
    0 ≤ (A * B) x := by
  rw [AddMonoidAlgebra.mul_apply_left, Finsupp.sum]
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (hA y) (hB _))

omit [NeZero N] in
theorem cyclic_prod_nonnegative {ι : Type*} (S : Finset ι)
    (D : ι → AddMonoidAlgebra ℤ (ZMod N))
    (hD : ∀ i ∈ S, ∀ x, 0 ≤ D i x) : ∀ x, 0 ≤ (∏ i ∈ S, D i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro x
    simp only [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
    split_ifs <;> omega
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact cyclic_mul_nonnegative (D i) _ (hD i (Finset.mem_insert_self i S))
      (ih (fun j hj => hD j (Finset.mem_insert_of_mem hj)))

/-- A finite product of digit factors; coefficient collisions are permitted
at construction time and removed automatically by exact convolution. -/
def digitComplement {ι : Type*} (S : Finset ι) (q step : ι → ℕ) :
    AddMonoidAlgebra ℤ (ZMod N) := ∏ i ∈ S, digitMask (q i) (step i)

theorem digitComplement_nonnegative {ι : Type*} (S : Finset ι) (q step : ι → ℕ) :
    ∀ x : ZMod N, 0 ≤ digitComplement S q step x :=
  cyclic_prod_nonnegative S _ (fun i _ => digitMask_nonnegative (q i) (step i))

theorem digitComplement_mass {ι : Type*} (S : Finset ι) (q step : ι → ℕ) :
    FiberMass.mass (digitComplement (N := N) S q step) = ∏ i ∈ S, (q i : ℤ) := by
  rw [← FiberMass.massHom_apply]
  simp only [digitComplement, map_prod, FiberMass.massHom_apply, digitMask_mass]

theorem digitComplement_evaluate_zero {ι : Type*} (S : Finset ι) (q step : ι → ℕ)
    {z : ℂ} (hz : z ^ N = 1)
    (hzero : ∃ i ∈ S, (z ^ step i) ^ q i = 1 ∧ z ^ step i ≠ 1) :
    CyclicEvaluation.evaluate (digitComplement (N := N) S q step) z = 0 := by
  classical
  obtain ⟨i, hi, hp, hn⟩ := hzero
  rw [← CyclicEvaluation.evaluationHom_apply hz]
  simp only [digitComplement, map_prod, CyclicEvaluation.evaluationHom_apply]
  exact Finset.prod_eq_zero hi (digitMask_evaluate_zero (q i) (step i) hz hp hn)

/-- The q-primary digit at the zero-based level k, with all other primary
components of the ambient period killed by the step. -/
def primaryDigitStep (N q k : ℕ) : ℕ := q ^ k * (N / q ^ N.factorization q)

theorem root_primaryDigitStep {d q k : ℕ} (hd : 0 < d) (hq : q.Prime)
    (hdN : d ∣ N) (hk : d.factorization q = k + 1)
    {z : ℂ} (hz : IsPrimitiveRoot z d) :
    (z ^ primaryDigitStep N q k) ^ q = 1 ∧ z ^ primaryDigitStep N q k ≠ 1 := by
  have hstep : 0 < primaryDigitStep N q k :=
    Nat.mul_pos (pow_pos hq.pos _) (Nat.ordCompl_pos q (NeZero.ne N))
  constructor
  · rw [← pow_mul]
    apply (hz.pow_eq_one_iff_dvd _).mpr
    have hdiv := Nat.mul_dvd_mul_left (q ^ (k + 1))
      (Nat.ordCompl_dvd_ordCompl_of_dvd hdN q)
    have hdid : q ^ (k + 1) * (d / q ^ d.factorization q) = d := by
      rw [← hk]
      exact Nat.ordProj_mul_ordCompl_eq_self d q
    rw [hdid] at hdiv
    convert hdiv using 1
    simp only [primaryDigitStep, pow_succ]
    ring
  · intro heq
    have hdiv := (hz.pow_eq_one_iff_dvd _).mp heq
    have hf := (Nat.factorization_le_iff_dvd hd.ne' hstep.ne').mpr hdiv q
    rw [primaryDigitStep, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero)
      (Nat.ordCompl_pos q (NeZero.ne N)).ne', hq.factorization_pow,
      Nat.factorization_ordCompl] at hf
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.erase_same, add_zero, hk] at hf
    omega

theorem tileMask_evaluate_eq_aeval (E : Finset ℕ) {z : ℂ} (hz : z ^ N = 1) :
    CyclicEvaluation.evaluate (IntegerCyclicReduction.tileMask (N := N) E) z =
      Polynomial.aeval z (mask E) := by
  rw [← CyclicEvaluation.evaluationHom_apply hz]
  simp only [IntegerCyclicReduction.tileMask, map_sum, CyclicEvaluation.evaluationHom_apply,
    cyclic_evaluate_single_nat _ hz, mask, map_pow, Polynomial.aeval_X]

theorem tileMask_mass (E : Finset ℕ) :
    FiberMass.mass (IntegerCyclicReduction.tileMask (N := N) E) = (mask E).eval 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [← cyclic_evaluate_one, tileMask_evaluate_eq_aeval E (one_pow N)]
  rw [mask_eval_one]
  simp [mask, map_sum]

/-- The classical complement is the product of the missing primary digits. -/
def standardComplement (P : ℤ[X]) : AddMonoidAlgebra ℤ (ZMod N) :=
  digitComplement (missingLevels P N) (fun v => v.1)
    (fun v => primaryDigitStep N v.1 v.2)

theorem standardComplement_nonnegative (P : ℤ[X]) :
    ∀ x : ZMod N, 0 ≤ standardComplement P x :=
  digitComplement_nonnegative _ _ _

theorem standardComplement_mass (P : ℤ[X]) :
    FiberMass.mass (standardComplement (N := N) P) =
      ∏ v ∈ missingLevels P N, (v.1 : ℤ) := digitComplement_mass _ _ _

/-- T2 alone gives complete root coverage by the tile polynomial and the
constructed complement. All prime factors of the actual root order are used. -/
theorem standardComplement_root_coverage (P : ℤ[X]) (hT2 : T2 P)
    {z : ℂ} (hz : z ^ N = 1) (hne : z ≠ 1) :
    Polynomial.aeval z P = 0 ∨
      CyclicEvaluation.evaluate (standardComplement (N := N) P) z = 0 := by
  classical
  obtain ⟨d, hd, hprim, hdN, hneiff⟩ :=
    PrimeDirectionArithmetic.exists_primitive_order (Nat.pos_of_ne_zero (NeZero.ne N)) hz
  have hprime : ∀ q ∈ d.primeFactors, q.Prime :=
    fun q hq => Nat.prime_of_mem_primeFactors hq
  have hpositive : ∀ q ∈ d.primeFactors, 0 < d.factorization q :=
    fun q hq => (hprime q hq).factorization_pos_of_dvd hd.ne'
      (Nat.dvd_of_mem_primeFactors hq)
  by_cases hall : ∀ q ∈ d.primeFactors, cyclotomic (q ^ d.factorization q) ℤ ∣ P
  · left
    have hdiv := hT2 d.primeFactors d.factorization
      (Nat.nonempty_primeFactors.mpr (hneiff.mp hne)) hprime hpositive hall
    have hid : T2Induction.selectedOrder d.primeFactors d.factorization = d :=
      Nat.factorization_prod_pow_eq_self hd.ne'
    rw [hid] at hdiv
    exact (T2Induction.cyclotomic_dvd_iff_aeval_zero P hd hprim).mp hdiv
  · right
    push_neg at hall
    obtain ⟨q, hqd, hmissing⟩ := hall
    let k := d.factorization q - 1
    have hk : d.factorization q = k + 1 := by have := hpositive q hqd; omega
    have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hprime q hqd, (Nat.dvd_of_mem_primeFactors hqd).trans hdN, NeZero.ne N⟩
    have hkN : k < N.factorization q := by
      have := (Nat.factorization_le_iff_dvd hd.ne' (NeZero.ne N)).mpr hdN q
      omega
    apply digitComplement_evaluate_zero (missingLevels P N) (fun v => v.1)
      (fun v => primaryDigitStep N v.1 v.2) hz
    refine ⟨⟨q, k⟩, ?_, root_primaryDigitStep hd (hprime q hqd) hdN hk hprim⟩
    exact (mem_missingLevels_iff P N ⟨q, k⟩).mpr
      ⟨hqN, hkN, by simpa only [hk] using hmissing⟩

/-- Classical T1+T2 sufficiency for every nonempty finite set of natural
exponents. The actual integer complement is constructed explicitly. -/
theorem natural_tiling_of_T1_T2 (E : Finset ℕ) (hE : E.Nonempty)
    (hT1 : T1 (mask E)) (hT2 : T2 (mask E)) :
    ∃ c : ℤ → ℕ, ∀ t : ℤ, (∑ e ∈ E, c (t - (e : ℤ))) = 1 := by
  let N := primaryPeriod (mask E)
  letI : NeZero N := ⟨(primaryPeriod_pos (mask E)).ne'⟩
  let B : AddMonoidAlgebra ℤ (ZMod N) := standardComplement (mask E)
  refine ⟨integerComplementOfMask B,
    integer_tiling_of_cyclic_convolution E B (standardComplement_nonnegative _) ?_⟩
  apply cyclic_tiling_of_mass_and_root_coverage
  · rw [tileMask_mass]
    change (mask E).eval 1 * FiberMass.mass (standardComplement (N := N) (mask E)) = _
    rw [standardComplement_mass]
    exact T1_missing_level_mass (mask E) (mask_ne_zero E hE) hT1 N (NeZero.ne N)
      (fun s hs => primary_dvd_primaryPeriod (mask E) hs)
  · intro z hz hne
    rw [tileMask_evaluate_eq_aeval E hz]
    exact standardComplement_root_coverage (mask E) hT2 hz hne

/-- Classical sufficiency for arbitrary finite subsets of Z. Normalization
does not restrict the set or the number of prime factors. -/
theorem finite_integer_tiling_of_T1_T2 (F : Finset ℤ) (hF : F.Nonempty)
    (hT1 : T1 (normalizedMask F hF)) (hT2 : T2 (normalizedMask F hF)) :
    TilesZ F := by
  let m := F.min' hF
  let E := IntegerSetNormalization.normalizedSet F m
  have hE : E.Nonempty :=
    ⟨0, IntegerSetNormalization.zero_mem_normalizedSet F m (Finset.min'_mem F hF)⟩
  obtain ⟨c, hc⟩ := natural_tiling_of_T1_T2 E hE hT1 hT2
  exact ⟨fun t => c (t + m), integer_tiling_of_normalized_tiling F m
    (fun f hf => Finset.min'_le F f hf) c hc⟩

/-- Full classical Coven--Meyerowitz characterization. Empty sets are
excluded by the derived nonemptiness witness, not an external hypothesis. -/
theorem finite_integer_tiling_iff_T1_T2 (F : Finset ℤ) :
    TilesZ F ↔ ∃ hF : F.Nonempty,
      T1 (normalizedMask F hF) ∧ T2 (normalizedMask F hF) := by
  constructor
  · exact arbitrary_integer_tile_conditions F
  · rintro ⟨hF, hT1, hT2⟩
    exact finite_integer_tiling_of_T1_T2 F hF hT1 hT2

end CMCharacterization

/-- info: 'CMCharacterization.cyclic_mask_eq_of_evaluations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.cyclic_mask_eq_of_evaluations

/-- info: 'CMCharacterization.cyclic_tiling_of_mass_and_root_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.cyclic_tiling_of_mass_and_root_coverage

/-- info: 'CMCharacterization.integer_tiling_of_cyclic_convolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.integer_tiling_of_cyclic_convolution

/-- info: 'CMCharacterization.integer_tiling_of_normalized_tiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.integer_tiling_of_normalized_tiling

/-- info: 'CMCharacterization.root_primaryDigitStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.root_primaryDigitStep

/-- info: 'CMCharacterization.standardComplement_root_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.standardComplement_root_coverage

/-- info: 'CMCharacterization.natural_tiling_of_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.natural_tiling_of_T1_T2

/-- info: 'CMCharacterization.finite_integer_tiling_of_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.finite_integer_tiling_of_T1_T2

/-- info: 'CMCharacterization.finite_integer_tiling_iff_T1_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMCharacterization.finite_integer_tiling_iff_T1_T2
