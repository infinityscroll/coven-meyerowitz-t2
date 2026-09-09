import PeriodicMatrixCollapse
import PhaseTilings
import PhaseIsolation
import ResidueGrading
import PrimeCharacter
import RamifiedCyclotomic
import SpectralIdentities
import CyclicFiberEvaluation
import PeriodicPhaseReduction
import CoprimeTilingFibers
import FiberProductBoolean

/-!
Guarded axiom checks for the actual final bridge theorems. A changed
dependency list, including sorryAx or a new mathematical axiom, fails
this source check. This is not an assertion of full CM formalization.
-/

/-- info: 'PeriodicMatrixCollapse.periodic_product_row_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PeriodicMatrixCollapse.periodic_product_row_collapse

/-- info: 'PhaseTilings.actual_integer_phase_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PhaseTilings.actual_integer_phase_family

/-- info: 'PhaseIsolation.theta_power_phase_isolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PhaseIsolation.theta_power_phase_isolation

/-- info: 'ResidueGrading.cyclotomic_mul_dvd_residue_sum_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ResidueGrading.cyclotomic_mul_dvd_residue_sum_iff

/-- info: 'PrimeCharacter.coprime_character_rectangles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCharacter.coprime_character_rectangles

/-- info: 'PrimeCharacter.carry_coefficient_sum_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeCharacter.carry_coefficient_sum_product

/-- info: 'RamifiedCyclotomic.low_degree_product_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RamifiedCyclotomic.low_degree_product_zero

/-- info: 'CyclicEvaluation.tiling_evaluation_product_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CyclicEvaluation.tiling_evaluation_product_zero

/-- info: 'SpectralIdentities.evaluations_determine_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SpectralIdentities.evaluations_determine_mask

/-- info: 'SpectralIdentities.spectral_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SpectralIdentities.spectral_period

/-- info: 'CyclicFiberEvaluation.ramified_tiling_fiber_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CyclicFiberEvaluation.ramified_tiling_fiber_zero

/-- info: 'PeriodicPhaseReduction.periodic_product_phase_tilings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PeriodicPhaseReduction.periodic_product_phase_tilings

/-- info: 'CoprimeTilingFibers.actual_coprime_character_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CoprimeTilingFibers.actual_coprime_character_identities

/-- info: 'FiberProductBoolean.dephased_fiber_products_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FiberProductBoolean.dephased_fiber_products_boolean
