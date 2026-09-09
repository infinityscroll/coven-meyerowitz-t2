import FullCovenMeyerowitz
import CMFinalCyclicColdProbe

/- Exact dependency tripwires for the full statements, not just auxiliary
lemmas. An added axiom, missing declaration, or sorryAx fails this check. -/

/-- info: 'CyclicT2Completion.actual_cyclic_tiling_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CyclicT2Completion.actual_cyclic_tiling_T2

/-- info: 'CMFinalCyclicColdProbe.literal_function_cyclic_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMFinalCyclicColdProbe.literal_function_cyclic_T2

/-- info: 'ActualIntegerReduction.actual_integer_ordinary_phase_tilings' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ActualIntegerReduction.actual_integer_ordinary_phase_tilings

/-- info: 'IntegerCyclicReduction.normalized_integer_tiling_to_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegerCyclicReduction.normalized_integer_tiling_to_cyclic

/-- info: 'IntegerT2Completion.integer_tiling_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IntegerT2Completion.integer_tiling_T2

/-- info: 'FullCovenMeyerowitz.integer_tile_cyclotomic_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FullCovenMeyerowitz.integer_tile_cyclotomic_product

/-- info: 'FullCovenMeyerowitz.finite_integer_tiling_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FullCovenMeyerowitz.finite_integer_tiling_T2

/-- info: 'FullCovenMeyerowitz.arbitrary_integer_tile_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FullCovenMeyerowitz.arbitrary_integer_tile_T2
