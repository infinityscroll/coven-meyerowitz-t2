#!/bin/sh
set -eu

# Preserve the original pinned Lake setup. Rebuild every authored source;
# ordinary `lake build` only includes the frozen old StripeCollapse target.
cd -- "$(dirname -- "$0")"
shasum -a 256 -c SHA256SUMS.completion
sh ./verify_bridges.sh

# Fifteen additional proof modules, in dependency order.
for module in \
  PrimeDirectionArithmetic CanonicalMaskPolynomial PrimaryAllocation \
  DephasedMasks ActualTilingSpectra CommonComplementLift T2Induction \
  ActualPrimeReduction ActualIntegerReduction CyclicT2Completion \
  IntegerTilingPeriodicity IntegerCyclicReduction IntegerSetNormalization \
  IntegerT2Completion FullCovenMeyerowitz
do
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done

# Fresh independent literal-function semantics probe, then guarded axioms.
lake env lean -o .lake/build/lib/lean/CMFinalCyclicColdProbe.olean CMFinalCyclicColdProbe.lean
lake env lean CompletionAudit.lean
