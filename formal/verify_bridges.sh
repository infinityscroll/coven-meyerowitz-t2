#!/bin/sh
set -eu

# Execute from this script's own directory; preserve the frozen Lake setup.
cd -- "$(dirname -- "$0")"
shasum -a 256 -c SHA256SUMS
shasum -a 256 -c SHA256SUMS.bridges
mkdir -p .lake/build/lib/lean

# Recompile sources in dependency order. The old default Lake target does
# not include these new modules and is not used as a substitute for them.
for module in \
  StripeCollapse BooleanStripes PeriodicDescent PeriodicFactorization \
  MatrixCollapse FiberMass PeriodicMatrixCollapse PhaseTilings \
  PhaseIsolation ResidueGrading RelativeCyclotomic RamifiedCyclotomic \
  PrimeCharacter CyclicEvaluation FourierPeriod SpectralIdentities \
  CyclicFiberEvaluation CoprimeTilingFibers PeriodicPhaseReduction \
  FiberProductBoolean
do
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done

# Exact guarded messages make unexpected theorem axioms a failing check.
lake env lean BridgeAudit.lean
