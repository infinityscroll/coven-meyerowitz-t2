#!/bin/sh
set -eu

# Run in this checkout with its own pinned Lean/Lake/Mathlib environment.
# Prerequisites: elan (or the pinned lean/lake binaries) and dependencies from
# lake-manifest.json, obtained with `lake exe cache get` as documented for
# the existing verifier. Do not replace the pinned manifest. This script
# does not locate, import, or fall back to another research checkout.
cd -- "$(dirname -- "$0")"
unset LEAN_PATH

verification_dir=$(mktemp -d "${TMPDIR:-/tmp}/cm-characterization-replay.XXXXXX")
verification_receipt="$verification_dir/receipt.txt"
printf '%s\n' "Verification artifacts: $verification_dir"

# Every run gets a distinct receipt. PASS is written only after the old full
# T2 replay, all new source compilations, and all exact axiom guards succeed.
# Partial/failed runs cannot reuse a PASS file from an earlier invocation.
verification_status=FAILED
finish_receipt() {
  verification_exit=$?
  if [ "$verification_exit" -ne 0 ]; then verification_status=FAILED; fi
  {
    printf 'status=%s\n' "$verification_status"
    printf 'exit_code=%s\n' "$verification_exit"
    printf 'finished_utc=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    printf 'scope=%s\n' 'full existing T2 replay; four characterization modules; guarded literal signed-set iff'
    printf 'checkout=%s\n' "$(pwd -P)"
    printf 'log_directory=%s\n' "$verification_dir"
  } > "$verification_receipt"
  printf 'Receipt: %s (%s)\n' "$verification_receipt" "$verification_status"
}
trap finish_receipt EXIT

# Record the actual local toolchain, source identities, and pinned dependency
# manifest alongside the logs. These are provenance, not a priority claim.
lake env lean --version > "$verification_dir/lean-version.txt"
shasum -a 256 lean-toolchain lakefile.toml lake-manifest.json \
  SHA256SUMS SHA256SUMS.bridges SHA256SUMS.completion \
  verify_full_t2.sh verify_bridges.sh \
  verify_characterization.sh CMCharacterizationDefinitions.lean \
  CMCharacterizationT1.lean CMCharacterizationSufficiency.lean \
  CMCharacterizationSemanticsAudit.lean > "$verification_dir/SHA256SUMS"

if sh ./verify_full_t2.sh > "$verification_dir/full-t2.log" 2>&1; then
  printf '%s\n' 'PASS existing full T2 replay'
else
  sed -n '1,240p' "$verification_dir/full-t2.log"
  exit 1
fi

# No default `lake build` shortcut: the four new files are compiled explicitly
# in dependency order, with outputs in this checkout's normal Lake library.
for module in \
  CMCharacterizationDefinitions CMCharacterizationT1 \
  CMCharacterizationSufficiency CMCharacterizationSemanticsAudit
do
  if lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean" \
      > "$verification_dir/$module.log" 2>&1; then
    printf 'PASS %s\n' "$module"
  else
    sed -n '1,240p' "$verification_dir/$module.log"
    exit 1
  fi
done

# Detect accidental source changes during a run before issuing its receipt.
shasum -a 256 -c "$verification_dir/SHA256SUMS" > "$verification_dir/source-recheck.log" 2>&1
verification_status=PASS
