#!/usr/bin/env bash
set -euo pipefail

toolchain=$(<lean/lean-toolchain)
for attempt in 1 2 3; do
    if elan toolchain install "$toolchain"; then
        exit 0
    fi

    if (( attempt < 3 )); then
        delay=$((10 * attempt))
        printf 'Lean toolchain install attempt %s failed. Retrying in %s seconds.\n' "$attempt" "$delay" >&2
        sleep "$delay"
    fi
done

printf 'Failed to install Lean toolchain %s after three attempts.\n' "$toolchain" >&2
exit 1
