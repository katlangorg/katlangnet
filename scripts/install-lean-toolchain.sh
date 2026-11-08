#!/usr/bin/env bash
set -euo pipefail

retry() {
    local operation=$1
    shift
    local attempt delay

    for attempt in 1 2 3; do
        if "$@"; then
            return 0
        fi

        if (( attempt < 3 )); then
            delay=$((10 * attempt))
            printf '%s failed on attempt %s. Retrying in %s seconds.\n' "$operation" "$attempt" "$delay" >&2
            sleep "$delay"
        fi
    done

    printf '%s failed after three attempts.\n' "$operation" >&2
    return 1
}

toolchain=$(<lean/lean-toolchain)
installer="$RUNNER_TEMP/elan-init.sh"
retry 'Downloading the Elan bootstrap script' curl --proto '=https' --tlsv1.2 -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/227caca133724d5516bee25c2aeb3e609478f2d8/elan-init.sh \
    -o "$installer"
printf '%s  %s\n' 'a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53' "$installer" | sha256sum -c -
retry 'Installing Elan' sh "$installer" -y --default-toolchain none
retry "Installing Lean toolchain $toolchain" "$HOME/.elan/bin/elan" toolchain install "$toolchain"
printf '%s\n' "$HOME/.elan/bin" >> "$GITHUB_PATH"
