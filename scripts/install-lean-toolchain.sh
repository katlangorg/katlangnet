#!/usr/bin/env bash
set -euo pipefail

toolchain=$(<lean/lean-toolchain)
if [[ ! $toolchain =~ ^leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9.-]+)?)$ ]]; then
    printf 'Expected a Lean release tag in lean/lean-toolchain, got %s.\n' "$toolchain" >&2
    exit 1
fi
tag=${BASH_REMATCH[1]}
asset_name="lean-${tag#v}-linux.tar.zst"
release_api=https://api.github.com/repos/leanprover/lean4/releases
curl_options=(--proto '=https' --proto-redir '=https' --tlsv1.2 --fail --silent --show-error --location --retry 2 --retry-delay 10)

# The public release download redirects have returned 504s on GitHub-hosted runners.
printf 'Resolving %s via the GitHub releases API.\n' "$asset_name"
release=$(curl "${curl_options[@]}" --header 'Accept: application/vnd.github+json' "$release_api/tags/$tag")
asset=$(jq -er --arg name "$asset_name" \
    '.assets[] | select(.name == $name and .state == "uploaded") | [.id, .digest] | @tsv' <<< "$release")
IFS=$'\t' read -r asset_id digest <<< "$asset"
if [[ ! $asset_id =~ ^[0-9]+$ || ! $digest =~ ^sha256:[a-f0-9]{64}$ ]]; then
    printf 'Release asset %s lacks a valid ID or SHA-256 digest.\n' "$asset_name" >&2
    exit 1
fi

archive="$RUNNER_TEMP/$asset_name"
install_dir="$RUNNER_TEMP/lean-toolchain"
printf 'Downloading %s from release asset %s.\n' "$asset_name" "$asset_id"
curl "${curl_options[@]}" --header 'Accept: application/octet-stream' \
    "$release_api/assets/$asset_id" --output "$archive"
printf '%s  %s\n' "${digest#sha256:}" "$archive" | sha256sum -c -
mkdir -p "$install_dir"
tar --zstd --strip-components=1 -xf "$archive" -C "$install_dir"
test -x "$install_dir/bin/lake"
printf '%s\n' "$install_dir/bin" >> "$GITHUB_PATH"
