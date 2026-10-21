#!/usr/bin/env bash
#
# Verified bootstrap for the native libfuzzer-dotnet fork-server driver (SEC-05).
#
# Prints the path of a driver built from ONE reviewed, immutable upstream revision whose source
# matches the SHA-256 pinned below, building and caching it on first use. It is the only supported
# way to obtain the driver: fuzz/run-campaign.sh calls it, and fuzz/README.md tells manual users to.
#
# Usage:  DRIVER=$(bash fuzz/libfuzzer-driver.sh [DRIVER_DIR])     (default: $HOME/katlang-fuzz)
#
# Diagnostics go to stderr; stdout carries only the verified driver path. Exit 0 = verified driver,
# nonzero = no driver may be used (nothing is ever executed from an unverified cache).
#
# Trust model:
#   * The trust anchor is the pin: a full commit SHA and the SHA-256 of the reviewed source file.
#     The source is fetched from that commit (never a branch) into a private temporary directory
#     and compared with the pinned digest BEFORE clang runs. Any mismatch or failure fails closed.
#   * A cache entry lives in a directory keyed by the pin and is published with one rename only
#     after verification, compilation and its manifest are complete. Reuse re-checks the manifest
#     identity, the cached source against the pinned digest, and the driver against the digest
#     recorded when it was built. That recorded driver digest detects accidental or unexpected
#     changes to the cache; it is NOT a signature and says nothing about the compiler's honesty.
#   * The executable the pre-SEC-05 runner built from mutable master ($DRIVER_DIR/libfuzzer-dotnet)
#     has no verification metadata and is never used.
#   * A valid cache needs no network. Without one, the source must be downloaded; there is no
#     other source and no fallback.
#
# Updating the pin is a deliberate repository change; see "Native driver" in fuzz/README.md.
set -euo pipefail

# ---- Repository pin (reviewed; update only with the procedure in fuzz/README.md) ----------------
LIBFUZZER_DOTNET_COMMIT=bd39d4e88d715ab460a929943645be2a186cde52
LIBFUZZER_DOTNET_SHA256=90f019e2e9ad3a0b93c7ecc2c5afb2fbfc8b5aab6aac51c7e0d349ec79354f36
# -----------------------------------------------------------------------------------------------

readonly UPSTREAM_REPO=https://github.com/Metalnem/libfuzzer-dotnet
readonly SOURCE_NAME=libfuzzer-dotnet.cc
readonly SOURCE_URL="https://raw.githubusercontent.com/Metalnem/libfuzzer-dotnet/${LIBFUZZER_DOTNET_COMMIT}/${SOURCE_NAME}"
readonly BUILD_FLAGS=-fsanitize=fuzzer
readonly CACHE_FORMAT=katlang-libfuzzer-dotnet-cache/1
readonly DRIVER_NAME=libfuzzer-dotnet
readonly MANIFEST_NAME=driver.manifest
readonly MAX_SOURCE_BYTES=1048576

log() { printf '[driver] %s\n' "$*" >&2; }
die() { printf '[driver] ERROR: %s\n' "$*" >&2; exit 3; }

is_sha256() { [[ "$1" =~ ^[0-9a-f]{64}$ ]]; }
is_commit() { [[ "$1" =~ ^[0-9a-f]{40}$ ]]; }

is_commit "$LIBFUZZER_DOTNET_COMMIT" || die "pinned commit is not a full 40-hex SHA: $LIBFUZZER_DOTNET_COMMIT"
is_sha256 "$LIBFUZZER_DOTNET_SHA256" || die "pinned source digest is not 64 lowercase hex: $LIBFUZZER_DOTNET_SHA256"

DRIVER_DIR=${1:-$HOME/katlang-fuzz}
CACHE="$DRIVER_DIR/$DRIVER_NAME-${LIBFUZZER_DOTNET_COMMIT:0:12}-${LIBFUZZER_DOTNET_SHA256:0:12}"
LEGACY_DRIVER="$DRIVER_DIR/$DRIVER_NAME"

# Without sha256sum nothing can be verified, so even a cached driver is refused.
command -v sha256sum >/dev/null 2>&1 || die "sha256sum not found; the driver cannot be verified."

# Prints the SHA-256 of one regular, non-symlink file; dies on missing or malformed output.
sha256_of() {
  local out digest
  out=$(sha256sum -- "$1") || die "sha256sum failed for $1"
  digest=${out%% *}
  is_sha256 "$digest" || die "malformed sha256sum output for $1"
  printf '%s' "$digest"
}

regular_file() { [ -f "$1" ] && [ ! -L "$1" ]; }

manifest_text() { # $1 = compiler line, $2 = driver digest
  printf '%s\n' \
    "format=$CACHE_FORMAT" \
    "upstream=$UPSTREAM_REPO" \
    "commit=$LIBFUZZER_DOTNET_COMMIT" \
    "source_path=$SOURCE_NAME" \
    "source_sha256=$LIBFUZZER_DOTNET_SHA256" \
    "build=clang $BUILD_FLAGS" \
    "compiler=$1" \
    "driver_sha256=$2"
}

# Validates a cache directory. Sets REASON on failure and VALID_DRIVER on success.
REASON=
VALID_DRIVER=
cache_valid() {
  local dir=$1 lines=() line compiler recorded
  REASON=; VALID_DRIVER=
  if [ ! -e "$dir" ] && [ ! -L "$dir" ]; then REASON="no verified cache"; return 1; fi
  if [ ! -d "$dir" ] || [ -L "$dir" ]; then REASON="cache path is not a plain directory"; return 1; fi
  if ! regular_file "$dir/$MANIFEST_NAME"; then REASON="cache manifest missing (incomplete or legacy cache)"; return 1; fi
  # Bash silently drops NUL bytes in an ordinary line read. Detect them before parsing so
  # corrupt metadata cannot normalize back into the expected identity. Every line must also
  # have its terminating newline, as written by manifest_text when the build completes.
  if IFS= read -r -d '' line < "$dir/$MANIFEST_NAME"; then REASON="cache manifest malformed (NUL byte)"; return 1; fi
  while IFS= read -r line; do lines+=("$line"); done < "$dir/$MANIFEST_NAME"
  if [ "${#lines[@]}" -ne 8 ] || [ -n "$line" ]; then REASON="cache manifest malformed"; return 1; fi
  compiler=${lines[6]#compiler=}
  recorded=${lines[7]#driver_sha256=}
  if [ "${lines[6]}" = "$compiler" ] || [ -z "$compiler" ] || [ "${lines[7]}" = "$recorded" ] || ! is_sha256 "$recorded"; then
    REASON="cache manifest malformed"; return 1
  fi
  if [ "$(printf '%s\n' "${lines[@]}")" != "$(manifest_text "$compiler" "$recorded")" ]; then
    REASON="cache manifest does not match the pinned revision, digest or build configuration"; return 1
  fi
  if ! regular_file "$dir/$SOURCE_NAME"; then REASON="cached source missing"; return 1; fi
  if [ "$(sha256_of "$dir/$SOURCE_NAME")" != "$LIBFUZZER_DOTNET_SHA256" ]; then REASON="cached source does not match the pinned digest"; return 1; fi
  if ! regular_file "$dir/$DRIVER_NAME" || [ ! -x "$dir/$DRIVER_NAME" ]; then REASON="cached driver missing or not executable"; return 1; fi
  if [ "$(sha256_of "$dir/$DRIVER_NAME")" != "$recorded" ]; then REASON="cached driver does not match its recorded digest"; return 1; fi
  VALID_DRIVER="$dir/$DRIVER_NAME"
}

log "libfuzzer-dotnet $LIBFUZZER_DOTNET_COMMIT ($UPSTREAM_REPO), source sha256 $LIBFUZZER_DOTNET_SHA256"
if regular_file "$LEGACY_DRIVER" || [ -L "$LEGACY_DRIVER" ]; then
  log "ignoring unverified legacy driver $LEGACY_DRIVER (pre-SEC-05 build from mutable master; safe to delete)"
fi

if cache_valid "$CACHE"; then
  log "cache verified (manifest, source sha256, driver sha256): $VALID_DRIVER"
  printf '%s\n' "$VALID_DRIVER"
  exit 0
fi
log "cache: $REASON at $CACHE; rebuilding from the pinned source"

command -v curl >/dev/null 2>&1 || die "curl not found; cannot fetch the pinned driver source."
command -v clang >/dev/null 2>&1 || die "clang not found in this WSL distro; cannot build the driver."

mkdir -p -- "$DRIVER_DIR"
TMP=$(mktemp -d -- "$DRIVER_DIR/.build.XXXXXXXX") || die "cannot create a temporary build directory in $DRIVER_DIR"
trap 'rm -rf -- "$TMP"' EXIT

if ! curl --proto '=https' --proto-redir '=https' --tlsv1.2 --max-filesize "$MAX_SOURCE_BYTES" \
     -fsSL "$SOURCE_URL" -o "$TMP/$SOURCE_NAME"; then
  die "download of the pinned driver source failed: $SOURCE_URL
[driver] No verified cache is available, so the driver cannot be used offline. Rerun with network
[driver] access once; later runs reuse the verified cache without downloading."
fi
regular_file "$TMP/$SOURCE_NAME" || die "download produced no source file."

ACTUAL=$(sha256_of "$TMP/$SOURCE_NAME")
if [ "$ACTUAL" != "$LIBFUZZER_DOTNET_SHA256" ]; then
  die "driver source digest mismatch for commit $LIBFUZZER_DOTNET_COMMIT
[driver]   expected $LIBFUZZER_DOTNET_SHA256
[driver]   actual   $ACTUAL
[driver] The source was rejected and not compiled."
fi
log "source sha256 verified"

COMPILER=$(clang --version 2>/dev/null | { IFS= read -r first || true; printf '%s' "$first"; }) || true
[ -n "$COMPILER" ] || COMPILER=unknown
log "building with clang $BUILD_FLAGS ($COMPILER)"
clang "$BUILD_FLAGS" "$TMP/$SOURCE_NAME" -o "$TMP/$DRIVER_NAME" || die "clang failed to build the driver; nothing was cached."
{ regular_file "$TMP/$DRIVER_NAME" && [ -x "$TMP/$DRIVER_NAME" ]; } || die "clang produced no executable driver."

manifest_text "$COMPILER" "$(sha256_of "$TMP/$DRIVER_NAME")" > "$TMP/$MANIFEST_NAME"

# Publish atomically: the identity directory appears complete or not at all.
rm -rf -- "$CACHE"
mv -T -- "$TMP" "$CACHE" || die "could not publish the driver cache at $CACHE"
trap - EXIT

cache_valid "$CACHE" || die "freshly published cache failed validation: $REASON"
log "built and cached: $VALID_DRIVER"
printf '%s\n' "$VALID_DRIVER"
