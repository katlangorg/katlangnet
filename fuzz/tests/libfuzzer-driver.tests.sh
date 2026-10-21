#!/usr/bin/env bash
#
# Offline regression tests for the verified libfuzzer-dotnet bootstrap (SEC-05).
#
# Never touches the network, the real clang, or the user's driver cache. Each case copies
# fuzz/libfuzzer-driver.sh and fuzz/run-campaign.sh into a fresh sandbox whose path contains
# spaces, rewrites ONLY the two pin lines of the copy to a fixture commit and the fixture's digest,
# and puts fake `curl` and `clang` first on PATH. The fake curl serves a fixture file (or fails);
# the fake clang "compiles" a small script driver that records its argv. The production script
# itself has no test hook.
#
# Usage: bash fuzz/tests/libfuzzer-driver.tests.sh       (exit 0 and "ALL <n> CHECKS PASSED" = green)
set -uo pipefail

HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
FUZZ=$(cd -- "$HERE/.." && pwd)
BOOTSTRAP="$FUZZ/libfuzzer-driver.sh"
RUNNER="$FUZZ/run-campaign.sh"
BASH_BIN=$(command -v bash)

PASSED=0
FAILED=0
CASE=
ROOTS=()
trap 'rm -rf -- "${ROOTS[@]}"' EXIT

check() { # check DESCRIPTION COMMAND...
  local desc=$1; shift
  if "$@"; then PASSED=$((PASSED + 1)); else FAILED=$((FAILED + 1)); printf 'FAIL [%s] %s\n' "$CASE" "$desc"; fi
}
contains() { [[ "$1" == *"$2"* ]]; }
lacks() { [[ "$1" != *"$2"* ]]; }
calls() { cat -- "$LOG" 2>/dev/null || true; }
build_dirs() { find "$DRIVER_DIR" -maxdepth 1 -name '.build.*' 2>/dev/null | wc -l; }

FIXTURE_COMMIT_A=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
FIXTURE_COMMIT_B=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb

# ---- sandbox ------------------------------------------------------------------------------------

new_sandbox() { # new_sandbox CASE-NAME
  CASE=$1
  SB_ROOT=$(mktemp -d); ROOTS+=("$SB_ROOT")
  SB="$SB_ROOT/sand box $CASE"
  mkdir -p "$SB/fuzz dir" "$SB/fake bin" "$SB/home dir"
  BIN="$SB/fake bin"
  LOG="$SB/calls.log"
  : > "$LOG"
  SOURCE_FIXTURE="$SB/fixture source.cc"
  printf '// fixture driver source for %s\nint main() { return 0; }\n' "$CASE" > "$SOURCE_FIXTURE"
  FIXTURE_SHA=$(sha256sum < "$SOURCE_FIXTURE"); FIXTURE_SHA=${FIXTURE_SHA%% *}
  DRIVER_DIR="$SB/driver dir"
  cp -- "$RUNNER" "$SB/fuzz dir/run-campaign.sh"
  pin "$FIXTURE_COMMIT_A" "$FIXTURE_SHA"

  cat > "$BIN/curl" <<EOF
#!$BASH_BIN
out=; url=
while [ \$# -gt 0 ]; do
  case "\$1" in
    -o) out=\$2; shift ;;
    --proto|--proto-redir|--max-filesize) shift ;;
    https://*) url=\$1 ;;
  esac
  shift
done
printf 'curl %s\n' "\$url" >> "\$FAKE_LOG"
[ "\${FAKE_CURL_FAIL:-0}" = 1 ] && exit 22
cp -- "\$FAKE_SOURCE" "\$out"
EOF
  cat > "$BIN/clang" <<EOF
#!$BASH_BIN
if [ "\$1" = --version ]; then echo "fake clang version 1.0"; exit 0; fi
printf 'clang %s\n' "\$*" >> "\$FAKE_LOG"
out=; src=
while [ \$# -gt 0 ]; do
  case "\$1" in -o) out=\$2; shift ;; *.cc) src=\$1 ;; esac
  shift
done
got=\$(sha256sum < "\$src"); got=\${got%% *}
[ "\$got" = "\$FAKE_EXPECTED_SHA" ] || printf 'UNVERIFIED-COMPILE\n' >> "\$FAKE_LOG"
if [ "\${FAKE_CLANG_FAIL:-0}" = 1 ]; then printf 'partial' > "\$out"; chmod +x "\$out"; exit 1; fi
cat > "\$out" <<'DRV'
#!$BASH_BIN
printf 'driver-ran\n' >> "\$FAKE_LOG"
printf '%s\n' "\$@" > "\$FAKE_DRIVER_ARGS"
exit "\${FAKE_DRIVER_EXIT:-0}"
DRV
chmod +x "\$out"
EOF
  chmod +x "$BIN/curl" "$BIN/clang"
}

# Writes the bootstrap copy with the given pin. Fails the suite if the production pin lines are
# not exactly where the rewrite expects them, so a test can never silently run the production pin.
pin() { # pin COMMIT SHA256
  local commit_lines sha_lines
  commit_lines=$(grep -c '^LIBFUZZER_DOTNET_COMMIT=[0-9a-f]\{40\}$' "$BOOTSTRAP")
  sha_lines=$(grep -c '^LIBFUZZER_DOTNET_SHA256=[0-9a-f]\{64\}$' "$BOOTSTRAP")
  if [ "$commit_lines" != 1 ] || [ "$sha_lines" != 1 ]; then
    echo "FATAL: production pin lines not found exactly once in $BOOTSTRAP" >&2; exit 2
  fi
  PIN_COMMIT=$1; PIN_SHA=$2
  sed -e "s/^LIBFUZZER_DOTNET_COMMIT=.*/LIBFUZZER_DOTNET_COMMIT=$1/" \
      -e "s/^LIBFUZZER_DOTNET_SHA256=.*/LIBFUZZER_DOTNET_SHA256=$2/" \
      "$BOOTSTRAP" > "$SB/fuzz dir/libfuzzer-driver.sh"
  CACHE="$DRIVER_DIR/libfuzzer-dotnet-${1:0:12}-${2:0:12}"
}

# Runs the bootstrap copy: sets OUT, ERR, CODE.
bootstrap() { # bootstrap [extra env assignments...]
  local errfile="$SB/stderr.txt"
  OUT=$(env PATH="$BIN:$PATH" HOME="$SB/home dir" FAKE_LOG="$LOG" FAKE_SOURCE="$SOURCE_FIXTURE" \
        FAKE_EXPECTED_SHA="$PIN_SHA" FAKE_DRIVER_ARGS="$SB/driver args.txt" \
        FAKE_CURL_FAIL=0 FAKE_CLANG_FAIL=0 FAKE_DRIVER_EXIT=0 "$@" \
        "$BASH_BIN" "$SB/fuzz dir/libfuzzer-driver.sh" "$DRIVER_DIR" 2> "$errfile")
  CODE=$?
  ERR=$(cat -- "$errfile")
}

make_publish() {
  PUB="$SB/publish dir"; SEEDS="$SB/seed dir"; CORPUS="$SB/corpus dir"; CRASHES="$SB/crash dir"; DICT="$SB/dict file.dict"
  mkdir -p "$PUB" "$SEEDS"
  printf '#!%s\nexit 0\n' "$BASH_BIN" > "$PUB/KatLang.ParserFuzz"
  : > "$DICT"
}

# Runs the run-campaign.sh copy with the standard positional arguments: sets OUT, ERR, CODE.
campaign() { # campaign [DRIVER_DIR-or-empty] [extra env assignments...]
  local dd=$1; shift
  local errfile="$SB/stderr.txt" args=("$PUB" "$SEEDS" "$CORPUS" "$CRASHES" "$DICT" 7 123 5 2048)
  [ -n "$dd" ] && args+=("$dd")
  OUT=$(env PATH="$BIN:$PATH" HOME="$SB/home dir" FAKE_LOG="$LOG" FAKE_SOURCE="$SOURCE_FIXTURE" \
        FAKE_EXPECTED_SHA="$PIN_SHA" FAKE_DRIVER_ARGS="$SB/driver args.txt" \
        FAKE_CURL_FAIL=0 FAKE_CLANG_FAIL=0 FAKE_DRIVER_EXIT=0 KATLANG_FUZZ_MODE= KATLANG_FUZZ_SEED= "$@" \
        "$BASH_BIN" "$SB/fuzz dir/run-campaign.sh" "${args[@]}" 2> "$errfile")
  CODE=$?
  ERR=$(cat -- "$errfile")
}

tamper_script() { printf '#!%s\nprintf "TAMPERED-RAN\\n" >> "$FAKE_LOG"\n' "$BASH_BIN" > "$1"; chmod +x "$1"; }

# ---- T0: production pin -------------------------------------------------------------------------

CASE=T0-production-pin
PROD=$(cat -- "$BOOTSTRAP")
check "pins a full commit SHA" grep -q '^LIBFUZZER_DOTNET_COMMIT=[0-9a-f]\{40\}$' "$BOOTSTRAP"
check "pins a SHA-256" grep -q '^LIBFUZZER_DOTNET_SHA256=[0-9a-f]\{64\}$' "$BOOTSTRAP"
check "source URL is built from the pinned commit" \
  contains "$PROD" 'libfuzzer-dotnet/${LIBFUZZER_DOTNET_COMMIT}/${SOURCE_NAME}'
check "no mutable branch reference" lacks "$PROD" '/master/'
check "runner has no download or compile of its own" \
  bash -c '! grep -v "^[[:space:]]*#" "$1" | grep -Eq "curl|clang|raw\.githubusercontent"' _ "$RUNNER"
check "runner obtains the driver from the bootstrap" grep -q 'libfuzzer-driver.sh' "$RUNNER"

# ---- T1: valid source accepted ------------------------------------------------------------------

new_sandbox T1
bootstrap
check "exit 0" [ "$CODE" = 0 ]
check "prints the cached driver path" [ "$OUT" = "$CACHE/libfuzzer-dotnet" ]
check "downloads from the pinned commit" contains "$(calls)" "curl https://raw.githubusercontent.com/Metalnem/libfuzzer-dotnet/$FIXTURE_COMMIT_A/libfuzzer-dotnet.cc"
check "compiles once with -fsanitize=fuzzer" [ "$(grep -c '^clang -fsanitize=fuzzer ' "$LOG")" = 1 ]
check "compiled only verified source" lacks "$(calls)" UNVERIFIED-COMPILE
check "reports verification before building" bash -c '[[ "$1" == *"source sha256 verified"*"building with clang"* ]]' _ "$ERR"
check "publishes the driver executable" [ -x "$CACHE/libfuzzer-dotnet" ]
check "publishes the verified source" cmp -s "$CACHE/libfuzzer-dotnet.cc" "$SOURCE_FIXTURE"
check "manifest records commit" grep -qx "commit=$FIXTURE_COMMIT_A" "$CACHE/driver.manifest"
check "manifest records source digest" grep -qx "source_sha256=$FIXTURE_SHA" "$CACHE/driver.manifest"
check "manifest records build configuration" grep -qx "build=clang -fsanitize=fuzzer" "$CACHE/driver.manifest"
DRIVER_SHA=$(sha256sum < "$CACHE/libfuzzer-dotnet"); DRIVER_SHA=${DRIVER_SHA%% *}
check "manifest records the driver digest" grep -qx "driver_sha256=$DRIVER_SHA" "$CACHE/driver.manifest"
check "no temporary build directory left" [ "$(build_dirs)" = 0 ]

# ---- T2: modified source rejected ---------------------------------------------------------------

new_sandbox T2
printf 'X' | dd of="$SOURCE_FIXTURE" bs=1 seek=3 conv=notrunc status=none   # one byte changed
bootstrap
check "nonzero exit" [ "$CODE" != 0 ]
check "reports digest mismatch" contains "$ERR" "digest mismatch"
check "reports expected digest" contains "$ERR" "expected $FIXTURE_SHA"
check "compiler not invoked" lacks "$(calls)" "clang "
check "prints no driver path" [ -z "$OUT" ]
check "no cache published" [ ! -e "$CACHE" ]
check "no temporary build directory left" [ "$(build_dirs)" = 0 ]

# ---- T3: download failure -----------------------------------------------------------------------

new_sandbox T3
bootstrap FAKE_CURL_FAIL=1
check "nonzero exit" [ "$CODE" != 0 ]
check "reports download failure" contains "$ERR" "download of the pinned driver source failed"
check "attempted only the pinned URL" [ "$(grep -c '^curl ' "$LOG")" = 1 ]
check "never fetches master" lacks "$(calls)" "/master/"
check "compiler not invoked" lacks "$(calls)" "clang "
check "no cache published" [ ! -e "$CACHE" ]
check "no temporary build directory left" [ "$(build_dirs)" = 0 ]

# ---- T4: existing valid cache -------------------------------------------------------------------

new_sandbox T4
bootstrap
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "exit 0" [ "$CODE" = 0 ]
check "reuses the cached driver" [ "$OUT" = "$CACHE/libfuzzer-dotnet" ]
check "reports cache verification" contains "$ERR" "cache verified"
check "no download" lacks "$(calls)" "curl "
check "no compilation" lacks "$(calls)" "clang "

# ---- T5: legacy unverified executable -----------------------------------------------------------

new_sandbox T5
make_publish
mkdir -p "$DRIVER_DIR"
printf '#!%s\nprintf "LEGACY-RAN\\n" >> "$FAKE_LOG"\n' "$BASH_BIN" > "$DRIVER_DIR/libfuzzer-dotnet"
chmod +x "$DRIVER_DIR/libfuzzer-dotnet"
printf 'legacy source\n' > "$DRIVER_DIR/libfuzzer-dotnet.cc"
campaign "$DRIVER_DIR" FAKE_CURL_FAIL=1
check "offline with only a legacy driver fails" [ "$CODE" = 3 ]
check "legacy driver never runs (offline)" lacks "$(calls)" "LEGACY-RAN"
check "legacy driver reported as ignored" contains "$ERR" "ignoring unverified legacy driver"
check "campaign not started" lacks "$OUT" "[run] libFuzzer"
: > "$LOG"
campaign "$DRIVER_DIR"
check "online: rebuilds securely and succeeds" [ "$CODE" = 0 ]
check "online: verified driver runs" contains "$(calls)" "driver-ran"
check "online: legacy driver never runs" lacks "$(calls)" "LEGACY-RAN"
check "online: campaign uses the verified path" contains "$OUT" "[run] driver=$CACHE/libfuzzer-dotnet"
check "legacy files left untouched" grep -q LEGACY-RAN "$DRIVER_DIR/libfuzzer-dotnet"

# ---- T6: modified cached binary -----------------------------------------------------------------

new_sandbox T6
make_publish
bootstrap
tamper_script "$CACHE/libfuzzer-dotnet"
: > "$LOG"
campaign "$DRIVER_DIR" FAKE_CURL_FAIL=1
check "offline: tampered driver rejected" [ "$CODE" = 3 ]
check "offline: reason reported" contains "$ERR" "cached driver does not match its recorded digest"
check "offline: tampered driver never runs" lacks "$(calls)" "TAMPERED-RAN"
: > "$LOG"
campaign "$DRIVER_DIR"
check "online: rebuilt and run" [ "$CODE" = 0 ]
check "online: tampered driver never runs" lacks "$(calls)" "TAMPERED-RAN"
check "online: rebuilt driver ran" contains "$(calls)" "driver-ran"
check "online: cache valid again" bash -c 'grep -q driver-ran "$1"' _ "$CACHE/libfuzzer-dotnet"

# ---- T7: modified cached source -----------------------------------------------------------------

new_sandbox T7
bootstrap
printf '// edited\n' >> "$CACHE/libfuzzer-dotnet.cc"
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "offline: inconsistent cache rejected" [ "$CODE" != 0 ]
check "offline: reason reported" contains "$ERR" "cached source does not match the pinned digest"
check "offline: no driver path" [ -z "$OUT" ]
: > "$LOG"
bootstrap
check "online: rebuilt" [ "$CODE" = 0 ]
check "online: downloaded and compiled again" bash -c '[[ "$1" == *"curl "*"clang "* ]]' _ "$(calls)"
check "online: cached source restored" cmp -s "$CACHE/libfuzzer-dotnet.cc" "$SOURCE_FIXTURE"

# ---- T8: revision or digest change --------------------------------------------------------------

new_sandbox T8
bootstrap
OLD_CACHE=$CACHE
pin "$FIXTURE_COMMIT_B" "$FIXTURE_SHA"
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "new commit: old cache cannot satisfy it offline" [ "$CODE" != 0 ]
check "new commit: fetches the new commit only" contains "$(calls)" "/$FIXTURE_COMMIT_B/libfuzzer-dotnet.cc"
: > "$LOG"
bootstrap
check "new commit: authenticated rebuild" [ "$CODE" = 0 ]
check "new commit: new cache path" [ "$OUT" = "$CACHE/libfuzzer-dotnet" ]
check "new commit: path differs from the old cache" [ "$CACHE" != "$OLD_CACHE" ]
# A different expected digest: the fixture no longer matches, so nothing is accepted.
pin "$FIXTURE_COMMIT_A" "$(printf '%064d' 0)"
: > "$LOG"
bootstrap
check "new digest: mismatching source rejected" [ "$CODE" != 0 ]
check "new digest: not compiled" lacks "$(calls)" "clang "
# An old cache copied under the new identity's directory name is still refused by its manifest.
pin "$FIXTURE_COMMIT_B" "$FIXTURE_SHA"
NEW_CACHE=$CACHE
pin "$FIXTURE_COMMIT_A" "$FIXTURE_SHA"
rm -rf -- "$NEW_CACHE"; cp -a -- "$CACHE" "$NEW_CACHE"
pin "$FIXTURE_COMMIT_B" "$FIXTURE_SHA"
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "relabelled cache rejected by manifest" contains "$ERR" "cache manifest does not match"
check "relabelled cache: nonzero exit offline" [ "$CODE" != 0 ]

# ---- T9: interrupted build ----------------------------------------------------------------------

new_sandbox T9
bootstrap FAKE_CLANG_FAIL=1
check "compile failure: nonzero exit" [ "$CODE" != 0 ]
check "compile failure: reported" contains "$ERR" "clang failed"
check "compile failure: no cache published" [ ! -e "$CACHE" ]
check "compile failure: no partial executable at the cache path" [ ! -e "$CACHE/libfuzzer-dotnet" ]
check "compile failure: temporary directory removed" [ "$(build_dirs)" = 0 ]
# A build killed before publication leaves only a .build.* directory: it is never consulted.
mkdir -p "$DRIVER_DIR/.build.killed"
tamper_script "$DRIVER_DIR/.build.killed/libfuzzer-dotnet"
# A cache directory without its manifest (as an interrupted non-atomic copy would leave) is refused.
mkdir -p "$CACHE"; cp -- "$SOURCE_FIXTURE" "$CACHE/libfuzzer-dotnet.cc"; tamper_script "$CACHE/libfuzzer-dotnet"
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "incomplete cache: refused offline" [ "$CODE" != 0 ]
check "incomplete cache: reason reported" contains "$ERR" "cache manifest missing"
: > "$LOG"
bootstrap
check "recovery: next online run succeeds" [ "$CODE" = 0 ]
check "recovery: rebuilt driver is the fake build" grep -q driver-ran "$CACHE/libfuzzer-dotnet"
check "recovery: leftover build dir never used" [ "$OUT" = "$CACHE/libfuzzer-dotnet" ]
# A truncated manifest is refused as well.
head -n 3 "$CACHE/driver.manifest" > "$SB/m"; cat "$SB/m" > "$CACHE/driver.manifest"
bootstrap FAKE_CURL_FAIL=1
check "truncated manifest refused" contains "$ERR" "cache manifest malformed"
check "truncated manifest: nonzero exit" [ "$CODE" != 0 ]

# Bash's ordinary read discards NUL bytes; a corrupted manifest must be rejected byte-for-byte.
bootstrap
cp -- "$CACHE/driver.manifest" "$SB/good manifest"
printf '\0' > "$CACHE/driver.manifest"
cat "$SB/good manifest" >> "$CACHE/driver.manifest"
bootstrap FAKE_CURL_FAIL=1
check "NUL-corrupted manifest refused" contains "$ERR" "cache manifest malformed"
check "NUL-corrupted manifest: nonzero exit offline" [ "$CODE" != 0 ]
check "NUL-corrupted manifest: no driver path" [ -z "$OUT" ]
# Simulate interruption immediately before the final newline of the metadata write.
head -c -1 "$SB/good manifest" > "$CACHE/driver.manifest"
bootstrap FAKE_CURL_FAIL=1
check "unterminated manifest refused" contains "$ERR" "cache manifest malformed"
check "unterminated manifest: nonzero exit offline" [ "$CODE" != 0 ]
cp -- "$SB/good manifest" "$CACHE/driver.manifest"
printf 'unfinished extra field' >> "$CACHE/driver.manifest"
bootstrap FAKE_CURL_FAIL=1
check "unterminated extra metadata refused" contains "$ERR" "cache manifest malformed"
check "unterminated extra metadata: nonzero exit offline" [ "$CODE" != 0 ]
bootstrap
check "corrupt metadata: authenticated rebuild recovers" [ "$CODE" = 0 ]

# ---- T10: offline operation ---------------------------------------------------------------------

new_sandbox T10
bootstrap FAKE_CURL_FAIL=1
check "no cache offline: fails" [ "$CODE" != 0 ]
check "no cache offline: actionable message" contains "$ERR" "cannot be used offline"
check "no cache offline: compiler not invoked" lacks "$(calls)" "clang "
bootstrap
: > "$LOG"
bootstrap FAKE_CURL_FAIL=1
check "valid cache offline: succeeds" [ "$CODE" = 0 ]
check "valid cache offline: no network" lacks "$(calls)" "curl "

# ---- T11: command-line compatibility ------------------------------------------------------------

new_sandbox T11
make_publish
campaign "$DRIVER_DIR" KATLANG_FUZZ_SEED=42 KATLANG_FUZZ_MODE=metamorphic FAKE_DRIVER_EXIT=77
EXPECTED_ARGS=$(printf '%s\n' \
  "--target_path=$PUB/KatLang.ParserFuzz" -max_len=123 -timeout=5 -rss_limit_mb=2048 -max_total_time=7 \
  "-dict=$DICT" "-artifact_prefix=$CRASHES/" -print_final_stats=1 -seed=42 "$CORPUS" "$SEEDS")
check "driver argv unchanged" [ "$(cat -- "$SB/driver args.txt")" = "$EXPECTED_ARGS" ]
check "libFuzzer exit code propagated" [ "$CODE" = 77 ]
check "mode echoed" contains "$OUT" "[run] KATLANG_FUZZ_MODE=metamorphic"
check "corpus dir created" [ -d "$CORPUS" ]
check "crash dir created" [ -d "$CRASHES" ]
check "done line reports exit" contains "$OUT" "[done] libFuzzer exit=77"
campaign "$DRIVER_DIR" KATLANG_FUZZ_SEED=0
EXPECTED_ARGS=$(printf '%s\n' \
  "--target_path=$PUB/KatLang.ParserFuzz" -max_len=123 -timeout=5 -rss_limit_mb=2048 -max_total_time=7 \
  "-dict=$DICT" "-artifact_prefix=$CRASHES/" -print_final_stats=1 "$CORPUS" "$SEEDS")
check "zero seed: argv unchanged" [ "$(cat -- "$SB/driver args.txt")" = "$EXPECTED_ARGS" ]
check "zero seed: exit 0" [ "$CODE" = 0 ]
# Test helpers isolate the campaign from a developer's exported seed/mode and fake-tool settings.
(
  export KATLANG_FUZZ_SEED=314159 KATLANG_FUZZ_MODE=frontend FAKE_CURL_FAIL=1 FAKE_CLANG_FAIL=1 FAKE_DRIVER_EXIT=88
  campaign "$DRIVER_DIR"
  [ "$CODE" = 0 ] && [ "$(cat -- "$SB/driver args.txt")" = "$EXPECTED_ARGS" ] && \
    [[ "$OUT" == *'KATLANG_FUZZ_MODE=<unset: raw parser>'* ]]
)
check "inherited campaign settings do not alter the fixture" [ "$?" = 0 ]
env PATH="$BIN:$PATH" "$BASH_BIN" "$SB/fuzz dir/run-campaign.sh" a b c > /dev/null 2>&1
check "usage error still exits 2" [ "$?" = 2 ]

# ---- T12: path handling -------------------------------------------------------------------------

new_sandbox T12
make_publish
DEFAULT_DIR="$SB/home dir/katlang-fuzz"
campaign ""
check "default DRIVER_DIR under HOME with spaces" [ "$CODE" = 0 ]
check "default cache used" contains "$OUT" "[run] driver=$DEFAULT_DIR/libfuzzer-dotnet-"
check "default cache published" bash -c 'ls -d "$1"/libfuzzer-dotnet-*/driver.manifest >/dev/null' _ "$DEFAULT_DIR"
CUSTOM="$SB/custom driver dir/with  two spaces"
campaign "$CUSTOM"
check "custom DRIVER_DIR with spaces" [ "$CODE" = 0 ]
check "custom cache used" contains "$OUT" "[run] driver=$CUSTOM/libfuzzer-dotnet-"
check "custom cache published" bash -c 'ls -d "$1"/libfuzzer-dotnet-*/driver.manifest >/dev/null' _ "$CUSTOM"
check "driver received the spaced target path" grep -qx -- "--target_path=$PUB/KatLang.ParserFuzz" "$SB/driver args.txt"

# ---- T13: missing tools -------------------------------------------------------------------------

new_sandbox T13
NO_TOOLS="$SB/no tools"; mkdir -p "$NO_TOOLS"
OUT=$(env PATH="$NO_TOOLS" "$BASH_BIN" "$SB/fuzz dir/libfuzzer-driver.sh" "$DRIVER_DIR" 2> "$SB/stderr.txt"); CODE=$?
check "missing sha256sum: fails closed" [ "$CODE" != 0 ]
check "missing sha256sum: reported" grep -q "sha256sum not found" "$SB/stderr.txt"
# Everything but clang: a cache miss must fail before anything is downloaded.
TOOLS="$SB/tools"; mkdir -p "$TOOLS"
for t in sha256sum mkdir mktemp rm mv cat; do ln -s "$(command -v "$t")" "$TOOLS/$t"; done
ln -s "$BIN/curl" "$TOOLS/curl"
OUT=$(env PATH="$TOOLS" FAKE_LOG="$LOG" FAKE_SOURCE="$SOURCE_FIXTURE" \
      "$BASH_BIN" "$SB/fuzz dir/libfuzzer-driver.sh" "$DRIVER_DIR" 2> "$SB/stderr.txt"); CODE=$?
check "missing clang: fails" [ "$CODE" != 0 ]
check "missing clang: reported" grep -q "clang not found" "$SB/stderr.txt"
check "missing clang: nothing downloaded" lacks "$(calls)" "curl "

# ---- T14: malformed or failed checksum output ---------------------------------------------------

new_sandbox T14
cat > "$BIN/sha256sum" <<EOF
#!$BASH_BIN
case "\${FAKE_SHA_MODE:-empty}" in
  empty) exit 0 ;;
  malformed) printf 'not-a-sha256  fixture\\n' ;;
  failure) exit 1 ;;
esac
EOF
chmod +x "$BIN/sha256sum"
for mode in empty malformed failure; do
  : > "$LOG"
  bootstrap FAKE_SHA_MODE="$mode"
  check "$mode checksum output: nonzero exit" [ "$CODE" != 0 ]
  check "$mode checksum output: diagnosed" contains "$ERR" "sha256sum"
  check "$mode checksum output: not compiled" lacks "$(calls)" "clang "
  check "$mode checksum output: no driver path" [ -z "$OUT" ]
  check "$mode checksum output: no cache published" [ ! -e "$CACHE" ]
done

# ---- summary ------------------------------------------------------------------------------------

TOTAL=$((PASSED + FAILED))
if [ "$FAILED" -ne 0 ]; then
  printf '%d OF %d CHECKS FAILED\n' "$FAILED" "$TOTAL"
  exit 1
fi
printf 'ALL %d CHECKS PASSED\n' "$TOTAL"
