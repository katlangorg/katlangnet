#!/usr/bin/env bash
#
# WSL-side runner for the KatLang parser fuzzing campaign.
#
# This machine has no native Windows clang/libFuzzer, so the actual coverage-guided
# run happens in WSL: build (and cache) the libfuzzer-dotnet fork-server driver with
# clang, then run libFuzzer against the self-contained, sharpfuzz-instrumented harness
# publish produced on the Windows side by scripts/fuzz-parser.ps1.
#
# It needs clang on PATH and, on first run only, internet access to fetch the driver
# source. No .NET install is required in WSL because the harness publish is
# self-contained (linux-x64).
#
# Usage (all paths must be WSL paths, e.g. /mnt/d/...):
#   run-campaign.sh PUBLISH_DIR SEED_DIR CORPUS_DIR CRASH_DIR DICT_FILE \
#                   MAX_TOTAL_TIME MAX_LEN TIMEOUT RSS_LIMIT_MB [DRIVER_DIR]
set -euo pipefail

if [ "$#" -lt 9 ]; then
  echo "usage: run-campaign.sh PUBLISH_DIR SEED_DIR CORPUS_DIR CRASH_DIR DICT_FILE MAX_TOTAL_TIME MAX_LEN TIMEOUT RSS_LIMIT_MB [DRIVER_DIR]" >&2
  exit 2
fi

PUB=$1; SEEDS=$2; CORPUS=$3; CRASHES=$4; DICT=$5
MAXTIME=$6; MAXLEN=$7; TIMEOUT=$8; RSS=$9
DRIVER_DIR=${10:-$HOME/katlang-fuzz}
DRIVER_SRC_URL=https://raw.githubusercontent.com/Metalnem/libfuzzer-dotnet/master/libfuzzer-dotnet.cc

mkdir -p "$DRIVER_DIR" "$CORPUS" "$CRASHES"
DRIVER="$DRIVER_DIR/libfuzzer-dotnet"

# Build the driver once and cache it (the WSL home dir persists across instance stops;
# /tmp does not).
if [ ! -x "$DRIVER" ]; then
  echo "[driver] building libfuzzer-dotnet with clang..."
  command -v clang >/dev/null 2>&1 || { echo "ERROR: clang not found in this WSL distro." >&2; exit 3; }
  curl -fsSL "$DRIVER_SRC_URL" -o "$DRIVER_DIR/libfuzzer-dotnet.cc"
  clang -fsanitize=fuzzer "$DRIVER_DIR/libfuzzer-dotnet.cc" -o "$DRIVER"
fi

APPHOST="$PUB/KatLang.ParserFuzz"
[ -f "$APPHOST" ] || { echo "ERROR: harness apphost not found: $APPHOST (run scripts/fuzz-parser.ps1 first)." >&2; exit 4; }
chmod +x "$APPHOST" 2>/dev/null || true

echo "[run] libFuzzer: max_total_time=${MAXTIME}s max_len=${MAXLEN} timeout=${TIMEOUT}s rss_limit_mb=${RSS}"
echo "[run] driver=$DRIVER"
echo "[run] corpus(write)=$CORPUS  seeds(read)=$SEEDS"

# The first corpus dir is writable (new coverage-increasing inputs land there); the
# seed dir is read-only. Crash/timeout artifacts go under CRASHES via artifact_prefix.
# A non-zero exit here typically means libFuzzer found a crash — that is a FINDING,
# not a script error, so we surface the code rather than failing hard.
set +e
"$DRIVER" --target_path="$APPHOST" \
  -max_len="$MAXLEN" -timeout="$TIMEOUT" -rss_limit_mb="$RSS" -max_total_time="$MAXTIME" \
  -dict="$DICT" -artifact_prefix="$CRASHES/" -print_final_stats=1 \
  "$CORPUS" "$SEEDS"
code=$?
set -e

echo "[done] libFuzzer exit=$code  corpus_units=$(find "$CORPUS" -type f | wc -l)  crash_artifacts=$(find "$CRASHES" -type f 2>/dev/null | wc -l)"
exit "$code"
