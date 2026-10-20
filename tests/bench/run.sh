#!/bin/sh
# Microbenchmark of the fast SHA-256 (sha256#40): hashes 1 MiB many times
# and reports time a MiB and instructions a byte.
#
#   tests/bench/run.sh <repository-dir> [debug|release]
#
# bats must be on PATH (BATS_REPOSITORY is not read; pass the directory).
# Native only. Prints, for hash and for the incremental API (pieces of 4096
# bytes), the least wall time a MiB of 5 runs of 20 MiB and, when valgrind is
# there, the instructions a byte measured by callgrind as the difference of
# a run of 3 MiB and a run of 1 MiB (so the fill of the buffer is not
# counted). The digest printed is the same in every variant.
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
MODE=${2:-release}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp -R "$1" "$TMP/repo"
(cd "$ROOT" && bats upload --repository "$TMP/repo" >/dev/null)
PKG=sha256
NEW=$(ls -t "$TMP/repo/$PKG"/*.bats | head -1)
for a in "$TMP/repo/$PKG"/*.bats; do
  [ "$a" = "$NEW" ] || rm -f "$a" "$a.sha256"
done
cp -R "$ROOT/tests/bench/bench" "$TMP/w"
(cd "$TMP/w" && bats lock --dev --repository "$TMP/repo" && bats build --only "$MODE" --only native --repository "$TMP/repo") > "$TMP/build.log" 2>&1 \
  || { cat "$TMP/build.log"; exit 1; }
BIN="$TMP/w/dist/$MODE/bench"
for api in ${BENCH_APIS:-hash incremental proved}; do
  echo "== $MODE, $api"
  # the least of 5 runs of 20 MiB: the machine is shared
  for r in 1 2 3 4 5; do
    BENCH_API=$api BENCH_ITERATIONS=20 "$BIN" 2>&1 >"$TMP/digest" | sed 's/ x 1 MiB: / /'
  done | sort -k2 -n | head -1 | awk '{ printf "time: %s ms a MiB (least of 5 runs of 20 MiB)\n", $2 }'
  cat "$TMP/digest"
  if command -v valgrind >/dev/null 2>&1; then
    for n in 1 3; do
      BENCH_API=$api BENCH_ITERATIONS=$n valgrind --tool=callgrind --callgrind-out-file="$TMP/cg.$n.out" "$BIN" >/dev/null 2>"$TMP/cg.$n.err"
      grep -E 'Collected' "$TMP/cg.$n.err" | sed 's/.*: *//' > "$TMP/ir.$n" || true
    done
    awk -v a="$(cat "$TMP/ir.1")" -v b="$(cat "$TMP/ir.3")" 'BEGIN { printf "instructions a byte: %.1f (callgrind, (3 MiB - 1 MiB) / 2 MiB)\n", (b - a) / 2 / 1048576 }'
  fi
done
