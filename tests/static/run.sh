#!/bin/sh
# Static tests. Each package under tests/static/accept/ must build
# (`bats build`: some errors, like a missing template instance, surface
# only when patsopt generates C); each under tests/static/reject/ must
# fail to, exactly as its `expect` says (quire#585): the function, the
# line of its src/bin/<name>.bats and patsopt's error word for word, and no
# other error. expect.py decides; a reject with no expect, an empty one or
# another error fails. expect_test.py tests expect.py itself and runs first.
# Fixtures depend on this checkout, which is uploaded to a scratch copy
# of the repository first.
#
# usage: tests/static/run.sh <repository-dir>   (bats must be on PATH)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
PYTHONDONTWRITEBYTECODE=1 python3 -I "$ROOT/tests/static/expect_test.py"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp -R "$1" "$TMP/repo"
(cd "$ROOT" && bats upload --repository "$TMP/repo" >/dev/null)
# Keep only the archive just uploaded, so lock cannot pick a published
# version instead (an uncommitted checkout uploads as <version>dev1,
# which sorts below a release of the same commit).
PKG=$(sed -n 's/^name *= *"\(.*\)"/\1/p' "$ROOT/bats.toml" | head -1)
NEW=$(ls -t "$TMP/repo/$PKG"/*.bats | head -1)
for a in "$TMP/repo/$PKG"/*.bats; do
  [ "$a" = "$NEW" ] || rm -f "$a" "$a.sha256"
done

fail=0
check() { # dir -> runs lock + build, log in $TMP/<name>.log
  w="$TMP/w-$(basename "$1")"
  rm -rf "$w"; cp -R "$1" "$w"
  # --dev: the checkout uploads as a dev version, which bats lock skips
  # without it (as the Rust bats does).
  (cd "$w" && bats lock --dev --repository "$TMP/repo" && bats build --only debug --only native --repository "$TMP/repo") \
    > "$TMP/$(basename "$1").log" 2>&1
}

for d in "$ROOT"/tests/static/accept/*/; do
  [ -d "$d" ] || continue
  n=$(basename "$d")
  if check "$d"; then echo "ok   accept/$n"
  else echo "FAIL accept/$n: should build"; grep -E 'error' "$TMP/$n.log" | head -5; fail=1; fi
done

for d in "$ROOT"/tests/static/reject/*/; do
  [ -d "$d" ] || continue
  n=$(basename "$d")
  if check "$d"; then echo "FAIL reject/$n: should be rejected"; fail=1
  elif python3 -I "$ROOT/tests/static/expect.py" "$d" "$TMP/$n.log" > "$TMP/$n.expect" 2>&1; then echo "ok   reject/$n"
  else echo "FAIL reject/$n: rejected, but not as its expect says: $(cat "$TMP/$n.expect")"; grep -E 'error' "$TMP/$n.log" | head -5; fail=1; fi
done
exit $fail
