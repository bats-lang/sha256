#!/usr/bin/env python3
"""Writes the static fixtures of the SHA256_K, SHA1_K and SHA256_IV proofs (sha256#75, #76 and #77, pieces of #31).

SHA256_K_t(t, high, low) states the definition (FIPS 180-4, section 4.2.2) as
its guard: x = i * 2^32 + 65536 * high + low has x^3 <= p * 2^96 < (x + 1)^3,
with p the (t+1)-th prime and i the integer part of its cube root. This
writes, from that definition alone (integer arithmetic, no table copied from
the standard), under tests/static:

  accept/sha256-k-used                 all 64 constructors at the definition's word
  reject/sha256-k-<t>-one-over         word t one bit too high (cube_fraction_le fails)
  reject/sha256-k-<t>-one-under        word t one bit too low (cube_fraction_gt fails)

for t in 0 to 63: 128 reject fixtures, each with the exact `expect`
(function, line, patsopt's error) that tests/static/expect.py demands.
patsopt stops at the first unsolved constraint of a function, so a fixture
holds one word and one direction.

SHA256_IV_mk states the definition (section 5.3.3) for each of the eight words
as its guard: word j, with p the (j+1)-th prime and i the integer part of its
square root, is x = i * 2^32 + 65536 * high + low with x^2 <= p * 2^64 <
(x + 1)^2. This writes, again from the definition alone:

  accept/sha256-iv-used                the constructor at the definition's eight words
  reject/sha256-iv-<j>-one-over        word j one bit too high (sqrt_fraction32_le fails)
  reject/sha256-iv-<j>-one-under       word j one bit too low (sqrt_fraction32_gt fails)

for j in 0 to 7: 16 reject fixtures.

  tests/static/make-sha256-k-fixtures.py          rewrite the fixtures
  tests/static/make-sha256-k-fixtures.py --check  fail when the committed
                                                  fixtures are not what this writes
                                                  (tests/static/run.sh runs it)

Python is used here because the package's tests already generate theirs with
it (tests/dynamic/*/make-expected.py, scripts/gen-fast-compress.py), and the
bats test tooling of the package has no generator to build on.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOML = """[package]
name = "%s"
kind = "bin"

[dependencies]
"arith" = ""
"array" = ""
"sha256" = ""
"""
PRELUDE = """#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

"""


def primes(count):
    found = []
    n = 2
    while len(found) < count:
        if all(n % q for q in found if q * q <= n):
            found.append(n)
        n += 1
    return found


def icbrt(n):
    """floor of the cube root of n, by integers"""
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def words():
    """(t, p, i, x): x = floor(cbrt(p) * 2^32), i its integer part"""
    out = []
    for t, p in enumerate(primes(64)):
        x = icbrt(p << 96)
        out.append((t, p, x >> 32, x))
    return out


def isqrt(n):
    """floor of the square root of n, by integers"""
    lo, hi = 0, 1
    while hi * hi <= n:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return lo


# SHA1_K constructors: (name, a t in its range, n); K = floor(sqrt(n) * 2^30)
SHA1_RANGES = (("0-to-19", 0, 2), ("20-to-39", 20, 3), ("40-to-59", 40, 5), ("60-to-79", 60, 10))


def sha1_words():
    """(name, t, n, x): x = floor(sqrt(n) * 2^30), from the definition"""
    return [(name, t, n, isqrt(n << 60)) for name, t, n in SHA1_RANGES]


def iv_words():
    """(j, p, i, x): x = floor(sqrt(p) * 2^32) for the first eight primes, i its integer part"""
    out = []
    for j, p in enumerate(primes(8)):
        x = isqrt(p << 64)
        out.append((j, p, x >> 32, x))
    return out


def halves(x, i):
    low_32 = x - (i << 32)
    assert 0 <= low_32 < (1 << 32)
    return low_32 >> 16, low_32 & 0xffff


def claim(t, high, low):
    return "$SHA.SHA256_K(%d, 0x%04x, 0x%04x) = $SHA.SHA256_K_%d()" % (t, high, low, t)


def accept():
    text = PRELUDE
    text += "(* every constant of the table as the cube-root definition gives it: all 64 constructors are accepted (sha256#31) *)\n"
    for t, p, i, x in words():
        high, low = halves(x, i)
        text += "prfn claim_%d (): %s\n" % (t, claim(t, high, low))
    text += "\nimplement main0 () = ()\n"
    return {"sha256-k-used": text}


def sha1_claim(name, t, x):
    return "$SHA.SHA1_K(%d, 0x%04x, 0x%04x) = $SHA.SHA1_K_%s()" % (t, x >> 16, x & 0xffff, name.replace("-", "_"))


def sha1_accept():
    text = PRELUDE
    text += "(* every constant of SHA-1 as the square-root definition gives it: all 4 constructors are accepted (sha256#31) *)\n"
    for name, t, n, x in sha1_words():
        text += "prfn claim_%s (): %s\n" % (name.replace("-", "_"), sha1_claim(name, t, x))
    text += "\nimplement main0 () = ()\n"
    return {"sha1-k-used": text}


def sha1_reject():
    out = {}
    for name, t, n, x in sha1_words():
        for direction, shift in (("over", 1), ("under", -1)):
            fixture = "sha1-k-%s-one-%s" % (name, direction)
            if direction == "over":
                guard, what = "sqrt_fraction_le", "x^2 <= n * 2^60"
            else:
                guard, what = "sqrt_fraction_gt", "n * 2^60 < (x + 1)^2"
            source = PRELUDE
            source += "(* K_%d one %s: %s fails, with x = floor(sqrt(n) * 2^30) (sha256#31) *)\n" % (t, direction, what)
            source += "prfn claim (): %s\n\nimplement main0 () = ()\n" % sha1_claim(name, t, x + shift)
            expect = "function claim\nline 7\n"
            expect += ("unsolved constraint: C3NSTRprop(C3TKmain(); S2Eapp(S2Ecst(%s); S2EVar(13991->S2Eintinf(%d)), "
                       "S2EVar(13992->S2Eintinf(%d)), S2Eintinf(%d)))\n"
                       % (guard, (x + shift) >> 16, (x + shift) & 0xffff, n))
            out[fixture] = (source, expect)
    return out


def iv_claim(values):
    """values: the eight x"""
    ws = ["$SHA.w32(0x%04x, 0x%04x)" % halves(x, x >> 32) for x in values]
    return ("$SHA.SHA256_IV($SHA.eight(%s,\n  %s)) =\n  $SHA.SHA256_IV_mk()"
            % (", ".join(ws[:4]), ", ".join(ws[4:])))


def iv_accept():
    text = PRELUDE
    text += "(* the initial value as the square-root definition gives it: the constructor is accepted (sha256#77) *)\n"
    text += "prfn claim (): %s\n\nimplement main0 () = ()\n" % iv_claim([x for j, p, i, x in iv_words()])
    return {"sha256-iv-used": text}


def iv_reject():
    out = {}
    exact = [x for j, p, i, x in iv_words()]
    for j, p, i, x in iv_words():
        for direction, shift in (("over", 1), ("under", -1)):
            name = "sha256-iv-%d-one-%s" % (j, direction)
            values = list(exact)
            values[j] = x + shift
            high, low = halves(x + shift, i)
            if direction == "over":
                guard, what = "sqrt_fraction32_le", "x^2 <= p * 2^64"
            else:
                guard, what = "sqrt_fraction32_gt", "p * 2^64 < (x + 1)^2"
            source = PRELUDE
            source += "(* H(0)_%d one %s: %s fails, with x = floor(sqrt(p) * 2^32) (sha256#77) *)\n" % (j, direction, what)
            source += "prfn claim (): %s\n\nimplement main0 () = ()\n" % iv_claim(values)
            # the constructor is on line 9; patsopt numbers the two halves' variables 14022 + 2j and 14023 + 2j
            expect = "function claim\nline 9\n"
            expect += ("unsolved constraint: C3NSTRprop(C3TKmain(); S2Eapp(S2Ecst(%s); S2Eintinf(%d), "
                       "S2EVar(%d->S2Eintinf(%d)), S2EVar(%d->S2Eintinf(%d)), S2Eintinf(%d)))\n"
                       % (guard, i, 14022 + 2 * j, high, 14023 + 2 * j, low, p))
            out[name] = (source, expect)
    return out


def reject():
    out = {}
    for t, p, i, x in words():
        for direction, shift in (("over", 1), ("under", -1)):
            name = "sha256-k-%d-one-%s" % (t, direction)
            high, low = halves(x + shift, i)
            if direction == "over":
                guard, what = "cube_fraction_le", "x^3 <= p * 2^96"
            else:
                guard, what = "cube_fraction_gt", "p * 2^96 < (x + 1)^3"
            source = PRELUDE
            source += "(* K_%d one %s: %s fails, with x = floor(cbrt(p) * 2^32) (sha256#31) *)\n" % (t, direction, what)
            source += "prfn claim (): %s\n\nimplement main0 () = ()\n" % claim(t, high, low)
            expect = "function claim\nline 7\n"
            expect += ("unsolved constraint: C3NSTRprop(C3TKmain(); S2Eapp(S2Ecst(%s); S2Eintinf(%d), "
                       "S2EVar(13974->S2Eintinf(%d)), S2EVar(13975->S2Eintinf(%d)), S2Eintinf(%d)))\n"
                       % (guard, i, high, low, p))
            out[name] = (source, expect)
    return out


def files():
    """path (under tests/static) -> text"""
    out = {}
    for name, text in list(accept().items()) + list(sha1_accept().items()) + list(iv_accept().items()):
        out["accept/%s/bats.toml" % name] = TOML % name
        out["accept/%s/src/bin/%s.bats" % (name, name)] = text
    for name, (source, expect) in list(reject().items()) + list(sha1_reject().items()) + list(iv_reject().items()):
        out["reject/%s/bats.toml" % name] = TOML % name
        out["reject/%s/expect" % name] = expect
        out["reject/%s/src/bin/%s.bats" % (name, name)] = source
    return out


def present():
    """every file under the directories this owns: accept/sha256-k-used and reject/sha256-k-*"""
    out = set()
    for kind, prefix in (("accept", "sha256-k-used"), ("accept", "sha1-k-used"), ("accept", "sha256-iv-used"), ("reject", "sha256-k-"), ("reject", "sha1-k-"), ("reject", "sha256-iv-")):
        base = os.path.join(HERE, kind)
        for name in os.listdir(base):
            if name.startswith(prefix):
                for root, _, names in os.walk(os.path.join(base, name)):
                    for n in names:
                        out.add(os.path.relpath(os.path.join(root, n), HERE))
    return out


def main():
    want = files()
    if "--check" in sys.argv:
        bad = []
        for path, text in sorted(want.items()):
            full = os.path.join(HERE, path)
            if not os.path.isfile(full) or open(full).read() != text:
                bad.append(path)
        extra = sorted(present() - set(want))
        if bad or extra:
            for path in bad:
                print("differs from what the generator writes: tests/static/" + path)
            for path in extra:
                print("not written by the generator: tests/static/" + path)
            sys.exit(1)
        print("ok: %d files, 3 accept and %d reject fixtures" % (len(want), len(reject()) + len(sha1_reject()) + len(iv_reject())))
        return
    for path, text in want.items():
        full = os.path.join(HERE, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w") as f:
            f.write(text)


main()
